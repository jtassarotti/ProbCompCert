(** * Semantics of the Stanlight language.

  See Stanlight.v for the syntax.

  The semantics of a program is a function from data to a posterior
  distribution on parameters.

  To achieve this, the semantics is divided up into two parts, an operational layer and
  a denotational layer.  The operational layer gives a small-step
  semantics for Stanlight programs in a style similar to how CompCert
  specifies small-step semantics for all of its IRs. The denotational layer
  defines a probability distribution on the program's parameters using
  the operational layer.

  Note: Stan's built-ins for various mathematical operations and
  distributions are not modeled as primitive parts of the
  semantics. Instead, these are represented as function calls in the
  AST, and in all proofs, we shall implicitly assume there is some
  ambient environment. We assume that this environment contains the
  math operations (exp, logit, etc.) that the compiler inserts, but
  otherwise make no assumptions. This is because the compiler does not
  need to reason about the semantics of those distributions for its
  transformations as it does not change them.

*)

From Coq Require Import Reals Psatz ssreflect Utf8.
Require Import Coqlib Errors Maps String.
Local Open Scope string_scope.
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs.
Require Import Ctypes Stanlight.
Require Import Smallstep.
Require Import Linking.
Require Import IteratedRInt.
Require Import Sop.
Require Import ParamMap.
Require Import StanEnv.
Require Vector.

Set Bullet Behavior "Strict Subproofs".

Require Import Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

Definition genv := Genv.t fundef variable.

Definition globalenv (p: program) := Genv.globalenv p.

Definition env := param_mem val.

Definition empty_env: env := empty _.

(* Helper definitions for accessing locations from CompCert's memory model based on their
   size/reference type *)

Definition access_mode (ty: basic) : mode :=
  match ty with
  | Bint => By_value Mint32
  | Breal => By_value Mfloat64
  | Barray _ _ => By_reference
  | Bfunction _ _ => By_reference
end.

Fixpoint sizeof (t: basic) : Z :=
  match t with
  | Bint => 4
  | Breal => 8
  | Barray t' n => sizeof t' * Z.max 0 n
  | Bfunction _ _ => 1
  end.

(* Deref a pointer (i.e. a block b + pointer offset ofs) from memory m. *)

Inductive deref_loc (ty: basic) (m: mem) (b: block) (ofs: ptrofs) : val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs (Vptr b ofs).

(* Assign through a pointer (i.e. a block b + pointer offset ofs) from memory m. *)

Inductive assign_loc (ce: genv) (ty: basic) (m: mem) (b: block) (ofs: ptrofs): val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs v m'.

Section SEMANTICS.

(* This section defines the operational semantics for Stanlight programs.
   We follow the CompCert framework for small step semantics which involves 4 ingredients:

   (1) a type of program states
   (2) a small step transition relation between states
   (3) a predicate classifying which states are valid initial states

   (4) a relation classifying which states are valid final states, and
   the return value from reaching such a final state.

 *)

Variable ge: genv.

Inductive alloc_variables: env -> list (ident * basic) -> env -> Prop :=
  | alloc_variables_nil:
      forall e,
      alloc_variables e nil e
  | alloc_variables_cons:
      forall e id ty vars e2,
      alloc_variables (setv e id (Z.to_nat (sizeof ty)) Vundef) vars e2 ->
      alloc_variables e ((id, ty) :: vars) e2.

Section EXPR.

(* Evaluation of expressions is done in a big-step style. The evaluation relation is indexed by a number of parameters,
   which we represent as Variables in this section: *)

(* A CompCert env and memory *)
Variable e: env.
Variable m: mem.
(* parameter "memory" is a mapping from parameter ids + offsets to floats, in contrast
  to the CompCert memory m which is indexed by memory addresses + offsets *)
Variable pm : param_mem float.
(* the current value of the distinguished "target" variable *)
Variable t: float.

(* We reuse CompCert's model of various operations like addition, multiplication, etc.
   In C, the meaning of, say `x + y` depends upon the typos of x and y, so in CompCert,
   the semantics of such operations are indexed by the types of the operands. Thus, we need
   to map Stanlight types down to the analogous C types *)

Fixpoint transf_type (t: basic) : type :=
  match t with
  | Bint => tint
  | Breal => tdouble
  | Barray ty i => tarray (transf_type ty) i
  | Bfunction tl rty => Tfunction (transf_typelist tl) (transf_type rty) AST.cc_default
  end
with transf_typelist (tl: basiclist) : typelist :=
  match tl with
  | Bnil =>  Tnil
  | Bcons t tl => Ctypes.Tcons (transf_type t) (transf_typelist tl)
  end.

(* Converting Stanlight operations into corresponding CompCert operations *)
Definition unary_op_conversion (op: u_op): unary_operation :=
  match op with
  | PNot => Onotbool
  end.

Definition binary_op_conversion (op: b_op): binary_operation :=
  match op with
  | Stanlight.Plus => Oadd
  | Minus => Osub
  | Times => Omul
  | Divide => Odiv
  | Modulo => Omod
  | Or => Oor
  | And => Oand
  | Equals => Oeq
  | NEquals => One
  | Less => Olt
  | Leq => Ole
  | Greater => Ogt
  | Geq => Oge
  end.

(* This captures that an external call of a particular function does not
   depend on the memory, i.e. if it returned the result vres in memory m,
   it will also do so in memory m'. *)
Definition no_mem_dep ef ge vargs m vres : Prop :=
  external_call ef ge vargs m E0 vres m ->
  forall m', external_call ef ge vargs m' E0 vres m'.

(* Evaluation of expressions -- compare with Clight *)

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int: forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float: forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Eunop: forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation (unary_op_conversion op) v1 (transf_type (typeof a)) = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation (PTree.empty composite) (binary_op_conversion op) v1 (transf_type (typeof a1)) v2 (transf_type (typeof a2)) = Some v ->
      eval_expr (Ebinop a1 op a2 ty) v
  (* To model calls a(al) where al is a list of arguments, we first
      (1) evaluate a to the function identifier vf
      (2) evaluate the arguemtns al to vargs
      (3) lookup the function in the environment, which is presumed to be an external

      Then we check to see if the function evaluates to some value vres with an empty
      trace of events and does not modify the memory m. If so, that is the return value.

      Thus, external calls to functions that could modify memory / emit events are UB. But this is
      appropriate for the fragment of Stan we consider *)
  | eval_Ecall: forall a al vf ef name sig fd vargs tyargs ty vres tyres cconv,
      eval_expr a vf ->
      eval_exprlist al vargs ->
      Genv.find_funct ge vf = Some fd ->
      ef = EF_external name sig ->
      fd = External ef tyargs tyres cconv ->
      (* External calls must not (1) modify memory or (2) emit an observable trace event *)
      external_call ef ge vargs m E0 vres m ->
      eval_expr (Ecall a al ty) vres
  | eval_Etarget: forall ty,
      eval_expr (Etarget ty) (Vfloat t)
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (transf_type (typeof a)) (transf_type ty) = Some v ->
      eval_expr (Ecast a ty) v
  (* Looking up variables is handled differently depending on if the variable is a pointer, data, or otherwise: *)
  (* Looking up local variables *)
  | eval_Elvalue: forall a id ofs v,
      eval_llvalue a id ofs ->
      ParamMap.get e id (Ptrofs.intval ofs) = Some v ->
      eval_expr a v
  (* Looking up parameters *)
  | eval_Eplvalue: forall a id ofs f,
      eval_llvalue a id ofs ->
      ParamMap.is_id_alloc e id = false ->
      ParamMap.get pm id (Ptrofs.intval ofs) = Some f ->
      eval_expr a (Vfloat f)
  (* Looking up globals *)
  | eval_Eglvalue: forall a loc ofs v,
      eval_glvalue a loc ofs ->
      deref_loc (typeof a) m loc ofs v ->
      eval_expr a v

with eval_llvalue: expr -> ident -> ptrofs -> Prop :=
  | eval_Evar_st: forall id ty,
      eval_llvalue (Evar id ty) id Ptrofs.zero
  | eval_Eindexed_st: forall id al tya ty v,
      eval_exprlist al ((Vint v) :: nil) ->
      eval_llvalue (Eindexed (Evar id tya) al ty) id (Ptrofs.of_int v)

(* These handle evaluation of a pointer variable into an address/offset value: *)
with eval_glvalue: expr -> block -> ptrofs -> Prop :=
  | eval_Evar_global: forall id l ty,
      ParamMap.is_id_alloc pm id = false ->
      ParamMap.is_id_alloc e id = false ->
      Genv.find_symbol ge id = Some l ->
      eval_glvalue (Evar id ty) l Ptrofs.zero
  | eval_Eindexed: forall id al tya ty l v,
      eval_glvalue (Evar id tya) l Ptrofs.zero->
      eval_exprlist al ((Vint v) :: nil) ->
      eval_glvalue (Eindexed (Evar id tya) al ty) l (Ptrofs.of_int v)

with eval_exprlist: exprlist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist Enil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr a1 v1 ->
      eval_exprlist al vl ->
      eval_exprlist (Econs a1 al) (v1 :: vl).

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind2 := Minimality for eval_exprlist Sort Prop
  with eval_llvalue_ind2 := Minimality for eval_llvalue Sort Prop
  with eval_glvalue_ind2 := Minimality for eval_glvalue Sort Prop.
Combined Scheme eval_exprs_ind from eval_expr_ind2, eval_exprlist_ind2, eval_llvalue_ind2, eval_glvalue_ind2.

End EXPR.

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont (* Kseq s2 k = after s1 in s1;s2 *)
  | Kfor: ident -> expr -> statement -> cont -> cont
        (* Kfor i e2 s k = runs after s in for(i = e1 to e2) { s } *)
  .

(* States for the small step relation. Many of these parameters are
   similar to in Clight and other CompCert languages. Important
   differences are (1) the parameter t which represents the value of
   the target float variable, and (2) the parameter pm which stores
   the values of parameters. *)

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (t: float)
      (k: cont)
      (e: env)
      (m: mem)
      (pm: param_mem float)
  | Start
      (f: function)
      (s: statement)
      (t: float)
      (e: env)
      (m: mem)
      (pm: param_mem float)
  | Return
      (t: float)
    : state.

Definition var_names (vars: list(ident * basic)) : list ident :=
  List.map (@fst ident basic) vars.

(* Small step relation between program states. The interesting cases are tilde and target *)
Inductive step: state -> trace -> state -> Prop :=
  | step_start : forall f s t e m pm,
      step (Start f s t e m pm)
        E0 (State f s t Kstop e m pm)

  | step_return : forall f t e m pm,
      step (State f Sskip t Kstop e m pm)
        E0 (Return t)

  | step_skip_seq: forall f t s k e m pm,
      step (State f Sskip t (Kseq s k) e m pm)
        E0 (State f s t k e m pm)

  | step_seq: forall f t s1 s2 k e m pm,
    step (State f (Ssequence s1 s2) t k e m pm) E0 (State f s1 t (Kseq s2 k) e m pm)

  (* TODO: we so far only give sem to case where Bop is none *)
  | step_assign_env: forall f t a1 a2 k e m pm id ofs v2 e',
      eval_llvalue e m pm t a1 id ofs ->
      eval_expr e m pm t a2 v2 ->
      ParamMap.store e id (Ptrofs.intval ofs) v2 = Some e' ->
      step (State f (Sassign a1 None a2) t k e m pm)
        E0 (State f Sskip t k e' m pm)

  | step_assign_mem: forall f t a1 a2 k e m pm loc ofs v2 v m',
      eval_glvalue e m pm t a1 loc ofs ->
      eval_expr e m pm t a2 v2 ->
      sem_cast v2 (transf_type (typeof a2)) (transf_type (typeof a1)) = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      step (State f (Sassign a1 None a2) t k e m pm)
        E0 (State f Sskip t k e m' pm)

  | step_ifthenelse: forall f t a s1 s2 k e m pm v1 b,
    eval_expr e m pm t a v1 ->
    bool_val v1 (transf_type (typeof a)) = Some b ->
    step (State f (Sifthenelse a s1 s2) t k e m pm) E0 (State f (if b then s1 else s2) t k e m pm)

  (* target += a -- evaluate a, add to the designated target variable t; a must evaluate to a float *)
  | step_target: forall f t a v k e m pm,
    eval_expr e m pm t a (Vfloat v) ->
    step (State f (Starget a) t k e m pm) E0 (State f Sskip (Floats.Float.add t v) k e m pm)

  (* a ~ ad(al) -- evaluate a, ad, al -- ad should yield a function f and we call f(a, al) to get
     a value that is added to target. The distribution function f cannot modify memory/generate traces *)
  | step_tilde: forall f t a ad al v k e m pm vf vargs vres ef name sig tyargs tyres cconv fd,
    eval_expr e m pm t ad vf ->
    eval_expr e m pm t a v ->
    eval_exprlist e m pm t al vargs ->
    Genv.find_funct ge vf = Some fd ->
    ef = EF_external name sig ->
    fd = External ef tyargs tyres cconv ->
    (* External calls must not (1) modify memory or (2) emit an observable trace event *)
    external_call ef ge (v :: vargs) m E0 (Vfloat vres) m ->
    step (State f (Stilde a ad al) t k e m pm) E0 (State f Sskip (Floats.Float.add t vres) k e m pm)

  | step_for_start_true: forall f i a1 a2 s t k e m pm loc ofs v1 e' v2,
    eval_llvalue e m pm t (Evar i Bint) loc ofs ->
    eval_expr e m pm t a1 (Values.Vint v1) ->
    eval_expr e m pm t a2 (Values.Vint v2) ->
    ParamMap.store e loc (Ptrofs.intval ofs) (Values.Vint v1) = Some e' ->
    (Int.unsigned v1 <= Int.unsigned v2)%Z ->
    step (State f (Sfor i a1 a2 s) t k e m pm) E0
         (State f s t (Kfor i a2 s k) e' m pm)
  (* TODO: the manual is ambiguous as to whether if
     you have for (n in 2:1) { } whether n will have 2 outside the loop.
     Here we assume not *)
  | step_for_start_false: forall f i a1 a2 s t k e m pm v1 v2,
    eval_expr e m pm t a1 (Values.Vint v1) ->
    eval_expr e m pm t a2 (Values.Vint v2) ->
    ¬ (Int.unsigned v1 <= Int.unsigned v2)%Z ->
    step (State f (Sfor i a1 a2 s) t k e m pm) E0
         (State f Sskip t k e m pm)
  | step_for_iter_true: forall f i a2 s t k e m pm loc ofs v1 (e' : env) v2,
    eval_llvalue e m pm t (Evar i Bint) loc ofs ->
    ParamMap.get e loc (Ptrofs.intval ofs) = Some (Values.Vint v1) ->
    eval_expr e m pm t a2 (Values.Vint v2) ->
    ParamMap.store e loc (Ptrofs.intval ofs) (Values.Vint (Int.add v1 Int.one) : val) = Some e' ->
    (Int.unsigned v1 < Int.unsigned v2)%Z ->
    step (State f Sskip t (Kfor i a2 s k) e m pm) E0
         (State f s t (Kfor i a2 s k) e' m pm)
  | step_for_iter_false: forall f i a2 s t k e m pm loc ofs v1 v2,
    eval_llvalue e m pm t (Evar i Bint) loc ofs ->
    ParamMap.get e loc (Ptrofs.intval ofs) = Some (Values.Vint v1) ->
    eval_expr e m pm t a2 (Values.Vint v2) ->
    ¬ (Int.unsigned v1 < Int.unsigned v2)%Z ->
    step (State f Sskip t (Kfor i a2 s k) e m pm) E0
         (State f Sskip t k e m pm)
.

Fixpoint type_of_basic (b: basic) : Type :=
  match b with
  | Bint => Z
  | Breal => Floats.float
  | Barray b z => Vector.t (type_of_basic b) (Z.to_nat z)
  | _ => unit
  end.

Fixpoint type_of_basic_list (bs: list basic) : Type :=
  match bs with
  | nil => unit
  | b :: bs => type_of_basic b * type_of_basic_list bs
  end.

Definition data_signature (p : program) : Type :=
  type_of_basic_list (map snd (pr_data_vars p)).

Definition parameters_signature (p : program) : Type :=
  type_of_basic_list (map (fun '(_, b, _) => b) (pr_parameters_vars p)).

Definition data_basic_to_list (ib : ident * basic) : list (ident * basic * Ptrofs.int) :=
  match snd ib with
  | Bint => (ib, Ptrofs.zero) :: nil
  | Breal => (ib, Ptrofs.zero) :: nil
  | Barray b z => combine (repeat (fst ib, b) (Z.to_nat z)) (count_up_ofs (Z.to_nat z))
  | Bfunction _ _ => (ib, Ptrofs.zero) :: nil
  end.

Definition pr_parameters_ids (p: program) : list ident :=
  map (λ '(id, _, _), id) (pr_parameters_vars p).

Definition parameter_basic_to_list (ibf : ident * basic * option (expr -> expr)) : list (ident * basic * Ptrofs.int) :=
  data_basic_to_list (fst ibf).

Definition variable_to_list {A} (ib : ident * variable * A) : list (ident * variable * A) :=
  let '(i, v, a) := ib in
  match vd_type v with
  | Bint => ib :: nil
  | Breal => ib :: nil
  | Barray b z => repeat (i, {| vd_type := b; vd_constraint := vd_constraint v |}, a) (Z.to_nat z)
  | Bfunction _ _ => ib :: nil
  end.

(* Parameters and data can be arrays. However, when defining the
   denotational semantics, we need to integrate over the parameter
   space. Thus, it is useful to "flatten" the array of parameters as
   if a parameter real p[10] was really 10 parameters p0, ..., p9. The
   following helper functions flatten a list of parameters in this way
   *)

Definition flatten_data_list (ibs: list (ident * basic)) :
  list (ident * basic * Ptrofs.int) :=
  List.concat (map data_basic_to_list ibs).

Definition flatten_parameter_list (ibs: list (ident * basic * option (expr -> expr))) :
  list (ident * basic * Ptrofs.int) :=
  List.concat (map parameter_basic_to_list ibs).

Definition flatten_ident_variable_list {A} (ibs: list (ident * variable * A)) :=
  List.concat (map variable_to_list ibs).

(* The next several definitions are used for initializing program state with globals, parameters, etc. *)

Inductive assign_global_locs (ge: genv) : list (ident * basic * Ptrofs.int) -> mem -> list val -> mem -> Prop :=
  | assign_global_locs_nil : forall m,
      assign_global_locs ge nil m nil m
  | assign_global_locs_cons : forall m1 m2 m3 id ty ofs l v bs vs,
      Genv.find_symbol ge id = Some l ->
      assign_loc ge ty m1 l ofs v m2 ->
      assign_global_locs ge bs m2 vs m3 ->
      assign_global_locs ge ((id, ty, ofs) :: bs) m1 (v :: vs) m3.

Inductive reserve_global_params : list ident -> param_mem float -> param_mem float -> Prop :=
  | reserve_global_params_nil : forall m,
      reserve_global_params nil m m
  | reserve_global_params_cons : forall m1 m2 m3 id bs,
      ParamMap.reserve m1 id = m2 ->
      reserve_global_params bs m2 m3 ->
      reserve_global_params (id :: bs) m1 m3.

Inductive assign_global_params : list (ident * basic * Ptrofs.int) -> param_mem float -> list val -> param_mem float -> Prop :=
  | assign_global_params_nil : forall m,
      assign_global_params nil m nil m
  | assign_global_params_cons : forall m1 m2 m3 id ty ofs f bs vs,
      ParamMap.set m1 id (Ptrofs.intval ofs) f = m2 ->
      assign_global_params bs m2 vs m3 ->
      assign_global_params ((id, ty, ofs) :: bs) m1 ((Vfloat f) :: vs) m3.

Definition set_global_params ids flat_ids flat_vals pm1 pm2 :=
  exists pm_res, reserve_global_params ids pm1 pm_res /\
                 assign_global_params flat_ids pm_res flat_vals pm2.

Lemma reserve_global_preserves_alloc bs m1 m2 id :
  reserve_global_params bs m1 m2 ->
  is_id_alloc m2 id = false ->
  is_id_alloc m1 id = false.
Proof.
  induction 1.
  - rewrite //=.
  - intros Hfalse.
    exploit (IHreserve_global_params); auto. intros Hfalse'.
    eapply reserve_preserves_alloc_rev; try eassumption.
Qed.

Lemma assign_global_params_preserves_alloc bs m1 vs m2 id :
  assign_global_params bs m1 vs m2 ->
  is_id_alloc m2 id = false ->
  is_id_alloc m1 id = false.
Proof.
  induction 1.
  - rewrite //=.
  - intros Hfalse.
    exploit (IHassign_global_params); auto. intros Hfalse'.
    eapply set_preserves_alloc_rev; try eassumption.
Qed.

Lemma set_global_params_preserves_alloc ids bs m1 vs m2 id :
  set_global_params ids bs vs m1 m2 ->
  is_id_alloc m2 id = false ->
  is_id_alloc m1 id = false.
Proof.
  intros (?&?&?).
  intros.
  eapply reserve_global_preserves_alloc; eauto.
  eapply assign_global_params_preserves_alloc; eauto.
Qed.


Definition default {A : Type} (x : A) (o: option A) :=
  match o with
  | None => x
  | Some a => a
  end.

(* initial_state p d p describes a starting state of execution that
   has the lists d and p of data and parameters loaded into
   memory/param mapping *)
(* TODO: this initial state loading here will not be correct for nested array data/params *)

Inductive initial_state (p: program) (data : list val) (params: list val) : state -> Prop :=
  | initial_state_intro: forall b f m0 m1 e pm,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge $"model" = Some b ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      alloc_variables empty_env f.(fn_vars) e ->
      assign_global_locs ge (flatten_data_list p.(pr_data_vars)) m0 data m1 ->
      set_global_params (pr_parameters_ids p) (flatten_parameter_list p.(pr_parameters_vars))
                            params (ParamMap.empty float) pm ->
      initial_state p data params (Start f f.(fn_body) ((Floats.Float.of_int Integers.Int.zero)) e m1 pm).


(* We would like to represent a model block in a Stanlight program as
   operationally returning the target value computed by the model
   block.  However, CompCert's framework for operational semantics
   requires "return values" of a final state to be an integer (which
   makes sense for describing complete C programs). To work around
   this, we parameterize the predicate final_state by a float
   "testval". Then, the final_state returns 0 if at termination the
   target matches testval and 1 otherwise.

   This 0 vs. 1 convention may seem backwards from one expecting this to
   function like an "indicator" (where 1 is true), but we are adhering
   to the unix tradition where "0" return value is "normal" and 1 is
   exceptional. *)
Inductive final_state (testval: float) : state -> int -> Prop :=
  | final_state_match: forall t,
      testval = t ->
      final_state testval (Return t) Integers.Int.zero
  | final_state_nonmatch: forall t,
      testval <> t ->
      final_state testval (Return t) Integers.Int.one.

End SEMANTICS.

(* We can now assemble the pieces to define a semantics of a program p, as a function of
   data, params, and a testval *)

Definition semantics (p: program) (data: list val) (params: list val) (testval: float) :=
  let ge := Genv.globalenv p in
  Semantics_gen step (initial_state p data params) (final_state testval) ge ge.


(* The operational semantics just defined is deterministic, as we now
   prove. This is important for two reasons:

   (1) It lets us prove backwards simulation via proof of forward
       simulation (as in CompCert)

   (2) For the denotational semantics, we will want to interpret the
       operational semantics of a model block as defining a partial
       function that represents a probability density function. For
       this to make sense, we want the operational semantics to be
       deterministic so that the induced function has a unique value.

*)

Ltac determ_aux :=
    match goal with
    | [ H: eval_llvalue _ _ _ _ _ _ _ _  |- _ ] => try (inversion H; fail)
    | [ H: eval_glvalue _ _ _ _ _ _ _ _  |- _ ] => try (inversion H; fail)
    end.

Lemma assign_loc_determ ce ty m0 b ofs v m m' :
  assign_loc ce ty m0 b ofs v m ->
  assign_loc ce ty m0 b ofs v m' ->
  m' = m.
Proof.
  intros Hd1 Hd2. inv Hd1; inv Hd2; try congruence.
Qed.

Lemma deref_loc_determ ty m loc ofs v v' :
  deref_loc ty m loc ofs v ->
  deref_loc ty m loc ofs v' ->
  v' = v.
Proof.
  intros Hd1 Hd2. inv Hd1; inv Hd2; try congruence.
Qed.

Lemma eval_exprs_determ:
  forall (ge : genv) (sp: env) (m: mem) pm (t: float),
  (forall (e: expr) v, eval_expr ge sp m pm t e v ->
                         forall v', eval_expr ge sp m pm t e v' -> v' = v) /\
  (forall (e: exprlist) l, eval_exprlist ge sp m pm t e l ->
                         forall l', eval_exprlist ge sp m pm t e l' -> l' = l) /\
  (forall (e: expr) blk ofs, eval_llvalue ge sp m pm t e blk ofs ->
                         forall blk' ofs', eval_llvalue ge sp m pm t e blk' ofs' -> blk' = blk /\ ofs' = ofs) /\
  (forall (e: expr) blk ofs, eval_glvalue ge sp m pm t e blk ofs ->
                         forall blk' ofs', eval_glvalue ge sp m pm t e blk' ofs' -> blk' = blk /\ ofs' = ofs).
Proof.
  intros ge sp m pm t.
  apply (eval_exprs_ind ge sp m pm t); intros; try (inv H; auto; try determ_aux; auto; fail).
  - inv H2; auto; try determ_aux; auto. assert (v0 = v1) by eauto. congruence.
  - inv H4; auto; try determ_aux; auto.
    assert (v0 = v1) by eauto.
    assert (v3 = v2) by eauto. congruence.
  - inv H7; auto; try determ_aux; auto.
    assert (vargs0 = vargs) by eauto.
    assert (vf0 = vf) by eauto.
    assert (sig0 = sig) by congruence.
    assert (name0 = name) by congruence.
    subst.
    exploit external_call_determ. eexact H6. eexact H17.
    intros (?&Heq). symmetry; eapply Heq; auto.
  - inv H2; auto; try determ_aux; auto. assert (v0 = v1) by eauto. congruence.
  - inv H2; auto; try determ_aux; auto; exploit H0; eauto.
    { intros (->&->). congruence. }
    { inv H; inv H3; subst; try congruence.
      exploit (@gs_is_alloc val); eauto; intros; congruence.
      exploit (@gs_is_alloc val); eauto; intros; congruence.
    }
    { inv H; inv H3; subst; try congruence.
      { exploit (@gs_is_alloc val); eauto; intros. congruence. }
      { inv H10. exploit (@gs_is_alloc val); eauto; intros; congruence. }
    }
  - inv H3; auto; try determ_aux; auto; exploit H0; eauto.
    { intros (->&->). exploit (@gs_is_alloc val); eauto; intros; congruence. }
    { intros (->&->). congruence. }
    inv H; inv H4; try congruence.
    { exploit (@gs_is_alloc float); eauto; intros. congruence. }
    { inv H11. exploit (@gs_is_alloc float); eauto; intros. congruence. }
  - inv H2; auto; try determ_aux; auto; exploit H0; eauto.
    { inv H; inv H3; subst; try congruence.
      exploit (@gs_is_alloc val); eauto; intros; congruence.
      inv H2. exploit (@gs_is_alloc val); eauto; intros; congruence.
    }
    { inv H; inv H3; subst; try congruence.
      { exploit (@gs_is_alloc float); eauto; intros. congruence. }
      { inv H2. exploit (@gs_is_alloc float); eauto; intros; congruence. }
    }
    intros (->&->). eauto. eapply deref_loc_determ; eauto.
  - inv H3; auto; try determ_aux.
    f_equal; eauto.
  - inv H1; split; try determ_aux; exploit H0; eauto.
    inversion 1; subst. eauto.
  - inv H2; split; congruence.
  - inv H3. exploit H0; eauto.
    intros (->&_). split; auto.
    exploit H2; eauto. inversion 1; subst; eauto.
Qed.

Lemma eval_expr_determ:
  forall ge sp e m pm a v, eval_expr ge sp e m pm a v ->
  forall v', eval_expr ge sp e m pm a v' -> v' = v.
Proof.
  intros. eapply eval_exprs_determ; eauto.
Qed.

Lemma eval_exprlist_determ:
  forall ge sp e m pm al vl, eval_exprlist ge sp e m pm al vl ->
  forall vl', eval_exprlist ge sp e m pm al vl' -> vl' = vl.
Proof.
  intros. eapply eval_exprs_determ; eauto.
Qed.

Lemma eval_llvalue_determ:
  forall ge sp e m pm t blk vl, eval_llvalue ge sp e m pm t blk vl ->
  forall blk' vl', eval_llvalue ge sp e m pm t blk' vl' -> blk' = blk /\ vl' = vl.
Proof. intros. edestruct eval_exprs_determ as (E1&E2&E3&E4); eauto. Qed.

Lemma eval_glvalue_determ:
  forall ge sp e m pm t blk vl, eval_glvalue ge sp e m pm t blk vl ->
  forall blk' vl', eval_glvalue ge sp e m pm t blk' vl' -> blk' = blk /\ vl' = vl.
Proof.
  intros. eapply eval_exprs_determ; eauto.
Qed.

Lemma alloc_variables_determ:
  forall e0 vs e, alloc_variables e0 vs e ->
  forall e', alloc_variables e0 vs e' -> e' = e.
Proof.
  induction 1; intros e' A; inv A; auto.
Qed.

Lemma assign_global_locs_determ:
  forall ge ids m0 vs m, assign_global_locs ge ids m0 vs m ->
  forall m', assign_global_locs ge ids m0 vs m' -> m' = m.
Proof.
  induction 1; intros m' A; inv A; auto.
  assert (l0 = l) by congruence; subst.
  assert (m4 = m2) by (eapply assign_loc_determ; eauto); subst.
  eauto.
Qed.

Lemma reserve_global_params_determ:
  forall ids m0 m, reserve_global_params ids m0 m ->
  forall m', reserve_global_params ids m0 m' -> m' = m.
Proof.
  induction 1; intros m' A; inv A; auto.
Qed.

Lemma assign_global_params_determ:
  forall ids m0 vs m, assign_global_params ids m0 vs m ->
  forall m', assign_global_params ids m0 vs m' -> m' = m.
Proof.
  induction 1; intros m' A; inv A; auto.
Qed.

Lemma set_global_params_determ:
  forall ids flat_ids m0 vs m, set_global_params ids flat_ids vs m0 m ->
  forall m', set_global_params ids flat_ids vs m0 m' -> m' = m.
Proof.
  intros ????? (mint1&?&?) m' (mint2&?&?).
  exploit (reserve_global_params_determ ids m0 mint1); eauto.
  intros; subst.
  eapply assign_global_params_determ; eauto.
Qed.

Ltac Determ :=
  try congruence;
  match goal with
  | [ |- match_traces _ E0 E0 /\ (_ -> _) ]  =>
          split; [constructor|intros _; Determ]
  | [ H1: eval_expr _ _ _ _ _ ?a ?v1, H2: eval_expr _ _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_expr_determ; eauto);
          clear H1 H2; Determ
  | [ H1: eval_exprlist _ _ _ _ _ ?a ?v1, H2: eval_exprlist _ _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_exprlist_determ; eauto);
          clear H1 H2; Determ
  | [ H1: eval_llvalue _ _ _ _ _ ?a ?blk1 ?v1, H2: eval_llvalue _ _ _ _ _ ?a ?blk2 ?v2 |- _ ] =>
          assert (blk1 = blk2 /\ v1 = v2) as (?&?) by (eapply eval_llvalue_determ; eauto);
          clear H1 H2; Determ
  | [ H1: eval_glvalue _ _ _ _ _ ?a ?blk1 ?v1, H2: eval_glvalue _ _ _ _ _ ?a ?blk2 ?v2 |- _ ] =>
          assert (blk1 = blk2 /\ v1 = v2) as (?&?) by (eapply eval_glvalue_determ; eauto);
          clear H1 H2; Determ
  | _ => idtac
  end.

Lemma semantics_determinate:
  forall (p: program) data params tval, determinate (semantics p data params tval).
Proof.
  intros. constructor; set (ge := Genv.globalenv p); simpl; intros.
- (* determ *)
  inv H; inv H0; Determ.
  (*
  + subst vargs0. exploit external_call_determ. eexact H2. eexact H13.
    intros (A & B). split; intros; auto.
    apply B in H; destruct H; congruence.
   *)
  + subst v0.
    inv H1; inv H13.
    { exploit (@store_some_is_id_alloc val); eauto.
      intros; intuition congruence. }
    { inv H7. exploit (@store_some_is_id_alloc val); eauto.
      intros; intuition congruence. }
  + subst v0.
    inv H14; inv H1.
    { exploit (@store_some_is_id_alloc val); eauto.
      intros; intuition congruence. }
    { inv H9. exploit (@store_some_is_id_alloc val); eauto.
      intros; intuition congruence. }
  + subst v0. eauto. subst loc0. subst ofs0.
    assert (v1 = v) by congruence; subst.
    assert (m' = m'0) by (eapply assign_loc_determ; eauto). subst. eauto.
  + subst.
    assert (b0 = b) by congruence. subst. auto.
  + subst.
    assert (name0 = name) by congruence; subst.
    assert (sig0 = sig) by congruence; subst.
    exploit external_call_determ.
    { eapply H7. }
    { eapply H22. }
    intros Himpl. intuition congruence.
  + subst.
    assert (v2 = v3) by congruence; subst.
    assert (v1 = v0) by congruence; subst.
    intuition.
  + subst.
    assert (v2 = v3) by congruence; subst.
    assert (v1 = v0) by congruence; subst.
    intuition.
- (* single event *)
  red; simpl. destruct 1; simpl; try lia;
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0.
  assert (m0 = m2) by congruence; subst.
  unfold ge0, ge1 in *.
  assert (b0 = b) by congruence; subst.
  assert (f0 = f) by congruence; subst.
  exploit alloc_variables_determ. eexact H4. eexact H9. intros; subst.
  exploit assign_global_locs_determ. eexact H5. eexact H10. intros; subst.
  exploit set_global_params_determ. eexact H6. eexact H11. intros; subst.
  eauto.
- (* nostep final state *)
  red; intros; red; intros. inv H; inv H0.
- (* final states *)
  inv H; inv H0; auto; try congruence.
Qed.

Lemma semantics_receptive:
  forall (p: program) data params tval, receptive (semantics p data params tval).
Proof.
  intros.
  set (ge := globalenv p). constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step ge s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
(* trace length *)
  red; simpl; intros. inv H; simpl; try lia.
Qed.

Axiom variable_eq: forall (ty1 ty2: variable), {ty1=ty2} + {ty1<>ty2}.

Global Program Instance LV: Linker variable := {
  link := fun t1 t2 => if variable_eq t1 t2 then Some t1 else None;
  linkorder := fun t1 t2 => t1 = t2
}.
Next Obligation.
destruct (variable_eq x y); inversion H; subst; auto.
Defined.

Axiom program_eq: forall (ty1 ty2: program), {ty1=ty2} + {ty1<>ty2}.

Global Program Instance Linker_program: Linker program := {
  link := fun t1 t2 => if program_eq t1 t2 then Some t1 else None;
  linkorder := fun t1 t2 => t1 = t2
}.
Next Obligation.
destruct (program_eq x y); inversion H; subst; auto.
Defined.

Require ClassicalEpsilon.

Section DENOTATIONAL.

(* This section defines the denotational semantics of programs.  The
   strategy (already alluded to above) is to interpret the operational
   semantics as inducing a partial function that defines a probability
   density, which is then integrated and normalized to give a
   distribution.

 *)

  (* returns_target_value p data params t holds if it is possible for p to go from an
     initial state with data and params loaded to a final state with t as the target value *)
  Definition returns_target_value (p: program) (data: list val) (params: list val) (t: float) :=
    exists s1 s2,
      Smallstep.initial_state (semantics p data params t) s1 /\
        Star (semantics p data params t) s1 E0 s2 /\
        Smallstep.final_state (semantics p data params t) s2 Integers.Int.zero.

  (* Alternate versions for paper *)
  Definition returns_target_value' (p: program) (data: list val) (params: list val) (t: float) :=
    exists s1,
      Smallstep.initial_state (semantics p data params t) s1 /\
        Star (semantics p data params t) s1 E0 (Return t).

  Lemma returns_target_value_equiv p data params t :
    returns_target_value p data params t <->
      returns_target_value' p data params t.
  Proof.
    split.
    - intros (s1&s2&Hinit&Hstar&Hfin). inv Hfin.
      { eexists; split; eauto. }
    - intros (s1&Hinit&Hstar). exists s1. eexists; split; eauto.
      split; eauto. econstructor. auto.
  Qed.

   (* The above definition defines a _relation_ from which we want to obtain a _function_
      of type program -> list val -> list val -> Real

     To do so we will use Hilbert's Epsilon operator, which lets us define a Coq function
     from a predicate. We wrap this up in the following helper function, pred_to_default_fun.

     Given a predicate P : V -> Prop, pred_to_default_fun P default will return
     an arbitrary value v such that P v holds, if such a v exists, and otherwise returns default. *)

  Definition pred_to_default_fun {V: Type} (P: V -> Prop) (default: V) : V :=
    let s := ClassicalEpsilon.excluded_middle_informative (exists v : V, P v) in
    match s with
    | left e => let (x, _) := ClassicalEpsilon.constructive_indefinite_description P e in x
    | right _ => default
    end.

  Lemma pred_to_default_fun_spec1 {V: Type} (P: V -> Prop) (default: V) :
    (∃ v, P v /\ pred_to_default_fun P default = v) \/
      ((∀ v, ¬ P v) /\ pred_to_default_fun P default = default).
  Proof.
    rewrite /pred_to_default_fun.
    destruct ClassicalEpsilon.excluded_middle_informative.
    - destruct ClassicalEpsilon.constructive_indefinite_description; eauto.
    - right. firstorder.
  Qed.

  Lemma pred_to_default_fun_default {V: Type} (P: V -> Prop) (default: V) :
   (∀ v, ¬ P v) -> pred_to_default_fun P default = default.
  Proof.
    intros Hnex.
    rewrite /pred_to_default_fun.
    destruct ClassicalEpsilon.excluded_middle_informative.
    - exfalso; firstorder.
    - auto.
  Qed.

  (* We now apply pred_to_default_fun to the returns_target_value predicate we defined above, thereby
     obtaining the log density induced by the model block.

     This returns the final target value if one can be obtained from running the program, otherwise
     returns Float.zero, and then we coerce these floats to coq Reals (R) using IFR. *)
  Definition log_density_of_program (p: program) (data: list val) (params: list val) : R :=
    IFR (pred_to_default_fun (returns_target_value p data params) Float.zero).

  Lemma star_determinacy_nostep L:
    determinate L ->
    forall s t s', Star L s t s' -> Nostep L s' ->
                    forall s'', Star L s t s'' -> Nostep L s'' -> s' = s''.
  Proof.
    intros Hdeterm s t s' Hstar Hno s'' Hstar'' Hno''.
    exploit star_determinacy.
    { exact Hdeterm. }
    { eexact Hstar. }
    { eexact Hstar''. }
    intros [Hstep1|Hstep2].
    { inv Hstep1; auto. exfalso. eapply Hno; eauto. }
    { inv Hstep2; auto. exfalso. eapply Hno''; eauto. }
  Qed.

  (* Because the semantics is determinstic, return_target_value is deterministic *)
  Lemma returns_target_value_determ p data params t t' :
    returns_target_value p data params t ->
    returns_target_value p data params t' ->
    t' = t.
  Proof.
    rewrite /returns_target_value.
    intros (s1&s2&Hinit&Hstar&Hfin).
    intros (s1'&s2'&Hinit'&Hstar'&Hfin').
    assert (s1' = s1).
    { eapply sd_initial_determ; eauto using semantics_determinate. }
    subst.
    assert (s2' = s2).
    { eapply star_determinacy_nostep; eauto using semantics_determinate, sd_final_nostep.
      inversion Hfin; subst.
      intros ?? Hstep. inv Hstep.
    }
    subst.
    inv Hfin.
    inv Hfin'. auto.
  Qed.

  Lemma log_density_of_program_trace p data params t :
    returns_target_value p data params t ->
    log_density_of_program p data params = IFR t.
  Proof.
    intros Hreturns.
    rewrite /log_density_of_program. f_equal.
    rewrite /pred_to_default_fun.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hv|Hnv]; last first.
    { exfalso. apply Hnv. eauto. }
    destruct ClassicalEpsilon.constructive_indefinite_description as [v' Hv']; last first.
    eapply returns_target_value_determ; eauto.
  Qed.

  (* The model block defines the _log_ density, so we must exponentiate before integrating *)
  Definition density_of_program (p: program) (data: list val) (params: list val) : R :=
    exp (log_density_of_program p data params).

  (* The model block specifies an _unnormalized_ density, which we
     must normalize to get a probability distribution. However, when
     normalizing, we only want to consider the probabilities of
     parameter values that respect the constraints specified by the
     program. Thus, we map these constraints into intervals over the
     reals, which will give the bounds of integration. *)

  Definition constraint_to_interval (c: constraint) :=
    match c with
    | Cidentity => mk_interval m_infty p_infty
    | Clower f  => mk_interval (IFR f) p_infty
    | Cupper f  => mk_interval m_infty (IFR f)
    | Clower_upper f1 f2 => mk_interval (IFR f1) (IFR f2)
    end.

  (* A "rectangle" is a product of intervals. We represent these
     either as a dependent type rectangle n or as a list of arbitrary
     length. The following definitions are indicator functions that return 1 when a
     vector or list of reals lies within a specified rectangle, and 0 otherwise. *)

  Definition rect_list_indicator (rt: rectangle_list) (v: list R) : R.
    destruct (ClassicalEpsilon.excluded_middle_informative (in_list_rectangle v rt)).
    - exact 1.
    - exact 0.
  Defined.

  Definition rect_indicator {n} (rt: rectangle n) (v: Vector.t R n) : R.
    destruct (ClassicalEpsilon.excluded_middle_informative (in_rectangle v rt)).
    - exact 1.
    - exact 0.
  Defined.

  Definition default_var : variable :=
    {| vd_type := Breal; vd_constraint := Cidentity |}.

  Definition is_gvar {F V: Type} (vd: globdef F V) :=
    match vd with
    | Gvar _ => true
    | _ => false
    end.

  Definition lookup_def_ident (p: program) (id: ident) :=
    match List.find (fun '(id', v) => positive_eq_dec id id' && is_gvar v) (pr_defs p) with
    | Some (_, Gvar v) => (id, gvar_info v)
    | _ => (id, default_var)
    end.

  Lemma list_find_fst_forall2 {A B: Type} (P: A * B -> bool) (l1 l2: list (A * B))
    (Q: (A * B) -> (A * B) -> Prop):
    list_forall2 Q l1 l2 ->
    (forall x1 x2, Q x1 x2 -> fst x1 = fst x2) ->
    (forall x1 x2, Q x1 x2 -> P x1 = P x2) ->
    (exists a b1 b2, find P l1 = Some (a, b1) /\ find P l2 = Some (a, b2) /\ Q (a, b1) (a, b2)) \/
     (find P l1 = None /\ find P l2 = None).
  Proof.
    induction 1.
    - intros. right => //=.
    - intros HQ HQP. simpl.
      destruct a1 as (a&b).
      destruct b1 as (a'&b').
      assert (a'= a).
      { exploit HQ; eauto. }
      subst.
      destruct (P (a, b)) eqn:HPa1.
      * assert (P (a, b') = true) as ->.
        { rewrite -HPa1. symmetry. eapply HQP; eauto. }
        left. exists a, b, b'. repeat split; auto.
      * assert (P (a, b') = false) as ->.
        { rewrite -HPa1. symmetry. eapply HQP; eauto. }
        eapply IHlist_forall2; eauto.
  Qed.

  (* Again it is necessary to "flatten" the arrays of parameters into a list so we can talk about
     the rectangle that corresponds to the parameter space *)
  Definition flatten_parameter_variables (p: program) :=
    flatten_ident_variable_list (map (fun '(id, _, f) => (lookup_def_ident p id, f)) (pr_parameters_vars p)).

  Definition flatten_parameter_constraints (p: program) : list constraint :=
    map (fun '(id, v, _) => vd_constraint v) (flatten_parameter_variables p).

  Definition flatten_parameter_out (p: program) : list (expr -> expr) :=
    map (fun '(_, v, f) => default (fun x => x) f) (flatten_parameter_variables p).

  Definition parameter_dimension (p: program) : nat :=
    List.length (map (constraint_to_interval) (flatten_parameter_constraints p)).

  Definition parameter_list_rect p :=
   (map (constraint_to_interval) (flatten_parameter_constraints p)).

  Definition parameter_rect (p: program) : rectangle (parameter_dimension p) :=
    Vector.of_list (parameter_list_rect p).

  (* We can use the same pred_to_default_fun to get a function that returns what an expression would evaluate to.
     It is necessary to specify some default memory/target values in which the expression will evaluate to,
     we choose empty here. *)
  Definition eval_expr_fun p a :=
    pred_to_default_fun (eval_expr (globalenv p) empty_env Mem.empty (ParamMap.empty float)
                           (Float.zero) a) (Vfloat (Float.zero)).

  Lemma eval_expr_fun_spec p a v :
    eval_expr (globalenv p) empty_env Mem.empty (ParamMap.empty float) (Float.zero) a v ->
    eval_expr_fun p a = v.
  Proof.
    intros Hexp. rewrite /eval_expr_fun/pred_to_default_fun.
    destruct (ClassicalEpsilon.excluded_middle_informative _) as [(?&Hx)|Hn] => /=; last first.
    { exfalso. eapply Hn. eexists; eauto. }
    destruct (ClassicalEpsilon.constructive_indefinite_description _).
    eapply eval_expr_determ; eauto.
  Qed.


  Definition sub_external_funct (ge1 ge2: Genv.t fundef variable) :=
    ∀ vf name sig tyargs tyres cconv,
      Genv.find_funct ge1 vf = Some (External (EF_external name sig) tyargs tyres cconv) ->
      Genv.find_funct ge2 vf = Some (External (EF_external name sig) tyargs tyres cconv).

  Definition match_external_funct ge1 ge2 := sub_external_funct ge1 ge2 /\ sub_external_funct ge2 ge1.

  Definition match_find_symbol {F V} (ge1 ge2 : Genv.t F V) :=
    ∀ s : ident, Genv.find_symbol ge1 s = Genv.find_symbol ge2 s.

  Lemma eval_expr_match_aux ge1 e m pm x:
    (∀ a v, eval_expr ge1 e m pm x a v ->
            (∀ ge2, match_external_funct ge1 ge2 ->
                    Senv.equiv ge1 ge2 ->
                    eval_expr ge2 e m pm x a v)) /\
    (∀ als vs, eval_exprlist ge1 e m pm x als vs ->
               (∀ ge2, match_external_funct ge1 ge2 ->
                       Senv.equiv ge1 ge2 ->
                       eval_exprlist ge2 e m pm x als vs)) /\
    (∀ a blk ofs, eval_llvalue ge1 e m pm x a blk ofs ->
                  (∀ ge2, match_external_funct ge1 ge2 ->
                          Senv.equiv ge1 ge2 ->
                          eval_llvalue ge2 e m pm x a blk ofs)) /\
    (∀ a blk ofs, eval_glvalue ge1 e m pm x a blk ofs ->
                  (∀ ge2, match_external_funct ge1 ge2 ->
                          Senv.equiv ge1 ge2 ->
                          eval_glvalue ge2 e m pm x a blk ofs)).
  Proof.
    apply (eval_exprs_ind ge1 e m pm x); intros; try (econstructor; eauto; done).
    - econstructor; eauto.
      { subst. eapply H7; eauto. }
      { eapply external_call_symbols_preserved; eauto. }
    - econstructor; eauto.
      destruct H3 as (H2a&H2b&H2c). rewrite /Senv.find_symbol/= in H2a. rewrite H2a. eauto.
  Qed.

  Lemma match_external_funct_sym ge1 ge2 :
    match_external_funct ge1 ge2 ->
    match_external_funct ge2 ge1.
  Proof. intros (?&?); split; auto. Qed.

  Lemma senv_equiv_sym ge1 ge2:
    Senv.equiv ge1 ge2 ->
    Senv.equiv ge2 ge1.
  Proof. rewrite /Senv.equiv; intuition. Qed.

  Lemma eval_expr_match ge1 ge2 e m pm x a v:
    eval_expr ge1 e m pm x a v ->
    match_external_funct ge1 ge2 ->
    Senv.equiv ge1 ge2 ->
    eval_expr ge2 e m pm x a v.
  Proof. intros. eapply eval_expr_match_aux; eauto. Qed.

  Lemma eval_expr_fun_match p1 p2 a :
    match_external_funct (globalenv p1) (globalenv p2) ->
    Senv.equiv (globalenv p1) (globalenv p2) ->
    eval_expr_fun p1 a = eval_expr_fun p2 a.
  Proof.
    intros. rewrite {1}/eval_expr_fun. symmetry.
    destruct (pred_to_default_fun_spec1 (eval_expr (globalenv p1) empty_env Mem.empty (ParamMap.empty _) Float.zero a)
                (Vfloat Float.zero)) as [(v&Hv&Heq)|(Hnex&Heq)].
    - rewrite Heq. apply eval_expr_fun_spec; eauto.
      eapply eval_expr_match; eauto.
    - rewrite Heq. rewrite /eval_expr_fun. apply pred_to_default_fun_default.
      intros v Hfalso. eapply Hnex.
      eapply eval_expr_match; eauto using senv_equiv_sym, match_external_funct_sym.
  Qed.

  Definition val2R v : R :=
    match v with
    | Vfloat flt => IFR flt
    | _ => 0
    end.

  Definition R2val v : val :=
    Vfloat (IRF v).

  (* Recall that in the program ast from Stanlight.v, we track a special "out mapping" function
     for each parameter, which models the function that the generated code uses to print "unconstrained"
     internal parameters back to the "constrained" representation that the user expects.

     The following two definitions take a program a list/vector of parameter values and apply these
     mapping expressions to each value to get a list/vector of constrained outputs *)

  Definition eval_param_map_list (p : program) (vt: list R) : list R :=
    List.map (fun '(v,f) => val2R (eval_expr_fun p (f (Econst_float (IRF v) Breal))))
      (List.combine vt (flatten_parameter_out p)).

  Program Definition eval_param_map (p : program) (vt: Vector.t R (parameter_dimension p)) :
    Vector.t R (parameter_dimension p) :=
    (Vector.map2 (fun v f => val2R (eval_expr_fun p (f (Econst_float (IRF v) Breal))))
                 vt (Vector.of_list (flatten_parameter_out p))).
  Next Obligation.
    unfold parameter_dimension, flatten_parameter_out, flatten_parameter_constraints.
    repeat rewrite map_length. auto.
  Qed.

  (* The next definitions assigns an unnormalized "probability" to a
     rectangle rt of parameters by integrating the density of the
     program times an indicator which checks whether the variable of
     integration is in the parameter rectangle rt after
     constraining. *)

  Definition unnormalized_program_distribution_integrand p data rt :=
    (fun v => density_of_program p data (map (fun r => Vfloat (IRF r)) v)
              * rect_list_indicator rt (eval_param_map_list p v)).

  Definition is_unnormalized_program_distribution p data rt v : Prop :=
    is_IIRInt_list (unnormalized_program_distribution_integrand p data rt) (parameter_list_rect p) v.

  Definition ex_unnormalized_program_distribution p data rt : Prop :=
    ∃ v, is_unnormalized_program_distribution p data rt v.

  Definition unnormalized_program_distribution (p: program) (data: list val) : rectangle_list -> R :=
    fun rt =>
      IIRInt_list
        (unnormalized_program_distribution_integrand p data rt)
        (parameter_list_rect p).

  (* We next define the normalization constant, which uses the same integrand without the indicator variable. *)
  Definition program_normalizing_constant_integrand p data :=
        (fun v => density_of_program p data (map (fun r => Vfloat (IRF r)) v)).

  Definition is_program_normalizing_constant p data v : Prop :=
    is_IIRInt_list (program_normalizing_constant_integrand p data) (parameter_list_rect p) v.

  Definition ex_program_normalizing_constant p data :=
    ∃ v, is_program_normalizing_constant p data v.

  Definition program_normalizing_constant (p : program) (data: list val) : R :=
      IIRInt_list (program_normalizing_constant_integrand p data) (parameter_list_rect p).

  (* Finally, the actual distribution is obtained by dividing the
  unnormalized values by the normalization constant. *)

  Definition is_program_distribution (p: program) (data: list val) (rt : rectangle_list) (v: R) : Prop :=
    ∃ vnum vnorm, vnorm <> 0 /\
      is_program_normalizing_constant p data vnorm /\
      is_unnormalized_program_distribution p data rt vnum /\
      v = vnum/vnorm.

  Definition program_distribution (p: program) (data: list val) : rectangle_list -> R :=
    fun rt => (unnormalized_program_distribution p data rt) / program_normalizing_constant p data.

  (* We need to restrict our attention to source programs that don't trigger "undefined behavior",
     i.e. safe programs that do not get "stuck" operationally for any valid parameter assignment *)
  Definition is_safe p data params : Prop :=
    (forall t, exists s, Smallstep.initial_state (semantics p data params t) s) /\
    (forall t s, Smallstep.initial_state (semantics p data params t) s ->
                 safe (semantics p data params t) s) /\
    (exists t, returns_target_value p data params t).

  Definition safe_data p data : Prop :=
    (forall params,
    in_list_rectangle params (parameter_list_rect p) ->
    is_safe p data (map (fun r => Vfloat (IRF r)) params)).

  (* The compiler is said to be correct if compiled programs refine source programs, where
     p1 refines p2 if:

    (1) They have the same dimensions of parameter space,
    (2) Anything that is considered a "safe" data input for p2 is also safe for p1
    (3) For all of those safe data inputs, the distribution of p1 is the same as p2 for all rectangular subsets
        of that dimension
  *)

  Definition denotational_refinement (p1 p2: program) :=
    ∃ (Hpf: parameter_dimension p1 = parameter_dimension p2),
      (∀ data, wf_rectangle_list (parameter_list_rect p2) ->
               genv_has_mathlib (globalenv p2) ->
               safe_data p2 data ->
               safe_data p1 data) /\
      (∀ data rt vt, safe_data p2 data ->
                  genv_has_mathlib (globalenv p2) ->
                  wf_rectangle_list (parameter_list_rect p2) ->
                  is_program_distribution p2 data rt vt ->
                  is_program_distribution p1 data rt vt) /\
      (genv_has_mathlib (globalenv p2) -> genv_has_mathlib (globalenv p1)) /\
      (wf_rectangle_list (parameter_list_rect p2) -> wf_rectangle_list (parameter_list_rect p1)).

End DENOTATIONAL.

(* The remainder of this file proves a few helper lemmas. *)

Lemma denotational_refinement_trans p1 p2 p3 :
  denotational_refinement p1 p2 ->
  denotational_refinement p2 p3 ->
  denotational_refinement p1 p3.
Proof.
  intros Hd1 Hd2.
  destruct Hd1 as (Hpf1&Hsafe1&Hdist1&Hmathlib1&Hwf1).
  destruct Hd2 as (Hpf2&Hsafe2&Hdist2&Hmathlib2&Hwf2).
  unshelve (eexists _).
  { congruence. }
  split; [| split].
  { intros. eapply Hsafe1; eauto using wf_rectangle_list_subset. }
  { intros. eapply Hdist1; eauto using wf_rectangle_list_subset. }
  split.
  { intuition. }
  { eauto. }
Qed.

Lemma alloc_variables_in_env env vs env' :
  alloc_variables env vs env'->
  ∀ id, is_id_alloc env' id = true ->
              (∃ b, In (id, b) vs) \/ is_id_alloc env id = true.
Proof.
  induction 1.
  - intros. eauto.
  - intros. edestruct IHalloc_variables as [Hleft|Hright].
    { eauto. }
    { left. destruct Hleft.  eexists; right. eauto. }
    destruct (Pos.eq_dec id0 id). subst.
    { left. eexists. left. eauto. }
    { rewrite is_id_setv_other // in Hright. right; eauto. }
Qed.

Lemma assign_global_params_is_id_alloc_in_flat1 flat_ids pm1 vs pm2 :
  assign_global_params flat_ids pm1 vs pm2 ->
  ∀ id, ParamMap.is_id_alloc pm2 id  = true ->
               (ParamMap.is_id_alloc pm1 id = true) ∨
               (∃ b ofs', In (id, b, ofs') flat_ids).
Proof.
  induction 1.
  - intuition.
  - intros id' Halloc.
    edestruct IHassign_global_params as [Hleft|Hright]; eauto.
    { subst.
      destruct (Pos.eq_dec id id'); subst.
      { right. do 2 eexists; by left; eauto. }
      { rewrite is_id_set_other in Hleft; eauto. }
    }
    right. clear -Hright. destruct Hright as (?&?&?).
    do 2 eexists; eauto. right. eauto.
Qed.

Lemma assign_global_params_some_in_flat1 flat_ids pm1 vs pm2 :
  assign_global_params flat_ids pm1 vs pm2 ->
  ∀ id ofs fl, ParamMap.get pm2 id ofs = Some fl ->
               (ParamMap.get pm1 id ofs = Some fl) ∨
               (∃ b ofs', In (id, b, ofs') flat_ids /\ Integers.Ptrofs.intval ofs' = ofs).
Proof.
  induction 1.
  - intuition.
  - intros id' ofs' fl' Hget.
    edestruct IHassign_global_params as [Hleft|Hright]; eauto.
    { subst.
      destruct (Pos.eq_dec id id'); subst.
      { destruct (Z.eq_dec (Integers.Ptrofs.intval ofs) ofs'); subst.
        { right. do 2 eexists; split; eauto.
          left; eauto. }
        { rewrite ParamMap.gso in Hleft; last by (right; congruence).
          eauto. }
      }
      rewrite ParamMap.gso in Hleft; auto.
    }
    right. clear -Hright. destruct Hright as (?&?&?&?).
    do 2 eexists; split; eauto. right. eauto.
Qed.

Lemma reserve_global_params_is_id_alloc_true ids pm1 pm2 id :
  reserve_global_params ids pm1 pm2 ->
  is_id_alloc pm2 id = true ->
  (is_id_alloc pm1 id = true \/ In id ids).
Proof.
  induction 1.
  - auto.
  - intros His. subst. destruct IHreserve_global_params.
    { eauto. }
    { destruct (Pos.eq_dec id id0).
      { subst. right. by left. }
      { rewrite ParamMap.is_id_reserve_other in H; auto. }
    }
    right. by right.
Qed.

Lemma In_flatten_parameter_list_id' prs id b ofs :
  In (id, b, ofs) (flatten_parameter_list prs) ->
  In id (map (fun '(id, _ ,_) => id) prs).
Proof.
  induction prs.
  - inversion 1.
  - destruct a as ((?&[])&?) => //=;
    try (destruct 1 as [Hleft|Hright]; [ left; congruence | right; eauto ]).
    rewrite /flatten_parameter_list/=.
    intros [Hleft|Hright]%in_app_or.
    { rewrite /parameter_basic_to_list/data_basic_to_list/= in Hleft.
      apply in_combine_l in Hleft. apply repeat_spec in Hleft. left; congruence. }
    { right. eauto. }
Qed.

Lemma In_flatten_parameter_list_id pr id b ofs :
  In (id, b, ofs) (flatten_parameter_list (pr_parameters_vars pr)) ->
  In id (pr_parameters_ids pr).
Proof. eapply In_flatten_parameter_list_id'. Qed.

Lemma set_global_params_is_id_alloc id vs pm tprog :
  set_global_params (pr_parameters_ids tprog) (flatten_parameter_list (pr_parameters_vars tprog))
    vs (empty _) pm ->
  ParamMap.is_id_alloc pm id = true -> In id (pr_parameters_ids tprog).
Proof.
  destruct 1 as (pm'&Hres&Hassign). intros His.
  exploit assign_global_params_is_id_alloc_in_flat1; eauto.
  intros Hcases.
  destruct Hcases as [Hpm'|Hin'].
  {
    exploit reserve_global_params_is_id_alloc_true; eauto.
    rewrite is_id_empty.
    intros [Hemp|Hshadow]; first congruence.
    auto.
  }
  {
    destruct Hin' as (b&ofs'&Hin').
    apply In_flatten_parameter_list_id in Hin'. auto.
  }
Qed.
