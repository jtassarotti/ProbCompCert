Require Import Coqlib Errors Maps String.
Local Open Scope string_scope.
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs.
Require Import Ctypes Cop Stanlight.
Require Import Smallstep.
Require Import Linking.
Require Import ImproperRInt.
Require Vector.

Require Import Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

Definition genv := Genv.t fundef variable.

(* Neither used nor right... *)
Definition globalenv (p: program) := Genv.globalenv p.

Definition env := PTree.t (block * basic).

Definition empty_env: env := (PTree.empty (block * basic)).

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

Inductive deref_loc (ty: basic) (m: mem) (b: block) (ofs: ptrofs) : val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs (Vptr b ofs).

Inductive assign_loc (ce: genv) (ty: basic) (m: mem) (b: block) (ofs: ptrofs): val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs v m'.

Section SEMANTICS.

Variable ge: genv.

Inductive alloc_variables: env -> mem ->
                           list (ident * basic) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ty) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

Section EXPR.

Variable e: env.
Variable m: mem.
Variable t: float.

Definition typeof (e: expr) : basic :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Evar _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecall e el ty => ty
  | Eindexed e el ty => ty
  | Etarget ty => ty
  end.

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

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int: forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float: forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Eunop: forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation (unary_op_conversion op) v1 (transf_type (typeof a)) m = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation (PTree.empty composite) (binary_op_conversion op) v1 (transf_type (typeof a1)) v2 (transf_type (typeof a2)) m = Some v ->
      eval_expr (Ebinop a1 op a2 ty) v
  | eval_Ecall: forall a al vf ef name sig fd vargs tyargs m ty vres tyres  m' cconv t, 
      eval_expr a vf ->
      eval_exprlist al vargs ->
      Genv.find_funct ge vf = Some fd ->
      ef = EF_external name sig ->
      fd = External ef tyargs tyres cconv ->
      external_call ef ge vargs m t vres m' ->
      eval_expr (Ecall a al ty) vres 
  | eval_Etarget: forall ty,
      eval_expr (Etarget ty) (Vfloat t)
  | eval_Elvalue: forall a loc ofs v,
      eval_lvalue a loc ofs ->
      deref_loc (typeof a) m loc ofs v ->
      eval_expr a v

with eval_lvalue: expr -> block -> ptrofs -> Prop :=
  | eval_Evar_local: forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Ptrofs.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Evar id ty) l Ptrofs.zero
  | eval_Ederef: forall a al ty l v,
      eval_expr a (Vptr l (Ptrofs.of_int Integers.Int.zero)) ->
      (* Currently only doing array *)
      eval_exprlist al ((Vint v) :: nil) ->
      eval_lvalue (Eindexed a al ty) l (Ptrofs.of_int v)

with eval_exprlist: exprlist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist Enil nil
  | eval_Econs: forall a bl v1 v2 vl ty,
      eval_expr a v1 ->
      sem_cast v1 (transf_type (typeof a)) ty m = Some v2 -> 
      eval_exprlist bl vl ->
      eval_exprlist (Econs a bl) (v2 :: vl).

End EXPR.

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont (* Kseq s2 k = after s1 in s1;s2 *)
  | Kifthenelse: statement -> statement -> cont -> cont (* Kifthenelse s1 s2 k = after x in if (x) { s1 } else { s2 } *)
  | Kfor2: expr -> statement -> statement -> cont -> cont (* Kfor2 e2 e3 s k = after e2 in for(e1;e2;e3) s *)
  | Kfor3: expr -> statement -> statement -> cont -> cont (* Kfor3 e2 e3 s k = after s in for(e1;e2;e3) s *)
  | Kfor4: expr -> statement -> statement -> cont -> cont (* Kfor4 e2 e3 s k = after e3 in for(e1;e2;e3) s *)
  .

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (t: float)
      (k: cont)
      (e: env)
      (m: mem) : state.

Definition var_names (vars: list(ident * basic)) : list ident :=
  List.map (@fst ident basic) vars.

Inductive step: state -> trace -> state -> Prop :=
  | step_skip_seq: forall f t s k e m,
      step (State f Sskip t (Kseq s k) e m)
        E0 (State f s t k e m)

  | step_seq: forall f t s1 s2 k e m,
    step (State f (Ssequence s1 s2) t k e m) E0 (State f s1 t (Kseq s2 k) e m)

  | step_assign: forall f t a1 a2 k e m loc ofs v2 v m',
      eval_lvalue e m t a1 loc ofs ->
      eval_expr e m t a2 v2 ->
      sem_cast v2 (transf_type (typeof a2)) (transf_type (typeof a1)) m = Some v -> 
      assign_loc ge (typeof a1) m loc ofs v m' ->
      step (State f (Sassign a1 None a2) t k e m)
        E0 (State f Sskip t k e m')

  | step_ifthenelse: forall f t a s1 s2 k e m v1 b,
    eval_expr e m t a v1 ->
    bool_val v1 (transf_type (typeof a)) m = Some b ->
    step (State f (Sifthenelse a s1 s2) t k e m) E0 (State f (if b then s1 else s2) t k e m)

  | step_target: forall f t a v k e m,
    eval_expr e m t a (Vfloat v) ->
    step (State f (Starget a) t k e m) E0 (State f Sskip (Floats.Float.add t v) k e m)
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
  type_of_basic_list (map snd (pr_parameters_vars p)).

Fixpoint count_down_ofs (n: nat) :=
  match n with
  | O => nil
  | S n' => (Ptrofs.repr (Z.of_nat n')) :: count_down_ofs n'
  end.

Definition count_up_ofs (n: nat) := rev (count_down_ofs n).

Definition basic_to_list (ib : ident * basic) : list (ident * basic * Ptrofs.int) :=
  match snd ib with
  | Bint => (ib, Ptrofs.zero) :: nil
  | Breal => (ib, Ptrofs.zero) :: nil
  | Barray b z => combine (repeat (fst ib, b) (Z.to_nat z)) (count_up_ofs (Z.to_nat z))
  | _ => nil
  end.

Definition flatten_ident_list (ibs: list (ident * basic)) : list (ident * basic * Ptrofs.int) :=
  List.concat (map basic_to_list ibs).

Inductive assign_global_locs (ge: genv) : list (ident * basic * Ptrofs.int) -> mem -> list val -> mem -> Prop :=
  | assign_global_locs_nil : forall m,
      assign_global_locs ge nil m nil m
  | assign_global_locs_cons : forall m1 m2 m3 id ty ofs l v bs vs,
      Genv.find_symbol ge id = Some l ->
      assign_loc ge ty m1 l ofs v m2 ->
      assign_global_locs ge bs m2 vs m3 ->
      assign_global_locs ge ((id, ty, ofs) :: bs) m1 (v :: vs) m3.

(* Joe: TODO: this initial state loading here may not be correct for array data/params *)
Inductive initial_state (p: program) (data : list val) (params: list val) : state -> Prop :=
  | initial_state_intro: forall b f m0 m1 m2 m3 e,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge $"model" = Some b ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      alloc_variables empty_env m0 f.(fn_vars) e m1 ->
      assign_global_locs ge (flatten_ident_list p.(pr_data_vars)) m1 data m2 ->
      assign_global_locs ge (flatten_ident_list p.(pr_parameters_vars)) m2 params m3 ->
      initial_state p data params (State f f.(fn_body) ((Floats.Float.of_int Integers.Int.zero)) Kstop e m3).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall f t e m,
      final_state (State f Sskip t Kstop e m) Integers.Int.zero.

End SEMANTICS.

Definition semantics (p: program) (data: list val) (params: list val) :=
  let ge := Genv.globalenv p in
  Semantics_gen step (initial_state p data params) final_state ge ge.

(* Example of what needs to be done: https://compcert.org/doc/html/compcert.cfrontend.Ctypes.html#Linker_program *)

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
Require Import Reals.

Section DENOTATIONAL.

  (* returns_target_value p data params t holds if it is possible for p to go from an
     initial state with data and params loaded to a final state with t as the target value *)
  Definition returns_target_value (p: program) (data: list val) (params: list val) (t: float) :=
    exists s1 tr f e m,
      Smallstep.initial_state (semantics p data params) s1 /\
      Star (semantics p data params) s1 tr (State f Sskip t Kstop e m).

  (* Given a predicate P : V -> Prop, pred_to_default_fun P default will return
     an arbitrary value v such that P v holds, if such a v exists, and otherwise returns default. *)
  Definition pred_to_default_fun {V: Type} (P: V -> Prop) (default: V) : V :=
    let s := ClassicalEpsilon.excluded_middle_informative (exists v : V, P v) in
    match s with
    | left e => let (x, _) := ClassicalEpsilon.constructive_indefinite_description P e in x
    | right _ => default
    end.

  (* Return a final target value if one can be obtained from running the program, otherwise
     returns Float.zero *)
  Definition log_density_of_program (p: program) (data: list val) (params: list val) : float :=
    pred_to_default_fun (returns_target_value p data params) Float.zero.

  Record interval := mk_interval { interval_lb : Rbar; interval_ub : Rbar}.

  Definition interval_subset (i1 i2: interval) :=
    Rbar_le (interval_lb i2) (interval_lb i1) /\ Rbar_le (interval_ub i1) (interval_ub i2).

  (* IFR -> inject float into real, named in analogy to INR : nat -> R, IZR: Z -> R *)
  Axiom IFR : float -> R.
  Axiom IRF: R -> float.

  Fixpoint constraint_to_interval (c: constraint) :=
    match c with
    | Cidentity => mk_interval m_infty p_infty
    | Clower f  => mk_interval (IFR f) p_infty
    | Cupper f  => mk_interval m_infty (IFR f)
    | Clower_upper f1 f2 => mk_interval (IFR f1) (IFR f2)
    end.

End DENOTATIONAL.
