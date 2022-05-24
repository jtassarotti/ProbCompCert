Require Import Coqlib Errors Maps String.
Local Open Scope string_scope.
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs.
Require Import Ctypes Cop StanE.
Require Import Smallstep.

Require Import Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

(*
Require Import String.
Require Clight Clightdefs. 
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.
*)

Definition genv := Genv.t fundef variable.

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

Inductive bind_parameters (e: env):
                           mem -> list (ident * basic) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ge ty m b Ptrofs.zero v1 m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

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

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int: forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float: forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Eunop: forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation (unary_op_conversion op) v1 (transf_type (typeof a)) m = Some v ->
      eval_expr (Eunop op a ty) v
(*
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
*)
  | eval_Ecall: forall a al vf ef fd vargs tyargs m ty vres tyres  m' cconv t, 
      eval_expr a vf ->
      eval_exprlist al vargs ->
      Genv.find_funct ge vf = Some fd ->
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
  | eval_Ederef: forall a ty l ofs i,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Eindexed a i ty) l ofs

with eval_exprlist: exprlist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist Enil nil
  | eval_Econs: forall a bl v1 v2 vl,
      eval_expr a v1 ->
      (* sem_cast v1 (typeof a) ty m = Some v2 -> *)
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
  | Kreturn: cont -> cont.

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
  | step_assign: forall f t a1 a2 k e m loc ofs v2 v m',
      eval_lvalue e m t a1 loc ofs ->
      eval_expr e m t a2 v2 ->
      (* sem_cast v2 (typeof a2) (typeof a1) m = Some v -> *)
      assign_loc ge (typeof a1) m loc ofs v m' ->
      step (State f (Sassign a1 None a2) t k e m)
        E0 (State f Sskip t k e m')

  | step_seq: forall f t s1 s2 k e m,
    step (State f (Ssequence s1 s2) t k e m) E0 (State f s1 t (Kseq s2 k) e m)

  | step_skip_seq: forall f t s k e m,
      step (State f Sskip t (Kseq s k) e m)
        E0 (State f s t k e m)

  | step_ifthenelse: forall f t a s1 s2 k e m v1 b,
    eval_expr e m t a v1 ->
      bool_val v1 (transf_type (typeof a)) m = Some b ->
      step (State f (Sifthenelse a s1 s2) t k e m)
        E0 (State f (if b then s1 else s2) t k e m)

.

(* Note: no binding of parameters, no check for repetition, no parameters *)
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0 m1 e,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge $"model" = Some b ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      alloc_variables empty_env m0 f.(fn_vars) e m1 ->
      initial_state p (State f f.(fn_body) ((Floats.Float.of_int Integers.Int.zero)) Kstop e m1).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall f t e m,
      final_state (State f Sskip t Kstop e m) Integers.Int.zero.

End SEMANTICS.

Definition semantics (p: program) :=
  let ge := Genv.globalenv p in
  Semantics_gen step (initial_state p) final_state ge ge.
