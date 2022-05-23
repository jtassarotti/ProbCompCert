Require Import StanE.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Events.
Require Import Integers.
Require Import Maps.
Require Import Floats.
Require Import Values. 
Require Import Cop. 

Require Import String.
Require Clight Clightdefs. 
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Definition genv:= Genv.t fundef variable.

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
(*
Inductive eval_expr: genv -> expr -> val -> Prop :=
  | eval_Econst_int: forall ge i ty,
      eval_expr ge (Econst_int i ty) (Vint i)
  | eval_Econst_float: forall ge f ty,
      eval_expr ge (Econst_float f ty) (Vfloat f)
  | eval_Econst_binop: forall ge e1 v1 op e2 v2 ty,
      eval_expr ge e1 v1 ->
      eval_expr ge e2 v2 ->
      sem_binary_operation ge op v1 (typeof e1) v2 (typeof e2) m = Some v ->
      eval_expr ge (Ebinop e1 op e2 ty). 

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont.

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont) : state
  | Callstate
      (fd: fundef)
      (args: list val)
      (k: cont) : state
.

Inductive step: genv -> state -> trace -> state -> Prop :=
  | step_seq: forall ge f s1 s2 k,
      step ge (State f (Ssequence s1 s2) k)
        E0 (State f s1 (Kseq s2 k))
  | step_skip_seq: forall ge f s k,
      step ge (State f Sskip (Kseq s k))
        E0 (State f s k)
.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      Genv.find_symbol ge $"model" = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      initial_state p (Callstate f nil Kstop).

Parameter initial_state: program -> state -> Prop.

Parameter final_state: state -> int -> Prop.

Definition semantics (p: program) :=
  let ge := Genv.globalenv p in
  Semantics_gen step (initial_state p) final_state ge ge.
*)
Parameter semantics: program -> semantics.
