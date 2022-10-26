From Coq Require Import Reals Psatz ssreflect Utf8.
Require Import Smallstep.
Require Import Errors.
Require Import Linking.
Require Import Globalenvs.

Require Import Floats.
Require Import Stanlight.
Require Import Coqlib.
Require Import Transforms.
Require Import IteratedRInt.
Require Import Memory.
Require Import Maps.
Require Import ParamMap.


Local Open Scope string_scope.
Require Import Clightdefs.
Import Clightdefs.ClightNotations.

Local Open Scope clight_scope.

Require Import RealsExt.
Import Continuity.

(* IFR -> inject float into real, named in analogy to INR : nat -> R, IZR: Z -> R *)
Axiom IFR : float -> R.
Axiom IRF: R -> float.

Axiom IFR_IRF_inv :
  ∀ x, IFR (IRF x) = x.
Axiom IRF_IFR_inv :
  ∀ x, IRF (IFR x) = x.

Implicit Types genv : Genv.t fundef (Stanlight.variable).

Definition exp_ef_external :=
  (AST.EF_external "exp" (AST.mksignature (AST.Tfloat :: nil) (AST.Tret AST.Tfloat)
                            (AST.mkcallconv None false false))).


Definition genv_exp_spec genv : Prop :=
  exists loc,
  Globalenvs.Genv.find_symbol genv ($"exp") = Some loc /\
  Globalenvs.Genv.find_funct genv (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            exp_ef_external
            (Ctypes.Tcons tdouble Ctypes.Tnil)
            tdouble
            (AST.mkcallconv None false false)).

Axiom exp_ext_spec :
  forall a ge m,
  Events.external_call exp_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m Events.E0 (Values.Vfloat (IRF (exp a))) m.

(*
Axiom exp_ext_no_mem_dep :
  forall a ge m,
  no_mem_dep exp_ef_external ge (Values.Vfloat (IRF a) :: nil) m
    (Values.Vfloat (IRF (exp a))).
*)

Definition expit_ef_external :=
  (AST.EF_external "expit" (AST.mksignature (AST.Tfloat :: nil) (AST.Tret AST.Tfloat)
                            (AST.mkcallconv None false false))).

Definition genv_expit_spec genv := 
  exists loc,
  Globalenvs.Genv.find_symbol genv ($"expit") = Some loc /\
  Globalenvs.Genv.find_funct genv (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            expit_ef_external
            (Ctypes.Tcons tdouble Ctypes.Tnil)
            tdouble
            (AST.mkcallconv None false false)).

Axiom expit_ext_spec :
  forall a ge m,
  Events.external_call expit_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m Events.E0 (Values.Vfloat (IRF (logit_inv a))) m.

(*
Axiom expit_ext_no_mem_dep :
  forall a ge m,
  no_mem_dep expit_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m (Values.Vfloat (IRF (logit_inv a))).
*)

Definition log_ef_external :=
  (AST.EF_external "log" (AST.mksignature (AST.Tfloat :: nil) (AST.Tret AST.Tfloat)
                            (AST.mkcallconv None false false))).

Definition genv_log_spec genv :=
  exists loc,
  Globalenvs.Genv.find_symbol genv ($"log") = Some loc /\
  Globalenvs.Genv.find_funct genv (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            log_ef_external
            (Ctypes.Tcons tdouble Ctypes.Tnil)
            tdouble
            (AST.mkcallconv None false false)).

Axiom log_ext_spec :
  forall a ge m,
  Events.external_call log_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m Events.E0 (Values.Vfloat (IRF (ln a))) m.

Lemma log_ext_spec' :
  forall a ge m,
  Events.external_call log_ef_external ge
    (Values.Vfloat a :: nil) m Events.E0 (Values.Vfloat (IRF (ln (IFR a)))) m.
Proof.
  intros.
  rewrite -{1}(IRF_IFR_inv a). eapply log_ext_spec.
Qed.

Lemma log_ext_spec'' :
  forall a b ge m,
  IRF (ln (IFR a)) = b ->
  Events.external_call log_ef_external ge
    (Values.Vfloat a :: nil) m Events.E0 (Values.Vfloat b) m.
Proof.
  intros ???? <-. eapply log_ext_spec'.
Qed.

(*
Axiom log_ext_no_mem_dep :
  forall a ge m,
  no_mem_dep log_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m (Values.Vfloat (IRF (ln a))).
*)

Definition genv_has_mathlib genv :=
  genv_exp_spec genv ∧
  genv_expit_spec genv ∧
  genv_log_spec genv.

Definition math_idents := ($"log" :: $"expit" :: $"exp" :: nil).

Definition env_no_shadow_mathlib {B} (env: PTree.t B) :=
  Forall (fun id => PTree.get id env = None) math_idents.

Definition param_mem_no_shadow_mathlib {B} (pm: param_mem B) :=
  Forall (fun id => is_id_alloc pm id = false) math_idents.

Axiom float_add_irf: forall a b,
  (Floats.Float.add (IRF a) (IRF b)) = IRF (a + b).
Axiom float_sub_irf: forall a b,
  (Floats.Float.sub (IRF a) (IRF b)) = IRF (a - b).
Axiom float_mul_irf: forall a b,
  (Floats.Float.mul (IRF a) (IRF b)) = IRF (a * b).
Axiom IFR_zero :
  IFR (Floats.Float.zero) = 0.
Axiom IFR_one :
  IFR (Floats.Float.of_int Integers.Int.one) = 1.

Lemma IFR_0 :
  IFR (Floats.Float.zero) = 0.
Proof. apply IFR_zero. Qed.

Lemma IRF_0 :
  IRF 0 = Floats.Float.zero.
Proof. rewrite -IFR_0 IRF_IFR_inv //. Qed.

Lemma float_add_irf': forall a b,
  (Floats.Float.add a b) = IRF (IFR a + IFR b).
Proof. intros a b. rewrite -float_add_irf ?IRF_IFR_inv //. Qed.

Lemma float_sub_irf': forall a b,
  (Floats.Float.sub a b) = IRF (IFR a - IFR b).
Proof. intros a b. rewrite -float_sub_irf ?IRF_IFR_inv //. Qed.

Lemma float_mul_irf': forall a b,
  (Floats.Float.mul a b) = IRF (IFR a * IFR b).
Proof. intros a b. rewrite -float_mul_irf ?IRF_IFR_inv //. Qed.

Lemma IRF_inj t1 t2 :
  IRF t1 = IRF t2 ->
  t1 = t2.
Proof.
  intros Heq.
  rewrite -(IFR_IRF_inv t1).
  rewrite -(IFR_IRF_inv t2).
  congruence.
Qed.
