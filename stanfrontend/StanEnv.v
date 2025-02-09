(* Axioms about floating points and math environments.

   The transformations performed by the compiler (and even Stan's
   reference compiler) can only be seen as semantically preserving if
   one pretends that floating point operations behave as if they were
   exact computations on the reals. Similarly, we must assume that the
   standard libraries for various math operations in the program's
   environment (exp, normal_lpdf, etc.) perfectly compute their
   mathematical equivalents.

   This file defines these assumptions and the requirements on the
   global environment.

   WARNING: The axioms herein can be used to derive False IF one
   treats floats as anything other than an abstract type (E.g. trying
   to exploit the fact that floats technically have a finite encoding,
   would let one derive a contradiction because IFR/IRF would imply
   the reals are a finite set.)

   See the discussion in the paper on this subject for caveats about
   what such assumptions mean for the correctness guarantees of the
   compiler.


*)

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

(* IFR/IRF inject float into real and vice versa, named in analogy to
   INR : nat -> R, IZR: Z -> R from Coq *)

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

Lemma IFR_inj t1 t2 :
  IFR t1 = IFR t2 ->
  t1 = t2.
Proof.
  intros Heq.
  rewrite -(IRF_IFR_inv t1).
  rewrite -(IRF_IFR_inv t2).
  congruence.
Qed.

Definition normal_lpdf_ef_external :=
  (AST.EF_external "normal_lpdf" (AST.mksignature (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                                    (AST.Tret AST.Tfloat)
                                    (AST.mkcallconv None false false))).

Definition genv_normal_lpdf_spec genv :=
  exists loc,
  Globalenvs.Genv.find_symbol genv ($"normal_lpdf") = Some loc /\
  Globalenvs.Genv.find_funct genv (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            normal_lpdf_ef_external
            (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble Ctypes.Tnil)))
            tdouble
            (AST.mkcallconv None false false)).

Axiom normal_lpdf_ext_spec :
  forall x mean variance ge m,
  Events.external_call normal_lpdf_ef_external ge
    (Values.Vfloat (IRF x) :: Values.Vfloat (IRF mean) :: Values.Vfloat (IRF variance) :: nil) m
    Events.E0
    (Values.Vfloat (IRF (ln (1 / sqrt(variance * 2 * PI) * exp (- (x - mean)^2 / (2 * variance)))))) m.

Axiom normal_lpdf_ext_inv :
  forall vs v ge m,
  Events.external_call normal_lpdf_ef_external ge
    vs m
    Events.E0
    v m ->
  ∃ x mean variance,
    0 < variance ∧
    vs = (Values.Vfloat (IRF x) :: Values.Vfloat (IRF mean) :: Values.Vfloat (IRF variance) :: nil) ∧
    v = (Values.Vfloat (IRF (ln (1 / sqrt(variance * 2 * PI) * exp (- (x - mean)^2 / (2 * variance)))))).

Definition normal_lupdf_ef_external :=
  (AST.EF_external "normal_lupdf" (AST.mksignature (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                                    (AST.Tret AST.Tfloat)
                                    (AST.mkcallconv None false false))).

Definition genv_normal_lupdf_spec genv :=
  exists loc,
  Globalenvs.Genv.find_symbol genv ($"normal_lupdf") = Some loc /\
  Globalenvs.Genv.find_funct genv (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            normal_lupdf_ef_external
            (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble Ctypes.Tnil)))
            tdouble
            (AST.mkcallconv None false false)).

Axiom normal_lupdf_ext_spec :
  forall x mean variance ge m,
  Events.external_call normal_lupdf_ef_external ge
    (Values.Vfloat (IRF x) :: Values.Vfloat (IRF mean) :: Values.Vfloat (IRF variance) :: nil) m
    Events.E0
    (Values.Vfloat (IRF ( - ln(sqrt(variance)) - (x - mean)^2 / (2 * variance)))) m.

Definition cauchy_lpdf_ef_external :=
  (AST.EF_external "cauchy_lpdf" (AST.mksignature (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                                    (AST.Tret AST.Tfloat)
                                    (AST.mkcallconv None false false))).

Definition genv_cauchy_lpdf_spec genv :=
  exists loc,
  Globalenvs.Genv.find_symbol genv ($"cauchy_lpdf") = Some loc /\
  Globalenvs.Genv.find_funct genv (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            cauchy_lpdf_ef_external
            (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble Ctypes.Tnil)))
            tdouble
            (AST.mkcallconv None false false)).

Axiom cauchy_lpdf_ext_spec :
  forall x location scale ge m,
  Events.external_call normal_lpdf_ef_external ge
    (Values.Vfloat (IRF x) :: Values.Vfloat (IRF location) :: Values.Vfloat (IRF scale) :: nil) m
    Events.E0
    (Values.Vfloat (IRF (ln (1 / (PI * scale * (1 + ((x - location)/scale)^2)))))) m.

Axiom cauchy_lpdf_ext_inv :
  forall vs v ge m,
  Events.external_call cauchy_lpdf_ef_external ge
    vs m
    Events.E0
    v m ->
  ∃ x location scale,
    0 < scale ∧
    vs = (Values.Vfloat (IRF x) :: Values.Vfloat (IRF location) :: Values.Vfloat (IRF scale) :: nil) ∧
    v = (Values.Vfloat (IRF (ln (1 / (PI * scale * (1 + ((x - location)/scale)^2)))))).

Definition cauchy_lupdf_ef_external :=
  (AST.EF_external "cauchy_lupdf" (AST.mksignature (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                                    (AST.Tret AST.Tfloat)
                                    (AST.mkcallconv None false false))).

Definition genv_cauchy_lupdf_spec genv :=
  exists loc,
  Globalenvs.Genv.find_symbol genv ($"cauchy_lupdf") = Some loc /\
  Globalenvs.Genv.find_funct genv (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            cauchy_lupdf_ef_external
            (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble (Ctypes.Tcons tdouble Ctypes.Tnil)))
            tdouble
            (AST.mkcallconv None false false)).

Axiom cauchy_lupdf_ext_spec :
  forall x location scale ge m,
  Events.external_call cauchy_lupdf_ef_external ge
    (Values.Vfloat (IRF x) :: Values.Vfloat (IRF location) :: Values.Vfloat (IRF scale) :: nil) m
    Events.E0
    (Values.Vfloat (IRF ( - ln(scale * (1 + ((x - location)/scale)^2))))) m.

Record genv_has_mathlib genv :=
  { GENV_EXP: genv_exp_spec genv;
    GENV_EXPIT: genv_expit_spec genv;
    GENV_LOG: genv_log_spec genv;
    GENV_NORMAL_LPDF: genv_normal_lpdf_spec genv;
    GENV_NORMAL_LUPDF: genv_normal_lupdf_spec genv;
    GENV_CAUCHY_LPDF: genv_cauchy_lpdf_spec genv;
    GENV_CAUCHY_LUPDF: genv_cauchy_lupdf_spec genv;
  }.

Definition math_idents := ($"log" :: $"expit" :: $"exp" :: nil).
Definition pdf_idents := ($"normal_lpdf" :: $"normal_lupdf" :: $"cauchy_lpdf" :: $"cauchy_lupdf" :: nil).

Definition env_no_shadow_mathlib {B} (env: param_mem B) :=
  Forall (fun id => is_id_alloc env id = false) math_idents.

Definition param_mem_no_shadow_mathlib {B} (pm: param_mem B) :=
  Forall (fun id => is_id_alloc pm id = false) math_idents.

Definition no_shadow_pdflib {B} (env: param_mem B) :=
  Forall (fun id => is_id_alloc env id = false) pdf_idents.

Lemma no_shadow_pdflib_store {B} (env1 env2: param_mem B) id ofs v :
  no_shadow_pdflib env1 ->
  store env1 id ofs v = Some env2 ->
  no_shadow_pdflib env2.
Proof.
  rewrite /no_shadow_pdflib => Hforall Hstore.
  eapply Forall_impl; last eassumption.
  intros id' => /= ?.
  erewrite store_same_is_id_alloc; eauto.
Qed.
