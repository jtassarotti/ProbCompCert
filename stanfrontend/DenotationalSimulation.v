Require Import Coqlib Errors Maps String.
Local Open Scope string_scope.
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs.
Require Import Ctypes Cop Stanlight.
Require Import Smallstep.
Require Import Linking.
Require Import IteratedRInt.
Require Vector.

Require Import Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

Require ClassicalEpsilon.
Require Import Reals.
From Coq Require Import Reals Psatz ssreflect ssrbool Utf8.

Require Import Ssemantics.

(* TODO: move and generalize these results to any denotational semantics obtained this way *)
Section DENOTATIONAL_SIMULATION.

Variable prog: Stanlight.program.
Variable tprog: Stanlight.program.
(* prog is assumed to be safe/well-defined on data/params satisfying a predicate P *)

Variable inhabited_initial :
  ∀ data params t, is_safe prog data params -> ∃ s, Smallstep.initial_state (semantics prog data params t) s.

Variable transf_correct:
  forall data params t,
    is_safe prog data params ->
    forward_simulation (Ssemantics.semantics prog data params t) (Ssemantics.semantics tprog data params t).

Variable parameters_preserved:
  flatten_parameter_variables tprog = flatten_parameter_variables prog.

Lemma dimen_preserved:
  parameter_dimension tprog = parameter_dimension prog.
Proof. rewrite /parameter_dimension/flatten_parameter_constraints. rewrite parameters_preserved //. Qed.

Lemma returns_target_value_fsim data params t:
  is_safe prog data params ->
  returns_target_value prog data params t ->
  returns_target_value tprog data params t.
Proof.
  intros Hsafe.
  intros (s1&s2&Hinit&Hstar&Hfinal).
  destruct (transf_correct data params t) as [index order match_states props]; eauto.
  edestruct (fsim_match_initial_states) as (?&s1'&Hinit'&Hmatch1); eauto.
  edestruct (simulation_star) as (?&s2'&Hstar'&Hmatch2); eauto.
  eapply (fsim_match_final_states) in Hmatch2; eauto.
  exists s1', s2'; auto.
Qed.

Lemma returns_target_value_bsim data params t:
  is_safe prog data params ->
  returns_target_value tprog data params t ->
  returns_target_value prog data params t.
Proof.
  intros Hsafe (s1&s2&Hinit&Hstar&Hfinal).
  specialize (transf_correct data params t) as Hfsim.
  apply forward_to_backward_simulation in Hfsim as Hbsim;
    auto using semantics_determinate, semantics_receptive.
  destruct Hbsim as [index order match_states props].
  assert (∃ s10, Smallstep.initial_state (semantics prog data params t) s10) as (s10&?).
  { apply inhabited_initial; eauto. }
  edestruct (bsim_match_initial_states) as (?&s1'&Hinit'&Hmatch1); eauto.
  edestruct (bsim_E0_star) as (?&s2'&Hstar'&Hmatch2); eauto.
  eapply (bsim_match_final_states) in Hmatch2 as (s2''&?&?); eauto; last first.
  { eapply star_safe; last eapply Hsafe; eauto. }
  exists s1', s2''. intuition eauto.
  { eapply star_trans; eauto. }
Qed.

Lemma  log_density_equiv data params :
  is_safe prog data params ->
  log_density_of_program prog data params = log_density_of_program tprog data params.
Proof.
  intros HP.
  rewrite {1}/log_density_of_program.
  rewrite /pred_to_default_fun.
  destruct (ClassicalEpsilon.excluded_middle_informative) as [(v&Hreturns)|Hne].
  { destruct (ClassicalEpsilon.constructive_indefinite_description) as [x Hx].
    symmetry. apply log_density_of_program_trace. clear Hreturns.
    apply returns_target_value_fsim; auto.
  }
  symmetry.
  rewrite {1}/log_density_of_program.
  rewrite /pred_to_default_fun.
  destruct (ClassicalEpsilon.excluded_middle_informative) as [(v&Hreturns)|Hne']; auto.
  exfalso. apply Hne.
  exists v.
  apply returns_target_value_bsim; auto.
Qed.

Lemma safe_data_preserved :
  ∀ data, safe_data prog data -> safe_data tprog data.
Proof.
  intros data Hsafe.
  rewrite /safe_data. intros params Hin.
  assert (Hin': in_list_rectangle params (parameter_list_rect prog)).
  { move:Hin. rewrite /parameter_list_rect/flatten_parameter_constraints parameters_preserved //. } 
  specialize (Hsafe _ Hin').
  rewrite /is_safe. intros t s Hinit.
  specialize (transf_correct data (map (λ r, Vfloat (IRF r)) params) t) as Hfsim.
  apply forward_to_backward_simulation in Hfsim as Hbsim;
    auto using semantics_determinate, semantics_receptive.
  edestruct Hbsim as [index order match_states props].
  assert (∃ s10, Smallstep.initial_state (semantics prog data (map (λ r, Vfloat (IRF r)) params) t) s10) as (s10&?).
  { apply inhabited_initial; eauto. }
  edestruct (bsim_match_initial_states) as (?&s1'&Hinit'&Hmatch1); eauto.

  eapply bsim_safe; eauto.
Qed.

Lemma parameter_list_rect_preserved :
  parameter_list_rect tprog = parameter_list_rect prog.
Proof.
  rewrite /parameter_list_rect/flatten_parameter_constraints parameters_preserved //.
Qed.

Lemma denotational_preserved :
  denotational_refinement tprog prog.
Proof.
  exists (dimen_preserved).
  split.
  - intros data Hsafe. apply safe_data_preserved; auto.
  - intros data rt Hsafe Hwf Hsubset.
    rewrite /distribution_of_program. f_equal.
    { rewrite /distribution_of_program_unnormalized.
      rewrite parameter_list_rect_preserved.
      apply IIRInt_list_ext; auto.
      * intros x Hin. f_equal.
        { rewrite /density_of_program. rewrite log_density_equiv //. eapply Hsafe. eauto. }
      * f_equal. rewrite /eval_param_map_list.
        f_equal. rewrite /flatten_parameter_out. rewrite parameters_preserved //.
    }
    { rewrite /program_normalizing_constant.
      rewrite parameter_list_rect_preserved.
      apply IIRInt_list_ext; auto.
      * intros x Hin.
        { rewrite /density_of_program. rewrite log_density_equiv //. eapply Hsafe. eauto. }
    }
Qed.
  
End DENOTATIONAL_SIMULATION.
