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
(* unconstrain *)
Variable param_unmap : list R -> list R.
(* constrain *)
Variable param_map : list R -> list R.

Variable target_map : R -> R.
Variable target_unmap : R -> R.

Axiom target_map_unmap : ∀ x, target_map (target_unmap x) = x.
Axiom target_map_zero : target_map (IFR Float.zero) = IFR Float.zero.

Variable inhabited_initial :
  ∀ data params t, is_safe prog data params -> ∃ s, Smallstep.initial_state (semantics prog data params t) s.

Axiom dimen_preserved: parameter_dimension tprog = parameter_dimension prog.

Axiom param_map_unmap :
  ∀ x, in_list_rectangle x (parameter_list_rect prog) ->
       param_map (param_unmap x) = x.

Axiom param_unmap_map :
  ∀ x, in_list_rectangle x (parameter_list_rect tprog) ->
       param_unmap (param_map x) = x.

Axiom param_unmap_in_dom :
  ∀ x, in_list_rectangle x (parameter_list_rect prog) ->
       in_list_rectangle (param_unmap x) (parameter_list_rect tprog).

Axiom param_map_in_dom :
  ∀ x, in_list_rectangle x (parameter_list_rect tprog) ->
       in_list_rectangle (param_map x) (parameter_list_rect prog).

Axiom param_unmap_out_inv :
  ∀ data params, is_safe prog data (map R2val params) ->
                 eval_param_map_list prog params = eval_param_map_list tprog (param_unmap params).

Variable transf_correct:
  forall data params t,
    is_safe prog data (map R2val params) ->
    forward_simulation (Ssemantics.semantics prog data (map R2val params) (IRF t))
      (Ssemantics.semantics tprog data (map R2val (param_unmap params)) (IRF (target_map t))).

Axiom IFR_IRF_inv :
  ∀ x, IFR (IRF x) = x.
Axiom IRF_IFR_inv :
  ∀ x, IRF (IFR x) = x.

(*
Variable parameters_phi:
  flatten_parameter_variables tprog = flatten_parameter_variables prog.

Lemma dimen_preserved:
  parameter_dimension tprog = parameter_dimension prog.
Proof. rewrite /parameter_dimension/flatten_parameter_constraints. rewrite parameters_preserved //. Qed.
*)

Lemma returns_target_value_fsim data params t:
  is_safe prog data (map R2val params) ->
  returns_target_value prog data (map R2val params) (IRF t) ->
  returns_target_value tprog data (map R2val (param_unmap params)) (IRF (target_map t)).
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
  is_safe prog data (map R2val params) ->
  returns_target_value tprog data (map R2val (param_unmap params)) (IRF (target_map t)) ->
  returns_target_value prog data (map R2val params) (IRF t).
Proof.
  intros Hsafe (s1&s2&Hinit&Hstar&Hfinal).
  specialize (transf_correct data params t) as Hfsim.
  apply forward_to_backward_simulation in Hfsim as Hbsim;
    auto using semantics_determinate, semantics_receptive.
  destruct Hbsim as [index order match_states props].
  assert (∃ s10, Smallstep.initial_state (semantics prog data (map R2val params) (IRF t)) s10) as (s10&?).
  { apply inhabited_initial; eauto. }
  edestruct (bsim_match_initial_states) as (?&s1'&Hinit'&Hmatch1); eauto.
  edestruct (bsim_E0_star) as (?&s2'&Hstar'&Hmatch2); eauto.
  eapply (bsim_match_final_states) in Hmatch2 as (s2''&?&?); eauto; last first.
  { eapply star_safe; last eapply Hsafe; eauto. }
  exists s1', s2''. intuition eauto.
  { eapply star_trans; eauto. }
Qed.

Lemma  log_density_map data params :
  is_safe prog data (map R2val params) ->
  target_map (log_density_of_program prog data (map R2val params)) =
  log_density_of_program tprog data (map R2val (param_unmap params)).
Proof.
  intros HP.
  rewrite {1}/log_density_of_program.
  rewrite /pred_to_default_fun.
  destruct (ClassicalEpsilon.excluded_middle_informative) as [(v&Hreturns)|Hne].
  { destruct (ClassicalEpsilon.constructive_indefinite_description) as [x Hx].
    symmetry. erewrite log_density_of_program_trace; last first.
    { apply returns_target_value_fsim; auto.
      assert (x = IRF (IFR x)) as <-.
      { rewrite IRF_IFR_inv //. }
      eauto.
    }
    rewrite IFR_IRF_inv //.
  }
  rewrite {1}/log_density_of_program.
  rewrite /pred_to_default_fun.
  destruct (ClassicalEpsilon.excluded_middle_informative) as [(v&Hreturns)|Hne']; auto.
  {
    exfalso.
    replace v with (IRF (target_map (target_unmap (IFR v)))) in Hreturns; last first.
    { rewrite target_map_unmap IRF_IFR_inv //. }
    apply Hne.
    exists (IRF (target_unmap (IFR v))).
    apply returns_target_value_bsim; auto.
  }
  apply target_map_zero.
Qed.

Lemma safe_data_preserved :
  ∀ data, safe_data prog data -> safe_data tprog data.
Proof.
  intros data Hsafe.
  rewrite /safe_data. intros params Hin.
  assert (Hin': in_list_rectangle (param_map params) (parameter_list_rect prog)).
  { apply param_map_in_dom. auto. }
  specialize (Hsafe _ Hin').
  rewrite /is_safe. intros t s Hinit.
  epose proof (transf_correct data (param_map params) ((target_unmap (IFR t)))) as Hfsim.
  apply forward_to_backward_simulation in Hfsim as Hbsim;
    auto using semantics_determinate, semantics_receptive.
  edestruct Hbsim as [index order match_states props].
  eassert (∃ s10, Smallstep.initial_state (semantics prog data (map (λ r, Vfloat (IRF r)) (param_map params)) _) s10)
    as (s10&?).
  { apply inhabited_initial; eauto. }
  edestruct (bsim_match_initial_states) as (?&s1'&Hinit'&Hmatch1); eauto.
  { rewrite param_unmap_map //. eauto. }
  eapply bsim_safe; eauto.
  rewrite param_unmap_map in props; auto.
  rewrite target_map_unmap IRF_IFR_inv /R2val in props; eauto.
Qed.

Lemma denotational_preserved :
  denotational_refinement tprog prog.
Proof.
  exists (dimen_preserved).
  split.
  - intros data Hsafe. apply safe_data_preserved; auto.
  - intros data rt Hsafe Hwf Hsubset.
    rewrite /distribution_of_program. f_equal.
    2:{ rewrite /program_normalizing_constant.
        etransitivity; first eapply IIRInt_list_ext.
        { admit. }
        { intros xs Hin. rewrite /density_of_program.
          replace xs with (param_unmap (param_map xs)) at 1; last first.
          { rewrite param_unmap_map //. }
          rewrite -log_density_map.
          { reflexivity. }
          eapply Hsafe. apply param_map_in_dom. auto.
        }
Abort.
  
End DENOTATIONAL_SIMULATION.
