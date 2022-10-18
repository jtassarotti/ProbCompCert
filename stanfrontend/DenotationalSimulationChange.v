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

Section DENOTATIONAL_SIMULATION.

Variable prog: Stanlight.program.
Variable tprog: Stanlight.program.
(* unconstrain *)
Variable param_unmap : list R -> list R.
(* constrain *)
Variable param_map : list R -> list R.

(* Input:
   - data
   - unconstrained parameters 
   - original target
   Output:
   - corrected target *)

Variable target_map : list val -> list val -> R -> R.
Variable target_unmap : list val -> list val -> R -> R.

Variable target_map_unmap : ∀ d p x, target_map d p (target_unmap d p x) = x.

Lemma inhabited_initial :
  ∀ data params t, is_safe prog data params -> ∃ s, Smallstep.initial_state (semantics prog data params t) s.
Proof.
  intros data params t Hsafe. destruct Hsafe as (Hex&_). eapply Hex.
Qed.

Variable dimen_preserved: parameter_dimension tprog = parameter_dimension prog.

Variable wf_paramter_rect_tprog :
  wf_rectangle_list (parameter_list_rect prog) ->
  wf_rectangle_list (parameter_list_rect tprog).

Variable param_map_unmap :
  ∀ x, in_list_rectangle x (parameter_list_rect prog) ->
       param_map (param_unmap x) = x.

Variable param_unmap_map :
  ∀ x,
       wf_rectangle_list (parameter_list_rect prog) ->
       in_list_rectangle x (parameter_list_rect tprog) ->
       param_unmap (param_map x) = x.

Variable param_unmap_in_dom :
  ∀ x, in_list_rectangle x (parameter_list_rect prog) ->
       in_list_rectangle (param_unmap x) (parameter_list_rect tprog).

Variable param_map_in_dom :
  ∀ x,
       wf_rectangle_list (parameter_list_rect prog) ->
       in_list_rectangle x (parameter_list_rect tprog) ->
       in_list_rectangle (param_map x) (parameter_list_rect prog).

Variable transf_correct:
  forall data params t,
    is_safe prog data (map R2val params) ->
    forward_simulation (Ssemantics.semantics prog data (map R2val params) (IRF t))
      (Ssemantics.semantics tprog data (map R2val (param_unmap params))
         (IRF (target_map data (map R2val (param_unmap params)) t))).

Variable IFR_IRF_inv :
  ∀ x, IFR (IRF x) = x.
Variable IRF_IFR_inv :
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
  returns_target_value tprog data
    (map R2val (param_unmap params))
    (IRF (target_map data (map R2val (param_unmap params)) t)).
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
  returns_target_value tprog data (map R2val (param_unmap params))
    (IRF (target_map data (map R2val (param_unmap params)) t)) ->
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
  { eapply Hsafe; eauto. }
  eapply (bsim_match_final_states) in Hmatch2 as (s2''&?&?); eauto; last first.
  { eapply star_safe; last eapply Hsafe; eauto. }
  exists s1', s2''. intuition eauto.
  { eapply star_trans; eauto. }
Qed.

Lemma  log_density_map data params :
  is_safe prog data (map R2val params) ->
  target_map data (map R2val (param_unmap params)) (log_density_of_program prog data (map R2val params)) =
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
  exfalso. eapply Hne. eapply HP.
Qed.

Lemma safe_data_preserved :
  ∀ data, wf_rectangle_list (parameter_list_rect prog) -> safe_data prog data -> safe_data tprog data.
Proof.
  intros data Hwf Hsafe.
  rewrite /safe_data. intros params Hin.
  assert (Hin': in_list_rectangle (param_map params) (parameter_list_rect prog)).
  { apply param_map_in_dom; auto. }
  specialize (Hsafe _ Hin').
  rewrite /is_safe. split.
  { intros t.
    edestruct Hsafe as ((s&Hinit)&_).
    specialize (transf_correct data (param_map params) (target_unmap data (map R2val params) (IFR t)) Hsafe)
      as Hfsim.
    destruct Hfsim. edestruct fsim_match_initial_states as (ind&s'&?); eauto.
    exists s'. rewrite param_unmap_map in H; intuition.
  }
  split.
  {
    intros t s Hinit.
    epose proof (transf_correct data (param_map params) ((target_unmap data (map R2val params)
                                                            (IFR t)))) as Hfsim.
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
    apply Hsafe; eauto.
  }
  {
    edestruct Hsafe as (?&?&Hret). destruct Hret as (t&?).
    exists ((IRF (target_map data (map R2val (param_unmap (param_map params))) (IFR t)))).
    replace params with (param_unmap (param_map params)) at 1.
    { eapply returns_target_value_fsim; eauto. rewrite IRF_IFR_inv; eauto. }
    { rewrite param_unmap_map //. }
  }
Qed.

(* The last lemma assumes that the transformation actually in fact
   corresponds to a change of variables where we've accounted for the Jacobian *)
Variable gs : list (R -> R).
Variable log_dgs : list (R -> R).

Variable param_map_gs :
  ∀ x, in_list_rectangle x (parameter_list_rect tprog) ->
       list_apply gs x = param_map x.
Variable target_map_dgs :
  ∀ data x, in_list_rectangle x (parameter_list_rect tprog) ->
  target_map data (map R2val x) (log_density_of_program prog data (map R2val (param_map x))) =
  list_plus (list_apply log_dgs x) + log_density_of_program prog data (map R2val (param_map x)).
Variable gs_monotone :
  wf_rectangle_list (parameter_list_rect prog) ->
  Forall2 strict_monotone_on_interval (parameter_list_rect tprog) gs.
Variable gs_image :
  wf_rectangle_list (parameter_list_rect prog) ->
  Forall3 is_interval_image gs (parameter_list_rect tprog) (parameter_list_rect prog).
Variable gs_deriv :  Forall3 continuous_derive_on_interval (parameter_list_rect tprog) gs
    (map (λ (f : R → R) (x : R), exp (f x)) log_dgs).
Variable eval_param_map_list_preserved :
  ∀ x,
    in_list_rectangle x (parameter_list_rect tprog) ->
    eval_param_map_list tprog x = eval_param_map_list prog (param_map x).

Set Nested Proofs Allowed.

Lemma exp_list_plus l :
  exp (list_plus l) = list_mult (map exp l).
Proof.
  induction l.
  - rewrite //= exp_0 //.
  - rewrite //= exp_plus IHl //.
Qed.

Lemma map_list_apply {A B C} (g : B -> C) (fs : list (A -> B)) xs :
  map g (list_apply fs xs) = list_apply (map (λ f, λ x, g (f x)) fs) xs.
Proof.
  revert xs.
  induction fs => xs.
  - rewrite //=.
  - destruct xs => //=.
    rewrite IHfs /=.
    rewrite /list_apply/=//.
Qed.

Lemma denotational_preserved :
  denotational_refinement tprog prog.
Proof.
  exists (dimen_preserved).
  split.
  - intros data Hwf Hsafe. apply safe_data_preserved; auto.
  - intros data rt vt Hsafe Hwf Hsubset.
    rewrite /is_program_distribution/is_program_normalizing_constant/is_unnormalized_program_distribution.
    intros (vnum&vnorm&Hneq0&His_norm&His_num&Hdiv).
    eexists vnum, vnorm;  repeat split; auto.
    {
      assert (vnorm = IIRInt_list (program_normalizing_constant_integrand prog data) (parameter_list_rect prog))
        as ->.
      { symmetry. apply is_IIRInt_list_unique. auto. }
      eapply is_IIRInt_list_ext; last first.
      { eapply (is_IIRInt_list_comp_noncont _ gs (map (λ f, λ x, exp (f x)) log_dgs));
          last (by (eexists; eauto)); eauto.
      }
      2: {  eauto. }
      intros x Hin. simpl.
      rewrite /program_normalizing_constant_integrand/density_of_program.
      symmetry.
      replace x with (param_unmap (param_map x)) at 1; last first.
      { rewrite param_unmap_map //. }
      rewrite -log_density_map; eauto.
      rewrite param_unmap_map //.
      rewrite target_map_dgs; eauto.
      rewrite exp_plus.
      rewrite exp_list_plus.

      rewrite map_list_apply -param_map_gs //.
    }
    {
      assert (vnum = IIRInt_list (unnormalized_program_distribution_integrand prog data rt)
                       (parameter_list_rect prog))
        as ->.
      { symmetry. apply is_IIRInt_list_unique. auto. }
      eapply is_IIRInt_list_ext; last first.
      { eapply (is_IIRInt_list_comp_noncont _ gs (map (λ f, λ x, exp (f x)) log_dgs));
          last (by (eexists; eauto)); eauto.
      }
      2: {  eauto. }
      intros x Hin. simpl.
      rewrite /unnormalized_program_distribution_integrand/density_of_program.
      symmetry.
      replace x with (param_unmap (param_map x)) at 1; last first.
      { rewrite param_unmap_map //. }
      rewrite -log_density_map; eauto.
      rewrite param_unmap_map //.
      rewrite target_map_dgs; eauto.
      rewrite exp_plus.
      rewrite exp_list_plus.

      rewrite map_list_apply -param_map_gs //.
      rewrite -?Rmult_assoc.
      f_equal.


      rewrite eval_param_map_list_preserved //.
      rewrite param_map_gs //.
    }
Qed.

End DENOTATIONAL_SIMULATION.
