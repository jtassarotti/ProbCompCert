(* This is not directly used currently, but it helps explain the
general idea. *)

Require Import Coqlib Errors Maps String.
Local Open Scope string_scope.
Require Import Integers Floats Values AST Memory Builtins Events Globalenvs.
Require Import Ctypes Cop Stanlight.
Require Import Smallstep.
Require Import Linking.
Require Import IteratedRInt.
Require Import StanEnv.
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
(* prog is assumed to be safe/well-defined on data/params satisfying a predicate P *)

Lemma inhabited_initial :
  ∀ data params t, is_safe prog data params -> ∃ s, Smallstep.initial_state (semantics prog data params t) s.
Proof.
  intros data params t Hsafe. destruct Hsafe as (Hex&_). eapply Hex.
Qed.

Variable target_map : list val -> list val -> R -> R.
Variable param_map : list val -> list val.

(* This could be dropped if we were a bit more careful. *)
Variable target_map_inv : ∀ d ps r, ∃ r', target_map d ps r' = r.

Variable transf_correct:
  forall data params t,
    genv_has_mathlib (globalenv prog) ->
    is_safe prog data params ->
    forward_simulation (Ssemantics.semantics prog data params (IRF t)) (Ssemantics.semantics tprog data (param_map params) (IRF (target_map data params t))).

Variable external_funct_preserved:
  match_external_funct (globalenv prog) (globalenv tprog).

Variable global_env_equiv :
  Senv.equiv (globalenv prog) (globalenv tprog).

Variable symbols_preserved:
  forall id,
  Genv.find_symbol (globalenv tprog) id = Genv.find_symbol (globalenv prog) id.

Lemma tprog_genv_has_mathlib :
  genv_has_mathlib (globalenv prog) ->
  genv_has_mathlib (globalenv tprog).
Proof.
  destruct 1.
  split; rewrite /genv_exp_spec/genv_log_spec/genv_expit_spec/genv_normal_lpdf_spec/genv_normal_lupdf_spec;
         rewrite /genv_cauchy_lpdf_spec/genv_cauchy_lupdf_spec;
    rewrite ?symbols_preserved.
  intuition.
  { destruct GENV_EXP as (loc&?). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct GENV_EXPIT as (loc&?). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct GENV_LOG as (loc&?). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct GENV_NORMAL_LPDF as (loc&Hnor). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct GENV_NORMAL_LUPDF as (loc&Hnor). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct GENV_CAUCHY_LPDF as (loc&Hnor). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct GENV_CAUCHY_LUPDF as (loc&Hnor). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
Qed.

Lemma match_flatten_parameter_variables (p tp : program) f :
  match_program f eq p tp ->
  pr_parameters_vars p = pr_parameters_vars tp ->
  flatten_parameter_variables tp = flatten_parameter_variables p.
Proof.
  intros Hmatch Heq.
    unfold flatten_parameter_variables. simpl.
    unfold flatten_ident_variable_list.
    rewrite Heq.
    f_equal. f_equal.
    apply List.map_ext.
    intros ((id&b)&f').
    f_equal.
    unfold lookup_def_ident.
    destruct Hmatch as (H1&H2).
    simpl in H1.
    edestruct (@list_find_fst_forall2 _ (AST.globdef fundef variable)
               ((fun '(id', v) => Pos.eq_dec id id' && is_gvar v))) as [Hleft|Hright]; first eauto.
    { intros ?? (?&?); auto. }
    { intros (?&?) (?&?). inversion 1 as [Hfst Hglob].
      simpl in Hfst; subst. simpl in Hglob. inversion Hglob. subst.
      * rewrite //=.
      * subst. rewrite //=.
    }
    { simpl. destruct Hleft as (id'&g1&g2&->&->&Hident).
      inversion Hident as [Hfst_eq Hglob]. simpl in Hglob.
      inversion Hglob; auto.
      subst. inversion H. congruence. }
    { destruct Hright as (->&->). auto. }
Qed.

Lemma match_program_external_funct (p tp : program) transf_fundef :
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp ->
  (∀ ef tyargs tyres cconv,
      transf_fundef (Ctypes.External ef tyargs tyres cconv) =
      Ctypes.External ef tyargs tyres cconv) ->
  (∀ f ef tyargs tyres cconv,
      transf_fundef (Internal f) <> External ef tyargs tyres cconv) ->
  match_external_funct (globalenv p) (globalenv tp).
Proof.
  intros Hmatch Hext Hint.
  - unfold match_external_funct, sub_external_funct.
    split.
    * intros. rewrite -Hext. eapply @Genv.find_funct_transf; eauto.
    * intros.
      edestruct (Genv.find_funct_transf_rev Hmatch) as (p'&->&Htransf); eauto.
      destruct p'; simpl in Htransf; try congruence.
      { exfalso. eapply Hint. eauto. }
      rewrite Hext in Htransf.
      inversion Htransf. subst. eauto.
Qed.

Variable dimen_preserved:
  parameter_dimension tprog = parameter_dimension prog.

Section has_mathlib.

Variable MATH: genv_has_mathlib (globalenv prog).

Lemma returns_target_value_fsim data params t:
  is_safe prog data params ->
  returns_target_value prog data params (IRF t) ->
  returns_target_value tprog data (param_map params) (IRF (target_map data params t)).
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
  returns_target_value tprog data (param_map params) (IRF (target_map data params t)) ->
  returns_target_value prog data params (IRF t).
Proof.
  intros Hsafe (s1&s2&Hinit&Hstar&Hfinal).
  specialize (transf_correct data params t) as Hfsim.
  apply forward_to_backward_simulation in Hfsim as Hbsim;
    auto using semantics_determinate, semantics_receptive.
  destruct Hbsim as [index order match_states props].
  assert (∃ s10, Smallstep.initial_state (semantics prog data params (IRF t)) s10) as (s10&?).
  { apply inhabited_initial; eauto. }
  edestruct (bsim_match_initial_states) as (?&s1'&Hinit'&Hmatch1); eauto.
  edestruct (bsim_E0_star) as (?&s2'&Hstar'&Hmatch2); eauto.
  { eapply Hsafe; eauto. }
  eapply (bsim_match_final_states) in Hmatch2 as (s2''&?&?); eauto; last first.
  { eapply star_safe; last eapply Hsafe; eauto. }
  exists s1', s2''. intuition eauto.
  { eapply star_trans; eauto. }
Qed.

Lemma  log_density_equiv data params :
  is_safe prog data params ->
  target_map data params (log_density_of_program prog data params)
  = log_density_of_program tprog data (param_map params).
Proof.
  intros HP.
  rewrite {1}/log_density_of_program.
  rewrite /pred_to_default_fun.
  destruct (ClassicalEpsilon.excluded_middle_informative) as [(v&Hreturns)|Hne].
  { destruct (ClassicalEpsilon.constructive_indefinite_description) as [x Hx].
    symmetry.
    replace x with (IRF (IFR x)) in Hx; last by (rewrite IRF_IFR_inv).
    exploit returns_target_value_fsim; eauto.
    intros Heq%log_density_of_program_trace. rewrite Heq.
    rewrite IFR_IRF_inv //.
  }
  symmetry.
  rewrite {1}/log_density_of_program.
  rewrite /pred_to_default_fun.
  destruct (ClassicalEpsilon.excluded_middle_informative) as [(v&Hreturns)|Hne']; auto.
  {
    exfalso. apply Hne.
    edestruct (target_map_inv data params (IFR v)) as (r'&Heq).
    rewrite -{1}(IRF_IFR_inv v) in Hreturns. 
    rewrite -Heq in Hreturns.
    eexists.
    exploit returns_target_value_bsim; eauto.
  }
  { exfalso. eapply Hne. eapply HP. }
Qed.

End has_mathlib.

End DENOTATIONAL_SIMULATION.
