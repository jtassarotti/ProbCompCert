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

(* TODO: generalize these results to any denotational semantics obtained this way *)
Section DENOTATIONAL_SIMULATION.

Variable prog: Stanlight.program.
Variable tprog: Stanlight.program.
(* prog is assumed to be safe/well-defined on data/params satisfying a predicate P *)

Lemma inhabited_initial :
  ∀ data params t, is_safe prog data params -> ∃ s, Smallstep.initial_state (semantics prog data params t) s.
Proof.
  intros data params t Hsafe. destruct Hsafe as (Hex&_). eapply Hex.
Qed.

Variable transf_correct:
  forall data params t,
    is_safe prog data params ->
    forward_simulation (Ssemantics.semantics prog data params t) (Ssemantics.semantics tprog data params t).

Variable parameters_preserved:
  flatten_parameter_variables tprog = flatten_parameter_variables prog.

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
  rewrite /genv_has_mathlib.
  rewrite /genv_exp_spec/genv_log_spec/genv_expit_spec.
  rewrite ?symbols_preserved.
  intros (Hexp&Hexpit&Hlog).
  intuition.
  { destruct Hexp as (loc&?). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct Hexpit as (loc&?). exists loc. split; first by intuition.
    eapply external_funct_preserved; intuition eauto. }
  { destruct Hlog as (loc&?). exists loc. split; first by intuition.
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
  { eapply Hsafe; eauto. }
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
  rewrite /is_safe. split.
  { intros t.
    edestruct Hsafe as ((s&Hinit)&_).
    specialize (transf_correct data (map (λ r, Vfloat (IRF r)) params) t Hsafe) as Hfsim.
    destruct Hfsim. edestruct fsim_match_initial_states as (ind&s'&?); eauto.
    exists s'. intuition.
  }
  split.
  {
    intros t s Hinit.
    specialize (transf_correct data (map (λ r, Vfloat (IRF r)) params) t) as Hfsim.
    apply forward_to_backward_simulation in Hfsim as Hbsim;
      auto using semantics_determinate, semantics_receptive.
    edestruct Hbsim as [index order match_states props].
    assert (∃ s10, Smallstep.initial_state (semantics prog data (map (λ r, Vfloat (IRF r)) params) t) s10) as (s10&?).
    { apply inhabited_initial; eauto. }
    edestruct (bsim_match_initial_states) as (?&s1'&Hinit'&Hmatch1); eauto.
    eapply bsim_safe; eauto.
    apply Hsafe; eauto.
  }
  {
    edestruct Hsafe as (?&?&Hret). destruct Hret as (t&?).
    eexists. apply returns_target_value_fsim; eauto.
  }
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
  split; [| split; [| split]].
  - intros data Hsafe ?. apply safe_data_preserved; auto.
  - intros data rt vt Hsafe Hwf Hsubset.
    rewrite /is_program_distribution/is_program_normalizing_constant/is_unnormalized_program_distribution.
    intros ? (vnum&vnorm&Hneq0&His_norm&His_num&Hdiv).
    exists vnum, vnorm. repeat split; auto.
    {
      rewrite parameter_list_rect_preserved.
      eapply is_IIRInt_list_ext; try eassumption; [].
      * intros x Hin. rewrite /program_normalizing_constant_integrand.
        { rewrite /density_of_program. rewrite log_density_equiv //. eapply Hsafe. eauto. }
    }
    {
      rewrite parameter_list_rect_preserved.
      eapply is_IIRInt_list_ext; try eassumption; [].
      intros x Hin. rewrite /unnormalized_program_distribution_integrand. f_equal.
      { rewrite /density_of_program. rewrite log_density_equiv //. eapply Hsafe. eauto. }
      { f_equal. rewrite /eval_param_map_list.
        assert (flatten_parameter_out prog = flatten_parameter_out tprog) as ->.
        { rewrite /flatten_parameter_out parameters_preserved //. }
        eapply map_ext.
        intros (r&f) => /=. f_equal.
        apply eval_expr_fun_match; eauto.
      }
    }
  - intros. apply tprog_genv_has_mathlib; auto.
  - rewrite /parameter_list_rect/flatten_parameter_constraints. rewrite parameters_preserved //.
    apply rectangle_list_subset_refl.
Qed.

End DENOTATIONAL_SIMULATION.
