(* Proof of correctness of the Sampling pass.

   Since it preserves operational behavior exactly, this transform is
   the simplest verified pass so far. The forward simulation invariant
   is exact matching between the two program states.

*)

Require Import Smallstep.
Require Import Linking.
Require Import Globalenvs.

Require Import Stanlight.
Require Import Ssemantics.
Require Import Sampling.
Require Import DenotationalSimulation.
Require Import Coqlib.

Set Bullet Behavior "Strict Subproofs".

Definition match_prog (p: program) (tp: program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp /\
  pr_data_vars p = pr_data_vars tp /\
  pr_parameters_vars p = pr_parameters_vars tp.

Lemma transf_program_match:
  forall p: program,  match_prog p (transf_program p).
Proof.
  intros. unfold match_prog.
  unfold transf_program. destruct p; simpl.
  repeat split; eauto.
  eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variable data : list Values.val.
Variable params : list Values.val.
Variable TRANSL: match_prog prog tprog.
Let ge := globalenv prog.
Let tge := globalenv tprog.

Hint Unfold match_prog : core.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros. destruct TRANSL.
  eapply Genv.find_funct_transf; eauto.
Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof.
  intros. destruct TRANSL.
  eapply Genv.find_funct_ptr_transf; eauto.
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. destruct TRANSL.
  eapply Genv.find_symbol_transf; eauto.
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  intros. destruct TRANSL.
  eapply Genv.senv_transf; eauto.
Qed.

Lemma evaluation_preserved en m pm t:
      (forall e v, eval_expr ge en m pm t e v -> eval_expr tge en m pm t e v)
  /\  (forall el vl, eval_exprlist ge en m pm t el vl -> eval_exprlist tge en m pm t el vl)
  /\  (forall e loc ofs, eval_llvalue ge en m pm t e loc ofs -> eval_llvalue tge en m pm t e loc ofs)
  /\  (forall e loc ofs, eval_glvalue ge en m pm t e loc ofs -> eval_glvalue tge en m pm t e loc ofs).
Proof.
  intros.
  apply (eval_exprs_ind ge en m pm t).
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    { generalize (functions_translated _ _ H3). subst. simpl. auto. }
    { eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved. }
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - intros. eapply eval_Eplvalue; eauto.
  - intros. eapply eval_Eglvalue; eauto.
  - econstructor.
  - intros. econstructor; eauto.
  - intros. econstructor.
  - intros. econstructor. eauto.
  - intros. econstructor; eauto.
    rewrite symbols_preserved; auto.
  - intros. econstructor; eauto.
Qed.

Lemma eval_expr_preserved:
  forall en m pm t e v,
  eval_expr ge en m pm t e v ->
  eval_expr tge en m pm t e v.
Proof.
  intros.
  eapply evaluation_preserved; eauto.
Qed.

Lemma eval_glvalue_preserved:
  forall en m pm t e loc ofs,
  eval_glvalue ge en m pm t e loc ofs ->
  eval_glvalue tge en m pm t e loc ofs.
Proof.
  intros.
  eapply evaluation_preserved; eauto.
Qed.

Lemma eval_llvalue_preserved:
  forall en m pm t e loc ofs,
  eval_llvalue ge en m pm t e loc ofs ->
  eval_llvalue tge en m pm t e loc ofs.
Proof.
  intros.
  eapply evaluation_preserved; eauto.
Qed.

Lemma eval_exprlist_preserved:
  forall en m pm t el vl,
  eval_exprlist ge en m pm t el vl ->
  eval_exprlist tge en m pm t el vl.
Proof.
  intros.
  eapply evaluation_preserved; eauto.
Qed.

Lemma assign_global_locs_preserved bs m1 vs m2 :
  assign_global_locs ge bs m1 vs m2 ->
  assign_global_locs tge bs m1 vs m2.
Proof.
  induction 1; econstructor; eauto.
  - rewrite symbols_preserved; eauto.
  - inversion H0; eapply assign_loc_value; eauto.
Qed.

Lemma reserve_global_params_preserved bs m1 m2 :
  reserve_global_params bs m1 m2 ->
  reserve_global_params bs m1 m2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma assign_global_params_preserved bs m1 vs m2 :
  assign_global_params bs m1 vs m2 ->
  assign_global_params bs m1 vs m2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma set_global_params_preserved ids bs m1 vs m2 :
  set_global_params ids bs vs m1 m2 ->
  set_global_params ids bs vs m1 m2.
Proof.
  intros (?&?&?). eexists; split;
    eauto using reserve_global_params_preserved, assign_global_params_preserved.
Qed.

Lemma data_vars_preserved :
  pr_data_vars tprog = pr_data_vars prog.
Proof.
  unfold match_prog in TRANSL. intuition.
Qed.

Lemma parameters_vars_preserved :
  pr_parameters_vars tprog = pr_parameters_vars prog.
Proof.
  unfold match_prog in TRANSL. intuition.
Qed.

Lemma parameters_ids_preserved :
  pr_parameters_ids tprog = pr_parameters_ids prog.
Proof.
  unfold pr_parameters_ids. rewrite parameters_vars_preserved. auto.
Qed.

Inductive match_cont: cont -> cont -> Prop :=
  | match_Kseq: forall s k k',
      match_cont k k' ->
      match_cont (Kseq s k) (Kseq (transf_statement s) k')
  | match_Kstop:
      match_cont Kstop Kstop
  | match_Kfor: forall id e2 s k k',
      match_cont k k' ->
      match_cont (Kfor id e2 s k) (Kfor id e2 (transf_statement s) k').

Inductive match_states: state -> state -> Prop :=
  | match_start_states: forall f s t e m pm,
      match_states (Start f s t e m pm) (Start (transf_function f) (transf_statement s) t e m pm)
  | match_regular_states: forall f s t k k' e m pm
      (MCONT: match_cont k k'),
      match_states (State f s t k e m pm) (State (transf_function f) (transf_statement s) t k' e m pm)
  | match_return_states: forall t,
      match_states (Return t) (Return t).

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inversion MS; simpl in *; subst.
  - (* Start *)
  exists (State (transf_function f) (transf_statement s) t Kstop e m pm).
  split.
  econstructor.
  econstructor; eauto.
  econstructor; eauto.
  - (* Return *)
  inv MCONT.
  exists (Return t).
  split.
  econstructor.
  econstructor; eauto.
  - (* Skip *)
  inversion MCONT; subst.
  exists (State (transf_function f) (transf_statement s) t k'0 e m pm).
  split.
  econstructor.
  econstructor; eauto.
  - (* Sequence *)
  exists (State (transf_function f) (transf_statement s1) t (Kseq (transf_statement s2) k') e m pm).
  split.
  econstructor.
  econstructor. econstructor; eauto.
  - (* Local Assignment *)
  exists (State (transf_function f) Sskip t k' e' m pm).
  split.
  generalize (eval_expr_preserved _ _ _ _ _ _ H0); intro.
  generalize (eval_llvalue_preserved _ _ _ _ _ _ _ H); intro.
  econstructor; eauto.
  econstructor; eauto.
  - (* Global Assignment *)
  exists (State (transf_function f) Sskip t k' e m' pm).
  split.
  generalize (eval_expr_preserved _ _ _ _ _ _ H0); intro.
  generalize (eval_glvalue_preserved _ _ _ _ _ _ _ H); intro.
  econstructor; eauto. inversion H2.
  eapply assign_loc_value; eauto.
  econstructor; eauto.
  - (* Conditional statement *)
  exists (State (transf_function f) (if b then (transf_statement s1) else (transf_statement s2)) t k' e m pm).
  split.
  generalize (eval_expr_preserved _ _ _ _ _ _ H); intro.
  econstructor; eauto.
  destruct b; econstructor; eauto.
  - (* Target *)
  exists (State (transf_function f) Sskip (Floats.Float.add t v) k' e m pm).
  split.
  generalize (eval_expr_preserved _ _ _ _ _ _ H); intro.
  econstructor; eauto.
  econstructor; eauto.
  - (* Tilde *)
  exists (State (transf_function f) Sskip (Floats.Float.add t vres) k' e m pm).
  split.
  generalize (eval_expr_preserved _ _ _ _ _ _ H); intro.
  generalize (eval_expr_preserved _ _ _ _ _ _ H0); intro.
  generalize (eval_exprlist_preserved _ _ _ _ _ _ H1); intro.
  econstructor.
  {
    econstructor; eauto using functions_translated.
    * econstructor; eauto.
    * simpl. eauto.
    * eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
  }
  econstructor; eauto.
  - (* For start true *)
  eexists. split.
  econstructor; eauto using eval_llvalue_preserved, eval_expr_preserved.
  econstructor. econstructor; eauto.
  - (* For start false *)
  eexists. split.
  eapply step_for_start_false; eauto using eval_llvalue_preserved, eval_expr_preserved.
  econstructor. eauto.
  - (* For iter true *)
  inv MCONT.
  eexists. split.
  econstructor; eauto using eval_llvalue_preserved, eval_expr_preserved.
  econstructor. econstructor; eauto.
  - (* For iter false *)
  inv MCONT.
  eexists. split.
  eapply step_for_iter_false; eauto using eval_llvalue_preserved, eval_expr_preserved.
  econstructor. eauto.
Qed.

Lemma transf_initial_states:
  forall S1, initial_state prog data params S1 ->
  exists S2, initial_state tprog data params S2 /\ match_states S1 S2.
Proof.
  intros. inversion H.
  exists (Start (transf_function f) (transf_statement (fn_body f)) (Floats.Float.of_int Integers.Int.zero) e m1 pm).
  split.
  econstructor; eauto.
  destruct TRANSL as (TRANSL'&_).
  eapply (Genv.init_mem_match TRANSL'); eauto.
  rewrite symbols_preserved. eauto.
  generalize (function_ptr_translated b (Ctypes.Internal f) H2); intro TR.
  unfold transf_fundef in TR. eauto.
  eapply assign_global_locs_preserved. rewrite data_vars_preserved; eauto.
  eapply set_global_params_preserved; rewrite parameters_vars_preserved, parameters_ids_preserved. eauto.
  econstructor; eauto.
Qed.

Lemma transf_final_states:
  forall S1 S2 t r, match_states S1 S2 -> final_state t S1 r -> final_state t S2 r.
Proof.
  intros S1 S2 t r Hmatch Hfinal. inv Hfinal; inv Hmatch.
  { econstructor. auto. }
  { econstructor. auto. }
Qed.

Theorem transf_program_correct t:
  forward_simulation (Ssemantics.semantics prog data params t) (Ssemantics.semantics tprog data params t).
Proof.
  eapply forward_simulation_step.
  eapply senv_preserved.
  eexact transf_initial_states.
  intros. eapply transf_final_states; eauto.
  exact step_simulation.
Qed.

End PRESERVATION.

Section DENOTATIONAL_PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variable TRANSL: match_prog prog tprog.

Theorem denotational_preserved :
  denotational_refinement tprog prog.
Proof.
  eapply DenotationalSimulation.denotational_preserved.
  - intros data params t Hsafe.
    apply transf_program_correct; eauto.
  - destruct TRANSL as (Hmatch&?&?). eapply match_flatten_parameter_variables; eauto.
  - destruct TRANSL as (Hmatch&_). eapply match_program_external_funct; eauto.
    intros. simpl. congruence.
  - eapply Genv.senv_transf; apply TRANSL.
  - apply symbols_preserved; auto.
Qed.

End DENOTATIONAL_PRESERVATION.
