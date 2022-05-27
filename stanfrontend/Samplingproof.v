Require Import Smallstep.
Require Import Linking.
Require Import Globalenvs.

Require Import Stanlight.
Require Import Ssemantics.
Require Import Sampling.

Definition match_prog (p: program) (tp: program) :=
      match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.  

Lemma transf_program_match:
  forall p: program,  match_prog p (transf_program p).
Proof.
  intros. unfold match_prog.
  unfold transf_program. destruct p; simpl. 
  eapply match_transform_program; eauto.  
Qed. 

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variable TRANSL: match_prog prog tprog.
Let ge := globalenv prog.
Let tge := globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros. 
  eapply Genv.find_funct_transf; eauto.  
Qed. 

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof.
  intros. 
  eapply Genv.find_funct_ptr_transf; eauto. 
Qed. 

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. 
  eapply Genv.find_symbol_transf; eauto. 
Qed. 

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  intros. 
  eapply Genv.senv_transf; eauto.  
Qed. 

Scheme eval_expr_rec := Minimality for eval_expr Sort Prop
  with eval_lvalue_rec := Minimality for eval_lvalue Sort Prop
  with eval_exprlist_rec := Minimality for eval_exprlist Sort Prop.

Combined Scheme eval_expr_mutind from eval_expr_rec, eval_lvalue_rec, eval_exprlist_rec. 

Lemma evaluation_preserved:
  forall en m t,
      (forall e v, eval_expr ge en m t e v -> eval_expr tge en m t e v)
  /\  (forall e loc ofs, eval_lvalue ge en m t e loc ofs -> eval_lvalue tge en m t e loc ofs)
  /\  (forall el vl, eval_exprlist ge en m t el vl -> eval_exprlist tge en m t el vl).
Proof.
  intros. 
  set (P1 := fun e v => eval_expr ge en m t e v -> eval_expr tge en m t e v). 
  set (P2 := fun e loc ofs => eval_lvalue ge en m t e loc ofs -> eval_lvalue tge en m t e loc ofs).
  set (P3 := fun el vl => eval_exprlist ge en m t el vl -> eval_exprlist tge en m t el vl). 
  generalize (eval_expr_mutind ge en m t P1 P2 P3); intro IND.

  (* Evaluation of expressions *)
  split.
  intros e v EVAL. 
  eapply IND; eauto; intros; subst; subst P1; subst P2; subst P3; simpl; intros.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  generalize (functions_translated _ _ H3); intro FUN. eauto. 
  eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply eval_Evar_global; eauto. 
  rewrite symbols_preserved; auto. 
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.

  (* Evaluation of lvalues *)
  split.
  intros e loc ofs EVAL. 
  eapply IND; eauto; intros; subst; subst P1; subst P2; subst P3; simpl; intros.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  generalize (functions_translated _ _ H3); intro FUN. eauto. 
  eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply eval_Evar_global; eauto. 
  rewrite symbols_preserved; auto. 
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.

  (* Evaluation of list of expressions *)
  intros el vl EVAL. 
  eapply IND; eauto; intros; subst; subst P1; subst P2; subst P3; simpl; intros.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  generalize (functions_translated _ _ H3); intro FUN. eauto. 
  eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply eval_Evar_global; eauto. 
  rewrite symbols_preserved; auto. 
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
Qed.   

Lemma eval_expr_preserved:
  forall en m t e v,
  eval_expr ge en m t e v ->
  eval_expr tge en m t e v.
Proof. 
  intros. 
  eapply evaluation_preserved; eauto. 
Qed. 

Lemma eval_lvalue_preserved:
  forall en m t e loc ofs,
  eval_lvalue ge en m t e loc ofs ->
  eval_lvalue tge en m t e loc ofs.
Proof.
  intros. 
  eapply evaluation_preserved; eauto.  
Qed. 

Inductive match_cont: cont -> cont -> Prop :=
  | match_Kseq: forall s k k',
      match_cont k k' -> 
      match_cont (Kseq s k) (Kseq (transf_statement s) k')
  | match_Kstop: 
      match_cont Kstop Kstop.

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: forall f s t k k' e m
      (MCONT: match_cont k k'), 
      match_states (State f s t k e m) (State (transf_function f) (transf_statement s) t k' e m). 

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inversion MS; simpl in *; subst.
  - (* Skip *)
  inversion MCONT; subst.   
  exists (State (transf_function f) (transf_statement s) t k'0 e m).
  split.  
  econstructor.
  econstructor; eauto.
  - (* Sequence *) 
  exists (State (transf_function f) (transf_statement s1) t (Kseq (transf_statement s2) k') e m).
  split.
  econstructor.
  econstructor. econstructor; eauto.  
  - (* Assignment *)
  exists (State (transf_function f) Sskip t k' e m').
  split.
  generalize (eval_expr_preserved _ _ _ _ _ H0); intro.
  generalize (eval_lvalue_preserved _ _ _ _ _ _ H); intro.
  econstructor; eauto. inversion H2. 
  eapply assign_loc_value; eauto.  
  econstructor; eauto. 
  - (* Conditional statement *)  
  exists (State (transf_function f) (if b then (transf_statement s1) else (transf_statement s2)) t k' e m).
  split.
  generalize (eval_expr_preserved _ _ _ _ _ H); intro.
  econstructor; eauto.
  destruct b; econstructor; eauto.
  - (* Target *) 
  exists (State (transf_function f) Sskip (Floats.Float.add t v) k' e m).
  split.
  generalize (eval_expr_preserved _ _ _ _ _ H); intro.
  econstructor; eauto.
  econstructor; eauto.
Qed.   

Lemma transf_initial_states:
  forall S1, initial_state prog S1 ->
  exists S2, initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inversion H. 
  exists (State (transf_function f) (transf_statement (fn_body f)) (Floats.Float.of_int Integers.Int.zero) Kstop e m1).
  split. 
  econstructor; eauto. 
  eapply (Genv.init_mem_match TRANSL); eauto.
  rewrite symbols_preserved. eauto.
  generalize (function_ptr_translated b (Ctypes.Internal f) H2); intro TR.
  unfold transf_fundef in TR. eauto.  
  econstructor; eauto.
  econstructor.  
Qed. 

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> final_state S1 r -> final_state S2 r.
Proof.
  intros. 
  inversion H. inversion H0. subst. inversion H3; subst.   
  inversion MCONT; subst. 
  simpl. 
  econstructor; eauto. 
Qed. 

Theorem transf_program_correct:
  forward_simulation (Ssemantics.semantics prog) (Ssemantics.semantics tprog).
Proof.
  eapply forward_simulation_step.
  eapply senv_preserved. 
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.  
Qed. 

End PRESERVATION.

Global Instance TransfSamplingLink : TransfLink match_prog.
Admitted.