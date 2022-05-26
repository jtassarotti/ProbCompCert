Require Import Smallstep.
Require Import Linking.
Require Import Globalenvs.

Require Import Stanlight.
Require Import Ssemantics.
Require Import Sampling.

Parameter match_prog: program -> program -> Prop.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
Admitted.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variable TRANSL: match_prog prog tprog.
Let ge := globalenv prog.
Let tge := globalenv tprog.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
Admitted. 

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. 
Admitted. 

Lemma eval_expr_preserved:
  forall en m t e v,
  eval_expr ge en m t e v ->
  eval_expr tge en m t e v.
Proof. 
Admitted.

Lemma eval_lvalue_preserved:
  forall en m t e loc ofs,
  eval_lvalue ge en m t e loc ofs ->
  eval_lvalue tge en m t e loc ofs.
Proof.
Admitted. 

Inductive match_cont: cont -> cont -> Prop :=
  | match_Kseq: forall s k k',
      match_cont k k' -> 
      match_cont (Kseq s k) (Kseq (transf_statement s) k').

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
  econstructor; eauto. 
  admit. (* Preservation of assign location *)
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
Admitted.   

Lemma transf_initial_states:
  forall S1, initial_state prog S1 ->
  exists S2, initial_state tprog S2 /\ match_states S1 S2.
Proof.
Admitted. 

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> final_state S1 r -> final_state S2 r.
Proof.
Admitted. 

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