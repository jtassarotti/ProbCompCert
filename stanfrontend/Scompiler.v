Require Import Stanlight.
Require Import Ssemantics.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.
Require Import Asm. 
Require Import String.

Require Import Compiler.
Require Import Reparameterization. 
Require Import Clightification.
Require Import Sampling.
Require Import VariableAllocation.
Require Import Target.
Require Import Sbackend.
Require Import Coqlib.
Require Import Linking. 

Require Reparameterizationproof.
Require Clightificationproof.
Require Samplingproof.
Require VariableAllocationproof.
Require Targetproof.
Require Sbackendproof.

Open Scope string_scope.
Local Open Scope linking_scope.

(** Pretty-printers (defined in Caml). *)
Parameter print_CStan: Z -> CStan.program -> unit.

Definition transf_stan_program(p: Stanlight.program): res Clight.program :=
  OK p
  @@ time "Sampling" Sampling.transf_program
  @@@ time "Reparameterization" Reparameterization.transf_program
  @@@ time "Clightification" Clightification.transf_program
  @@ print (print_CStan 0)
  @@@ time "VariableAllocation" VariableAllocation.transf_program
  @@ print (print_CStan 1)
  @@@ time "Target" Target.transf_program
  @@ print (print_CStan 2)
  @@@ time "Backend" backend. 

Definition ProbCompCert's_passes :=
      mkpass Samplingproof.match_prog
  ::: mkpass Reparameterizationproof.match_prog
  ::: mkpass Clightificationproof.match_prog
  ::: mkpass VariableAllocationproof.match_prog
  ::: mkpass Targetproof.match_prog
  ::: mkpass Sbackendproof.match_prog
  ::: pass_nil _.

Definition match_prog_test: Stanlight.program -> Clight.program -> Prop :=
  pass_match (compose_passes ProbCompCert's_passes).

Theorem transf_stan_program_match:
  forall p tp,
  transf_stan_program p = OK tp ->
  match_prog_test p tp.
Proof.
  intros p tp T.
  unfold transf_stan_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p1 :=  Sampling.transf_program p) in *. 
  destruct (Reparameterization.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Clightification.transf_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (VariableAllocation.transf_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  destruct (Target.transf_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (Sbackend.backend p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold match_prog_test; simpl.
  exists p1; split. eapply Samplingproof.transf_program_match; eauto.
  exists p2; split. eapply Reparameterizationproof.transf_program_match; eauto.
  exists p3; split. eapply Clightificationproof.transf_program_match; eauto.
  exists p4; split. eapply VariableAllocationproof.transf_program_match; eauto.
  exists p5; split. eapply Targetproof.transf_program_match; eauto.
  exists p6; split. eapply Sbackendproof.transf_program_match; eauto.
  inversion T.
  reflexivity.
Qed. 

Lemma transf_stan_program_correct_pre:
  forall p tp data params t,
  match_prog_test p tp ->
  transf_stan_program p = OK tp ->
  forward_simulation (Ssemantics.semantics p data params t) (Clight.semantics1 tp).
Proof.
  intros p tp data params t M. unfold match_prog_test, pass_match in M; simpl in M.
  Ltac DestructM_test :=
    match goal with
      [ H: exists p, _ /\ _ |- _ ] =>
        let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
        destruct H as (p & M & MM); clear H
    end.
  repeat DestructM_test. subst tp.

  intros.
  eapply compose_forward_simulations.
    eapply Samplingproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Reparameterizationproof.transf_program_correct; try eassumption.
  eapply compose_forward_simulations.
    eapply Clightificationproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply VariableAllocationproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Targetproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Sbackendproof.transf_program_correct; eassumption.  
  eapply forward_simulation_identity; eauto.
Qed.

Theorem transf_stan_program_correct:
  forall p tp data params t,
  transf_stan_program p = OK tp ->
  forward_simulation (Ssemantics.semantics p data params t) (Clight.semantics1 tp).
Proof.
  intros. 
  eapply transf_stan_program_correct_pre; try eassumption.
  eapply transf_stan_program_match; eassumption.
Qed.

Definition CompCert's_passes :=
      mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

Definition match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

Theorem transf_clight_program_match:
  forall p tp,
  transf_clight_program p = OK tp ->
  match_prog p tp.
Proof. 
  intros p tp T.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals.transf_program p) as [p1|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p1) as [p2|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p2) as [p3|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p3) as [p4|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p4) as [p5|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p6 := total_if Compopts.optim_tailcalls Tailcall.transf_program p5) in *.
  destruct (Inlining.transf_program p6) as [p7|e] eqn:P8; simpl in T; try discriminate.
  set (p8 := Renumber.transf_program p7) in *.
  set (p9 := total_if Compopts.optim_constprop Constprop.transf_program p8) in *.
  set (p10 := total_if Compopts.optim_constprop Renumber.transf_program p9) in *.
  destruct (partial_if Compopts.optim_CSE CSE.transf_program p10) as [p11|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if Compopts.optim_redundancy Deadcode.transf_program p11) as [p12|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p12) as [p13|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p13) as [p14|e] eqn:P15; simpl in T; try discriminate.
  set (p15 := Tunneling.tunnel_program p14) in *.
  destruct (Linearize.transf_program p15) as [p16|e] eqn:P17; simpl in T; try discriminate.
  set (p17 := CleanupLabels.transf_program p16) in *.
  destruct (partial_if Compopts.debug Debugvar.transf_program p17) as [p18|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p18) as [p19|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p1; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p2; split. apply Cshmgenproof.transf_program_match; auto.
  exists p3; split. apply Cminorgenproof.transf_program_match; auto.
  exists p4; split. apply Selectionproof.transf_program_match; auto.
  exists p5; split. apply RTLgenproof.transf_program_match; auto.
  exists p6; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p7; split. apply Inliningproof.transf_program_match; auto.
  exists p8; split. apply Renumberproof.transf_program_match; auto.
  exists p9; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p10; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p11; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p13; split. apply Unusedglobproof.transf_program_match; auto.
  exists p14; split. apply Allocproof.transf_program_match; auto.
  exists p15; split. apply Tunnelingproof.transf_program_match.
  exists p16; split. apply Linearizeproof.transf_program_match; auto.
  exists p17; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p18; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p19; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed. 

Lemma transf_clight_program_correct:
  forall p tp,
  match_prog p tp ->
  transf_clight_program p = OK tp ->
  forward_simulation (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
  Ltac DestructM :=
    match goal with
      [ H: exists p, _ /\ _ |- _ ] =>
        let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
        destruct H as (p & M & MM); clear H
    end.
  repeat DestructM. subst tp.

  intros.
  eapply compose_forward_simulations.
    eapply SimplLocalsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
  eapply Asmgenproof.transf_program_correct; eassumption.
Qed.

Definition transf_stan_program_complete(p: Stanlight.program): res Asm.program :=
  let p := transf_stan_program p in
  match p with
  | OK p => transf_clight_program p
  | Error s => Error s
  end.
  
Theorem transf_stan_program_correct_complete:
  forall p tp data params t,
  transf_stan_program_complete p = OK tp ->
  forward_simulation (Ssemantics.semantics p data params t) (Asm.semantics tp).
Proof.
  intros.
  unfold transf_stan_program_complete in H.
  case_eq (transf_stan_program p); intros.
  rewrite H0 in H.   
  apply (@compose_forward_simulations (Ssemantics.semantics p data params t)
                                      (Clight.semantics1 p0) (Asm.semantics tp)).
  apply transf_stan_program_correct; auto.
  apply transf_clight_program_correct; auto.
  apply transf_clight_program_match; auto.
  rewrite H0 in H. 
  discriminate. 
Qed.
