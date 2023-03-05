Require Import Stanlight.
Require Import Ssemantics.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.
Require Import Asm. 
Require Import String.

Require Import Compiler.
Require Import AdditiveConst.
Require Import Reparameterization. 
Require Import Clightification.
Require Import Sampling.
Require Import VariableAllocation.
Require Import Target.
Require Import Sbackend.
Require Import Coqlib.
Require Import Linking. 

Require AdditiveConstproof.
Require Reparameterizationproof.
Require Clightificationproof.
Require Samplingproof.
Require VariableAllocationproof.
Require Sbackendproof.

Open Scope string_scope.
Local Open Scope linking_scope.

(** Pretty-printers (defined in Caml). *)
Parameter print_CStan: Z -> CStan.program -> unit.

(* Source to source translations of Stanlight *)
Definition transf_stanlight_program (p: Stanlight.program) : res Stanlight.program :=
  OK p
  @@ time "Sampling" Sampling.transf_program
  @@@ time "Reparameterization" Reparameterization.transf_program
  @@@ time "AdditiveConst" AdditiveConst.transf_program.

(* Full translation of stanlight to Clight *)
Definition transf_stan_program(p: Stanlight.program): res Clight.program :=
  (transf_stanlight_program p)
  @@@ time "Clightification" Clightification.transf_program
  @@ print (print_CStan 0)
  @@@ time "VariableAllocation" VariableAllocation.transf_program
  @@ print (print_CStan 1)
  @@@ time "Target" Target.transf_program
  @@ print (print_CStan 2)
  @@@ time "Backend" backend. 

Theorem transf_stanlight_program_denotational_preserved:
  forall p tp,
  transf_stanlight_program p = OK tp ->
  denotational_refinement tp p.
Proof.
  intros p tp T.
  unfold transf_stanlight_program, time in T. simpl in T.
  destruct (Reparameterization.transf_program _) as [p2|e] eqn:P2; simpl in T; inv T.
  eapply (denotational_refinement_trans); last first.
  { eapply Samplingproof.denotational_preserved.
    eapply Samplingproof.transf_program_match. }
  eapply (denotational_refinement_trans); last first.
  { eapply Reparameterizationproof.denotational_preserved.
    eapply Reparameterizationproof.transf_program_match; eauto. }
  { eapply AdditiveConstproof.denotational_preserved.
    eapply AdditiveConstproof.transf_program_match; eauto. }
Qed.

Definition transf_stan_program_complete(p: Stanlight.program): res Asm.program :=
  let p := transf_stan_program p in
  match p with
  | OK p => transf_clight_program p
  | Error s => Error s
  end.
