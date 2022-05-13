Require Import StanE.
Require Import Ssemantics.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.
Require Import Asm. 
Require Import String.

Require Import Compiler.
Require Import Denumpyification.
Require Import Sampling.
Require Import Constraints.
Require Import VariableAllocation.
Require Import Target.
Require Import Sbackend.

Open Scope string_scope.

(** Pretty-printers (defined in Caml). *)
Parameter print_CStan: CStan.program -> unit.

Definition transf_stan_program(p: StanE.program): res Clight.program :=
  OK p
  @@@ time "Denumpyification" Denumpyification.transf_program
  @@@ time "Sampling" Sampling.transf_program
  @@ print (print_CStan)
  @@@ time "Constraints" Constraints.transf_program
  @@@ time "VariableAllocation" VariableAllocation.transf_program
  @@@ time "Target" Target.transf_program
  @@@ time "Backend" backend.
  
Theorem transf_stan_program_correct:
  forall p tp,
  transf_stan_program p = OK tp ->
  backward_simulation (Ssemantics.semantics p) (Clight.semantics2 tp).
Proof.
Admitted.

Definition transf_stan_program_complete(p: StanE.program): res Asm.program :=
  let p := transf_stan_program p in
  match p with
  | OK p => transf_clight_program p
  | Error s => Error s
  end.
  
Theorem transf_stan_program_correct_complete:
  forall p tp,
  transf_stan_program_complete p = OK tp ->
  backward_simulation (Ssemantics.semantics p) (Asm.semantics tp).
Proof.
Admitted.
