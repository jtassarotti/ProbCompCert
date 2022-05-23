Require Import StanE.
Require Import Ssemantics.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.
Require Import Asm. 
Require Import String.

Require Import Compiler.
Require Import Reparameterization. 
Require Import Denumpyification.
Require Import Sampling.
Require Import Constraints.
Require Import VariableAllocation.
Require Import Target.
Require Import Sbackend.
Require Import Coqlib.

Open Scope string_scope.

(** Pretty-printers (defined in Caml). *)
Parameter print_CStan: Z -> CStan.program -> unit.

Definition transf_stan_program(p: StanE.program): res Clight.program :=
  OK p
  @@@ time "Reparameterization" Reparameterization.transf_program
  @@@ time "Denumpyification" Denumpyification.transf_program
  @@ print (print_CStan 0)
  @@@ time "Sampling" Sampling.transf_program
  @@ print (print_CStan 1)
  (*
  @@@ time "Constraints" Constraints.transf_program
  @@ print (print_CStan 2)
  *)
  @@@ time "VariableAllocation" VariableAllocation.transf_program
  @@ print (print_CStan 2)
  @@@ time "Target" Target.transf_program
  @@ print (print_CStan 3)
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
