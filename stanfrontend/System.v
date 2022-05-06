Require Import Coqlib.
Require Import Runtime.
Require Import Compiler. 
Require Import Asm.
Require Import Compiler.
Require Import StanE.
Require Import Linking.
Require Import Scompiler.
Require Import Errors.
Require Import Smallstep.
Require Import Integers.
Require Import Rbase.
Require Import Events.
From Coquelicot Require Import Lim_seq.
From Coquelicot Require Import Rbar.


Parameter from_trace: Events.traceinf -> (nat -> R).

Parameter distribution: Type.

(* Change to CStan.program -> distribution *)
Parameter denotational_semantics: StanE.program -> distribution.

Parameter is_distributed_as: R -> distribution -> Prop.

Theorem convergence:
  forall p: StanE.program,
  forall tp: Clight.program,
  Scompiler.transf_stan_program p = OK tp ->
  forall system: Clight.program,
  link_list (ncons tp (nbase Runtime.prog)) = Some system ->
  forall t,
  forall init, Clight.initial_state system init ->
  forever Clight.step2 (Clight.globalenv system) init t ->
  forall path, path = from_trace t ->
  forall r, is_lim_seq path (Finite r) ->
  is_distributed_as r (denotational_semantics p).
Proof.
Admitted.



(*
  forall out, Clight.final_state out Int.zero ->
  starN Clight.step2 (Clight.globalenv system) n init t out ->
*)
