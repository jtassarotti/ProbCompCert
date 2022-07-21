Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require Stanlight.
Require Ssemantics. 
Require Reparameterization.

Parameter match_prog: Stanlight.program -> Stanlight.program -> Prop.

Lemma transf_program_match:
  forall p tp, Reparameterization.transf_program p = OK tp -> match_prog p tp.
Proof.
Admitted.

Section PRESERVATION.

Variable prog: Stanlight.program.
Variable tprog: Stanlight.program.
Variable data : list Values.val.
Variable params : list Values.val.
Variable TRANSL: match_prog prog tprog.

(* TODO: Joe: this doesn't make sense, because we ought to be remapping data/params in target *)
Theorem transf_program_correct tval:
  forward_simulation (Ssemantics.semantics prog data params tval) (Ssemantics.semantics tprog data params tval).
Proof.
Admitted.

End PRESERVATION.

Global Instance TransfReparameterizationtLink : TransfLink match_prog.
Admitted.
