Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require CStan.
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
Variable TRANSL: match_prog prog tprog.

Theorem transf_program_correct:
  forward_simulation (Ssemantics.semantics prog) (Ssemantics.semantics tprog).
Proof.
Admitted.

End PRESERVATION.

Global Instance TransfReparameterizationtLink : TransfLink match_prog.
Admitted.