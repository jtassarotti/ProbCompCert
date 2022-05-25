Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require CStan.
Require Ssemantics. 
Require Reparameterization.

Parameter match_prog: StanE.program -> StanE.program -> Prop.

Lemma transf_program_match:
  forall p tp, Reparameterization.transf_program p = OK tp -> match_prog p tp.
Proof.
Admitted.

Section PRESERVATION.

Variable prog: StanE.program.
Variable tprog: StanE.program.
Variable TRANSL: match_prog prog tprog.

Theorem transf_program_correct:
  forward_simulation (Ssemantics.semantics prog) (Ssemantics.semantics tprog).
Proof.
Admitted.

End PRESERVATION.

Global Instance TransfReparameterizationtLink : TransfLink match_prog.
Admitted.