Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require CStan.
Require StanE.
Require Ssemantics. 
Require CStanSemanticsTarget.
Require Denumpyification.


Parameter match_prog: StanE.program -> CStan.program -> Prop.

Lemma transf_program_match:
  forall p tp, Denumpyification.transf_program p = OK tp -> match_prog p tp.
Proof.
Admitted.

Section PRESERVATION.

Variable prog: StanE.program.
Variable tprog: CStan.program.
Variable TRANSL: match_prog prog tprog.

Theorem transf_program_correct:
  forward_simulation (Ssemantics.semantics prog) (CStanSemanticsTarget.semantics tprog).
Proof.
Admitted.

End PRESERVATION.

Global Instance TransfDenumpyificationLink : TransfLink match_prog.
Admitted.