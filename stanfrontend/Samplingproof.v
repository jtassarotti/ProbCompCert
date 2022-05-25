Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require CStan.
Require Sampling.
Require CStanSemanticsTarget.

Parameter match_prog: CStan.program -> CStan.program -> Prop.

Lemma transf_program_match:
  forall p tp, Sampling.transf_program p = OK tp -> match_prog p tp.
Proof.
Admitted.

Section PRESERVATION.

Variable prog: CStan.program.
Variable tprog: CStan.program.
Variable TRANSL: match_prog prog tprog.

Theorem transf_program_correct:
  forward_simulation (CStanSemanticsTarget.semantics prog) (CStanSemanticsTarget.semantics tprog).
Proof.
Admitted.

End PRESERVATION.

Global Instance TransfSamplingLink : TransfLink match_prog.
Admitted.