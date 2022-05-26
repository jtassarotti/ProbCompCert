Require Import Smallstep.
Require Import Linking.

Require Stanlight.
Require Sampling.
Require Ssemantics.

Parameter match_prog: Stanlight.program -> Stanlight.program -> Prop.

Lemma transf_program_match:
  forall p tp, Sampling.transf_program p = tp -> match_prog p tp.
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

Global Instance TransfSamplingLink : TransfLink match_prog.
Admitted.