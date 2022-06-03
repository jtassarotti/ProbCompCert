Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require CStan.
Require Stanlight.
Require Ssemantics. 
Require CStanSemanticsTarget.
Require Clightification.


Parameter match_prog: Stanlight.program -> CStan.program -> Prop.

Lemma transf_program_match:
  forall p tp, Clightification.transf_program p = OK tp -> match_prog p tp.
Proof.
Admitted.

Section PRESERVATION.

Variable prog: Stanlight.program.
Variable tprog: CStan.program.
Variable data : list Values.val.
Variable params : list Values.val.
Variable TRANSL: match_prog prog tprog.

(* TODO: Joe: this doesn't make sense yet, because we ought to load the data/params in tprog as well *)
Theorem transf_program_correct:
  forward_simulation (Ssemantics.semantics prog data params) (CStanSemanticsTarget.semantics tprog).
Proof.
Admitted.

End PRESERVATION.

Global Instance TransfClightificationLink : TransfLink match_prog.
Admitted.
