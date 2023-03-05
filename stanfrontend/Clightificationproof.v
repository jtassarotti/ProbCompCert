Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require CStan.
Require Stanlight.
Require Ssemantics. 
Require CStanSemanticsTarget.
Require Clightification.


Parameter match_prog: Stanlight.program -> CStan.program -> Prop.

Section PRESERVATION.

Variable prog: Stanlight.program.
Variable tprog: CStan.program.
Variable data : list Values.val.
Variable params : list Values.val.
Variable TRANSL: match_prog prog tprog.

End PRESERVATION.
