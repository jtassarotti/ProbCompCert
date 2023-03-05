Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require CStan.
Require VariableAllocation.
Require CStanSemanticsTarget.

Parameter match_prog: CStan.program -> CStan.program -> Prop.

Section PRESERVATION.

Variable prog: CStan.program.
Variable tprog: CStan.program.
Variable TRANSL: match_prog prog tprog.

End PRESERVATION.
