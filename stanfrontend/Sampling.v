(* Sampling transform.

   This pass compiles away the Stilde statement (e ~ f(e1,...,en))
   into directly calling a _lpdf function and adding the result to the
   target variable using an Starget statement.

   This transform is operational semantics preserving, because the
   small step semantics of Stilde has exactly the same effect as what
   the compiled statements do.

   Note: the handling of Stilde here is different than in the
   reference Stan compiler, which maps to _lupdf (unnormalized
   pdfs). In ProbCompCert, conversion from _lpdf to _lupdf happens later
   in the AdditiveConst pass.

*)

Require Import AST.
Require Import Stanlight.

Fixpoint transf_statement (s: statement) {struct s}: statement :=
  match s with
  | Ssequence s1 s2 =>
    let s1 := transf_statement s1 in
    let s2 := transf_statement s2 in
    Ssequence s1 s2
  | Sifthenelse e s1 s2 =>
    let s1 := transf_statement s1 in
    let s2 := transf_statement s2 in
    Sifthenelse e s1 s2
  | Sfor i e1 e2 s =>
    let s := transf_statement s in
    Sfor i e1 e2 s
  | Stilde e d el =>
    Starget (Ecall d (Econs e el) Breal)
  | _ => s
  end.

Definition transf_function (f: function) : function :=
  mkfunction (transf_statement f.(fn_body)) f.(fn_vars).

Definition transf_fundef (fd: fundef) : fundef :=
  match fd with
  | Ctypes.Internal f => Ctypes.Internal (transf_function f)
  | Ctypes.External ef targs tres cc => Ctypes.External ef targs tres cc
  end.

Definition transf_program(p: program): program :=
  let p1:= AST.transform_program transf_fundef p in
  {|
      Stanlight.pr_defs := AST.prog_defs p1;
      Stanlight.pr_parameters_vars := p.(pr_parameters_vars);
      Stanlight.pr_data_vars := p.(pr_data_vars);
    |}.
