Require Import List.
Require Import Cop.
Require Import Ctypes.
Require Import CStan.
Require Import Errors.
Require Import String.
Require Import Floats.
Open Scope string_scope.
Require Import Coqlib.
Require Import Sops.
Require Import Cop.
Require Import Globalenvs.
Require Import Integers.
Require AST.
Require SimplExpr.

Notation "'do' X <~ A ; B" := (SimplExpr.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition tdouble := Tfloat F64 noattr.
Definition float_one := Floats.Float.of_int Int.one.
Definition float_zero := Floats.Float.of_int Int.zero.

Notation mon := SimplExpr.mon.
Notation ret := SimplExpr.ret.
Notation error := SimplExpr.error.
Notation gensym := SimplExpr.gensym.

Fixpoint transf_statement (p: program) (s: CStan.statement) {struct s}: mon CStan.statement :=
match s with
  | Stilde e d le (oe0, oe1) =>
    do tmp <~ gensym tdouble;

    (* simulate function call: *)
    let etmp := (Etempvar tmp tdouble) in
    let params := e::le in
    ret (Ssequence
          (Scall (Some tmp) d params)
          (Starget etmp))
 
  | Ssequence s0 s1 =>
    do s0 <~ transf_statement p s0;
    do s1 <~ transf_statement p s1;
    ret (Ssequence s0 s1)

  | Sifthenelse e s0 s1 =>
    do s0 <~ transf_statement p s0;
    do s1 <~ transf_statement p s1;
    ret (Sifthenelse e s0 s1)

  | Sloop s0 s1 =>
    do s0 <~ transf_statement p s0;
    do s1 <~ transf_statement p s1;
    ret (Sloop s0 s1)

 | _ => ret s
end.

Definition transf_function (p:CStan.program) (f: function): res (function) :=
  match transf_statement p f.(fn_body) f.(fn_generator) with
  | SimplExpr.Err msg => Error msg
  | SimplExpr.Res tbody g i =>
    OK {|
      fn_params := f.(fn_params);
      fn_body := tbody;

      fn_temps := g.(SimplExpr.gen_trail) ++ f.(fn_temps);
      fn_vars := f.(fn_vars);
      fn_generator := g;

      fn_return := f.(fn_return);
      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
     |}
  end.

Definition transf_program := CStan.transf_program (transf_function).

