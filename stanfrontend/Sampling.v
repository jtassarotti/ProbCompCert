Require Import List. 
Require Import Ctypes.
Require Import CStan.
Require Import SimplExpr.

Notation "'do' X <~ A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition tdouble := Tfloat F64 noattr.

Definition tr_statement (p: program) (s: statement): mon statement :=
  match s with 
  | Stilde e d le (oe0, oe1) =>
    do tmp <~ gensym tdouble;
    let etmp := (Etempvar tmp tdouble) in
    let params := e::le in
    ret (Ssequence
          (Scall (Some tmp) d params)
          (Starget etmp))
  | _ => ret s
  end.

Definition transf_statement := map_transf_statement tr_statement. 

Definition transf_function := transf_function_basic transf_statement. 

Definition transf_program := transf_program (transf_function).

