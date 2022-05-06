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

(* FIXME how do I share this notation? *)
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

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

Definition transf_expr (e: CStan.expr) : mon CStan.expr :=
  match e with
  | CStan.Econst_int i t => ret (CStan.Econst_int i t)
  | CStan.Econst_float f t => ret (CStan.Econst_float f t)
  | CStan.Econst_single f t => ret (CStan.Econst_single f t)
  | CStan.Econst_long i t => ret (CStan.Econst_long i t)
  | CStan.Evar i t => ret (CStan.Evar i t)
  | CStan.Etempvar i t => ret (CStan.Etempvar i t)
  | CStan.Ederef e t => ret (CStan.Ederef e t)
  | CStan.Ecast e t => ret (CStan.Ecast e t)
  | CStan.Efield e i t => ret (CStan.Efield e i t)
  | CStan.Eaddrof e t => ret (CStan.Eaddrof e t)
  | CStan.Eunop uop e t => ret (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t => ret (CStan.Ebinop bop e0 e1 t)
  | CStan.Esizeof t0 t1 => ret (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => ret (CStan.Ealignof t0 t1)
  | CStan.Etarget t => ret (CStan.Etarget t)
end.

Fixpoint mon_mmap {A B : Type} (f: A -> mon B) (l: list A) {struct l} : mon (list B) :=
  match l with
  | nil => ret nil
  | hd :: tl =>
    do hd' <~ f hd;
    do tl' <~ mon_mmap f tl;
    ret (hd' :: tl')
  end.

Definition option_mon_mmap {X Y:Type} (f: X -> mon Y) (ox: option X) : mon (option Y) :=
  match ox with
  | None => ret None
  | Some x => do x <~ f x; ret (Some x)
  end.

Fixpoint transf_statement (s: CStan.statement) {struct s}: mon CStan.statement :=
match s with
  | Sskip => ret Sskip
  | Sassign e0 e1 =>
    do e0 <~ transf_expr e0;
    do e1 <~ transf_expr e1;
    ret (Sassign e0 e1)

  | Sset i e =>
    do e <~ transf_expr e;
    ret (Sset i e)

  | Scall oi e le =>
    do e <~ transf_expr e;
    do le <~ mon_mmap transf_expr le;
    ret (Scall oi e le)

  | Sbuiltin oi ef lt le => error (msg "ret (Sbuiltin oi ef lt le)")

  | Ssequence s0 s1 =>
    do s0 <~ transf_statement s0;
    do s1 <~ transf_statement s1;
    ret (Ssequence s0 s1)

  | Sifthenelse e s0 s1 =>
    do s0 <~ transf_statement s0;
    do s1 <~ transf_statement s1;
    ret (Sifthenelse e s0 s1)

  | Sloop s0 s1 =>
    do s0 <~ transf_statement s0;
    do s1 <~ transf_statement s1;
    ret (Sloop s0 s1)

  | Sbreak => ret Sbreak

  | Scontinue => ret Scontinue

  | Sreturn oe =>
    do oe <~ option_mon_mmap (transf_expr) oe;
    ret (Sreturn oe)

  | Starget e =>
    do e <~ transf_expr e;
    ret (Starget e)

  | Stilde e d le (oe0, oe1) =>
    do tmp <~ gensym tdouble;

    (* simulate function call: *)
    let etmp := (Etempvar tmp tdouble) in
    let params := e::le in
    ret (Ssequence
          (Scall (Some tmp) d params)
          (Starget etmp))
end.

Definition transf_function (p:CStan.program) (f: function): res (function) :=
  match transf_statement f.(fn_body) f.(fn_generator) with
  | SimplExpr.Err msg => Error msg
  | SimplExpr.Res tbody g i =>
    OK {|
      fn_params := f.(fn_params);
      fn_body := tbody;

      fn_temps := g.(SimplExpr.gen_trail) ++ f.(fn_temps);
      (* fn_temps := g.(SimplExpr.gen_trail) ++ f.(fn_temps); *)
      (* fn_temps := f.(fn_temps); (* NOTE only extract in the last stage *) *)
      fn_vars := f.(fn_vars);
      fn_generator := g;

      (*should not change*)
      fn_return := f.(fn_return);
      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
     |}
  end.

(* ================================================================== *)
(*                    Switch to Error Monad                           *)
(* ================================================================== *)

Definition transf_external (ef: AST.external_function) : res AST.external_function :=
  match ef with
  | AST.EF_external n sig => OK (AST.EF_external n sig) (*link to blas ops?*)
  | AST.EF_runtime n sig => OK (AST.EF_runtime n sig) (*link runtime?*)
  | _ => OK ef
  end.

Definition transf_fundef (p:CStan.program) (id: AST.ident) (fd: CStan.fundef) : res (CStan.fundef) :=
  match fd with
  | Internal f =>
      do tf <- transf_function p f;
      OK (Internal tf)
  | External ef targs tres cc =>
      do ef <- transf_external ef;
      OK (External ef targs tres cc)
  end.

Definition transf_variable (id: AST.ident) (v: type): res type :=
  OK v.

Definition transf_program(p: CStan.program): res CStan.program :=
  do p1 <- AST.transform_partial_program2 (transf_fundef p) transf_variable p;

  OK {|
      prog_defs := AST.prog_defs p1;
      prog_public := AST.prog_public p1;

      prog_data_vars:=p.(prog_data_vars);
      prog_data_struct:= p.(prog_data_struct);

      prog_constraints := p.(prog_constraints);
      prog_parameters_vars:= p.(prog_parameters_vars);
      prog_parameters_struct:= p.(prog_parameters_struct);

      prog_model:=p.(prog_model);
      prog_target:=p.(prog_target);
      prog_main:=p.(prog_main);

      prog_types:=p.(prog_types);
      prog_comp_env:=p.(prog_comp_env);
      prog_comp_env_eq:=p.(prog_comp_env_eq);

      prog_math_functions:= p.(prog_math_functions);
      prog_dist_functions:= p.(prog_dist_functions);
    |}.
