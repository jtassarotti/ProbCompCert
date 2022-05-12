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
Notation error_mmap := Errors.mmap.

Definition mon_fmap {A B : Type} (f: A -> B) (m: mon A)  : mon B := do a <~ m; ret (f a).

Definition option_fmap {X Y:Type} (f: X -> Y) (o: option X) : option Y :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint mon_mmap {A B : Type} (f: A -> mon B) (l: list A) {struct l} : mon (list B) :=
  match l with
  | nil => ret nil
  | hd :: tl =>
    do hd' <~ f hd;
    do tl' <~ mon_mmap f tl;
    ret (hd' :: tl')
  end.

Fixpoint res_mmap {A B : Type} (f: A -> res B) (l: list A) {struct l} : res (list B) :=
  match l with
  | nil => OK nil
  | hd :: tl =>
    do hd' <- f hd;
    do tl' <- res_mmap f tl;
    OK (hd' :: tl')
  end.

Definition option_mon_mmap {X Y:Type} (f: X -> mon Y) (ox: option X) : mon (option Y) :=
  match ox with
  | None => ret None
  | Some x => do x <~ f x; ret (Some x)
  end.

Definition option_res_mmap {X Y:Type} (f: X -> res Y) (ox: option X) : res (option Y) :=
  match ox with
  | None => OK None
  | Some x => do x <- f x; OK (Some x)
  end.

Definition maybe_ident (e: expr): option AST.ident :=
match e with
  | CStan.Evar i t => Some i
  | CStan.Etempvar i t => Some i
  | _ => None
end.

Fixpoint transf_expr (ot : AST.ident) (e: CStan.expr) {struct e}: res CStan.expr :=
  match e with
  | CStan.Econst_int i t => OK (CStan.Econst_int i t)
  | CStan.Econst_float f t => OK (CStan.Econst_float f t)
  | CStan.Econst_single f t => OK (CStan.Econst_single f t)
  | CStan.Econst_long i t => OK (CStan.Econst_long i t)
  | CStan.Evar i t => OK (CStan.Evar i t)
  | CStan.Etempvar i t =>
    if Pos.eqb i ot
    then Error (msg "cannot get the target identifier")
    else OK (CStan.Etempvar i t)
  | CStan.Ederef e t =>
    do e <- transf_expr ot e;
    OK (CStan.Ederef e t)
  | CStan.Ecast e t =>
    do e <- transf_expr ot e;
    OK (CStan.Ecast e t)
  | CStan.Efield e i t =>
    do e <- transf_expr ot e;
    OK (CStan.Efield e i t)
  | CStan.Eunop uop e t =>
    do e <- transf_expr ot e;
    OK (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t =>
    do e0 <- transf_expr ot e0;
    do e1 <- transf_expr ot e1;
    OK (CStan.Ebinop bop e0 e1 t)
  | CStan.Eaddrof e t =>
    do e <- transf_expr ot e;
    OK (CStan.Eaddrof e t)
  | CStan.Esizeof t0 t1 => OK (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => OK (CStan.Ealignof t0 t1)
  | CStan.Etarget ty => OK (CStan.Etempvar ot ty)
end.

Fixpoint transf_statement (p: program) (s: CStan.statement) {struct s}: res CStan.statement :=
let t := p.(prog_target) in
match s with
  | Sassign e0 e1 =>
    do e0 <- transf_expr t e0;
    do e1 <- transf_expr t e1;
    OK (Sassign e0 e1)
  | Sset i e =>
    do e <- transf_expr t e;
    if Pos.eqb i t
    then Error (msg "cannot set the target identifier")
    else OK (Sset i e)
  | Scall oi e le =>
    do e <- transf_expr t e;
    do le <- res_mmap (transf_expr t) le;
    match oi with
    | None => OK (Scall oi e le)
    | Some i =>
      if Pos.eqb i t
      then Error (msg "cannot set the target identifier")
      else OK (Scall oi e le)
    end
  | Sbuiltin oi ef lt le =>
    do le <- res_mmap (transf_expr t) le;
    match oi with
    | None => OK (Sbuiltin oi ef lt le)
    | Some i =>
      if Pos.eqb i t
      then Error (msg "cannot set the target identifier")
      else OK (Sbuiltin oi ef lt le)
    end
  | Ssequence s0 s1 =>
    do s0 <- transf_statement p s0;
    do s1 <- transf_statement p s1;
    OK (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>
    do e <- transf_expr t e;
    do s0 <- transf_statement p s0;
    do s1 <- transf_statement p s1;
    OK (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>
    do s0 <- transf_statement p s0;
    do s1 <- transf_statement p s1;
    OK (Sloop s0 s1)
  | Sreturn oe =>
    do oe <- option_res_mmap (transf_expr t) oe;
    OK (Sreturn oe)
  | Starget e =>
    OK (Sset t
         (Ebinop Cop.Oadd
           (Etempvar t tdouble) e tdouble))
 (* | Starget e =>
    do e <- transf_etarget_expr t e;
    OK (Starget e)*)
  | Stilde e i le (oe0, oe1) =>
    Error (msg "Stilde DNE in this stage of pipeline")
  | Sbreak => OK Sbreak
  | Sskip => OK Sskip
  | Scontinue => OK Scontinue
end.

Definition add_prelude_epilogue (tgt: AST.ident) (body: statement) : statement :=
  let prelude  := Sset tgt (Econst_float Float.zero tdouble) in
  let epilogue := Sreturn (Some (Etempvar tgt tdouble)) in
  Ssequence prelude (Ssequence body epilogue).

Definition transf_function (p: program) (f: function): res function :=
  let tgt := p.(prog_target) in
  do body <- transf_statement p f.(fn_body);
  OK {|
      fn_params := f.(fn_params);
      fn_body := add_prelude_epilogue tgt body;

      (* fn_temps := g.(SimplExpr.gen_trail) ++ f.(fn_temps); *)
      fn_temps := f.(fn_temps);
      fn_vars := f.(fn_vars);
      fn_generator := f.(fn_generator);

      (*should not change*)
      fn_return := f.(fn_return);
      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
     |}.

Definition transf_program := CStan.transf_program (transf_function).

