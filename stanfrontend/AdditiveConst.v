Require Import List.
Require Import String.
Require Import ZArith.
Require Floats.
Require Integers.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Require StanEnv.

Require Import Maps.
Require Import Stanlight.
Require Errors.
Require Import Clightdefs.
Import Clightdefs.ClightNotations.

Local Open Scope clight_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : option_monad_scope.

Local Open Scope option_monad_scope.

Definition math_fun_remap : PTree.t (AST.ident) :=
   PTree.set ($"normal_lpdf") ($"normal_lupdf") 
  (PTree.set ($"cauchy_lpdf") ($"cauchy_lupdf") 
             (PTree.empty _)).

Definition Ezero := Econst_float (Floats.Float.zero) Breal.

Fixpoint drop_const (e: Stanlight.expr) {struct e} : expr :=
  match e with
  | Econst_float _ Breal => Ezero
  | Ecall (Evar id (Bfunction ty1 ty2)) el ty =>
      match PTree.get id math_fun_remap with
      | Some id' =>
          Ecall (Evar id' (Bfunction ty1 ty2)) el ty
      | None =>
          e
      end
  | Ebinop e1 Plus e2 Breal =>
      match typeof e1, typeof e2 with
      | Breal, Breal => Ebinop (drop_const e1) Plus (drop_const e2) Breal
      | _, _ => Ebinop e1 Plus e2 Breal
      end
  | Ebinop e1 Minus e2 Breal =>
      match typeof e1, typeof e2 with
      | Breal, Breal => Ebinop (drop_const e1) Minus (drop_const e2) Breal
      | _, _ => Ebinop e1 Minus e2 Breal
      end
  | _ => e
  end.

(*
Fixpoint drop_const (cid: AST.ident -> bool) (e: Stanlight.expr) {struct e} : expr :=
  match e with
  | Evar id Breal =>
      if cid id then
        Ezero
      else
        Evar id Breal
  | Econst_float _ Breal => Ezero
  | Ecall (Evar id tyf) el ty =>
      match PTree.get id math_fun_remap with
      | Some id' =>
          Ecall (Evar id' tyf) el ty
      | None =>
          e
      end
  | Ebinop e1 Plus e2 Breal =>
      Ebinop (drop_const cid e1) Plus (drop_const cid e2) Breal
  | Ebinop e1 Minus e2 Breal =>
      Ebinop (drop_const cid e1) Minus (drop_const cid e2) Breal
  | _ => e
  end.
*)

Fixpoint check_no_target_expr (e: expr) : option (unit) :=
  match e with
  | Ecast e _ => check_no_target_expr e
  | Ecall e el ty =>
      do _ <- check_no_target_expr e;
      check_no_target_exprlist el
  | Eunop op e b => check_no_target_expr e
  | Ebinop e1 op e2 b => 
      do _ <- check_no_target_expr e1;
      check_no_target_expr e2
  | Eindexed e el b =>
      do _ <- check_no_target_expr e;
      check_no_target_exprlist el
  | Etarget b => None
  | _ => Some tt
  end

with check_no_target_exprlist el : option (unit) :=
  match el with
  | Enil => Some tt
  | Econs e el => 
      do _ <- check_no_target_expr e;
      check_no_target_exprlist el
  end.

Fixpoint check_no_assign i s : bool :=
  match s with
  | Sskip => true
  | Sassign e1 o e2 =>
      match e1 with
      | Evar id' _ | Eindexed (Evar id' _) _ _ =>
          if Pos.eq_dec id' i then
            false
          else
            true
      | _ => false
      end
  | Ssequence s1 s2 =>
      check_no_assign i s1 && check_no_assign i s2
  | Sfor id' e1 e2 s =>
      if Pos.eq_dec i id' then
        false
      else
        check_no_assign i s
  | Sifthenelse e s1 s2 =>
      check_no_assign i s1 && check_no_assign i s2
  | Starget e => true
  | Stilde _ _ _ => true
  end.

(* This checks for no Etarget; i.e. it does not depend upon the value of target;
   an Starget is ok *)
Fixpoint check_no_target_statement s : option unit :=
  match s with
  | Sskip => Some tt
  | Sassign e1 o e2 =>
    do _ <- check_no_target_expr e1;
    do _ <- check_no_target_expr e2;
    Some tt
  | Ssequence s1 s2 =>
    do _ <- (check_no_target_statement s1);
    do _ <- (check_no_target_statement s2);
    Some tt
  | Sifthenelse e s1 s2 =>
    do _ <- (check_no_target_expr e);
    do _ <- (check_no_target_statement s1);
    do _ <- (check_no_target_statement s2);
    Some tt
  | Sfor i e1 e2 s =>
    do _ <- (check_no_target_expr e1);
    do _ <- (check_no_target_expr e2);
    do _ <- (check_no_target_statement s);
    Some tt
  | Starget e =>
    check_no_target_expr e
  | Stilde e d el =>
    do _ <- check_no_target_expr e;
    check_no_target_exprlist el
  end.

Fixpoint transf_statement (s: Stanlight.statement) {struct s} : option (Stanlight.statement) :=
  match s with
  | Sskip => Some (Sskip)
  | Sassign e1 o e2 => Some (Sassign e1 o e2)
  | Ssequence s1 s2 =>
    do s1 <- (transf_statement s1);
    do s2 <- (transf_statement s2);
    Some (Ssequence s1 s2)
  | Sifthenelse e s1 s2 =>
    Some (Sifthenelse e s1 s2)
  | Sfor i (Econst_int i1 b1) (Econst_int i2 b2) s =>
    match check_no_assign i s with
    | true =>
        do s <- transf_statement s;
        Some (Sfor i (Econst_int i1 b1) (Econst_int i2 b2) s)
    | false => 
        Some (Sfor i (Econst_int i1 b1) (Econst_int i2 b2) s)
    end
  | Sfor i e1 e2 s =>
    Some (Sfor i e1 e2 s)
  | Starget e =>
    Some (Starget (drop_const e))
  | Stilde e d el => None
  end.


Definition vars_check_shadow (p: AST.ident * basic) : option unit :=
  let '(id, b) := p in
  if forallb (fun id' => match (Pos.eq_dec id' id) with
                      | left _ => false
                      | right _ => true
                         end) (StanEnv.pdf_idents ++ StanEnv.math_idents) then
    Some tt
  else
    None.

Fixpoint list_option_map {A B} (f: A -> option B) (l: list A) : option (list B) :=
  match l with
  | nil => Some nil
  | a :: l =>
      do b <- f a;
      do l' <- list_option_map f l;
      Some (b :: l')
  end.

Definition transf_function (f: Stanlight.function): (Stanlight.function) :=
  let res :=
    do _ <- list_option_map (vars_check_shadow) (f.(fn_vars));
    transf_statement f.(fn_body) in
  let body :=
    match res with
    | None => f.(fn_body)
    | Some b => b
    end in
   (mkfunction body f.(fn_vars)).

Definition transf_fundef (fd: Stanlight.fundef) : (Stanlight.fundef) :=
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

(* TODO: need to check whether params shadow *)
(*
Definition param_check_shadow (p: AST.ident * basic * option (expr -> expr)) :=
  let '(id, b, fe) := p in
  if forallb (fun id' => match (Pos.eq_dec id' id) with
                      | left _ => false
                      | right _ => true
                         end) StanEnv.math_idents then
    Errors.OK tt
  else
    Errors.Error (Errors.msg "Additive Const: parameter shadows global math functions").
*)
