(* Additive constant transformation.

   This is an optimization pass that removes addition of constants to the target variable.
   That is, we replace an expresison like

      target += x + c

   where c is a constant, with

      target += x + 0

   similarly, when there is a call to an lpdf function whose result is added to target, we replace the call
   with lupdf (i.e. the unnormalized pdf). E.g we replace

   target += normal_lpdf(x, mu, sigma)

   with

   target += normal_lupdf(x, mu, sigma)

   where _lupdf is a version of lpdf with additive constants similarly removed.

   The justification for this transformation is that the model block
   computes an *unnormalized* log density which is then later
   normalized. So, subtracting a constant c from the target
   effectively just scales this unnormalized density and the
   normalization constant by a constant factor of exp(-c), which is
   then canceled out by normalization.

   IMPORTANT: we can only drop the constant when the statement being
   modified has no control flow dependency on parameter
   values. Otherwise, such a dependency means that the constant being
   added is not really a constant! E.g.

   if (mu > 0) {
     target += c
   }

   is not adding a constant c to the target.

*)

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

(* This map stores what lpdfs should be replaced with which corresponding lupdf. *)
Definition math_fun_remap : PTree.t (AST.ident) :=
   PTree.set ($"normal_lpdf") ($"normal_lupdf")
  (PTree.set ($"cauchy_lpdf") ($"cauchy_lupdf")
             (PTree.empty _)).

Definition Ezero := Econst_float (Floats.Float.zero) Breal.

(* Returns an expression with additive constants dropped from e *)
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

(* We will need to check whether the program reads the target variable
   using Etarget. If it does, then dropping constants may not be
   semantically preserving, because the value read from from Etarget
   will change. This check could be made more precise. *)
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

(* This checks for no Etarget in a whole statement *)
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
  (* Impossible *)
  | Stilde e d el => None
  end.

(* Checks whether statement s assigns to the variable i. *)
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
  | Sfor i (Econst_int i1 Bint) (Econst_int i2 Bint) s =>
    (* We only do the transformation if the for loop iterator variable i is not
       modified in the body of the loop. *)
    match check_no_assign i s with
    | true =>
        do s <- transf_statement s;
        Some (Sfor i (Econst_int i1 Bint) (Econst_int i2 Bint) s)
    | false =>
        Some (Sfor i (Econst_int i1 Bint) (Econst_int i2 Bint) s)
    end
  | Sfor i e1 e2 s =>
    Some (Sfor i e1 e2 s)
  | Starget e =>
    Some (Starget (drop_const e))
  | Stilde e d el => None
  end.

Definition transf_statement' s :=
  match transf_statement s with
  | None => s
  | Some s' => s'
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

Definition transf_function_body (f: Stanlight.function) : option statement :=
    do _ <- list_option_map (vars_check_shadow) (f.(fn_vars));
    do _ <- check_no_target_statement f.(fn_body);
    transf_statement f.(fn_body).

Definition transf_function (f: Stanlight.function): (Stanlight.function) :=
  let body :=
    match transf_function_body f with
    | None => f.(fn_body)
    | Some b => b
    end in
   (mkfunction body f.(fn_vars)).

Definition transf_fundef (fd: Stanlight.fundef) : (Stanlight.fundef) :=
  match fd with
  | Ctypes.Internal f => Ctypes.Internal (transf_function f)
  | Ctypes.External ef targs tres cc => Ctypes.External ef targs tres cc
  end.

Definition param_check_shadow (p: AST.ident * basic * option (expr -> expr)) :=
  let '(id, b, fe) := p in
  if forallb (fun id' => match (Pos.eq_dec id' id) with
                      | left _ => false
                      | right _ => true
                         end) StanEnv.pdf_idents then
    Errors.OK tt
  else
    Errors.Error (Errors.msg "Additive Const: parameter shadows global math functions").

Definition transf_program(p: program): Errors.res program :=
  Errors.bind (Errors.mmap (param_check_shadow ) (p.(pr_parameters_vars)))
              (fun _ =>
                let p1:= AST.transform_program transf_fundef p in
                Errors.OK {|
                    Stanlight.pr_defs := AST.prog_defs p1;
                    Stanlight.pr_parameters_vars := p.(pr_parameters_vars);
                    Stanlight.pr_data_vars := p.(pr_data_vars);
                  |}).
