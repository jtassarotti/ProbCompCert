Require Import List.
Require Import String.
Require Import ZArith.
Require Floats.
Require Integers.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Require StanEnv.

Require Import Stanlight.
Require Errors.
Require Import Clightdefs.
Import Clightdefs.ClightNotations.

Local Open Scope clight_scope.

Notation "'do' X <- A ; B" := (Errors.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Fixpoint transf_expr (pmap: AST.ident -> option (expr -> expr)) (e: Stanlight.expr) {struct e}: Errors.res Stanlight.expr :=
  match e with
  | Evar id ty =>
      match pmap id with
      | Some fe =>
          match ty with
          | Breal => Errors.OK (fe (Evar id Breal))
          | _ =>  Errors.Error (Errors.msg "Reparameterization: parameter loaded with non real type")
          end
      | None => Errors.OK (Evar id ty)
      end
  | Ecall e el ty =>
    do e <- transf_expr pmap e;
    do el <- transf_exprlist pmap el;
    Errors.OK (Ecall e el ty)
  | Eunop o e ty =>
    do e <- transf_expr pmap e;
    Errors.OK (Eunop o e ty)
  | Ebinop e1 o e2 ty =>
    do e1 <- transf_expr pmap e1;
    do e2 <- transf_expr pmap e2;
    Errors.OK (Ebinop e1 o e2 ty)
  | Eindexed e el ty =>
    do el <- transf_exprlist pmap el;
    match e with
    | Evar id _ =>
        match pmap id with
        | Some fe =>
          match ty with
          | Breal => Errors.OK (fe (Eindexed e el Breal))
          | _ =>  Errors.Error (Errors.msg "Reparameterization: parameter loaded with non real type")
          end
        | None => Errors.OK (Eindexed e el ty)
        end
    | _ => Errors.OK (Eindexed e el ty)
    end
  | Ecast e ty =>
      do e <- transf_expr pmap e;
      Errors.OK (Ecast e ty)
  | Econst_int a b => Errors.OK (Econst_int a b)
  | Econst_float a b => Errors.OK (Econst_float a b)
  | Etarget b => Errors.OK (Etarget b)
  end

with transf_exprlist (pmap: AST.ident -> option (expr -> expr)) (el: exprlist) {struct el} : Errors.res exprlist :=
  match el with
  | Enil => Errors.OK Enil
  | Econs e el =>
      do e <- transf_expr pmap e;
      do el <- transf_exprlist pmap el;
      Errors.OK (Econs e el)
  end.

(* WARNING: missing lists *)
Fixpoint transf_statement (pmap: AST.ident -> option (expr -> expr))
  (s: Stanlight.statement) {struct s} : Errors.res (Stanlight.statement) :=
  match s with
  | Sskip => Errors.OK (Sskip)
  | Sassign e1 o e2 =>
    do e1 <- transf_expr pmap e1;
    do e2 <- transf_expr pmap e2;
    Errors.OK (Sassign e1 o e2)
  | Ssequence s1 s2 =>
    do s1 <- (transf_statement pmap s1);
    do s2 <- (transf_statement pmap s2);
    Errors.OK (Ssequence s1 s2)
  | Sifthenelse e s1 s2 =>
    do e <- (transf_expr pmap e);
    do s1 <- (transf_statement pmap s1);
    do s2 <- (transf_statement pmap s2);
    Errors.OK (Sifthenelse e s1 s2)
  | Sfor i e1 e2 s =>
    do e1 <- transf_expr pmap e1;
    do e2 <- transf_expr pmap e2;
    do s <- transf_statement pmap s;
    Errors.OK (Sfor i e1 e2 s)
  | Starget e =>
    do e <- transf_expr pmap e;
    Errors.OK (Starget e)
  | Stilde e d el =>
    Errors.Error (Errors.msg "Reparamterization: detected Stilde, but should have been removed in Sampling")
  end.

Definition check_non_param (pmap: AST.ident -> option (expr -> expr)) (v: AST.ident * basic) : Errors.res unit :=
  match pmap (fst v) with
  | Some _ => Errors.Error (Errors.msg "Reparameterization: function's local shadows a parameter")
  | None => Errors.OK tt
  end.

Definition vars_check_shadow (p: AST.ident * basic) :=
  let '(id, b) := p in
  if forallb (fun id' => match (Pos.eq_dec id' id) with
                      | left _ => false
                      | right _ => true
                         end) StanEnv.math_idents then
    Errors.OK tt
  else
    Errors.Error (Errors.msg "Reparameterization: variable shadows global math functions").


Definition transf_function (pmap: AST.ident -> option _) (correction: expr) (f: Stanlight.function): Errors.res
 (Stanlight.function) :=
  do _ <- Errors.mmap (check_non_param pmap) (f.(fn_vars));
  do _ <- Errors.mmap (vars_check_shadow) (f.(fn_vars));
  do body <- transf_statement pmap f.(fn_body);
  let body := Ssequence body (Starget correction) in
  Errors.OK (mkfunction body f.(fn_vars)).

Definition transf_fundef (pmap: AST.ident -> option _) (correction: expr) (fd: Stanlight.fundef) : Errors.res Stanlight.fundef :=
  match fd with
  | Ctypes.Internal f =>
      do tf <- transf_function pmap correction f;
      Errors.OK (Ctypes.Internal tf)
  | Ctypes.External ef targs tres cc => Errors.OK (Ctypes.External ef targs tres cc)
  end.

Definition transf_variable (_: AST.ident) (v: Stanlight.variable): Errors.res Stanlight.variable :=
  Errors.OK (mkvariable (v.(vd_type)) (Cidentity)).

(* TODO: the use of this should be removed and basics should be omitted from pr_parameters_vars in syntax *)
Definition valid_equiv_param_type (b1 b2 : basic) :=
  match b1, b2 with
  | Breal, Breal => true
  | Barray Breal z1, Barray Breal z2 =>
      if Z.eq_dec z1 z2 then true else false
  | _, _ => false
  end.

Lemma valid_equiv_param_type_spec b1 b2 :
  valid_equiv_param_type b1 b2 = true ->
  b1 = b2.
Proof.
  destruct b1, b2;
    try (simpl; inversion 1; fail); auto;
    try (simpl; destruct b1; inversion 1; fail); auto.
  simpl. destruct b1, b2; try (inversion 1; fail).
  destruct (Z.eq_dec).
  { intros; subst; auto. }
  { inversion 1. }
Qed.


Fixpoint find_parameter {A} (defs: list (AST.ident * AST.globdef fundef variable)) (entry: AST.ident * basic * A) {struct defs}: Errors.res (AST.ident * variable * A) :=
  let '(param, b, a) := entry in
  match defs with
  | nil => Errors.Error (Errors.msg "Reparameterization: parameter missing from list of global definitions")
  | (id,def) :: defs =>
    match def with
    | AST.Gvar v =>
        if positive_eq_dec id param then
          if valid_equiv_param_type (vd_type (AST.gvar_info v)) b then
               Errors.OK (param,v.(AST.gvar_info), a)
          else
            Errors.Error (Errors.msg "Reparameterization: parameter type inconsistent")
        else find_parameter defs entry
    | AST.Gfun _ => find_parameter defs entry
    end
  end.

Definition unconstrained_to_constrained_fun (c: constraint) : expr -> expr :=
  fun i =>
  match c with
  | Cidentity => i
  | Clower_upper a b =>
    let a := Econst_float a Breal in
    let b := Econst_float b Breal in
    let call := Ecall (Evar $"expit" (Bfunction (Bcons Breal Bnil) Breal)) (Econs i Enil) Breal in
    (Ebinop a Plus (Ebinop (Ebinop b Minus a Breal) Times call Breal) Breal)
  | Clower a =>
    let a := Econst_float a Breal in
    let call := Ecall (Evar $"exp" (Bfunction (Bcons Breal Bnil) Breal)) (Econs i Enil) Breal in
    (Ebinop call Plus a Breal)
  | Cupper b =>
    let b := Econst_float b Breal in
    let negi := Ebinop (Econst_float Floats.Float.zero Breal) Minus i Breal in
    let call := Ecall (Evar $"exp" (Bfunction (Bcons Breal Bnil) Breal)) (Econs negi Enil) Breal in
    (Ebinop b Minus call Breal)
  end.

Definition unconstrained_to_constrained (v: variable) : option (expr -> expr) :=
  let typ := v.(vd_type) in
  let constraint := v.(vd_constraint) in
  Some (unconstrained_to_constrained_fun constraint).

Fixpoint u_to_c_rewrite_map {A} (parameters: list (AST.ident * variable * A)) {struct parameters}: (AST.ident -> option (expr -> expr)) :=
  match parameters with
  | nil => fun x => None
  | (id, v, _) :: parameters =>
    let inner_map := u_to_c_rewrite_map parameters in
      fun param =>
        if positive_eq_dec id param then (unconstrained_to_constrained v) else (inner_map param)
  end.

Definition change_of_variable_correction_fun (c: constraint) : option (expr -> expr) :=
    match c with
    | Cidentity => None
    | Clower_upper a b =>
        Some (
            fun x =>
              let a := Econst_float a Breal in
              let b := Econst_float b Breal in
              let one := Econst_float (Floats.Float.of_int Integers.Int.one) Breal in
              let call := Ecall (Evar $"expit" (Bfunction (Bcons Breal Bnil) Breal)) (Econs x Enil) Breal in
              let pre_log := (Ebinop (Ebinop b Minus a Breal) Times
                                (Ebinop call Times (Ebinop one Minus call Breal) Breal) Breal) in
              Ecall (Evar $"log" (Bfunction (Bcons Breal Bnil) Breal)) (Econs pre_log Enil) Breal)
    | Clower a =>
      Some (fun x => x)
    | Cupper b =>
      Some (fun x => Ebinop (Econst_float Floats.Float.zero Breal) Minus x Breal)
    end.

Definition change_of_variable_correction (i: AST.ident) (v: variable): option expr :=
  let typ := v.(vd_type) in
  let c := v.(vd_constraint) in
  let ofe := change_of_variable_correction_fun c in
  match ofe with
  | None => None
  | Some fe =>
      match typ with
      | Breal => Some (fe (Evar i typ))
      (* TODO: we should probably emit loops to handle large arrays rather than unrolling like this *)
      | Barray Breal sz =>
          Some (fold_left (fun e ofs => Ebinop e Plus (fe (Eindexed (Evar i typ)
                                                          (Econs (Econst_int ofs Bint) Enil) Breal)) Breal)
                  (count_up_int (Z.to_nat sz))
                  (Econst_float Floats.Float.zero Breal))
      | _ => None
      end
  end.

Fixpoint collect_corrections {A} (parameters: list (AST.ident * variable * A)) {struct parameters}: expr :=
  match parameters with
  | nil => Econst_float (Floats.Float.of_int Integers.Int.zero) Breal
  | (id,v,_) :: parameters =>
    match change_of_variable_correction id v with
    | None => collect_corrections parameters
    | Some correction => Ebinop correction Plus (collect_corrections parameters) Breal
    end
  end.

Definition no_param_out (p: AST.ident * basic * option (expr -> expr)) :=
  let '(id, _, ofout) := p in
  match ofout with
  | None => (Errors.OK tt)
  | Some _ =>
      Errors.Error (Errors.msg "Reparameterization: parameter already has a non-empty output mapping function")
  end.

Definition param_check_shadow (p: AST.ident * basic * option (expr -> expr)) :=
  let '(id, b, fe) := p in
  if forallb (fun id' => match (Pos.eq_dec id' id) with
                      | left _ => false
                      | right _ => true
                         end) StanEnv.math_idents then
    Errors.OK tt
  else
    Errors.Error (Errors.msg "Reparameterization: parameter shadows global math functions").

Definition transf_program(p: Stanlight.program): Errors.res Stanlight.program :=

  do _ <- Errors.mmap (no_param_out) p.(pr_parameters_vars);
  do _ <- Errors.mmap (param_check_shadow ) (p.(pr_parameters_vars));
  do parameters <- Errors.mmap (find_parameter p.(pr_defs)) p.(pr_parameters_vars);
  let pmap := u_to_c_rewrite_map parameters in
  let correction := collect_corrections parameters in
  let pr_parameters_vars' := List.map (fun '(id, v, f) =>
                                 (id, vd_type v,
                                   Some (fun x => (unconstrained_to_constrained_fun (vd_constraint v) x))))
                               parameters in

  do p1 <- AST.transform_partial_program2 (fun id => transf_fundef pmap correction) transf_variable p;
  Errors.OK {|
      Stanlight.pr_defs := AST.prog_defs p1;
      Stanlight.pr_parameters_vars := pr_parameters_vars';
      Stanlight.pr_data_vars := p.(pr_data_vars);
    |}.
