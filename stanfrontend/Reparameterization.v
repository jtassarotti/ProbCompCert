Require Import List.
Require Import String.
Require Import ZArith.
Require Floats.
Require Integers.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Stanlight.
Require Errors.
Require Import Clightdefs.
Import Clightdefs.ClightNotations.

Local Open Scope clight_scope.

Notation "'do' X <- A ; B" := (Errors.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.



Fixpoint transf_expr (pmap: AST.ident -> option expr) (e: Stanlight.expr) {struct e}: Stanlight.expr :=
  match e with
  | Evar id ty =>
    match pmap id with
    | Some e => e
    | None => (Evar id ty)
    end
  | Ecall e el ty =>
    let e := transf_expr pmap e in
    let el := transf_exprlist pmap el in
    Ecall e el ty
  | Eunop o e ty =>
    let e := transf_expr pmap e in
    Eunop o e ty
  | Ebinop e1 o e2 ty =>
    let e1 := transf_expr pmap e1 in
    let e2 := transf_expr pmap e2 in
    Ebinop e1 o e2 ty
  | Eindexed e el ty =>
    let e := transf_expr pmap e in
    let el := transf_exprlist pmap el in
    Eindexed e el ty
  | _ => e
  end

with transf_exprlist (pmap: AST.ident -> option expr) (el: exprlist) {struct el} : exprlist :=
  match el with
  | Enil => Enil
  | Econs e el =>
      let e := transf_expr pmap e in
      let el := transf_exprlist pmap el in
      Econs e el
  end.

(* WARNING: missing lists *)
Fixpoint transf_statement (pmap: AST.ident -> option expr) (s: Stanlight.statement) {struct s} : Stanlight.statement :=
  match s with
  | Sskip => Sskip
  | Sassign e1 o e2 =>
    let e1 := transf_expr pmap e1 in
    let e2 := transf_expr pmap e2 in
    Sassign e1 o e2
  | Ssequence s1 s2 =>
    let s1 := (transf_statement pmap s1) in
    let s2 := (transf_statement pmap s2) in
    Ssequence s1 s2
  | Sifthenelse e s1 s2 =>
    let e := (transf_expr pmap e) in
    let s1 := (transf_statement pmap s1) in
    let s2 := (transf_statement pmap s2) in
    Sifthenelse e s1 s2
  | Sfor i e1 e2 s =>
    let e1 := transf_expr pmap e1 in
    let e2 := transf_expr pmap e2 in
    let s := transf_statement pmap s in
    Sfor i e1 e2 s
  | Starget e =>
    let e := transf_expr pmap e in
    Starget e
  | Stilde e d el =>
    let e := transf_expr pmap e in
    let el := transf_exprlist pmap el in
    let d := transf_expr pmap d in
    Stilde e d el
  end.

Definition transf_function (pmap: AST.ident -> option expr) (correction: expr) (f: Stanlight.function): Stanlight.function :=
  let body := transf_statement pmap f.(fn_body) in
  let body := Ssequence body (Starget correction) in
  mkfunction body f.(fn_vars).

Definition transf_fundef (pmap: AST.ident -> option expr) (correction: expr) (fd: Stanlight.fundef) : Errors.res Stanlight.fundef :=
  match fd with
  | Ctypes.Internal f =>
      let tf := transf_function pmap correction f in
      Errors.OK (Ctypes.Internal tf)
  | Ctypes.External ef targs tres cc => Errors.OK (Ctypes.External ef targs tres cc)
  end.

Definition transf_variable (_: AST.ident) (v: Stanlight.variable): Errors.res Stanlight.variable :=
  Errors.OK (mkvariable (v.(vd_type)) (Cidentity)).

Fixpoint find_parameter {A} (defs: list (AST.ident * AST.globdef fundef variable)) (entry: AST.ident * basic * A) {struct defs}: Errors.res (AST.ident * variable * A) :=
  let '(param, _, a) := entry in
  match defs with
  | nil => Errors.Error (Errors.msg "Reparameterization: parameter missing from list of global definitions")
  | (id,def) :: defs =>
    match def with
    | AST.Gvar v => if positive_eq_dec id param then Errors.OK (param,v.(AST.gvar_info), a) else find_parameter defs entry
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
    let call := Ecall (Evar $"exp" (Bfunction (Bcons Breal Bnil) Breal)) (Econs i Enil) Breal in
    (Ebinop b Minus call Breal)
  end.

Definition unconstrained_to_constrained (i: AST.ident) (v: variable) : option expr :=
  let typ := v.(vd_type) in
  let constraint := v.(vd_constraint) in
  match typ with
  | Breal => Some (unconstrained_to_constrained_fun constraint (Evar i typ))
  | Barray Breal _ =>
    match constraint with
    | Cidentity => Some (Evar i typ)
    | _ => None
    end
  | _ => None
  end.

Fixpoint u_to_c_rewrite_map {A} (parameters: list (AST.ident * variable * A)) {struct parameters}: (AST.ident -> option expr) :=
  match parameters with
  | nil => fun x => None
  | (id, v, _) :: parameters =>
    let inner_map := u_to_c_rewrite_map parameters in
      fun param =>
        if positive_eq_dec id param then (unconstrained_to_constrained id v) else (inner_map param)
  end.

Definition change_of_variable_correction (i: AST.ident) (v: variable): option expr :=
  let typ := v.(vd_type) in
  let constraint := v.(vd_constraint) in
  match typ with
  | Breal =>
    match constraint with
    | Cidentity => None
    | Clower_upper a b =>
      let a := Econst_float a Breal in
      let b := Econst_float b Breal in
      let one := Econst_float (Floats.Float.of_int Integers.Int.one) Breal in
      let call := Ecall (Evar $"expit" (Bfunction (Bcons Breal Bnil) Breal)) (Econs (Evar i typ) Enil) Breal in
      let pre_log := (Ebinop (Ebinop b Minus a Breal) Times (Ebinop call Times (Ebinop one Minus call Breal) Breal) Breal) in
      Some (Ecall (Evar $"log" (Bfunction (Bcons Breal Bnil) Breal)) (Econs pre_log Enil) Breal)
    | Clower a =>
      Some (Evar i typ)
    | Cupper b =>
      Some (Evar i typ)
    end
  | Barray Breal _ =>
    match constraint with
    | Cidentity => None
    | _ => None
    end
  | _ => None
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

Definition transf_program(p: Stanlight.program): Errors.res Stanlight.program :=

  do _ <- Errors.mmap (no_param_out) p.(pr_parameters_vars);
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
