Require Import List.
Require Import StanE.
Require Import Ctypes.
Require CStan.
Require Import Errors.
Require Import String.
Open Scope string_scope.
Require Import Coqlib.
Require Import Sops.
Require Import Cop.
Require Import Clightdefs.
Require Import Int.


Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition option_mmap {X Y:Type} (f: X -> res Y) (ox: option X) : res (option Y) :=
  match ox with
  | None => OK None
  | Some x => do x <- f x; OK (Some x)
  end.

Fixpoint transf_type (t: StanE.basic) : res type :=
  match t with
  | StanE.Bint => OK tint
  | StanE.Breal => OK tdouble
  | StanE.Barray ty i => 
      do ty <- transf_type ty;
      OK (tarray ty i)
  | StanE.Bfunction tl ret =>
    do tl <- transf_typelist tl;
    do ty <- transf_type ret;
    OK (Ctypes.Tfunction tl ty AST.cc_default)
  end
with transf_typelist (tl: StanE.basiclist) : res Ctypes.typelist :=
  match tl with
  | StanE.Bnil =>  OK Ctypes.Tnil
  | StanE.Bcons t tl =>
    do t <- transf_type t;
    do tl <- transf_typelist tl;
    OK (Ctypes.Tcons t tl)
  end.



Definition transf_operator (o: StanE.b_op): res Cop.binary_operation :=
  match o with
  | StanE.Plus => OK Cop.Oadd
  | StanE.Minus => OK Cop.Osub
  | StanE.Times => OK Cop.Omul
  | StanE.Divide => OK Cop.Odiv
  | StanE.Modulo => OK Cop.Omod
  | StanE.Or => OK Cop.Oor
  | StanE.And => OK Cop.Oand
  | StanE.Equals => OK Cop.Oeq
  | StanE.NEquals => OK Cop.One
  | StanE.Less => OK Cop.Olt
  | StanE.Leq => OK Cop.Ole
  | StanE.Greater => OK Cop.Ogt
  | StanE.Geq => OK Cop.Oge
  end.

Definition transf_operator_return (o: StanE.b_op): res Ctypes.type :=
  match o with
  | StanE.Plus => OK tdouble
  | StanE.Minus => OK tdouble
  | StanE.Times => OK tdouble
  | StanE.Divide => OK tdouble
  | StanE.Modulo => OK tint
  | StanE.Or => OK tbool
  | StanE.And => OK tbool
  | StanE.Equals => OK tbool
  | StanE.NEquals => OK tbool
  | StanE.Less => OK tbool
  | StanE.Leq => OK tbool
  | StanE.Greater => OK tbool
  | StanE.Geq =>	OK tbool
  end.


Definition transf_unary_operator (o: StanE.u_op): res Cop.unary_operation :=
  match o with
  | StanE.PNot => OK Cop.Onotbool
  end.


Fixpoint transf_expression (e: StanE.expr) {struct e}: res CStan.expr :=
  match e with
  | Econst_int i ty => do ty <- transf_type ty; OK (CStan.Econst_int i ty)
  | Econst_float f ty => do ty <- transf_type ty; OK (CStan.Econst_float f ty)
  | Evar i ty =>
    do ty <- transf_type ty;
    OK (CStan.Evar i ty)
  | Eunop o e ty =>
    do o <- transf_unary_operator o;
    do ty <- transf_type ty;
    do e <- transf_expression e;
    OK (CStan.Eunop o e ty)
  | Ebinop e1 o0 e2 ty =>
    do ty <- transf_type ty;
    do o <- transf_operator o0;
    do t <- transf_operator_return o0;
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    OK (CStan.Ebinop o e1 e2 ty)
  | Eindexed e (cons i nil) ty =>
    do e <- transf_expression e;
    do ty <- transf_type ty;
    do i <- transf_expression i;
    OK (CStan.Ederef (CStan.Ebinop Oadd e i (tptr ty)) ty)
  | Eindexed e _ ty =>
    Error (msg "Denumpyification.transf_expression (NYI): Eindexed [i, ...]")
  | Etarget ty => 
    do ty <- transf_type ty;
    OK (CStan.Etarget Tvoid)
  end.


Fixpoint list_mmap {X Y: Type} (f: X-> res Y)(l: list X) {struct l}: res (list Y) :=
  match l with
  | nil => OK (nil)
  | cons e l =>
    do e <- f e;
    do l <- list_mmap f l;
    OK (cons e l)
  end.


Fixpoint transf_statement (s: StanE.statement) {struct s}: res CStan.statement :=
  match s with
  | Sskip => OK CStan.Sskip
  | Sassign e1 None e2 => (* v = x *)
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    OK (CStan.Sassign e1 e2)
  | Sassign e1 (Some o) e2 => (* v ?= x *)
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    do o <- transf_operator o;
    Error (msg "Denumpyification.transf_statement (NYI): Sassign")
    (* OK (CStan.Sassign e1 (CStan.Ebinop o e1 e2 Tvoid)) TODO(stites): Tvoid seems wrong and I need to doublecheck. *)
  | Scall dst f ty el =>
    do el <- list_mmap transf_expression el;
    do ty <- transf_type ty;
    OK (CStan.Scall (Some dst) (CStan.Evar f ty) el) 
  | Ssequence s1 s2 =>
    do s1 <- (transf_statement s1);
    do s2 <- (transf_statement s2);
    OK (CStan.Ssequence s1 s2)
  | Sifthenelse e s1 s2 =>
    do e <- (transf_expression e); 
    do s1 <- (transf_statement s1);
    do s2 <- (transf_statement s2);
    OK (CStan.Sifthenelse e s1 s2)
  | Sfor i e1 e2 s =>
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    do body <- transf_statement s;

    let one := Integers.Int.repr 1 in
    let eone := CStan.Econst_int one tint in
    (* set i to first pointer in array: convert 1-idx to 0-idx *)
    let init := CStan.Sassign (CStan.Evar i tint) (CStan.Ebinop Osub e1 eone tint) in

    (* break condition of e1 == e2 *)
    let cond := CStan.Ebinop Olt (CStan.Evar i (CStan.typeof e1)) e2 tint in

    let eincr := CStan.Ebinop Oadd (CStan.Evar i (CStan.typeof e1)) eone tint in

    let incr := CStan.Sassign (CStan.Evar i tint) eincr in
    OK (CStan.Sfor init cond body incr)
  | Starget e =>
    do e <- transf_expression e;
    OK (CStan.Starget e)

  | Stilde e d el =>
    do e <- transf_expression e;
    do d <- transf_expression d;
    do el <- list_mmap transf_expression el;
    OK (CStan.Stilde e d el (None, None))
end.

Definition transf_constraint (c : StanE.constraint) : res CStan.constraint :=
  match c with
  | StanE.Cidentity => OK CStan.Cidentity
  | StanE.Clower e => OK (CStan.Clower (CStan.Econst_float e tdouble))
  | StanE.Cupper e => OK (CStan.Cupper (CStan.Econst_float e tdouble))
  | StanE.Clower_upper e0 e1 =>
    OK (CStan.Clower_upper (CStan.Econst_float e0 tdouble) (CStan.Econst_float e1 tdouble))
  end.
 
Definition transf_variable (_: AST.ident) (v: StanE.variable): res (type * CStan.constraint) :=
  do ty <- transf_type (StanE.vd_type v);
  do c <- transf_constraint (StanE.vd_constraint v);
  OK (ty, c).

Fixpoint mapM {X Y:Type} (f: X -> res Y) (xs: list X) : res (list Y) :=
  match xs with
  | nil => OK nil
  | cons x l =>
    do y <- f x;
    do l <- mapM f l;
    OK (cons y l)
  end.
(**********************************************************************************************************)
Definition transf_var (v: AST.ident * StanE.basic) : res (AST.ident * type) :=
  match v with
    | (i, t) => do t <- transf_type t; OK (i, t)
  end.

Definition transf_vars (vs: list (AST.ident * StanE.basic)) : res (list (AST.ident * type)) :=
  mapM transf_var vs.

(* FIXME: lambdas are too general? typechecker seems to want something more concrete... *)
Definition transf_param (p: StanE.basic * AST.ident) : res (AST.ident * type) :=
  match p with
    | (t, i) => do t <- transf_type t; OK (i, t)
  end.

Definition transf_params (ps: list (StanE.basic * AST.ident)) : res (list (AST.ident * type)) :=
  mapM transf_param ps.

Definition transf_function (f: StanE.function): res CStan.function :=
  do body <- transf_statement f.(StanE.fn_body);
  do temps <- transf_vars f.(StanE.fn_temps);
  do vars <- transf_vars f.(StanE.fn_vars);
  do ret <- option_mmap transf_type f.(StanE.fn_return);
  do params <- transf_params f.(StanE.fn_params);
  OK {|
      CStan.fn_return :=
        match ret with
          | Some ty => ty
          | None => Tvoid
        end;
      CStan.fn_params := params;
      CStan.fn_body := body;
      CStan.fn_blocktype := f.(StanE.fn_blocktype);
      CStan.fn_callconv := AST.cc_default;
      CStan.fn_temps := temps;
      CStan.fn_vars := vars;
      CStan.fn_generator := SimplExpr.initial_generator tt;
     |}.

Definition transf_fundef (id: AST.ident) (fd: StanE.fundef) : res CStan.fundef :=
  match fd with
  | Internal f =>
      do tf <- transf_function f; OK (Internal tf)
  | External ef targs tres cc =>
      OK (External ef targs tres cc)
  end.

Definition map_globdef {X} {Y} (f : X -> Y) (gty: AST.globdef CStan.fundef X) : option Y :=
  match gty with
  | AST.Gfun _ => None
  | AST.Gvar t => Some (f t.(AST.gvar_info))
  end.

Definition globdef_to_type : AST.globdef CStan.fundef type -> option type :=
  map_globdef id.

Definition ident_eq_dec : forall (x y : AST.ident), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.

Fixpoint ident_list_member (xs:list AST.ident) (x:AST.ident) : bool :=
  match xs with
  | nil => false
  | x'::xs => if ident_eq_dec x x' then true else ident_list_member xs x
  end.

Fixpoint catMaybes {X : Type} (xs : list (option X)) : list X :=
  match xs with
  | nil => nil
  | (Some x)::xs => x::(catMaybes xs)
  | None::xs => catMaybes xs
  end.

Definition filter_globvars (all_defs : list (AST.ident*AST.globdef CStan.fundef type)) (vars : list AST.ident) :
  members :=
  let maybe_member := fun tpl => option_map (fun ty => (fst tpl, ty)) (globdef_to_type (snd tpl)) in
  let all_members := catMaybes (List.map maybe_member all_defs) in
  let stan_members := List.filter (fun tpl => ident_list_member vars (fst tpl)) all_members in
  let plain_members := List.map (fun tpl => Member_plain (fst tpl) (snd tpl)) stan_members in
  plain_members.

Definition eglobdef_to_constr : AST.globdef CStan.fundef (type * CStan.constraint) -> option CStan.constraint :=
  map_globdef (fun x => match x with | (_, c) => c end).

Definition transf_elaborated_globdef (gd : AST.globdef CStan.fundef (type * CStan.constraint)) : AST.globdef CStan.fundef type :=
  match gd with
  | AST.Gfun f => AST.Gfun f
  | AST.Gvar t =>
    AST.Gvar {|
      AST.gvar_info := (fst t.(AST.gvar_info));
      AST.gvar_init := t.(AST.gvar_init);
      AST.gvar_readonly := t.(AST.gvar_readonly);
      AST.gvar_volatile := t.(AST.gvar_volatile);
    |}
  end.

Definition map_values {K V X:Type} (f : V -> X) : list (K * V) -> list (K * X) :=
  List.map (fun tpl => (fst tpl, f (snd tpl))).

Definition cat_values {K V :Type} (kvs : list (K * option V)) : list (K * V) :=
  catMaybes (List.map (fun tpl => option_map (fun x => (fst tpl, x)) (snd tpl)) kvs).

Parameter comp_env_eq : forall pty prog_comp_env,
  build_composite_env pty = OK prog_comp_env.

Definition mk_composite (all_defs : list (AST.ident * AST.globdef CStan.fundef type)) (struct_ident : AST.ident) (vars : list AST.ident) : composite_definition :=
  Composite
    struct_ident
    Ctypes.Struct
    (filter_globvars all_defs vars)
    Ctypes.noattr.

Definition transf_program(p: StanE.program): res CStan.program :=
  do p1 <- AST.transform_partial_program2 transf_fundef transf_variable p;

  let all_elaborated_defs := AST.prog_defs p1 in
  let all_defs := map_values transf_elaborated_globdef all_elaborated_defs in
  let all_contraints := cat_values (map_values eglobdef_to_constr all_elaborated_defs) in

  let params_struct_id := CStan.res_params_type (StanE.pr_parameters_struct p) in
  (* (* let params_struct := mk_composite all_defs params_struct_id p.(StanE.pr_parameters_vars) in *) *)
  (* let params_struct := Composite params_struct_id Ctypes.Struct (filter_globvars all_defs p.(StanE.pr_parameters_vars)) Ctypes.noattr in *)
  (* (* Error (MSG "list of params: " :: (List.map CTX p.(StanE.pr_parameters_vars))). *) *)

  do parameter_vars <- list_mmap (fun ib => do b <- transf_type (snd ib); OK (fst ib, b)) p.(StanE.pr_parameters_vars);
  let parameter_members := List.map (fun tlp => Member_plain (fst tlp) (snd tlp)) parameter_vars in
  let params_struct := Composite params_struct_id Ctypes.Struct parameter_members Ctypes.noattr in

  let data_struct_id := CStan.res_data_type (StanE.pr_data_struct p) in
  do data_vars <- list_mmap (fun ib => do b <- transf_type (snd ib); OK (fst ib, b)) p.(StanE.pr_data_vars);
  let data_members := List.map (fun tlp => Member_plain (fst tlp) (snd tlp)) data_vars in
  let data_struct := Composite data_struct_id Ctypes.Struct data_members Ctypes.noattr in

  let composite_types := data_struct :: params_struct :: nil in

  do comp_env <- Ctypes.build_composite_env composite_types;


  OK {|
      CStan.prog_defs := all_defs;
      CStan.prog_public:=p.(StanE.pr_public);
      CStan.prog_model:=p.(StanE.pr_model);
      CStan.prog_target:=p.(StanE.pr_target);
      CStan.prog_data_vars:=data_vars;
      CStan.prog_data_struct:= p.(StanE.pr_data_struct);
      CStan.prog_constraints := all_contraints;
      CStan.prog_parameters_vars:=parameter_vars;
      CStan.prog_parameters_struct:= p.(StanE.pr_parameters_struct);
      CStan.prog_types:=composite_types;
      CStan.prog_comp_env:=comp_env;
      CStan.prog_comp_env_eq:= comp_env_eq composite_types comp_env;
      CStan.prog_main:=p.(StanE.pr_main);
      CStan.prog_math_functions:= p.(StanE.pr_math_functions);
      CStan.prog_dist_functions:= p.(StanE.pr_dist_functions);
    |}.
