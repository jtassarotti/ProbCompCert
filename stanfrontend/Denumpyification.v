Require Import List.
Require Import StanE.
Require Import Ctypes.
Require CStan.
Require Errors.
Require Import String.
Open Scope string_scope.
Require Import Coqlib.
Require Import Sops.
Require Import Cop.
Require Import Clightdefs.
Require Import Int.
Require Import SimplExpr.
Require Import Maps.

Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Local Open Scope clight_scope.



Notation "'do' X <- A ; B" := (Errors.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Notation "'do' X <~ A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Notation "'do' ( X , Y ) <~ A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Fixpoint transf_type (t: StanE.basic) : mon type :=
  match t with
  | StanE.Bint => ret tint
  | StanE.Breal => ret tdouble
  | StanE.Barray ty i => 
      do ty <~ transf_type ty;
      ret (tarray ty i)
  | StanE.Bfunction tl rty =>
    do tl <~ transf_typelist tl;
    do ty <~ transf_type rty;
    ret (Ctypes.Tfunction tl ty AST.cc_default)
  end
with transf_typelist (tl: StanE.basiclist) : mon Ctypes.typelist :=
  match tl with
  | StanE.Bnil =>  ret Ctypes.Tnil
  | StanE.Bcons t tl =>
    do t <~ transf_type t;
    do tl <~ transf_typelist tl;
    ret (Ctypes.Tcons t tl)
  end.

Fixpoint transf_type_res (t: StanE.basic) : Errors.res type :=
  match t with
  | StanE.Bint => Errors.OK tint
  | StanE.Breal => Errors.OK tdouble
  | StanE.Barray ty i => 
      do ty <- transf_type_res ty;
      Errors.OK (tarray ty i)
  | StanE.Bfunction tl ret =>
    do tl <- transf_typelist_res tl;
    do ty <- transf_type_res ret;
    Errors.OK (Ctypes.Tfunction tl ty AST.cc_default)
  end
with transf_typelist_res (tl: StanE.basiclist) : Errors.res Ctypes.typelist :=
  match tl with
  | StanE.Bnil =>  Errors.OK Ctypes.Tnil
  | StanE.Bcons t tl =>
    do t <- transf_type_res t;
    do tl <- transf_typelist_res tl;
    Errors.OK (Ctypes.Tcons t tl)
  end.

Definition transf_operator (o: StanE.b_op): mon Cop.binary_operation :=
  match o with
  | StanE.Plus => ret Cop.Oadd
  | StanE.Minus => ret Cop.Osub
  | StanE.Times => ret Cop.Omul
  | StanE.Divide => ret Cop.Odiv
  | StanE.Modulo => ret Cop.Omod
  | StanE.Or => ret Cop.Oor
  | StanE.And => ret Cop.Oand
  | StanE.Equals => ret Cop.Oeq
  | StanE.NEquals => ret Cop.One
  | StanE.Less => ret Cop.Olt
  | StanE.Leq => ret Cop.Ole
  | StanE.Greater => ret Cop.Ogt
  | StanE.Geq => ret Cop.Oge
  end.

Definition transf_operator_return (o: StanE.b_op): mon Ctypes.type :=
  match o with
  | StanE.Plus => ret tdouble
  | StanE.Minus => ret tdouble
  | StanE.Times => ret tdouble
  | StanE.Divide => ret tdouble
  | StanE.Modulo => ret tint
  | StanE.Or => ret tbool
  | StanE.And => ret tbool
  | StanE.Equals => ret tbool
  | StanE.NEquals => ret tbool
  | StanE.Less => ret tbool
  | StanE.Leq => ret tbool
  | StanE.Greater => ret tbool
  | StanE.Geq =>	ret tbool
  end.


Definition transf_unary_operator (o: StanE.u_op): mon Cop.unary_operation :=
  match o with
  | StanE.PNot => ret Cop.Onotbool
  end.

Fixpoint unzip {X Y: Type} (l: list (X * Y)) {struct l} : (list X) * (list Y) :=
  match l with
  | nil => (nil,nil)
  | cons (e1,e2) l => 
    match unzip l with
    | (l1,l2) => (cons e1 l1,cons e2 l2)
    end
  end.

Fixpoint flatten (l: list (list CStan.statement)) {struct l} : list CStan.statement :=
  match l with
  | nil => nil
  | l :: ll => l ++ flatten ll
  end. 

Fixpoint transf_expression (e: StanE.expr) {struct e}: mon (list CStan.statement * CStan.expr) :=
  match e with
  | Econst_int i ty => 
    do ty <~ transf_type ty; 
    ret (nil, CStan.Econst_int i ty)
  | Econst_float f ty => 
    do ty <~ transf_type ty; 
    ret (nil, CStan.Econst_float f ty)
  | Evar i ty =>
    do ty <~ transf_type ty;
    ret (nil, CStan.Evar i ty)
  | Ecall e el ty =>
    (* WARNING: true for mini-Stan (for now), but type checking should ensure this *)
    do t <~ gensym tdouble;
    do (le, e) <~ transf_expression e;
    do (lel, el) <~ transf_exprlist el;
    do ty <~ transf_type ty;
    ret (le ++ CStan.Scall (Some t) e el :: nil, (CStan.Etempvar t ty))
  | Eunop o e ty =>
    do o <~ transf_unary_operator o;
    do ty <~ transf_type ty;
    do (ls, e) <~ transf_expression e;
    ret (ls, CStan.Eunop o e ty)
  | Ebinop e1 o0 e2 ty =>
    do ty <~ transf_type ty;
    do o <~ transf_operator o0;
    do t <~ transf_operator_return o0;
    do (ls1, e1) <~ transf_expression e1;
    do (ls2, e2) <~ transf_expression e2;
    ret (ls1 ++ ls2, CStan.Ebinop o e1 e2 ty)
  | Eindexed e (Econs i Enil) ty =>
    do (le, e) <~ transf_expression e;
    do ty <~ transf_type ty;
    do (li, i) <~ transf_expression i;
    (* ret (le ++ li, CStan.Ebinop Oadd (CStan.Ederef e (tptr ty)) i ty) *)
    ret (le ++ li, CStan.Ederef (CStan.Ebinop Oadd e i (tptr ty)) ty)
  | Eindexed e _ ty =>
    error (Errors.msg "Denumpyification.transf_expression (NYI): Eindexed [i, ...]")
  | Etarget ty => 
    do ty <~ transf_type ty;
    ret (nil, CStan.Etarget Tvoid)
  end

with transf_exprlist (el: exprlist) : mon (list CStan.statement * list CStan.expr) :=
  match el with
  | Enil =>
      ret (nil, nil)
  | Econs e el =>
      do (sl1, a1) <- transf_expression e;
      do (sl2, al2) <- transf_exprlist el;
      ret (sl1 ++ sl2, a1 :: al2)
  end.


Fixpoint list_mmap {X Y: Type} (f: X-> mon Y)(l: list X) {struct l}: mon (list Y) :=
  match l with
  | nil => ret (nil)
  | cons e l =>
    do e <~ f e;
    do l <~ list_mmap f l;
    ret (cons e l)
  end.

Fixpoint makeseq (l: list CStan.statement) (s: CStan.statement) : CStan.statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq l' (CStan.Ssequence s' s) 
  end.

Fixpoint transf_statement (s: StanE.statement) {struct s}: mon CStan.statement :=
  match s with
  | Sskip => ret CStan.Sskip
  | Sassign e1 None e2 => (* v = x *)
    do (le1, e1) <~ transf_expression e1;
    do (le2, e2) <~ transf_expression e2;
    ret (makeseq (le1 ++ le2) (CStan.Sassign e1 e2))
  | Sassign e1 (Some o) e2 => (* v ?= x *)
    do e1 <~ transf_expression e1;
    do e2 <~ transf_expression e2;
    do o <~ transf_operator o;
    error (Errors.msg "Denumpyification.transf_statement (NYI): Sassign")
  | Ssequence s1 s2 =>
    do s1 <~ (transf_statement s1);
    do s2 <~ (transf_statement s2);
    ret (CStan.Ssequence s1 s2)
  | Sifthenelse e s1 s2 =>
    do (l, e) <~ (transf_expression e); 
    do s1 <~ (transf_statement s1);
    do s2 <~ (transf_statement s2);
    ret (makeseq l (CStan.Sifthenelse e s1 s2))
  | Sfor i e1 e2 s =>
    do (le1, e1) <~ transf_expression e1;
    do (le2, e2) <~ transf_expression e2;
    do body <~ transf_statement s;

    let one := Integers.Int.repr 1 in
    let eone := CStan.Econst_int one tint in
    (* set i to first pointer in array: convert 1-idx to 0-idx *)
    let init := CStan.Sassign (CStan.Evar i tint) (CStan.Ebinop Osub e1 eone tint) in

    (* break condition of e1 == e2 *)
    let cond := CStan.Ebinop Olt (CStan.Evar i (CStan.typeof e1)) e2 tint in

    let eincr := CStan.Ebinop Oadd (CStan.Evar i (CStan.typeof e1)) eone tint in

    let incr := CStan.Sassign (CStan.Evar i tint) eincr in
    ret (makeseq (le1 ++ le2) (CStan.Sfor init cond body incr))
  | Starget e =>
    do (l, e) <~ transf_expression e;
    ret (makeseq l (CStan.Starget e))

  | Stilde e d el =>
    do (le, e) <~ transf_expression e;
    do (ld ,d) <~ transf_expression d;
    (* do (lel, el) <~ (CStan.mon_fmap unzip (CStan.mon_mmap transf_expression el)); *)
    do (lel, el) <~ transf_exprlist el;
    ret (makeseq (le ++ ld ++ lel) (CStan.Stilde e d el (None, None)))
end.

Definition transf_constraint (c : StanE.constraint) : mon CStan.constraint :=
  match c with
  | StanE.Cidentity => ret CStan.Cidentity
  | StanE.Clower e => ret (CStan.Clower (CStan.Econst_float e tdouble))
  | StanE.Cupper e => ret (CStan.Cupper (CStan.Econst_float e tdouble))
  | StanE.Clower_upper e0 e1 =>
    ret (CStan.Clower_upper (CStan.Econst_float e0 tdouble) (CStan.Econst_float e1 tdouble))
  end.
 
Fixpoint mapM {X Y:Type} (f: X -> mon Y) (xs: list X) : mon (list Y) :=
  match xs with
  | nil => ret nil
  | cons x l =>
    do y <~ f x;
    do l <~ mapM f l;
    ret (cons y l)
  end.
(**********************************************************************************************************)
Definition transf_var (v: AST.ident * StanE.basic) : mon (AST.ident * type) :=
  match v with
    | (i, t) => do t <~ transf_type t; ret (i, t)
  end.

Definition transf_vars (vs: list (AST.ident * StanE.basic)) : mon (list (AST.ident * type)) :=
  mapM transf_var vs.

(* FIXME: lambdas are too general? typechecker seems to want something more concrete... *)
Definition transf_param (p: StanE.basic * AST.ident) : mon (AST.ident * type) :=
  match p with
    | (t, i) => do t <~ transf_type t; ret (i, t)
  end.

Definition transf_params (ps: list (StanE.basic * AST.ident)) : mon (list (AST.ident * type)) :=
  mapM transf_param ps.

Definition option_mmap {X Y:Type} (f: X -> mon Y) (ox: option X) : mon (option Y) :=
  match ox with
  | None => ret None
  | Some x => do x <~ f x; ret (Some x)
  end.

Definition transf_variable (_: AST.ident) (v: StanE.variable): Errors.res (type * CStan.constraint) :=
  let m :=
    do ty <~ transf_type (StanE.vd_type v);
    do c <~ transf_constraint (StanE.vd_constraint v);
    ret (ty, c) in
  match m (SimplExpr.initial_generator tt) with
  | SimplExpr.Err msg => Errors.Error msg
  | SimplExpr.Res (ty, c) g i =>   Errors.OK (ty,c)
  end.

Definition transf_function (f: StanE.function): Errors.res CStan.function :=
  let m :=
    do body <~ transf_statement f.(StanE.fn_body);
    do vars <~ transf_vars f.(StanE.fn_vars);
    do ret_ty <~ option_mmap transf_type f.(StanE.fn_return);
    do params <~ transf_params f.(StanE.fn_params);
    ret (body,vars,ret_ty,params) in
  match m (SimplExpr.initial_generator tt) with
  | SimplExpr.Err msg => Errors.Error msg
  | SimplExpr.Res (body, vars, ret_ty, params) g i =>
  Errors.OK {|
      CStan.fn_return :=
        match ret_ty with
          | Some ty => ty
          | None => Tvoid
        end;
      CStan.fn_params := params;
      CStan.fn_body := body;
      CStan.fn_blocktype := CStan.BTModel;
      CStan.fn_callconv := AST.cc_default;
      CStan.fn_temps := nil;
      CStan.fn_vars := vars;
      CStan.fn_generator := g;
     |}
end.

Definition transf_fundef (id: AST.ident) (fd: StanE.fundef) : Errors.res CStan.fundef :=
  match fd with
  | Internal f =>
      do tf <- transf_function f; Errors.OK (Internal tf)
  | External ef targs tres cc =>
      Errors.OK (External ef targs tres cc)
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
  build_composite_env pty = Errors.OK prog_comp_env.

Definition mk_composite (all_defs : list (AST.ident * AST.globdef CStan.fundef type)) (struct_ident : AST.ident) (vars : list AST.ident) : composite_definition :=
  Composite
    struct_ident
    Ctypes.Struct
    (filter_globvars all_defs vars)
    Ctypes.noattr.

Fixpoint list_mmap_res {X Y: Type} (f: X-> Errors.res Y)(l: list X) {struct l}: Errors.res (list Y) :=
  match l with
  | nil => Errors.OK (nil)
  | cons e l =>
    do e <- f e;
    do l <- list_mmap_res f l;
    Errors.OK (cons e l)
  end.

Definition transf_program(p: StanE.program): Errors.res CStan.program :=
  do p1 <- AST.transform_partial_program2 transf_fundef transf_variable p;

  let all_elaborated_defs := AST.prog_defs p1 in
  let all_defs := map_values transf_elaborated_globdef all_elaborated_defs in
  let all_contraints := cat_values (map_values eglobdef_to_constr all_elaborated_defs) in

  let params_struct_id := $"Params" in 

  do parameter_vars <- list_mmap_res (fun ib => do b <- transf_type_res (snd ib); Errors.OK (fst ib, b)) p.(StanE.pr_parameters_vars);
  let parameter_members := List.map (fun tlp => Member_plain (fst tlp) (snd tlp)) parameter_vars in
  let params_struct := Composite params_struct_id Ctypes.Struct parameter_members Ctypes.noattr in

  let data_struct_id := $"Data" in
  do data_vars <- list_mmap_res (fun ib => do b <- transf_type_res (snd ib); Errors.OK (fst ib, b)) p.(StanE.pr_data_vars);
  let data_members := List.map (fun tlp => Member_plain (fst tlp) (snd tlp)) data_vars in
  let data_struct := Composite data_struct_id Ctypes.Struct data_members Ctypes.noattr in

  let composite_types := data_struct :: params_struct :: nil in

  do comp_env <- Ctypes.build_composite_env composite_types;


  Errors.OK {|
      CStan.prog_defs := all_defs;
      CStan.prog_public:=nil;
      CStan.prog_data_vars:=data_vars;
      CStan.prog_constraints := all_contraints;
      CStan.prog_parameters_vars:=parameter_vars;
      CStan.prog_types:= composite_types;
      CStan.prog_comp_env:= comp_env;
      CStan.prog_comp_env_eq:= comp_env_eq composite_types comp_env; 
    |}.
