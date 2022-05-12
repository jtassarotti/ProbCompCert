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

Definition option_mon_mmap {X Y:Type} (f: X -> mon Y) (ox: option X) : mon (option Y) :=
  match ox with
  | None => ret None
  | Some x => do x <~ f x; ret (Some x)
  end.

Fixpoint getmathfunc (t:math_func) (fs: list (math_func * AST.ident * Ctypes.type)) : mon (AST.ident * Ctypes.type) :=
  match fs with
  | nil => error (msg "impossible")
  | h::tl => if math_func_eq_dec (fst (fst h)) t then ret (snd (fst h), snd h) else getmathfunc t tl
  end.

Definition callmath (p: program) (t: math_func) (args : list expr) : mon (AST.ident * statement) :=
  do rt <~ gensym tdouble;
  do fty <~ getmathfunc t p.(prog_math_functions);
  ret (rt, Scall (Some rt) (Evar (fst fty) (snd fty)) args).

Definition stan_log (p: program) (e: expr) : mon (AST.ident * statement) := callmath p MFLog (e::nil).
Definition stan_exp (p: program) (e: expr) : mon (AST.ident * statement) := callmath p MFExp (e::nil).

Definition stan_logit (p: program) (e: expr) : mon (AST.ident * statement) := callmath p MFLogit (e::nil).
Definition stan_expit (p: program) (e: expr) : mon (AST.ident * statement) := callmath p MFExpit (e::nil).

Definition int2float (e:expr) : mon expr :=
  match e with
  | CStan.Econst_float _ _ => ret e
  | CStan.Econst_int i _ => ret (CStan.Econst_float (Float.of_int i) tdouble)
  | CStan.Econst_single f t => ret (CStan.Econst_float (Float.of_single f) tdouble)
  | CStan.Econst_long i t => ret (CStan.Econst_float (Float.of_long i) tdouble)
  | _ => error (msg "should never happen: incorrect use of this function")
  end.


Definition constraint_transform (p:program) (i: AST.ident) (c: constraint) : mon (option (AST.ident * statement)) :=
  let evar := Evar i tdouble in
  let t := tdouble in
  match c with
  | Cidentity => ret None
  | Clower a => do a <~ int2float a; mon_fmap Some (stan_log p (Ebinop Osub evar a t))
  | Cupper b => do b <~ int2float b; mon_fmap Some (stan_log p (Ebinop Osub b evar t))
  | Clower_upper a b =>
    mon_fmap Some (
      stan_logit p (Ebinop Odiv
        (Ebinop Osub evar a t)
        (Ebinop Osub b a t)
      t)
    )
  | Coffset e => error (msg "NYI constrained_to_unconstrained: Coffset")
  | Cmultiplier e => error (msg "NYI constrained_to_unconstrained: Cmultiplier")
  | Coffset_multiplier e0 e1 => error (msg "NYI constrained_to_unconstrained: Coffset_multiplier")
  | Cordered => error (msg "NYI constrained_to_unconstrained: Cordered")
  | Cpositive_ordered => error (msg "NYI constrained_to_unconstrained: Cpositive")
  | Csimplex => error (msg "NYI constrained_to_unconstrained: Csimplex")
  | Cunit_vector => error (msg "NYI constrained_to_unconstrained: Cunit")
  | Ccholesky_corr => error (msg "NYI constrained_to_unconstrained: Ccholesky")
  | Ccholesky_cov => error (msg "NYI constrained_to_unconstrained: Ccholesky")
  | Ccorrelation => error (msg "NYI constrained_to_unconstrained: Ccorrelation")
  | Ccovariance => error (msg "NYI constrained_to_unconstrained: Ccovariance")
  end.

Definition inv_constraint_transform (p:program) (i: AST.ident) (c: constraint) : mon (option (AST.ident * statement)) :=
  let evar := Evar i tdouble in
  let t := tdouble in
  match c with
  | Cidentity => ret None
  | Clower a =>
    do rt_call <~ stan_exp p evar;
    do a <~ int2float a;
    match rt_call with
    | (rt, call) =>
      do o <~ gensym t;
      ret (Some (o, Ssequence call (Sset o (Ebinop Oadd (Etempvar rt t) a t))))
    end
  | Cupper b =>
    do rt_call <~ stan_exp p evar;
    do b <~ int2float b;
    match rt_call with
    | (rt, call) =>
      do o <~ gensym t;
      ret (Some (o, Ssequence call (Sset o (Ebinop Osub b (Etempvar rt t) t))))
    end
  | Clower_upper a b =>
    do rt_call <~ stan_expit p evar;
    do a <~ int2float a;
    do b <~ int2float b;
    match rt_call with
    | (rt, call) =>
      let r := (Ebinop Oadd a (Ebinop Omul (Ebinop Osub b a t) (Etempvar rt tdouble) t) t) in
      do o <~ gensym t;
      ret (Some (o, Ssequence call (Sset o r)))
    end

  | Coffset e => error (msg "NYI constrained_to_unconstrained: Coffset")
  | Cmultiplier e => error (msg "NYI constrained_to_unconstrained: Cmultiplier")
  | Coffset_multiplier e0 e1 => error (msg "NYI constrained_to_unconstrained: Coffset_multiplier")
  | Cordered => error (msg "NYI constrained_to_unconstrained: Cordered")
  | Cpositive_ordered => error (msg "NYI constrained_to_unconstrained: Cpositive")
  | Csimplex => error (msg "NYI constrained_to_unconstrained: Csimplex")
  | Cunit_vector => error (msg "NYI constrained_to_unconstrained: Cunit")
  | Ccholesky_corr => error (msg "NYI constrained_to_unconstrained: Ccholesky")
  | Ccholesky_cov => error (msg "NYI constrained_to_unconstrained: Ccholesky")
  | Ccorrelation => error (msg "NYI constrained_to_unconstrained: Ccorrelation")
  | Ccovariance => error (msg "NYI constrained_to_unconstrained: Ccovariance")
  end.

Definition density_of_transformed_var (p:program) (i: AST.ident) (c: constraint): mon (option statement) :=
  let e := Evar i tdouble in
  let t := tdouble in
  match c with
  | Cidentity => ret None
  | Clower _ => do rt_call <~ stan_expit p e; ret (Some (Ssequence (snd rt_call) (Starget (Etempvar (fst rt_call) tdouble))))
  | Cupper _ => do rt_call <~ stan_expit p e; ret (Some (Ssequence (snd rt_call) (Starget (Etempvar (fst rt_call) tdouble))))
  | Clower_upper a b =>
    do rt_call <~ stan_expit p e;
    let rt := fst rt_call in
    let call := snd rt_call in
    do a <~ int2float a;
    do b <~ int2float b;
    do J1 <~ stan_log p (Ebinop Omul (Ebinop Osub b a t) (Etempvar rt tdouble) t);
    do J2 <~ stan_log p (Ebinop Osub (Econst_float float_one t) (Etempvar rt tdouble) t);
    ret
      (Some
        (Ssequence
          call
          (Ssequence (snd J1)
          (Ssequence (snd J2)
          (Starget
            (Ebinop Oadd
              (Etempvar (fst J1) t)
              (Etempvar (fst J2) t)
               t))))))

  | Coffset e => error (msg "NYI constrained_to_unconstrained: Coffset")
  | Cmultiplier e => error (msg "NYI constrained_to_unconstrained: Cmultiplier")
  | Coffset_multiplier e0 e1 => error (msg "NYI constrained_to_unconstrained: Coffset_multiplier")
  | Cordered => error (msg "NYI constrained_to_unconstrained: Cordered")
  | Cpositive_ordered => error (msg "NYI constrained_to_unconstrained: Cpositive")
  | Csimplex => error (msg "NYI constrained_to_unconstrained: Csimplex")
  | Cunit_vector => error (msg "NYI constrained_to_unconstrained: Cunit")
  | Ccholesky_corr => error (msg "NYI constrained_to_unconstrained: Ccholesky")
  | Ccholesky_cov => error (msg "NYI constrained_to_unconstrained: Ccholesky")
  | Ccorrelation => error (msg "NYI constrained_to_unconstrained: Ccorrelation")
  | Ccovariance => error (msg "NYI constrained_to_unconstrained: Ccovariance")
  end.

Fixpoint transf_constraints_expr (pmap: AST.ident -> option AST.ident) (e: CStan.expr) {struct e}: mon CStan.expr :=
  match e with
  | CStan.Econst_int i t => ret (CStan.Econst_int i t)
  | CStan.Econst_float f t => ret (CStan.Econst_float f t)
  | CStan.Econst_single f t => ret (CStan.Econst_single f t)
  | CStan.Econst_long i t => ret (CStan.Econst_long i t)

  (* TODO only works because all params are global right now. *)
  | CStan.Evar i t => 
    match pmap i with
    | None => ret (CStan.Evar i t)
    | Some i => ret (CStan.Etempvar i t)
    end
  | CStan.Etempvar i t => ret (CStan.Etempvar i t)
  | CStan.Ecast e t => do e <~ transf_constraints_expr pmap e; ret (CStan.Ecast e t)
  | CStan.Efield e i t => do e <~ transf_constraints_expr pmap e; ret (CStan.Efield e i t)
  | CStan.Ederef e t => do e <~ transf_constraints_expr pmap e; ret (CStan.Ederef e t) (* a transformation downstream would be invalid*)
  | CStan.Eaddrof e t => do e <~ transf_constraints_expr pmap e; ret (Eaddrof e t)
  | CStan.Eunop uop e t => do e <~ transf_constraints_expr pmap e; ret (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t =>
    do e0 <~ transf_constraints_expr pmap e0;
    do e1 <~ transf_constraints_expr pmap e1;
    ret (CStan.Ebinop bop e0 e1 t)
  | CStan.Esizeof t0 t1 => ret (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => ret (CStan.Ealignof t0 t1)
  | CStan.Etarget ty => ret (CStan.Etarget ty)
end.


Fixpoint transf_constraints_statement (pmap: AST.ident -> option AST.ident) (s: CStan.statement) {struct s}: mon CStan.statement :=
match s with
  | Sassign e0 e1 =>
    do e0 <~ transf_constraints_expr pmap e0;
    do e1 <~ transf_constraints_expr pmap e1;
    ret (Sassign e0 e1)
  | Sset i e => do e <~ transf_constraints_expr pmap e; ret (Sset i e)
  | Scall oi e le =>
    do e <~ transf_constraints_expr pmap e;
    do le <~ mon_mmap (transf_constraints_expr pmap) le;
    ret (Scall oi e le)
  | Sbuiltin oi ef lt le => error (msg "ret (Sbuiltin oi ef lt le)")
  | Ssequence s0 s1 =>
    do s0 <~ transf_constraints_statement pmap s0;
    do s1 <~ transf_constraints_statement pmap s1;
    ret (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>
    do e <~ transf_constraints_expr pmap e;
    do s0 <~ transf_constraints_statement pmap s0;
    do s1 <~ transf_constraints_statement pmap s1;
    ret (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>
    do s0 <~ transf_constraints_statement pmap s0;
    do s1 <~ transf_constraints_statement pmap s1;
    ret (Sloop s0 s1)
  | Sreturn oe => do oe <~ option_mon_mmap (transf_constraints_expr pmap) oe; ret (Sreturn oe)
  | Starget e => do e <~ transf_constraints_expr pmap e; ret (Starget e)
  | Stilde e i le (oe0, oe1) => error (msg "Stilde DNE in this stage of pipeline")
  | Sbreak => ret Sbreak
  | Sskip => ret Sskip
  | Scontinue => ret Scontinue
end.

Fixpoint sequence (xs : list statement) : option statement :=
  match xs with
  | nil => None
  | h::tail =>
    (* lookahead *)
    match sequence tail with
    | None => Some h
    | Some n => Some (Ssequence h n)
    end
  end.

(* Denumpyification.ident_eq_dec *)
Definition ident_eq_dec : forall (x y : AST.ident), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.

Fixpoint catMaybes {X : Type} (xs : list (option X)) : list X :=
  match xs with
  | nil => nil
  | (Some x)::xs => x::(catMaybes xs)
  | None::xs => catMaybes xs
  end.

Definition map_globdef {X} {Y} (f : X -> Y) (gty: AST.globdef CStan.fundef X) : option Y :=
  match gty with
  | AST.Gfun _ => None
  | AST.Gvar t => Some (f t.(AST.gvar_info))
  end.

Definition globdef_to_type : AST.globdef CStan.fundef type -> option type :=
  map_globdef id.

Fixpoint ident_list_member (xs:list AST.ident) (x:AST.ident) : bool :=
  match xs with
  | nil => false
  | x'::xs => if ident_eq_dec x x' then true else ident_list_member xs x
  end.

Definition filter_globvars (all_defs : list (AST.ident*AST.globdef CStan.fundef type)) (vars : list AST.ident) : list (AST.ident*type) :=
  let maybe_member := fun tpl => option_map (fun ty => (fst tpl, ty)) (globdef_to_type (snd tpl)) in
  let all_members := catMaybes (List.map maybe_member all_defs) in
  let stan_members := List.filter (fun tpl => ident_list_member vars (fst tpl)) all_members in
  stan_members.

Definition transform_with_original_ident (transform : program -> AST.ident -> constraint -> mon (option (AST.ident * statement))) (p:program) (i_ty : AST.ident * constraint) : mon (option (AST.ident * (AST.ident * statement))) :=
  do mtpl <~ transform p (fst i_ty) (snd i_ty);
  ret (option_fmap (fun tpl => (fst i_ty, tpl)) mtpl).

Definition parameter_transformed_map (ts : list (AST.ident * AST.ident)) (i : AST.ident) : option AST.ident :=
  option_fmap snd (List.find (fun lr => ident_eq_dec i (fst lr)) ts).

Definition transf_statement (p:program) (body : statement): mon statement :=

    (* let params_typed := filter_globvars (p.(prog_defs)) (p.(prog_parameters_vars)) in (*: list (AST.ident*CStan.type)*) *)
    let params_typed := (p.(prog_parameters_vars)) in (*: list (AST.ident*CStan.type)*)
    do params_transformed <~ mon_fmap catMaybes (mon_mmap (transform_with_original_ident inv_constraint_transform p) p.(prog_constraints));
    let params_map  := List.map (fun fr_to => (fst fr_to, fst (snd fr_to))) params_transformed in
    let params_stmts := List.map (fun fr_to => snd (snd fr_to)) params_transformed in

    do target_additions <~ mon_fmap catMaybes ((mon_mmap (fun i_ty => density_of_transformed_var p (fst i_ty) (snd i_ty)) p.(prog_constraints)));
    match sequence params_stmts with
    | None => ret body
    | Some params =>
      match sequence target_additions with
      | None => error (msg "FIXME: impossible, should reorganize this branch")
      | Some stgts =>
        do body <~ transf_constraints_statement (parameter_transformed_map params_map) body;
        ret (Ssequence params (Ssequence stgts body))
      end
    end.
(*
Definition transf_statement_pipeline (p:program) : mon CStan.statement :=
  let body := f.(fn_body) in
  do body <~ transf_constraints p  body;           (* apply constraint transformations *)
  ret body.*)

Definition transf_function (p:CStan.program) (f: function): res function :=
  match transf_statement p f.(fn_body) f.(fn_generator) with
  | SimplExpr.Err msg => Error msg
  | SimplExpr.Res tbody g i =>
    OK {|
      fn_params := f.(fn_params);
      fn_body := tbody;

      fn_temps := g.(SimplExpr.gen_trail) ++ f.(fn_temps);
      (* fn_temps := f.(fn_temps); (* NOTE only extract in the last stage *) *)
      fn_vars := f.(fn_vars);
      fn_generator := g;

      (*should not change*)
      fn_return := f.(fn_return);
      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
     |}
  end.

Definition transf_program := CStan.transf_program (transf_function). 

