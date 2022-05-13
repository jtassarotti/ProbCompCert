(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Stan.
Require Import SimplExpr.

Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)       (*FIXME: I think we can remove this *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *) (*FIXME: I think we can remove this *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Ecast: expr -> type -> expr           (**r type cast ([(ty) e]) *)
  | Efield: expr -> ident -> type -> expr (**r access to a member of a struct or union *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr        (**r alignment of a type *)
  | Etarget: type -> expr.

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Econst_single _ ty => ty
  | Econst_long _ ty => ty
  | Evar _ ty => ty
  | Etempvar _ ty => ty
  | Ederef _ ty => ty
  | Eaddrof _ ty => ty
  | Ecast _ ty => ty
  | Efield _ _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Esizeof _ ty => ty
  | Ealignof _ ty => ty
  | Etarget ty => ty
  end.

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Starget: expr -> statement              (**r target += expr *)
  | Stilde: expr -> expr -> list expr -> (option expr * option expr) -> statement
                      (**r expr ~ expr(list expr) T[option exr, option expr] *)

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

Definition Swhile (e: expr) (s: statement) :=
  Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

Definition Sfor
  (s1: statement) (* initializing statement *)
  (e2: expr) (* conditional *)
  (s3: statement) (* body *)
  (s4: statement) (* postprocessing statement *)
  := Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).

Inductive constraint :=
  | Cidentity
  | Clower: expr -> constraint
  | Cupper: expr -> constraint
  | Clower_upper: expr -> expr -> constraint
  | Coffset: expr -> constraint
  | Cmultiplier: expr -> constraint
  | Coffset_multiplier: expr -> expr -> constraint
  | Cordered
  | Cpositive_ordered
  | Csimplex
  | Cunit_vector
  | Ccholesky_corr
  | Ccholesky_cov
  | Ccorrelation
  | Ccovariance.

Inductive blocktype
  := BTModel
  | BTParameters
  | BTData
  | BTGetState | BTSetState
  | BTPropose
  | BTPrintState | BTPrintData | BTSetData
  | BTOther.

Record function := mkfunction {
  fn_return: Ctypes.type;
  fn_params: list (ident * Ctypes.type);
  fn_body: statement;
  fn_blocktype: blocktype;
  fn_generator: SimplExpr.generator;
  fn_callconv: calling_convention;
  fn_temps: list (ident * Ctypes.type);
  fn_vars: list (ident * Ctypes.type);
}.

Definition var_names (vars: list(ident * Ctypes.type)) : list ident :=
  List.map (@fst ident Ctypes.type) vars.

Definition fundef := Ctypes.fundef function.

Definition type_of_function (f: function) : Ctypes.type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : Ctypes.type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

Inductive math_func := MFLog | MFExp | MFLogit | MFExpit | MFSqrt
                       | MFPrintStart
                       | MFPrintDouble
                       | MFPrintInt
                       | MFPrintArrayInt
                       | MFPrintEnd
                       | MFInitUnconstrained.
Definition math_func_eq_dec : forall (x y : math_func), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.

Inductive dist_func := DBernPMF | DUnifPDF.
Definition dist_func_eq_dec : forall (x y : dist_func), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.

Record reserved_params := mkreserved_params {
  res_params_type: AST.ident;
  res_params_global_state: AST.ident;
  res_params_global_proposal: AST.ident;
  res_params_arg: AST.ident; (* arguments may not be in the temp list and, therefore, cannot be trivially added through gensym *)
  res_params_tmp: AST.ident; (* Cshmgen will not allow us to use temp idents for compond_env lookups *)
}.
Record reserved_data := mkreserved_data {
  res_data_type: AST.ident;
  res_data_global: AST.ident;
  res_data_arg: AST.ident; (* arguments may not be in the temp list and, therefore, cannot be trivially added through gensym *)
  res_data_tmp: AST.ident; (* Cshmgen will not allow us to use temp idents for compond_env lookups *)
}.

Record program : Type := {
  prog_defs: list (ident * globdef fundef type);
  prog_public: list ident;
  prog_main: ident;
  prog_model: ident;
  prog_target: ident;
  prog_constraints: list (ident * constraint);
  prog_parameters_vars: list (ident * type);
  prog_parameters_struct: reserved_params;
  prog_data_vars: list (ident * type);
  prog_data_struct: reserved_data;
  prog_types: list composite_definition;
  prog_comp_env: composite_env;
  prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env;
  prog_math_functions: list (math_func * ident * Ctypes.type);
  prog_dist_functions: list (dist_func * ident);
}.

Definition program_of_program (p: program) : AST.program fundef type :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.

Definition globalenv (p: program) :=
  {| genv_genv := Genv.globalenv p; genv_cenv := p.(prog_comp_env) |}.

Definition env := PTree.t (block * Ctypes.type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * Ctypes.type)).

(** The temporary environment maps local temporaries to values. *)

Definition temp_env := PTree.t val.

(** [deref_loc ty m b ofs bf v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs],
  and bitfield designation [bf].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)

Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) :
                                             bitfield -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs Full v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_bitfield: forall sz sg pos width v,
      load_bitfield ty sz sg pos width m (Vptr b ofs) v ->
      deref_loc ty m b ofs (Bits sz sg pos width) v.

Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
                                            bitfield -> val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs Full v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs Full (Vptr b' ofs') m'
  | assign_loc_bitfield: forall sz sg pos width v m' v',
      store_bitfield ty sz sg pos width m (Vptr b ofs) v m' v' ->
      assign_loc ce ty m b ofs (Bits sz sg pos width) v m'.

Notation "'do' X <~ A ; B" := (SimplExpr.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Local Open Scope gensym_monad_scope.

Fixpoint map_transf_statement (m: program -> statement -> mon statement) (p: program) (s: statement) {struct s}: mon statement :=
  match s with
  | Ssequence s0 s1 =>
    do s0 <- map_transf_statement m p s0;
    do s1 <~ map_transf_statement m p s1;
    m p (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>
    do s0 <- map_transf_statement m p s0;
    do s1 <- map_transf_statement m p s1;
    m p (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>
    do s0 <- map_transf_statement m p s0;
    do s1 <- map_transf_statement m p s1;
    m p (Sloop s0 s1)
  | _ => m p s
  end.



Section Util.
Require Import Errors.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Variable transf_statement: program -> statement -> mon statement. 

Definition transf_function_basic (p:CStan.program) (f: function): res (function) :=
  match transf_statement p f.(fn_body) f.(fn_generator) with
  | SimplExpr.Err msg => Error msg
  | SimplExpr.Res tbody g i =>
    OK {|
      fn_params := f.(fn_params);
      fn_body := tbody;

      fn_temps := g.(SimplExpr.gen_trail) ++ f.(fn_temps);
      fn_vars := f.(fn_vars);
      fn_generator := g;

      fn_return := f.(fn_return);
      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
     |}
  end.

Variable transf_function: program -> function -> res function.

Definition transf_external (ef: AST.external_function) : res AST.external_function :=
  match ef with
  | AST.EF_external n sig => OK (AST.EF_external n sig) (*link to blas ops?*)
  | AST.EF_runtime n sig => OK (AST.EF_runtime n sig) (*link runtime?*)
  | _ => OK ef
  end.

Definition transf_fundef (p:CStan.program) (id: AST.ident) (fd: CStan.fundef) : res CStan.fundef :=
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

End Util. 

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


