open Sparser.MenhirLibParser.Inter
open List
open C2C
open Lexing
open Sparser
open Smessages
open Int32
open Sstanlib

exception Internal of string
exception NIY_elab of string
exception Unsupported of string
exception TypeError of string

let type_table = Hashtbl.create 123456;;
Hashtbl.add type_table "target" Stanlight.Breal

module IdxTable =
  struct
    type t = BinNums.positive
    let equal i j = i=j
    let hash = Hashtbl.hash
  end

module IdxHashtbl = Hashtbl.Make(IdxTable)
let index_set = IdxHashtbl.create 123456;;
                 
let mapo o f =
  match o with
  | None -> None
  | Some o -> Some (f o)

let filter_b_op o =
  match o with
  | Stan.Plus -> Stanlight.Plus
  | Stan.Minus -> Stanlight.Minus
  | Stan.Times -> Stanlight.Times
  | Stan.Divide -> Stanlight.Divide
  | Stan.Modulo -> Stanlight.Modulo
  | Stan.Or -> Stanlight.Or
  | Stan.And -> Stanlight.And
  | Stan.Equals -> Stanlight.Equals
  | Stan.NEquals -> Stanlight.NEquals
  | Stan.Less -> Stanlight.Less
  | Stan.Leq -> Stanlight.Leq
  | Stan.Greater -> Stanlight.Greater
  | Stan.Geq -> Stanlight.Geq
  | Stan.IntDivide -> raise (Unsupported "binary operator: integer division")
  | Stan.LDivide -> raise (Unsupported "binary operator: L divide?")
  | Stan.EltTimes -> raise (Unsupported "binary operator: pointwise times")
  | Stan.EltDivide -> raise (Unsupported "binary operator: pointwise divide")
  | Stan.Pow -> raise (Unsupported "binary operator: power")
  | Stan.EltPow -> raise (Unsupported "binary operator: pointwise power")
  | Stan.Transpose -> raise (Unsupported "binary operator: transpose")
  | _ -> raise (Internal "unary operator in binary position")                   

let typeof e  =
  match e with
  | Stanlight.Econst_int (_, ty) -> ty
  | Stanlight.Econst_float (_, ty) -> ty
  | Stanlight.Evar (_, ty) -> ty
  | Stanlight.Ecall (_,_,ty) -> ty
  | Stanlight.Eunop (_, ty) -> ty
  | Stanlight.Ebinop (_, _, _, ty) -> ty
  | Stanlight.Eindexed (_, _, ty) -> ty
  | Stanlight.Etarget ty -> ty

let op_to_string o =
  match o with
  | Stanlight.Plus -> " + "
  | Stanlight.Minus -> " - "
  | Stanlight.Times -> " * "
  | Stanlight.Divide -> " / "
  | Stanlight.Modulo -> " % "
  | Stanlight.Or -> " || "
  | Stanlight.And -> " && "
  | Stanlight.Equals -> " == "
  | Stanlight.NEquals -> " != "
  | Stanlight.Less -> " < "
  | Stanlight.Leq -> " <= "
  | Stanlight.Greater -> " > "
  | Stanlight.Geq -> " >= "

let rec make_exprlist el =
  match el with
  | [] -> Stanlight.Enil
  | e :: l -> Stanlight.Econs (e, make_exprlist l)
               
let rec el_e e =
  match e with
  | Stan.Econst_int i -> Stanlight.Econst_int (Camlcoq.Z.of_sint (int_of_string i), Stanlight.Bint)
  | Stan.Econst_float f -> Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat (float_of_string f), Stanlight.Breal)
  | Stan.Evar i ->
    begin match Hashtbl.find_opt type_table i with
    | None -> raise (Internal ("Variable of unknown type " ^ i)) (* Stanlight.Evar (Camlcoq.intern_string i, Stanlight.Breal) *)
    | Some (Stanlight.Bfunction (_, _)) -> raise (Internal "Something to think about carefully")
    | Some ty -> Stanlight.Evar (Camlcoq.intern_string i, ty)
    end
  | Stan.Eunop (o,e) ->
     begin
       match o with
       | Stan.PNot -> raise (Internal "confused")(* Stanlight.Eunop (Stanlight.PNot, el_e e) *)
       | Stan.PPlus ->
          let e = el_e e in
          let ty = typeof e in
          begin
            match ty with
            | Stanlight.Bint -> Stanlight.Ebinop (Stanlight.Econst_int (Camlcoq.Z.of_sint 0, Stanlight.Bint),Stanlight.Plus,e,ty) 
            | Stanlight.Breal -> Stanlight.Ebinop (Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 0.0, Stanlight.Breal),Stanlight.Plus,e,ty) 
            | _ -> raise (TypeError "Unop PPlus")
          end
       | Stan.PMinus ->
          let e = el_e e in
          let ty = typeof e in
          begin
            match ty with
            | Stanlight.Bint -> Stanlight.Ebinop (Stanlight.Econst_int (Camlcoq.Z.of_sint 0, Stanlight.Bint),Stanlight.Minus,e,ty) 
            | Stanlight.Breal -> Stanlight.Ebinop (Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 0.0, Stanlight.Breal),Stanlight.Minus,e,ty) 
            | _ -> raise (TypeError "Unop PPlus")
          end
       | _ -> raise (Internal "binary operator used in unary position")
     end
  | Stan.Ebinop (e1,o,e2) ->
     (* Needs to be seriously improved to account for the operator!!! *)
     let e1 = el_e e1 in
     let e2 = el_e e2 in
     let t1 = typeof e1 in
     let t2 = typeof e2 in
     let o = filter_b_op o in
     let t =
       begin 
         match t1, t2 with
         | Stanlight.Bint, Stanlight.Bint -> Stanlight.Bint
         | Stanlight.Breal, Stanlight.Breal -> Stanlight.Breal
         | Stanlight.Breal, Stanlight.Bint -> raise (Unsupported ("Casting 1" ^ (op_to_string o)))
         | Stanlight.Bint, Stanlight.Breal -> raise (Unsupported ("Casting 2" ^ (op_to_string o)))
         | _, _ -> raise (TypeError "Type error: operator applied to array")
       end in
     Stanlight.Ebinop (e1,o,e2,t) 
  | Stan.Ecall (i,el) ->
     let (_,ty) = type_of_library_function i in
     let e = Stanlight.Evar (Camlcoq.intern_string i, ty) in
     let el = List.map el_e el in
     Stanlight.Ecall (e,make_exprlist el,Stanlight.Breal)
  | Stan.Econdition (e1,e2,e3) -> raise (Unsupported "expression: conditional")
  | Stan.Earray el -> raise (Unsupported "expression: array")
  | Stan.Erow el -> raise (Unsupported "expression: row")
  | Stan.Eindexed (e,il) ->
     let e = el_e e in
     let t = typeof e in
     let il = List.map el_i il in
     let index_are_all_ints = List.fold_left (fun b e -> b && typeof(e) == Stanlight.Bint) true il in
     begin
       match il, t, index_are_all_ints with
       | [], _, _ -> raise (TypeError "Type error: indexing with no indices")
       | _, _, false -> raise (TypeError "Type error: indices must be integers")
       | _ , Stanlight.Barray (it,_), _ -> Stanlight.Eindexed (e, make_exprlist il, it)
       | _, _, _ -> raise (TypeError "Type error: indexing can only be applied to arrays")
     end
  | Stan.Edist (i,el) -> raise (Unsupported "expression: distribution")
  | Stan.Etarget -> Stanlight.Etarget Stanlight.Breal

and el_i i =
  match i with
  | Stan.Iall -> raise (Unsupported "No support for advanced indexing")
  | Stan.Isingle e -> el_e e
  | Stan.Iupfrom e -> raise (Unsupported "No support for advanced indexing")
  | Stan.Idownfrom e -> raise (Unsupported "No support for advanced indexing")
  | Stan.Ibetween (e1,e2) -> raise (Unsupported "No support for advanced indexing")

let rec eval_e_aux e =
  match e with
  | Stan.Econst_int i -> (float_of_string i)
  | Stan.Econst_float f -> (float_of_string f)
  | Stan.Eunop (Stan.PMinus,e) -> -. (eval_e_aux e)
  | Stan.Eunop _ -> raise (Unsupported "Complex constant expression: unop")
  | Stan.Ebinop _ -> raise (Unsupported "Complex constant expression: binop")
  | Stan.Evar i -> raise (Unsupported "Complex constant expression: var")
  | Stan.Ecall (i,el) -> raise (Unsupported "Complex constant expression: call")
  | Stan.Econdition (e1,e2,e3) -> raise (Unsupported "Complex constant expression: condition")
  | Stan.Earray el -> raise (Unsupported "Complex constant expression: array")
  | Stan.Erow el -> raise (Unsupported "Complex constant expression: row")
  | Stan.Eindexed (e,il) -> raise (Unsupported "Complex constant expression: indexing")
  | Stan.Edist (i,el) -> raise (Unsupported "Complex constant expression: distribution")
  | Stan.Etarget -> raise (Unsupported "Complex constant expression: target")

let eval_e e = Camlcoq.coqfloat_of_camlfloat (eval_e_aux e)
                           
let el_p p =
  match p with
  | Stan.Pstring s -> raise (Unsupported "Printing")
  | Stan.Pexpr e -> raise (Unsupported "Printing")

let coqZ_of_string s =
  Integers.Int.intval (Camlcoq.coqint_of_camlint (of_int (int_of_string s)))                          
                  
let el_b b dims =
  match (b, dims) with
  | (Stan.Bint,  []) -> Stanlight.Bint
  | (Stan.Breal, []) -> Stanlight.Breal
  | (Stan.Bint,  [Stan.Econst_int i]) -> Stanlight.Barray (Stanlight.Bint,(coqZ_of_string i)) 
  | (Stan.Breal, [Stan.Econst_int i]) -> Stanlight.Barray (Stanlight.Breal,(coqZ_of_string i))
  | (Stan.Breal, _ ) -> raise (NIY_elab "compositive real")
  | (Stan.Bint, _ ) -> raise (NIY_elab "compositive int")        
  | (Stan.Bvector _, _) -> raise (Unsupported "vector type")
  | (Stan.Bmatrix _, _) -> raise (Unsupported "matrix type")
  | (Stan.Brow _, _) -> raise (Unsupported "matrix type")    


(* John: the following code can be removed if we set the index_table *)
let rec el_s_ids s =
  match s with
  | Stan.Sskip -> []
  | Stan.Sassign (e1,oo,e2) -> []
  | Stan.Sblock sl -> List.fold_left (fun s1 s2 -> s1 @ (el_s_ids s2)) [] sl
  | Stan.Sifthenelse (e,s1,s2) -> []
  | Stan.Swhile (e,s) -> raise (Unsupported "statement: while")
  | Stan.Sfor (i,e1,e2,s) -> el_s_ids s
  | Stan.Sbreak -> raise (Unsupported "statement: break")
  | Stan.Scontinue -> raise (Unsupported "statement: continue")
  | Stan.Sreturn oe -> raise (Unsupported "statement: return")
  | Stan.Svar v ->
     let id = Camlcoq.intern_string v.Stan.vd_id in
     let t = el_b v.Stan.vd_type v.Stan.vd_dims in
     Hashtbl.add type_table v.Stan.vd_id t;
     [(id,t)]
  | Stan.Scall (i,el) -> raise (Unsupported "statement: call")
  | Stan.Sprint lp -> raise (Unsupported "statement: print")
  | Stan.Sreject lp -> raise (Unsupported "statement: reject")
  | Stan.Sforeach (i,e,s) -> raise (Unsupported "statement: foreach")
  | Stan.Starget e -> []
  | Stan.Stilde (e,i,el,(None,None)) -> []
  | Stan.Stilde (e,i,el,(tr1,tr2)) -> raise (Unsupported "truncation")
                  
let rec el_s s =
  match s with
  | Stan.Sskip -> Stanlight.Sskip
  | Stan.Sassign (e1,oo,e2) -> Stanlight.Sassign (el_e e1, mapo oo filter_b_op, el_e e2)
  | Stan.Sblock sl -> List.fold_left (fun s1 s2 -> Stanlight.Ssequence (s1, (el_s s2))) Stanlight.Sskip sl
  | Stan.Sifthenelse (e,s1,s2) -> Stanlight.Sifthenelse (el_e e, el_s s1, el_s s2)
  | Stan.Swhile (e,s) -> raise (Unsupported "statement: while")
  | Stan.Sfor (i,e1,e2,s) ->
     let isym = Camlcoq.intern_string i in
     IdxHashtbl.add index_set isym ();
     Hashtbl.add type_table i Stanlight.Bint;
     Stanlight.Sfor (isym, el_e e1, el_e e2, el_s s)
  | Stan.Sbreak -> raise (Unsupported "statement: break")
  | Stan.Scontinue -> raise (Unsupported "statement: continue")
  | Stan.Sreturn oe -> raise (Unsupported "statement: return")
  | Stan.Svar v -> Stanlight.Sskip     
  | Stan.Scall (i,el) -> raise (Unsupported "statement: call")
  | Stan.Sprint lp -> raise (Unsupported "statement: print")
  | Stan.Sreject lp -> raise (Unsupported "statement: reject")
  | Stan.Sforeach (i,e,s) ->raise (Unsupported "statement: foreach")
  | Stan.Starget e -> Stanlight.Starget (el_e e)
  | Stan.Stilde (e,i,el,(None,None)) ->
     let (_id,_ty) = type_of_library_function i in
     (*
    let (_i, _ty) = match Hashtbl.find_opt transf_dist_idents i with
      | Some (ident, ty) -> (ident, ty)
      | None -> raise (NIY_elab ("tilde called with invalid distribution: "^ i))*)
    Stanlight.Stilde (el_e e, Stanlight.Evar (Camlcoq.intern_string _id, _ty), make_exprlist(map el_e el))
  | Stan.Stilde (e,i,el,(tr1,tr2)) -> raise (Unsupported "truncation")

let elab elab_fun ol =
  match ol with
  | None -> None
  | Some l -> Some (List.map elab_fun l)

let g_init_int_zero =
  AST.Init_int32 (Integers.Int.repr (Camlcoq.coqint_of_camlint 0l))
let g_init_double_zero =
  AST.Init_float64 (Floats.Float.of_bits (Integers.Int64.repr (Camlcoq.coqint_of_camlint 0l)))

let g_init_space sz =
  AST.Init_space (Camlcoq.coqint_of_camlint (Int32.of_int sz))
let g_init_uninit_array l sz =
  g_init_space ((int_of_string l) * sz)

let transf_v_init v dims =
  match (v, dims) with
  | (Stan.Bint,  []) -> [g_init_space 4]
  | (Stan.Bint, [Stan.Econst_int l]) -> [g_init_uninit_array l 4]
  | (Stan.Breal, []) -> [g_init_space 8]
  | (Stan.Breal, [Stan.Econst_int l]) -> [g_init_uninit_array l 8]
  | _ -> []
let str_to_coqint s =
  (Camlcoq.coqint_of_camlint (of_int (int_of_string s)))

let stype2basic s =
  match s with
  | Stan.Tint -> Stanlight.Bint
  | Stan.Treal -> Stanlight.Breal
  | _ -> raise (NIY_elab "stype2basic: do not call stype2basic on complex data representations")

let el_c c =
  match c with
  | Stan.Cidentity -> Stanlight.Cidentity
  | Stan.Clower e ->
     let b = eval_e e in
     Stanlight.Clower b
  | Stan.Cupper e ->
     let b = eval_e e in
     Stanlight.Cupper b
  | Stan.Clower_upper (l, u) ->
     let b1 = eval_e l in
     let b2 = eval_e u in
     Stanlight.Clower_upper (b1,b2)
  | Stan.Coffset e -> raise (Unsupported "constraint:offset")
  | Stan.Cmultiplier e -> raise (Unsupported "constraint:multiplier")
  | Stan.Coffset_multiplier (l, u) -> raise (Unsupported "constraint:offset_multiplier")
  | Stan.Cordered -> raise (Unsupported "constraint:ordered")
  | Stan.Cpositive_ordered -> raise (Unsupported "constraint:positive_ordered")
  | Stan.Csimplex -> raise (Unsupported "constraint:simplex")
  | Stan.Cunit_vector -> raise (Unsupported "constraint:unit_vector")
  | Stan.Ccholesky_corr -> raise (Unsupported "constraint:cholesky_corr")
  | Stan.Ccholesky_cov -> raise (Unsupported "constraint:cholesky_cov")
  | Stan.Ccorrelation -> raise (Unsupported "constraint:correlation")
  | Stan.Ccovariance -> raise (Unsupported "constraint:covariance")

let mkLocal v =
  let id = Camlcoq.intern_string v.Stan.vd_id in
  Hashtbl.add decl_atom id
    { a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_data Sections.Uninit];
      a_access = Sections.Access_default;
      a_inline = No_specifier;
      a_loc = (v.Stan.vd_id,0) };
  let basic = el_b v.Stan.vd_type v.Stan.vd_dims in
  Hashtbl.add type_table v.Stan.vd_id basic;
  (v, id, basic)

let mkVariableFromLocal (v, id, basic) =
  let vd = {
    Stanlight.vd_type = basic;
    Stanlight.vd_constraint = el_c(v.Stan.vd_constraint);
  } in
  (id,  AST.Gvar { AST.gvar_info = vd; gvar_init = transf_v_init v.Stan.vd_type v.Stan.vd_dims;
                   gvar_readonly = false; gvar_volatile = false})

let mkVariable v = mkVariableFromLocal (mkLocal v)
let declareVariable = mkVariable

let mkFunction name body rt params extraVars extraTemps =
  let id = Camlcoq.intern_string name in
  Hashtbl.add C2C.decl_atom id {
    a_storage = C.Storage_default;
    a_alignment = None;
    a_size = None;
    a_sections = [Sections.Section_text;Sections.Section_literal;Sections.Section_jumptable];
    a_access = Sections.Access_default;
    a_inline = Noinline;
    a_loc = (name,0) };
  let local_identifiers = List.fold_left (fun s1 s2 -> s1 @ (el_s_ids s2)) [] body in
  let body = List.fold_left (fun s1 s2 -> Stanlight.Ssequence (s1, (el_s s2))) Stanlight.Sskip body in
  
  let fd = {
    Stanlight.fn_vars = List.concat [extraVars @ local_identifiers; (IdxHashtbl.fold (fun k v acc -> (k,Stanlight.Bint)::acc) index_set [])];
    Stanlight.fn_body = body} in
  (id,  AST.Gfun(Ctypes.Internal fd))

let declareFundef name body rt params =
  mkFunction name body rt params [] []

let mapMaybe fn mval =
  match mval with
  | None -> None
  | Some v -> Some (fn v)

let fromMaybe default mval =
  match mval with
  | None -> default
  | Some v -> v

let maybe default fn mval =
  fromMaybe default (mapMaybe fn mval)

let sparam2stanEparam ((ad, ty), v) = ((ad, stype2basic ty), v)

let elaborate (sourcefile : string) (p: Stan.program) =
  match p with
    { Stan.pr_functions=f;
      Stan.pr_data=d;
      Stan.pr_transformed_data=td;
      Stan.pr_parameters=p;
      Stan.pr_transformed_parameters=tp;
      Stan.pr_model=m;
      Stan.pr_generated=g;
    } ->
    let get_code x = fromMaybe [Stan.Sskip] x in
    let unop x = fromMaybe [] x in

    let data_basics = List.map mkLocal (unop d) in
    let data_variables = List.map mkVariableFromLocal data_basics in
    let data_fields = List.map (fun tpl -> match tpl with (_, l, r) -> (l, r)) data_basics in

    let param_basics = List.map mkLocal (unop p) in
    let param_variables = List.map mkVariableFromLocal param_basics in
    let param_fields = List.map (fun tpl -> match tpl with (_, l, r) -> (l, r)) param_basics in

    let functions = [] in

    let _ = Camlcoq.intern_string "target" in
    let (id_model,f_model) =
      mkFunction "model" ((get_code td) @ (get_code tp) @ (get_code m)) (Some Stanlight.Breal) [] [] [] in 
    
    let functions = (id_model,f_model) :: functions in
 
    let functions =
      List.fold_left
        (fun acc -> fun ff -> (declareFundef ff.Stan.fn_name [ff.Stan.fn_body]
                                 (mapMaybe stype2basic ff.Stan.fn_return)
                                 (List.map sparam2stanEparam ff.Stan.fn_params)) :: acc)
        functions (unop f) in

    let gl1 = C2C.convertGlobdecls Env.empty [] (Env.initial_declarations()) in
    let _ = C2C.globals_for_strings gl1 in


    let _ =  Camlcoq.intern_string "Params" in
    let _ = Camlcoq.intern_string "Data" in
    let _ = Camlcoq.intern_string "__p__" in
    let _ = Camlcoq.intern_string "__d__" in

    let helpers = add_helper_functions [] in
    let all_math_fns = declare_library () in
    
    {
      Stanlight.pr_defs=  helpers @ data_variables @ param_variables @ functions @ all_math_fns;
      Stanlight.pr_data_vars=data_fields;
      Stanlight.pr_parameters_vars=param_fields;
    }

let location t =
  match t with
  (* These four tokens have a payload we ignore *)
  | STRINGLITERAL sp | REALNUMERAL sp | INTNUMERAL sp | IDENTIFIER sp -> snd sp
  (* All of the following tokens have no payload, just a position *)
  | WHILE p | VOID p | VECTOR p | UPPER p | UNITVECTOR p | TRUNCATE p 
  | TRANSPOSE p | TRANSFORMEDPARAMETERSBLOCK p | TRANSFORMEDDATABLOCK p 
  | TIMESASSIGN p | TIMES p | TILDE p | TARGET p | SIMPLEX p | SEMICOLON p 
  | RPAREN p | ROWVECTOR p | RETURN p | REJECT p | REAL p | RBRACK p 
  | RBRACE p | RABRACK p | QMARK p | PRINT p | POSITIVEORDERED p | PLUSASSIGN p 
  | PLUS p | PARAMETERSBLOCK p | ORDERED p | OR p | OFFSET p | NEQUALS p 
  | MULTIPLIER p | MODULO p | MODELBLOCK p | MINUSASSIGN p | MINUS p | MATRIX p 
  | LPAREN p | LOWER p | LEQ p | LDIVIDE p | LBRACK p | LBRACE p | LABRACK p 
  | INT p | IN p | IF_ p | IDIVIDE p | HAT p | GEQ p | GENERATEDQUANTITIESBLOCK p 
  | FUNCTIONBLOCK p | FOR p | EQUALS p | EOF p | ELTTIMESASSIGN p | ELTTIMES p 
  | ELTPOW p | ELTDIVIDEASSIGN p | ELTDIVIDE p | ELSE p | DIVIDEASSIGN p 
  | DIVIDE p | DATABLOCK p | COVMATRIX p | CORRMATRIX p | CONTINUE p | COMMA p 
  | COLON p | CHOLESKYFACTORCOV p | CHOLESKYFACTORCORR p | BREAK p | BAR p 
  | BANG p | ASSIGN p | AND p ->   
    p 

let state_num s =
  let coq_num = Sparser.Aut.coq_N_of_state s in
  let state = Camlcoq.N.to_int coq_num
  in 
  state

let handle_syntax_error file state token =
  let (pos1, pos2) as positions = location token in
  let line = pos2.pos_lnum in
  let st_num = state_num state in
  let col_start = let {pos_cnum;pos_bol} = pos1 in 1 + pos_cnum - pos_bol in
  let col_end = let {pos_cnum;pos_bol} = pos2 in 1 + pos_cnum - pos_bol in
  let msg = try message st_num with
    | Not_found -> "Unknown error in parser state " ^ string_of_int st_num
  in
  Printf.eprintf  "Syntax error in '%s', line %d, characters %d-%d:\n%s" file line col_start col_end msg;
  exit 1

let read_file sourcefile =
  let ic = open_in_bin sourcefile in
  let n = in_channel_length ic in
  let text = really_input_string ic n in
  close_in ic;
  text

let tokens_stream text: buffer =
  let lexbuf = Lexing.from_string text in
  let rec compute_buffer () =
    let loop t = Buf_cons (t, Lazy.from_fun compute_buffer) in
    loop (Slexer.token lexbuf)
  in
  Lazy.from_fun compute_buffer
  
let parse_stan_file sourcefile ifile =
  Hashtbl.clear C2C.decl_atom;
  Hashtbl.clear C2C.stringTable;
  Hashtbl.clear C2C.wstringTable;
  Camlcoq.use_canonical_atoms := true;

  let text = read_file sourcefile in
  let log_fuel = Camlcoq.Nat.of_int 50 in
  let p = match Sparser.program log_fuel (tokens_stream text) with
    | Sparser.MenhirLibParser.Inter.Fail_pr_full (state, token) -> handle_syntax_error sourcefile state token
    | Sparser.MenhirLibParser.Inter.Timeout_pr -> assert false
    | Sparser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) -> elaborate sourcefile ast in
  p
