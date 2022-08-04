exception NIY_propose of string

let generate_prologue () =
  String.concat "\n" [
      "void propose (struct Params* state, struct Params* candidate) {";
      "  double eps;";
      ""
    ]

let generate_epilogue () =
  String.concat "\n" [
      "}";
      ""
    ]

let generate_param (id, t) =
  let name = Camlcoq.extern_atom id in
  match t with
  | Stanlight.Breal -> String.concat "\n" [
                   "  eps = randn(0.0,1.0);";
                   "  candidate->" ^ name ^" = state->" ^ name ^" + eps;";
                     ]
  | Stanlight.Barray (Stanlight.Breal,sz) -> String.concat "\n" [
                                         "  for (int i = 0; i < " ^ (Camlcoq.Z.to_string sz) ^ " ; i++) {";
                                         "    eps = randn(0.0,1.0);";
                                         "    candidate->" ^ name ^ "[i]" ^ " = state->" ^ name ^ "[i]" ^" + eps;";
                                         "  }";
                                       ]
  | _ -> raise (NIY_propose "Not handling non-real types yet")

(*functions for converting op, basic, expression, statement types to string*)
let string_op b_op =
  match b_op with
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

(*
let rec string_uop uop =
  match uop with
  | Stanlight.PNot -> " ! "
  | _ -> ""
what do you mean PNot is unbound???*)

let rec string_basic bas =
  match bas with
  | Stanlight.Bint -> "int"
  | Stanlight.Breal -> "real"
  | Stanlight.Barray (basic, intgr) -> (string_basic basic) ^ "[" ^ Camlcoq.Z.to_string intgr ^ "]"
  | Stanlight.Bfunction (basiclist, basic) -> "inputs -> " ^ (string_basic basic)

(*uniform_lpdf and bernoulli_lpdf are both variables???*)
let rec string_expression expr =
  match expr with
  | Stanlight.Econst_int (intgr, bas) -> Camlcoq.Z.to_string intgr
  | Stanlight.Econst_float (flt, bas) -> "float" (*how to convert float to string??*)
  | Stanlight.Evar (ident, bas) -> "Var " ^ Camlcoq.extern_atom ident
  | Stanlight.Ecall (expr1, exprl, bas) -> String.concat "" ["Call "; string_expression expr1; "("; string_exprlist exprl; ")"]
  | Stanlight.Eunop (expr1, bas) -> "U_op !" ^ string_expression expr1 (*has 3 arguments in documents but apparently needs 2 here??*)
  | Stanlight.Ebinop (expr1, b_op, expr2, bas) -> "B_op " ^ String.concat "" [string_expression expr1; string_op b_op; string_expression expr2]
  | Stanlight.Eindexed (expr1, exprl, bas) -> "Index " ^ String.concat "" [string_expression expr1; "["; string_exprlist exprl; "]"]
  | Stanlight.Etarget bas -> "target expression " (*what is this??*)
and string_exprlist exprlist =
  match exprlist with
  | Stanlight.Enil -> ""
  | Stanlight.Econs (e, Stanlight.Enil) -> string_expression e
  | Stanlight.Econs (e, es) -> String.concat "" [string_expression e; ", "; string_exprlist es]


let diff_wrt expr sub_expr =
  let zero_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 0., Stanlight.Breal) in
  let one_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 1., Stanlight.Breal) in
  let two_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 2., Stanlight.Breal) in
  let neg_one_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat (-1.), Stanlight.Breal) in
  match expr with
  | Stanlight.Econst_int (_, _) -> zero_float
  | Stanlight.Econst_float (_, _) -> zero_float
  | Stanlight.Evar (_, bas) ->
    begin
      match sub_expr = expr with
      | true -> one_float
      | false -> zero_float
    end
  | Stanlight.Ecall (_,_,_)-> zero_float (*figure out what this is*)
  | Stanlight.Eunop (_,_) -> zero_float
  | Stanlight.Ebinop (expr1, op, expr2, bas) ->
    begin
      match op with
      | Stanlight.Plus ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> two_float
          | (true, false) -> one_float
          | (false, true) -> one_float
          | (false, false) -> zero_float
        end
      | Stanlight.Minus ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> zero_float
          | (true, false) -> one_float
          | (false, true) -> neg_one_float
          | (false, false) -> zero_float
        end
      | Stanlight.Times ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> Stanlight.Ebinop (expr1, Stanlight.Times, two_float, bas)
          | (true, false) -> expr2
          | (false, true) -> expr1
          | (false, false) -> zero_float
        end
      | Stanlight.Divide ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> zero_float
          | (true, false) -> Stanlight.Ebinop (one_float, Stanlight.Divide, expr2, bas)
          | (false, true) ->
            begin
              let minus_hi_dho = Stanlight.Ebinop (neg_one_float, Stanlight.Times, expr1, bas) in
              let ho_squared = Stanlight.Ebinop (expr2, Stanlight.Times, expr2, bas) in
              Stanlight.Ebinop (minus_hi_dho, Stanlight.Divide, ho_squared, bas)
            end
          | (false, false) -> zero_float
        end
      | _ -> zero_float (*figure out what to do with Modulo and logic operators*)
    end
  | Stanlight.Eindexed (_, _, _) -> zero_float
  | Stanlight.Etarget _ -> zero_float


let rec string_statement stmt =
  match stmt with
  | Stanlight.Sskip -> "Sskip\n"
  | Stanlight.Sassign (expr1, opr, expr2) -> String.concat "" [string_expression expr1; " = "; string_expression expr2; ";\n"] (*how to incorporate option op??*)
  | Stanlight.Ssequence (stmt1, stmt2) -> "Ssequence (\n" ^ string_statement stmt1 ^ string_statement stmt2 ^ ")\n"
  | Stanlight.Sifthenelse (expr, stmt1, stmt2) -> String.concat "" [string_expression expr; " ? "; string_statement stmt1; " : "; string_statement stmt2; ";\n"]
  | Stanlight.Sfor (ident, expr1, expr2, stmt1) -> String.concat "" ["for ("; Camlcoq.extern_atom ident; " in "; string_expression expr1; ":"; string_expression expr2; ") {\n"; string_statement stmt1; "}\n"]
  | Stanlight.Starget expr -> String.concat "" ["target += "; string_expression expr; ";\n"]
  | Stanlight.Stilde (expr1, expr2, exprl) -> String.concat "" [string_expression expr1; " ~ "; string_expression expr2; "("; string_exprlist exprl; ")"; ";\n"]

let rec get_expr variable variable_assignments =
  match variable_assignments with
  | [] -> variable
  | Stanlight.Sassign (expr1, opr, expr2) :: ls ->
  begin
    match variable = expr1 with
    | true -> expr2
    | false -> get_expr variable ls
  end
  | _ -> variable

let rec set_expr variable expression variable_assignments =
  match variable_assignments with
  | [] -> []
  | Stanlight.Sassign (expr1, opr, expr2) :: ls ->
    begin
      match variable = expr1 with
      | true -> Stanlight.Sassign (expr1, opr, expression) :: ls
      | false -> Stanlight.Sassign (expr1, opr, expr2) :: (set_expr variable expression ls)
    end
  | _ -> variable_assignments

let rec has_var_assignment variable variable_assignments =
  match variable_assignments with
  | [] -> false
  | Stanlight.Sassign (expr1, opr, expr2) :: ls ->
    begin
      match variable = expr1 with
      | true -> true
      | false -> has_var_assignment variable ls
    end
  | _ -> false

(*
let rec evaluate expr var_assignments =
  match expr with
  | Stanlight.Econst_int (intgr, _) -> intgr
  | Stanlight.Econst_float (flt, _) -> flt
  | Stanlight.Evar (ident, _) -> evaluate (get_expr expr var_assignments) var_assignments
  | Stanlight.Ecall (expr1, exprl, bas) -> evaluate expr1 var_assignments (*fill in*)
  | Stanlight.Eunop (expr1, bas) -> evaluate expr1 var_assignments (*fill in*)
  | Stanlight.Ebinop (expr1, b_op, expr2, bas) ->
    begin
      let expr1_val = evaluate expr1 var_assignments in
      let expr2_val = evaluate expr2 var_assignments in
      match b_op with
      | Stanlight.Plus -> expr1_val + expr2_val
      | Stanlight.Minus -> expr1_val - expr2_val
      | Stanlight.Times -> expr1_val * expr2_val
      | Stanlight.Divide -> expr1_val / expr2_val
      | Stanlight.Modulo -> expr1_val mod expr2_val
      | Stanlight.Or -> expr1_val || expr2_val
      | Stanlight.And -> expr1_val && expr2_val
      | Stanlight.Equals -> expr1_val = expr2_val
      | Stanlight.NEquals -> not (expr1_val = expr2_val)
      | Stanlight.Less -> expr1_val < expr2_val
      | Stanlight.Leq -> expr1_val <= expr2_val
      | Stanlight.Greater -> expr1_val > expr2_val
      | Stanlight.Geq -> expr1_val >= expr2_val
    end
  | Stanlight.Eindexed (expr1, exprl, bas) -> Integers.Int.int 0 (*fill in*)
  | Stanlight.Etarget bas -> Camlcoq.BinNums.coq_Z 0 (*fill in*)
*)

(*actually going through the program definitions to hunt down model*)
let unpack_fundef fdf =
  match fdf with
  | Ctypes.Internal f -> string_statement f.Stanlight.fn_body
  | Ctypes.External _ -> ""

let rec unpack_block gbs =
  match gbs with
  | [] -> ()
  | (ident, AST.Gfun f) :: gs ->
    begin
    match (Camlcoq.extern_atom ident) with
    | "model" ->
      let str_stmt = unpack_fundef f in
      print_string("\nmodel {\n" ^ str_stmt ^ "}\n")
    | _ -> unpack_block gs
    end
  | (ident, AST.Gvar v) :: gs -> unpack_block gs

let rec program_defs gbs =
  match gbs with
  | (ident, _) :: gs -> String.concat "\n" [Camlcoq.extern_atom ident; program_defs gs]
  | _ -> ""

let generate_proposal program =
  let _ = unpack_block program.Stanlight.pr_defs in
 (* let _ = print_string(program_defs program.Stanlight.pr_defs) in*)
  let pro = generate_prologue () in
  let epi = generate_epilogue () in
  let body = String.concat "\n" (List.map generate_param program.Stanlight.pr_parameters_vars) in
  String.concat "\n" [pro; body; ""; epi]
