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

let rec string_basic bas =
  match bas with
  | Stanlight.Bint -> "int"
  | Stanlight.Breal -> "real"
  | Stanlight.Barray (basic, intgr) -> (string_basic basic) ^ "[" ^ Camlcoq.Z.to_string intgr ^ "]"
  | Stanlight.Bfunction (basiclist, basic) -> "inputs -> " ^ (string_basic basic)

let rec string_expression expr =
  match expr with
  | Stanlight.Econst_int (intgr, bas) -> Camlcoq.Z.to_string intgr
  | Stanlight.Econst_float (flt, bas) -> "float" (*Float.to_string flt*)
  | Stanlight.Evar (ident, bas) -> Camlcoq.extern_atom ident
  | Stanlight.Ecall (expr1, exprl, bas) -> String.concat "" [string_expression expr1; "("; string_exprlist exprl; ")"]
  | Stanlight.Eunop (expr1, bas) -> "!" ^ string_expression expr
  | Stanlight.Ebinop (expr1, b_op, expr2, bas) -> String.concat "" [string_expression expr1; string_op b_op; string_expression expr2]
  | Stanlight.Eindexed (expr1, exprl, bas) -> String.concat "" [string_expression expr1; "["; string_exprlist exprl; "]"]
  | Stanlight.Etarget bas -> "target expression " (*what is this??*)

  and string_exprlist exprlist =
    match exprlist with
    | Stanlight.Enil -> ""
    | Stanlight.Econs (e, Stanlight.Enil) -> string_expression e
    | Stanlight.Econs (e, es) -> String.concat "" [string_expression e; ", "; string_exprlist es]

let rec string_statement stmt =
  match stmt with
  | Stanlight.Sskip -> ""
  | Stanlight.Sassign (expr1, opr, expr2) -> String.concat "" [string_expression expr1; " = "; string_expression expr2; ";\n"] (*how to incorporate option op??*)
  | Stanlight.Ssequence (stmt1, stmt2) -> string_statement stmt1 ^ string_statement stmt2
  | Stanlight.Sifthenelse (expr, stmt1, stmt2) -> String.concat "" [string_expression expr; " ? "; string_statement stmt1; " : "; string_statement stmt2; ";\n"]
  | Stanlight.Sfor (ident, expr1, expr2, stmt1) -> String.concat "" ["for ("; Camlcoq.extern_atom ident; " in "; string_expression expr1; ":"; string_expression expr2; ") {\n"; string_statement stmt1; "}\n"]
  | Stanlight.Starget expr -> String.concat "" ["target += "; string_expression expr; ";\n"]
  | Stanlight.Stilde (expr1, expr2, exprl) -> String.concat "" [string_expression expr1; " ~ "; string_expression expr2; "("; string_exprlist exprl; ")"; ";\n"]

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
