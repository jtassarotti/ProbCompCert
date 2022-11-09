exception NIY_gen of string

let basicToCString v btype =
  match btype with
  | Stanlight.Bint -> "int " ^ v
  | Stanlight.Breal -> "double " ^ v
  | Stanlight.Barray (Stanlight.Bint,sz) -> "int " ^ v ^ "[" ^ (Camlcoq.Z.to_string sz) ^ "]"
  | Stanlight.Barray (Stanlight.Breal,sz) -> "double " ^ v ^ "[" ^ (Camlcoq.Z.to_string sz) ^ "]"    
  | _ -> raise (NIY_gen "Unexpected type")

let renderStruct name vs =
  let renderField (p, t) = "  " ^ basicToCString (Camlcoq.extern_atom p) t ^ ";" in

  String.concat "\n" ([
    "struct " ^ name ^ " {"
  ] @ (List.map renderField vs) @ [
    "};\n"
  ])

let renderGlobalStruct global_name struct_type is_ptr =
  "struct " ^ struct_type ^ (if is_ptr then "*" else "") ^" "^ global_name ^";"
  
let printPreludeHeader sourcefile data params_fun =
  let sourceDir = Filename.dirname sourcefile in
  let file = sourceDir ^ "/" ^ "bridgeprelude.h" in
  Printf.fprintf stdout "Generating: %s\n" file;
  let ohc = open_out file in
  Printf.fprintf ohc "%s\n" (String.concat "\n" [
    "#ifndef RUNTIME_H";
    "#define RUNTIME_H";
    "";
    renderStruct "Data" data;
    "";
    "void print_data(struct Data* observations, FILE *fp);";
    "void read_data(struct Data* observations, char* file,char * perm);";
    "struct Data* alloc_data(void);";
    "void print_params_names(FILE *fp);";
    "void print_params(double* parameters, int convert, FILE *fp);";
    "void read_params(double* parameters, char* file,char * perm);";
    "double * alloc_params(void);";    
    "void propose(double * state, double * candidate);";
    "void copy_params(double * to, double * from);";
    "void constrained_to_unconstrained(double * constrained);";
    "void unconstrained_to_constrained(double * unconstrained);";
    "";
    "#endif";
  ]);
  close_out ohc

let annotate_param_ofs params =
  let sz_one (_, typ) =
    match typ with
    | Stanlight.Barray (_, sz) -> (Camlcoq.Z.to_int  sz)
    | _ -> 1
  in

  let rec gen_ofs (start : int) ls =
    match ls with
    | [] -> []
    | x :: ls ->
       ((start, x) :: (gen_ofs ((sz_one x) + start) ls))
  in

  gen_ofs 0 params

let generate_read_data vs =

  let generate_single v =
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "read_int(get(\"" ^ name ^ "\"),&observations->" ^ name ^ ");"
    | Stanlight.Breal -> "read_real(get(\"" ^ name ^ "\"),&observations->" ^ name ^ ");"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "read_int_array(get(\"" ^ name ^ "\"),observations->" ^  name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "read_real_array(get(\"" ^ name ^ "\"),observations->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void read_data(struct Data* observations, char* file,char * perm) {";
      "  parse(file);";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ]  

let generate_print_data vs =

  let generate_single v =
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "print_int(observations->" ^ name ^ ",fp);"
    | Stanlight.Breal -> "print_real(observations->" ^ name ^ ",fp);"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "print_int_array(observations->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ",fp);"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "print_real_array(observations->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ",fp);"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void print_data(struct Data* observations, FILE *fp) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ]

let generate_alloc_data () =
  String.concat "\n\n" [
      "struct Data* alloc_data() {";
      "  struct Data* data = (struct Data*) malloc(sizeof(struct Data));";
      "  return data;";
      "}"
    ]

let generate_read_params vs =

  let ofs_vs = annotate_param_ofs vs in

  let generate_single (ofs, v) =
    let ofs = string_of_int ofs in
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "read_int(get(\"" ^ name ^ "\"),parameters + " ^ ofs ^ ");"
    | Stanlight.Breal -> "read_real(get(\"" ^ name ^ "\"),parameters + " ^ ofs ^ ");"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "read_int_array(get(\"" ^ name ^ "\"),parameters + " ^  ofs ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "read_real_array(get(\"" ^ name ^ "\"),parameters + " ^ ofs ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void read_params(double * parameters, char* file,char * perm) {";
      "  parse(file);";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" ofs_vs;
      "  constrained_to_unconstrained(parameters);";
      "}"
    ]  
  
let generate_alloc_params params =
  let sz_one v =
    let typ = snd v in
    match typ with
    | Stanlight.Barray (_, sz) -> (Camlcoq.Z.to_int sz)
    | _ -> 1
  in

  let sz_params = List.fold_left (+) 0 (List.map sz_one params) in

  String.concat "\n\n" [
      "double * alloc_params() {";
      "  double * params = (double *) malloc(sizeof(double) *" ^  (string_of_int sz_params) ^ ");";
      "  return params;";
      "}"
    ]

let generate_print_params_names vs =

  let generate_single v =
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Barray (_, sz) ->
       String.concat ", " (List.init (Camlcoq.Z.to_int sz) (fun n -> name ^ "." ^ string_of_int (n + 1)))
    | _ -> name
  in

  let params_names_str = String.concat ", " (List.map generate_single vs) in
  let fprint_stmt = "  fprintf(fp, \"" ^ params_names_str ^ "\");" in

  String.concat "\n\n" [
      "void print_params_names(FILE *fp) {";
      fprint_stmt;
      "}"
    ]

let generate_print_params vs =

  let ofs_vs = annotate_param_ofs vs in
  
  let generate_single (ofs, v) =
    let ofs = string_of_int ofs in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "print_int(parameters[" ^ ofs ^ "],fp);"
    | Stanlight.Breal -> "print_real(parameters[" ^ ofs ^ "],fp);"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "print_int_array(parameters + " ^ ofs ^ "," ^ (Camlcoq.Z.to_string sz) ^ ",fp);"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "print_real_array(parameters + " ^ ofs ^ "," ^ (Camlcoq.Z.to_string sz) ^ ",fp);"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  let generate_strings =
    String.concat "\n  fprintf(fp, \",\");\n" (List.map (fun v -> "  " ^ generate_single v) ofs_vs)
  in

  String.concat "\n\n" [
      "void print_params(double * parameters, int convert, FILE *fp) {";
      "  if (convert) {";
      "    unconstrained_to_constrained(parameters);";
      "  }";
      generate_strings;
      "}"
    ]

let generate_copy_params vs =

  let ofs_vs = annotate_param_ofs vs in

  let generate_single (ofs, v) =
    let ofs = string_of_int ofs in
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Breal -> "to[" ^ ofs ^ "] = " ^ "from[" ^ ofs ^ "];"
    | Stanlight.Bint -> "to[" ^ name ^ "] = " ^ "from[" ^ ofs ^ "];"
    | Stanlight.Barray (_,sz) -> String.concat "\n" [
                                 "for (int i = 0; i < " ^ (Camlcoq.Z.to_string sz) ^ " ; i++) {";
                                 "    to[" ^ ofs ^ " + i]" ^ " = " ^ "from[" ^ ofs ^ "+ i]" ^ ";";
                                 "  };";
                               ] 
    | _ -> "ddd"
  in

  String.concat "\n\n" [
      "void copy_params(double * to, double * from) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" ofs_vs;
      "}"
    ]    

let generate_constrained_to_unconstrained vs =

  let sz_one (_, typ, _) =
    match typ with
    | Stanlight.Barray (_, sz) -> (Camlcoq.Z.to_int  sz)
    | _ -> 1
  in

  let rec gen_ofs (start : int) ls =
    match ls with
    | [] -> []
    | x :: ls ->
       ((start, x) :: (gen_ofs ((sz_one x) + start) ls))
  in

  let ofs_vs = gen_ofs 0 vs in

  let generate_single (ofs, (name,typ,cons)) =
    let ofs = string_of_int ofs in
    match cons with
    | Stanlight.Cidentity -> ""
    | Stanlight.Clower_upper (lower, upper) ->
       begin
         match typ with
         | Stanlight.Breal ->
            let x = "constrained[" ^ ofs ^ "]" in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let num = "(" ^ x ^ " - " ^ a ^ ")" in
            let den = "(" ^ b ^ " - " ^ a ^ ")" in
            let y = "logit(" ^ num ^ " / " ^ den ^")" in
            " constrained[" ^ ofs ^ "] = " ^ y ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end
    | Stanlight.Clower lower ->
       begin
         match typ with
         | Stanlight.Breal ->
            let x = "constrained[" ^ ofs ^ "]" in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let num = "(" ^ x ^ " - " ^ a ^ ")" in
            let y = "log(" ^ num ^ ")" in
            " constrained[" ^ ofs ^ "] = " ^ y ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")         
       end
    | Stanlight.Cupper upper ->
       begin
         match typ with
         | Stanlight.Breal ->
            let x = "constrained[" ^ ofs ^ "]" in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let t = "(" ^ b ^ " - " ^ x ^ ")" in
            let y = "-log(" ^ t ^")" in
            " constrained[" ^ ofs ^ "] = " ^ y ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end       
  in
  
  String.concat "\n\n" [
      "void constrained_to_unconstrained(double * constrained) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" ofs_vs;
      "}"
    ]   

let generate_unconstrained_to_constrained vs =

  let sz_one (_, typ, _) =
    match typ with
    | Stanlight.Barray (_, sz) -> (Camlcoq.Z.to_int  sz)
    | _ -> 1
  in

  let rec gen_ofs (start : int) ls =
    match ls with
    | [] -> []
    | x :: ls ->
       ((start, x) :: (gen_ofs ((sz_one x) + start) ls))
  in

  let ofs_vs = gen_ofs 0 vs in

  let generate_single (ofs, (name,typ,cons)) =
    let ofs = string_of_int ofs in
    match cons with
    | Stanlight.Cidentity -> ""
    | Stanlight.Clower_upper (lower, upper) ->
       begin
         match typ with
         | Stanlight.Breal ->
            let y = "unconstrained[" ^ ofs ^ "]" in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let x = a ^ " + " ^ "(" ^ b ^ " - " ^ a ^ ")" ^ " * " ^ "expit(" ^ y ^ ")" in
            " unconstrained[" ^ ofs ^ "] = " ^ x ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end
    | Stanlight.Clower lower ->
       begin
         match typ with
         | Stanlight.Breal ->
            let y = "unconstrained[" ^ ofs ^ "]" in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let x = a ^ " + " ^ "exp(" ^ y ^ ")" in
            " unconstrained[" ^ ofs ^ "] = " ^ x ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end       
    | Stanlight.Cupper upper ->
       begin
         match typ with
         | Stanlight.Breal ->
            let y = "unconstrained[" ^ ofs ^ "]" in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let x = b ^ " - " ^ "exp(-" ^ y ^ ")" in
            " unconstrained[" ^ ofs ^ "] = " ^ x ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end       
  in
  
  String.concat "\n\n" [
      "void unconstrained_to_constrained(double * unconstrained) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" ofs_vs;
      "}"
    ] 

let printPreludeFile sourcefile data params_funs proposal params_with_constraints =
  let params = List.map fst params_funs in
  let sourceDir = Filename.dirname sourcefile in
  let file = sourceDir ^ "/" ^ "bridgeprelude.c" in
  let oc = open_out file in
  Printf.fprintf stdout "Generating: %s\n" file;

  Printf.fprintf oc "%s\n" (String.concat "\n\n" [
    "#include <stdlib.h>";
    "#include <stdio.h>";
    "#include <math.h>";
    "#include \"stanlib.h\"";
    "#include \"parser.h\"";
    "#include \"bridgeprelude.h\"";
    proposal;
    generate_alloc_data ();
    generate_print_data data;
    generate_read_data data;
    generate_alloc_params params;
    generate_print_params_names params;
    generate_print_params params;
    generate_read_params params;
    generate_copy_params params;
    generate_constrained_to_unconstrained params_with_constraints;
    generate_unconstrained_to_constrained params_with_constraints;
  ]);
  close_out oc

let rec filter_params defs params =
  match defs with
  | [] -> []
  | (name,AST.Gvar v) :: defs ->
     let name = Camlcoq.extern_atom name in
     let filtered_params = filter_params defs params in
     if List.mem name params
     then (name,v.AST.gvar_info.Stanlight.vd_type,v.AST.gvar_info.Stanlight.vd_constraint) :: filtered_params
     else filtered_params
  | def :: defs -> filter_params defs params
     
let generate_prelude sourcefile program proposal =
  let defs = program.Stanlight.pr_defs in
  let params = program.Stanlight.pr_parameters_vars in
  let params_with_constraints = filter_params defs (List.map (fun v -> Camlcoq.extern_atom (fst (fst v))) params) in
  let data = program.Stanlight.pr_data_vars in
  printPreludeHeader sourcefile data params;
  printPreludeFile sourcefile data params proposal params_with_constraints
