
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
  
let printPreludeHeader sourcefile data params =
  let sourceDir = Filename.dirname sourcefile in
  let file = sourceDir ^ "/" ^ "prelude.h" in
  Printf.fprintf stdout "Generating: %s\n" file;
  let ohc = open_out file in
  Printf.fprintf ohc "%s\n" (String.concat "\n" [
    "#ifndef RUNTIME_H";
    "#define RUNTIME_H";
    "#include<stdbool.h>  ";
    "";
    renderStruct "Data" data;
    renderStruct "Params" params;
    "";
    "void print_data(struct Data* observations);";
    "void read_data(struct Data* observations, char* file,char * perm);";
    "struct Data* alloc_data(void);";
    "void print_params(struct Params* parameters, bool convert);";
    "void read_params(struct Params* parameters, char* file,char * perm);";
    "struct Params* alloc_params(void);";    
    "void propose(struct Params* state, struct Params* candidate);";
    "void copy_params(struct Params* to, struct Params* from);";
    "void constrained_to_unconstrained(struct Params* constrained);";
    "void unconstrained_to_constrained(struct Params* unconstrained);";
    "";
    "#endif";
  ]);
  close_out ohc

let generate_read_data vs =

  let generate_single v =
    let name = fst v in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "read_int(fp,&observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | Stanlight.Breal -> "read_real(fp,&observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "read_int_array(fp,observations->" ^  (Camlcoq.extern_atom name) ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "read_real_array(fp,observations->" ^ (Camlcoq.extern_atom name) ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void read_data(struct Data* observations, char* file,char * perm) {";
      "  FILE *fp;";
      "  fp = fopen(file, perm);";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "  fclose(fp);";
      "}"
    ]  

let generate_print_data vs =

  let generate_single v =
    let name = fst v in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "print_int(observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | Stanlight.Breal -> "print_real(observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "print_int_array(observations->" ^  (Camlcoq.extern_atom name) ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "print_real_array(observations->" ^ (Camlcoq.extern_atom name) ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void print_data(struct Data* observations) {";
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

  let generate_single v =
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "read_int(fp,&parameters->" ^ name ^ ");"
    | Stanlight.Breal -> "read_real(fp,&parameters->" ^ name ^ ");"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "read_int_array(fp,parameters->" ^  name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "read_real_array(fp,parameters->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void read_params(struct Params* parameters, char* file,char * perm) {";
      "  FILE *fp;";
      "  fp = fopen(file, perm);";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "  fclose(fp);";
      "  constrained_to_unconstrained(parameters);";
      "}"
    ]  
  
let generate_alloc_params () =
  String.concat "\n\n" [
      "struct Params* alloc_params() {";
      "  struct Params* params = (struct Params*) malloc(sizeof(struct Params));";
      "  return params;";
      "}"
    ]

let generate_print_params vs =

  let generate_single v =
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Bint -> "print_int(parameters->" ^ name ^ ");"
    | Stanlight.Breal -> "print_real(parameters->" ^ name ^ ");"
    | Stanlight.Barray (Stanlight.Bint,sz) ->
       "print_int_array(parameters->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | Stanlight.Barray (Stanlight.Breal,sz) ->
       "print_real_array(parameters->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void print_params(struct Params* parameters, bool convert) {";
      "  if (convert) {";
      "    unconstrained_to_constrained(parameters);";
      "  }";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ]

let generate_copy_params vs =

  let generate_single v =
    let name = Camlcoq.extern_atom (fst v) in
    let typ = snd v in
    match typ with
    | Stanlight.Breal -> "to->" ^ name ^ " = " ^ "from->" ^ name ^ ";"
    | Stanlight.Bint -> "to->" ^ name ^ " = " ^ "from->" ^ name ^ ";"
    | Stanlight.Barray (_,sz) -> String.concat "\n" [
                                 "for (int i = 0; i < " ^ (Camlcoq.Z.to_string sz) ^ " ; i++) {";
                                 "    to->" ^ name ^ "[i]" ^ " = " ^ "from->" ^ name ^ "[i]" ^ ";";
                                 "  };";
                               ] 
    | _ -> "ddd"
  in

  String.concat "\n\n" [
      "void copy_params(struct Params* to, struct Params* from) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ]    

let generate_constrained_to_unconstrained vs =

  let generate_single (name,typ,cons) =
    match cons with
    | Stanlight.Cidentity -> ""
    | Stanlight.Clower_upper (lower, upper) ->
       begin
         match typ with
         | Stanlight.Breal ->
            let x = "constrained->" ^ name in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let num = "(" ^ x ^ " - " ^ a ^ ")" in
            let den = "(" ^ b ^ " - " ^ a ^ ")" in
            let y = "logit(" ^ num ^ " / " ^ den ^")" in
            " constrained->" ^ name ^ " = " ^ y ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end
    | Stanlight.Clower lower ->
       begin
         match typ with
         | Stanlight.Breal ->
            let x = "constrained->" ^ name in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let num = "(" ^ x ^ " - " ^ a ^ ")" in
            let y = "log(" ^ num ^ ")" in
            " constrained->" ^ name ^ " = " ^ y ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")         
       end
    | Stanlight.Cupper upper ->
       begin
         match typ with
         | Stanlight.Breal ->
            let x = "constrained->" ^ name in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let t = "(" ^ b ^ " - " ^ x ^ ")" in
            let y = "log(" ^ t ^")" in
            " constrained->" ^ name ^ " = " ^ y ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end       
  in
  
  String.concat "\n\n" [
      "void constrained_to_unconstrained(struct Params* constrained) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ]   

let generate_unconstrained_to_constrained vs =

  let generate_single (name,typ,cons) =
    match cons with
    | Stanlight.Cidentity -> ""
    | Stanlight.Clower_upper (lower, upper) ->
       begin
         match typ with
         | Stanlight.Breal ->
            let y = "unconstrained->" ^ name in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let x = a ^ " + " ^ "(" ^ b ^ " - " ^ a ^ ")" ^ " * " ^ "expit(" ^ y ^ ")" in
            " unconstrained->" ^ name ^ " = " ^ x ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end
    | Stanlight.Clower lower ->
       begin
         match typ with
         | Stanlight.Breal ->
            let y = "unconstrained->" ^ name in
            let a = Float.to_string (Camlcoq.camlfloat_of_coqfloat lower) in
            let x = a ^ " + " ^ "exp(" ^ y ^ ")" in
            " unconstrained->" ^ name ^ " = " ^ x ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end       
    | Stanlight.Cupper upper ->
       begin
         match typ with
         | Stanlight.Breal ->
            let y = "unconstrained->" ^ name in
            let b = Float.to_string (Camlcoq.camlfloat_of_coqfloat upper) in
            let x = b ^ " - " ^ "expit(" ^ y ^ ")" in
            " unconstrained->" ^ name ^ " = " ^ x ^ ";"
         | Stanlight.Bint -> raise (NIY_gen "Typechecker failed, parameter cannot be int")
         | _ -> raise (NIY_gen "Constraints are currently only supported for scalars")
       end       
  in
  
  String.concat "\n\n" [
      "void unconstrained_to_constrained(struct Params* unconstrained) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ] 
  
let printPreludeFile sourcefile data params proposal params_with_constraints =
  let sourceDir = Filename.dirname sourcefile in
  let file = sourceDir ^ "/" ^ "prelude.c" in
  let oc = open_out file in
  Printf.fprintf stdout "Generating: %s\n" file;

  Printf.fprintf oc "%s\n" (String.concat "\n\n" [
    "#include <stdlib.h>";
    "#include <stdio.h>";
    "#include \"stanlib.h\"";
    "#include \"prelude.h\"";
    proposal;
    generate_alloc_data ();
    generate_print_data data;
    generate_read_data data;
    generate_alloc_params();
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
  let params_with_constraints = filter_params defs (List.map (fun v -> Camlcoq.extern_atom (fst v)) params) in
  let data = program.Stanlight.pr_data_vars in
  printPreludeHeader sourcefile data params;
  printPreludeFile sourcefile data params proposal params_with_constraints
