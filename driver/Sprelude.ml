
exception NIY_gen of string

let basicToCString v btype =
  match btype with
  | StanE.Bint -> "int " ^ v
  | StanE.Breal -> "double " ^ v
  | StanE.Barray (StanE.Bint,sz) -> "int " ^ v ^ "[" ^ (Camlcoq.Z.to_string sz) ^ "]"
  | StanE.Barray (StanE.Breal,sz) -> "double " ^ v ^ "[" ^ (Camlcoq.Z.to_string sz) ^ "]"    
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
  
let printPreludeHeader sourcefile data_basics param_basics =
  let sourceDir = Filename.dirname sourcefile in
  let file = sourceDir ^ "/" ^ "prelude.h" in
  Printf.fprintf stdout "Generating: %s\n" file;
  let ohc = open_out file in
  Printf.fprintf ohc "%s\n" (String.concat "\n" [
    "#ifndef RUNTIME_H";
    "#define RUNTIME_H";
    "";
    renderStruct "Data" data_basics;
    renderStruct "Params" param_basics;
    "";
    "void print_data(struct Data* observations);";
    "void read_data(struct Data* observations, char* file,char * perm);";
    "struct Data* alloc_data(void);";
    "void print_params(struct Params* parameters);";
    "void read_params(struct Params* parameters, char* file,char * perm);";
    "struct Params* alloc_params(void);";    
    "void propose(struct Params* state, struct Params* candidate);";
    "void copy_params(struct Params* to, struct Params* from);";
    "";
    "#endif";
  ]);
  close_out ohc

let generate_read_data vs =

  let generate_single v =
    let name = fst v in
    let typ = snd v in
    match typ with
    | StanE.Bint -> "read_int(fp,&observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | StanE.Breal -> "read_real(fp,&observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | StanE.Barray (StanE.Bint,sz) ->
       "read_int_array(fp,observations->" ^  (Camlcoq.extern_atom name) ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | StanE.Barray (StanE.Breal,sz) ->
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
    | StanE.Bint -> "print_int(observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | StanE.Breal -> "print_real(observations->" ^ (Camlcoq.extern_atom name) ^ ");"
    | StanE.Barray (StanE.Bint,sz) ->
       "print_int_array(observations->" ^  (Camlcoq.extern_atom name) ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | StanE.Barray (StanE.Breal,sz) ->
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
    | StanE.Bint -> "read_int(fp,&parameters->" ^ name ^ ");"
    | StanE.Breal -> "read_real(fp,&parameters->" ^ name ^ ");"
    | StanE.Barray (StanE.Bint,sz) ->
       "read_int_array(fp,parameters->" ^  name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | StanE.Barray (StanE.Breal,sz) ->
       "read_real_array(fp,parameters->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void read_params(struct Params* parameters, char* file,char * perm) {";
      "  FILE *fp;";
      "  fp = fopen(file, perm);";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "  fclose(fp);";
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
    | StanE.Bint -> "print_int(parameters->" ^ name ^ ");"
    | StanE.Breal -> "print_real(parameters->" ^ name ^ ");"
    | StanE.Barray (StanE.Bint,sz) ->
       "print_int_array(parameters->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | StanE.Barray (StanE.Breal,sz) ->
       "print_real_array(parameters->" ^ name ^ "," ^ (Camlcoq.Z.to_string sz) ^ ");"
    | _ -> raise (NIY_gen "Array of array or function")
  in

  String.concat "\n\n" [
      "void print_params(struct Params* parameters) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ]

let generate_copy_params vs =

  let generate_single v =
    let name = Camlcoq.extern_atom (fst v) in
    "to->" ^ name ^ " = " ^ "from->" ^ name ^ ";"
  in

  String.concat "\n\n" [
      "void copy_params(struct Params* to, struct Params* from) {";
      List.fold_left (fun str -> fun v -> str ^ "  " ^ (generate_single v) ^ "\n") "" vs;
      "}"
    ]    
  
let printPreludeFile sourcefile data_basics params_basics proposal =
  let sourceDir = Filename.dirname sourcefile in
  (*let sourceName = Filename.basename sourcefile in
  let preludeName = Filename.chop_extension sourceName in*)
  let file = sourceDir ^ "/" ^ "prelude.c" in
  let oc = open_out file in
  Printf.fprintf stdout "Generating: %s\n" file;

  Printf.fprintf oc "%s\n" (String.concat "\n" [
    "#include <stdlib.h>";
    "#include <stdio.h>";
    "#include \"stanlib.h\"";
    "#include \"prelude.h\"";
    "";
    proposal;
    generate_alloc_data ();
    generate_print_data data_basics;
    generate_read_data data_basics;
    generate_alloc_params();
    generate_print_params params_basics;
    generate_read_params params_basics;
    generate_copy_params params_basics;
  ]);
  close_out oc
        
let generate_prelude sourcefile program proposal =
  let params = program.StanE.pr_parameters_vars in
  let data = program.StanE.pr_data_vars in
  printPreludeHeader sourcefile data params;
  printPreludeFile sourcefile data params proposal
