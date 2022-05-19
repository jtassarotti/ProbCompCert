
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
    renderStruct "Data" data_basics;
    (* "extern "^(renderGlobalStruct "observations" "Data" false)^"\n"; *)
    renderStruct "Params" param_basics;
    "extern "^(renderGlobalStruct "state" "Params" false)^"\n";
    "";
    "void print_data(struct Data* observations);";
    "void read_data(struct Data* observations, char* file,char * perm);";
    "struct Data* alloc_data(void);";
    "void print_params(void*);";
    "void* get_state(void);";
    "void set_state(void*);";
    "void init_parameters(void);";
    "void* propose(void *);";
    "";
    "#endif";
  ]);
  close_out ohc

let renderGetAndSet global_name struct_type =
  String.concat "\n" ([
    "";
    "void* get_" ^ global_name ^ " () {";
    "  return (void*) &" ^ global_name ^ ";"; (* FIXME: this "return "*)
    (* "  void* o = (void*\) " ^ global_name ^ ";"; *)
    (* "  return o;"; *)
    "}";
    "";
    ("void set_" ^ global_name ^ " (void* opaque) {");
    ("  struct " ^ struct_type ^ "* s = (struct " ^ struct_type ^ "*) opaque;");
    ("  " ^ global_name ^ " = *s;");
    "}";
    "";
  ])
  
let renderPrintStruct name vs =
  let field var = "s->" ^ var in
  let index1 v ix = field v ^ "["^ string_of_int ix ^"]" in

  let printer str var = "printf(\"" ^ str ^ "\", " ^ field var ^ ");" in
  let typeTmpl t =
     match t with
    | StanE.Bint -> "%z"
    | StanE.Breal -> "%f"
    | StanE.Barray _ -> "%f"
    | _ -> raise (NIY_gen "renderPrintStruct.typeTmpl: invalid type")
  in
  let range n = List.map (fun x -> x - 1) (List.init n Int.succ) in
  let loopTmpl1 t size = "[" ^ (String.concat ", " (List.map (fun _ -> typeTmpl t) (range size))) ^ "]\\n" in
  let loopVars1 v size = (String.concat ",\n    " (List.map (fun i -> index1 v i) (range size))) in
  let loopPrinter1 v t size = "printf(\"" ^ v ^ " = " ^ loopTmpl1 t size ^ "\", " ^ loopVars1 v size ^ ");" in

  let printField (p, t) =
    let v = Camlcoq.extern_atom p in
    match t with
    | StanE.Breal -> ("  " ^ printer (v ^" = "^typeTmpl t^"\\n") v)
    | StanE.Bint -> ("  " ^ printer (v ^" = "^typeTmpl t^"\\n") v)
    | StanE.Barray (StanE.Bint, sz) -> ("  " ^ loopPrinter1 v t (Int32.to_int (Camlcoq.camlint_of_coqint sz)))
    | StanE.Barray (StanE.Breal, sz) -> ("  " ^ loopPrinter1 v t (Int32.to_int (Camlcoq.camlint_of_coqint sz)))
    | _ -> raise (NIY_gen "Printer: nested array")
  in
  String.concat "\n" ([
    ("void print_" ^ String.lowercase_ascii name ^ " (void* opaque) {");
    ("  struct " ^ name ^ "* s = (struct " ^ name ^ "*) opaque;");
  ] @ (List.map printField vs) @ [
    "}\n"
  ])

let renderParameters struct_type struct_vars =
  let ret = "s" in
  let renderField (p, t) =
    let v = Camlcoq.extern_atom p in
    match t with
    (* See: https://mc-stan.org/docs/2_29/reference-manual/initialization.html *)
    (* If there are no user-supplied initial values, the default initialization strategy is to initialize the unconstrained parameters directly with values drawn uniformly from the interval (−2,2) *)
    | StanE.Breal             -> ("  "^ret^"->" ^ v ^" = 0.0; // For debugging. uniform_sample(-2,2);")
    | _ -> "todo" (*raise (NIY_gen "renderParameters.renderField: incomplete for this type")*)
  in
  String.concat "\n" ([
    "void init_parameters () {";
    "  struct " ^ struct_type ^ "* "^ret^" = malloc(sizeof(struct " ^ struct_type ^ "));";
  ] @ (List.map renderField struct_vars) @ [
    ("  state = *"^ret^";");
    (* ("  return "^ret^";"); *)
    "}";
    "";
  ])

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

let printPreludeFile sourcefile data_basics param_basics proposal =
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
    renderGlobalStruct "state" "Params" false;
    proposal;
    renderGetAndSet "state" "Params";
    renderPrintStruct "Params" param_basics;
    renderParameters "Params" param_basics;
    generate_alloc_data ();
    generate_print_data data_basics;
    generate_read_data data_basics;
  ]);
  close_out oc
        
let generate_prelude sourcefile program proposal =
  let params = program.StanE.pr_parameters_vars in
  let data = program.StanE.pr_data_vars in
  printPreludeHeader sourcefile data params;
  printPreludeFile sourcefile data params proposal
