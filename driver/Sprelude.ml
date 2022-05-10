
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
    "extern "^(renderGlobalStruct "observations" "Data" false)^"\n";
    renderStruct "Params" param_basics;
    "extern "^(renderGlobalStruct "state" "Params" false)^"\n";
    "";
    "void print_data(void *);";
    "void print_params(void*);";
    "void* get_state();";
    "void set_state(void*);";
    "void load_from_cli(void* opaque, char *files[]);";
    "void init_parameters();";
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
    | _ -> "todo" (* raise (NIY_gen "renderParameters.renderField: incomplete for this type") *)
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

let renderDataLoaderFunctions vs =
  let parseType t =
     match t with
    | StanE.Bint -> "atof"
    | StanE.Breal -> "atoll"
    | StanE.Barray _ -> "atoll"
    | _ -> raise (NIY_gen "invalid type")
  in

  let loadField (p, t) =
    let v = Camlcoq.extern_atom p in
    match t with
    | StanE.Breal -> raise (NIY_gen "Data loading: single real")
    | StanE.Bint -> raise (NIY_gen "Data loading: single int")
    | StanE.Barray (StanE.Bint,_) ->
      String.concat "\n" [
        "  if (0 == access(f, 0))";
        "  {";
        "      FILE *fp = fopen(f, \"r\" );";
        "      char line[1024];";
        "      int num = 0;";
        "      while (fgets(line, 1024, fp))";
        "      {";
        "        char* tmp = strdup(line);";
        "        const char* tok;";
        "        for (tok = strtok(line, \",\");";
        "          tok && *tok;";
        "          tok = strtok(NULL, \",\\n\"))";
        "        {";
        "            " ^ "d->" ^v ^ "[num] = " ^ parseType t ^ "(tok);";
        "            num++;";
        "        }";
        "        free(tmp);";
        "      }";
        "      fclose(fp);";
        "  } else { printf(\"csv file not found for data field: "^ v ^"\\n\");}";
        ]
    | StanE.Barray (StanE.Breal,_) -> raise (NIY_gen "Data loading: array of reals")
    | _ -> raise (NIY_gen "Data loading: nested arrays")
  in

  let renderLoader (p, t) = let v = Camlcoq.extern_atom p in
    String.concat "\n" [
    "void load_" ^ v ^ " (void* opaque, char* f) {";
    "  struct Data* d = (struct Data*) opaque;";
    loadField (p, t);
    "}";
  ] in
  String.concat "\n" (List.map renderLoader vs)

let renderCLILoader vs =
  let runLoader ix (p, t) =
    "  load_" ^ Camlcoq.extern_atom p ^ "(opaque, files[" ^ string_of_int (ix) ^ "]);"
  in
  String.concat "\n" ([
    ("void load_from_cli (void* opaque, char *files[]) {");
  ] @ (List.mapi runLoader vs) @ [
    "}\n"
  ])


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
    "#include <unistd.h>";
    "#include <string.h>";
    "#include <math.h>";
    "#include \"stanlib.h\"";
    "#include \""^"prelude.h\"";
    "";
    (* strdup is not standard *)
    (* but ccomp doesn't permit for "#define _POSIX_C_SOURCE >= 200809L"; *)
    "extern char* strdup(const char*);";

    "";
    renderGlobalStruct "observations" "Data" false;
    renderGlobalStruct "state" "Params" false;
    (* file scope declarations: *)
    proposal;
    renderGetAndSet "observations" "Data";
    renderGetAndSet "state" "Params";
    renderPrintStruct "Data" data_basics;
    renderPrintStruct "Params" param_basics;
    renderParameters "Params" param_basics;
    renderDataLoaderFunctions data_basics;
    renderCLILoader data_basics;
  ]);
  close_out oc
        
let generate_prelude sourcefile program proposal =
  let params = program.StanE.pr_parameters_vars in
  let data = program.StanE.pr_data_vars in
  printPreludeHeader sourcefile data params;
  printPreludeFile sourcefile data params proposal
