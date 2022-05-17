open List
   
exception NIY_stanlib of string

let _ = Camlcoq.use_canonical_atoms := true

let tdouble = Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr)
let tint = Ctypes.Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr)
let ctarray (t, sz) = Ctypes.Tarray (t, sz, Ctypes.noattr)
      
let library_math_functions = [
    "log",
    AST.Tfloat,
    [AST.Tfloat];
    "exp",
    AST.Tfloat,
    [AST.Tfloat];
    "logit",
    AST.Tfloat,
    [AST.Tfloat];
    "expit",
    AST.Tfloat,
    [AST.Tfloat];
    "sqrt",
    AST.Tfloat,
    [AST.Tfloat];
    "uniform_lpdf",
    AST.Tfloat,
    [AST.Tfloat; AST.Tfloat; AST.Tfloat];
    "normal_lpdf",
    AST.Tfloat,
    [AST.Tfloat; AST.Tfloat; AST.Tfloat];
    "cauchy_lpdf",
    AST.Tfloat,
    [AST.Tfloat; AST.Tfloat; AST.Tfloat];
    "exponential_lpdf",
    AST.Tfloat,
    [AST.Tfloat; AST.Tfloat];
    "bernoulli_lpmf",
    AST.Tfloat,
    [AST.Tint; AST.Tfloat];
    "poisson_lpmf",
    AST.Tfloat,
    [AST.Tint; AST.Tfloat];
    "bernoulli_logit_lpmf",
    AST.Tfloat,
    [AST.Tint; AST.Tfloat];
  ]
         
let convert_AST_to_C x =
  match x with
  | AST.Tfloat -> tdouble 
  | AST.Tint -> tint
  | _ -> raise (NIY_stanlib "AST_to_C: incomplete for this type")

let mk_ctypelist xs =
  List.fold_left (fun tail h -> Ctypes.Tcons (h, tail)) Ctypes.Tnil xs

let mk_ctypelist_from_astlist xs =
    mk_ctypelist (List.rev (List.map convert_AST_to_C xs))
  
let mk_global_func ret str ast_args_list =
    AST.Gfun (Ctypes.External
       (AST.EF_external
          (List.init (String.length str) (String.get str), {
            AST.sig_args=ast_args_list;
            AST.sig_res=AST.Tret ret;
            AST.sig_cc=AST.cc_default;
          }),
       mk_ctypelist_from_astlist ast_args_list,
       convert_AST_to_C ret,
       AST.cc_default
    ))
                           
let library_function_declaration (name, tyres, tyargs) =
  (Camlcoq.intern_string name, mk_global_func tyres name tyargs)
                   
let all_math_fns = List.map library_function_declaration library_math_functions

let convert_AST_to_Stan ty =
  match ty with
  | AST.Tfloat -> StanE.Breal
  | AST.Tint -> StanE.Bint
  | _ -> raise (NIY_stanlib "Missing type conversion")
       
let rec search library name =
  match library with
  | [] -> raise (NIY_stanlib ("Missing function: " ^ name))
  | f :: l ->
     begin
     match f with
     | f_name, tyret, tyargs ->
        print_string ("Comparing: " ^ f_name ^ "\n");
        flush(stdout);
        if ((f_name = name) || (f_name = (name^"_lpdf")) || (f_name = (name^"_lpmf")))
                                then f else search l name
     end

let rec type_of_parameters tyargs =
  match tyargs with
  | [] -> StanE.Bnil
  | arg :: args -> StanE.Bcons (convert_AST_to_Stan arg, type_of_parameters args)
    
let type_of_library_function name =
  let (f,tyret,tyargs) = search library_math_functions name in
  (f,StanE.Bfunction (type_of_parameters tyargs, convert_AST_to_Stan tyret))



