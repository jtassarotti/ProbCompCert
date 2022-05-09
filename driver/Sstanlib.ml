open List
open C2C
open Int32
   
exception NIY_stanlib of string

let sizeof_basic t =
  begin match t with
  | StanE.Bint -> 4l
  | StanE.Breal -> 8l
  | StanE.Barray (ty, n) -> Int32.mul 8l  (Camlcoq.camlint_of_coqint n)
  | _ -> raise (Invalid_argument "Sparse does not calculate the size of this type")
  end

let sizeof_struct vars =
  List.fold_left (fun total var -> Int32.add total (sizeof_basic (snd var))) 0l vars

let init_int = AST.Init_space (Camlcoq.coqint_of_camlint 4l)
let init_dbl = AST.Init_space (Camlcoq.coqint_of_camlint 8l)
let init_ptr = AST.Init_space (Camlcoq.coqint_of_camlint 8l)
let init_struct members = AST.Init_space (Camlcoq.coqint_of_camlint (sizeof_struct members))

let ctarray (t, sz) = Ctypes.Tarray (t, sz, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let tdouble = Stypes.Treal
let bdouble = StanE.Breal
let ctdouble = Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let tint = Stypes.Tint
let bint = StanE.Bint
let ctint = Ctypes.Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let rt = Some tdouble
let to_charlist s = List.init (String.length s) (String.get s)
let ftype = Ctypes.Tfunction (Ctypes.Tnil, (Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr)), AST.cc_default)

let ast_to_ctype x =
  match x with
  | AST.Tfloat -> ctdouble
  | AST.Tint -> ctint
  | _ -> raise (NIY_stanlib "ast_to_ctype: incomplete for this type")

let mk_ctypelist xs =
  List.fold_left (fun tail h -> Ctypes.Tcons (h, tail)) Ctypes.Tnil xs

let mk_ctypelist_from_astlist xs =
    mk_ctypelist (List.rev (List.map ast_to_ctype xs))

let mk_cfunc xs = Ctypes.Tfunction (mk_ctypelist_from_astlist xs, ctdouble, AST.cc_default)

let mk_global_func ret str ast_args_list =
    AST.Gfun (Ctypes.External
       (AST.EF_external
          (to_charlist str, {
            AST.sig_args=ast_args_list;
            AST.sig_res=ret;
            AST.sig_cc=AST.cc_default;
          }),
       mk_ctypelist_from_astlist ast_args_list,
       ctdouble,
       AST.cc_default
    ))

let mk_global_math_func = mk_global_func (AST.Tret AST.Tfloat)

let st_uniform_lpdf = "uniform_lpdf"
let id_uniform_lpdf = Camlcoq.intern_string st_uniform_lpdf
let ty_uniform_lpdf = StanE.Bfunction (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, StanE.Bnil))))), Some bdouble)
let gl_uniform_lpdf = mk_global_math_func st_uniform_lpdf [AST.Tfloat; AST.Tfloat; AST.Tfloat]

let st_normal_lpdf = "normal_lpdf"
let id_normal_lpdf = Camlcoq.intern_string st_normal_lpdf
let ty_normal_lpdf = StanE.Bfunction (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, StanE.Bnil))))), Some bdouble)
let gl_normal_lpdf = mk_global_math_func st_normal_lpdf [AST.Tfloat; AST.Tfloat; AST.Tfloat]                    

let st_bernoulli_lpmf = "bernoulli_lpmf"
let id_bernoulli_lpmf = Camlcoq.intern_string st_bernoulli_lpmf
let ty_bernoulli_lpmf = StanE.Bfunction (StanE.Bcons (bint, (StanE.Bcons (bdouble, StanE.Bnil))), Some StanE.Breal)
let gl_bernoulli_lpmf = mk_global_math_func st_bernoulli_lpmf [AST.Tint; AST.Tfloat]

let transf_dist_idents = Hashtbl.create 3;;
Hashtbl.add transf_dist_idents "uniform" (id_uniform_lpdf, ty_uniform_lpdf);
Hashtbl.add transf_dist_idents "bernoulli" (id_bernoulli_lpmf, ty_bernoulli_lpmf);
Hashtbl.add transf_dist_idents "normal" (id_normal_lpdf, ty_normal_lpdf)
let stanlib_functions = [
    (id_uniform_lpdf,   gl_uniform_lpdf);
    (id_bernoulli_lpmf, gl_bernoulli_lpmf);
    (id_normal_lpdf, gl_normal_lpdf)
  ]
let pr_dist_functions = [(CStan.DBernPMF, id_bernoulli_lpmf);(CStan.DUnifPDF, id_uniform_lpdf)]

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                              math functions                                  *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
let mk_fn ret args s = (s, Camlcoq.intern_string s, mk_global_func ret s args, mk_cfunc args)
let mk_math_fn = mk_fn (AST.Tret AST.Tfloat)
let mk_unary_math_fn t = mk_math_fn [t]
let unary_math_fn = mk_unary_math_fn AST.Tfloat

let (st_log, id_log, gl_log, clog)       = unary_math_fn "log"
let (st_exp, id_exp, gl_exp, cexp)       = unary_math_fn "exp"
let (st_logit, id_logit, gl_logit, clogit) = unary_math_fn "logit"
let (st_expit, id_expit, gl_expit, cexpit) = unary_math_fn "expit"

let st_init_unconstrained = "init_unconstrained"
let id_init_unconstrained = Camlcoq.intern_string st_init_unconstrained
let ty_init_unconstrained = StanE.Bfunction (StanE.Bnil, Some bdouble)
let gl_init_unconstrained = mk_global_math_func st_init_unconstrained []

(* (\* temporary printing support *\) *)
(* let (st_print_double, id_print_double, gl_print_double, cprint_double) = mk_fn AST.Tvoid [AST.Tfloat] "print_double" *)
(* let (st_print_int, id_print_int, gl_print_int, cprint_int) = mk_fn AST.Tvoid [AST.Tint] "print_int" *)
(* (\* let (st_print_array_int, id_print_array_int, gl_print_array_int, cprint_array_int) = mk_fn AST.Tvoid [AST.Tint; AST.Tany64] "print_array_int" *\) *)
(* let (st_print_start, id_print_start, gl_print_start, cprint_start) = mk_fn AST.Tvoid [] "print_start" *)
(* let (st_print_end, id_print_end, gl_print_end, cprint_end) = mk_fn AST.Tvoid [] "print_end" *)

let __math_functions = [ (CStan.MFLog, id_log, gl_log, clog);
                         (CStan.MFLogit, id_logit, gl_logit, clogit);
                         (CStan.MFExp, id_exp, gl_exp, cexp);
                         (CStan.MFExpit, id_expit, gl_expit, cexpit);
                         (CStan.MFInitUnconstrained, id_init_unconstrained, gl_init_unconstrained, mk_cfunc []);

                         (* (CStan.MFPrintStart, id_print_start, gl_print_start, cprint_start); *)
                         (* (CStan.MFPrintDouble, id_print_double, gl_print_double, cprint_double); *)
                         (* (CStan.MFPrintInt, id_print_int, gl_print_int, cprint_int); *)
                         (* (\* (CStan.MFPrintArrayInt, id_print_array_int, gl_print_array_int, cprint_array_int); *\) *)
                         (* (CStan.MFPrintEnd, id_print_end, gl_print_end, cprint_end); *)
                        ]

let _as_prog_math_functions (e, i, g, c) = ((e, i), c)
let _as_global_math_functions (e, i, g, c) = (i, g)

let pr_math_functions = List.map _as_prog_math_functions __math_functions
let all_math_fns = List.map _as_global_math_functions __math_functions

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                               Struct work                                    *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
let mkGlobalStruct i members = AST.Gvar {
  AST.gvar_readonly = false;
  AST.gvar_volatile = false;
  AST.gvar_init = [init_struct members];
  AST.gvar_info = {
    StanE.vd_type = StanE.Bint; (* This is a placeholder, we just need to declare the structure's existence  *)
    StanE.vd_constraint = StanE.Cidentity;
  };
}

let declareStruct s members =
  let id = Camlcoq.intern_string s in
  Hashtbl.add decl_atom id
    { a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_data Sections.Uninit];
      a_access = Sections.Access_default;
      a_inline = No_specifier;
      a_loc = (s,0) };
  (id, mkGlobalStruct id members)

let declareGlobalStruct s =
  let id = Camlcoq.intern_string s in
  Hashtbl.add decl_atom id
    { a_storage = C.Storage_default;
      a_alignment = None;
      a_size = None;
      a_sections = [Sections.Section_data Sections.Uninit];
      a_access = Sections.Access_default;
      a_inline = No_specifier;
      a_loc = (s,0) };
  id

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                               Global Arrays                                  *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
let replicate n ls =
    let rec f l = function
        | 0 -> l
        | n -> f (List.rev_append ls l) (n-1) in
    List.rev (f [] n)

let mk_global_array ty len = AST.Gvar {
  AST.gvar_readonly = false;
  AST.gvar_volatile = false;
  AST.gvar_init = replicate (to_int len) ty;
  AST.gvar_info = {
    StanE.vd_type = StanE.Barray (StanE.Bint, (Camlcoq.coqint_of_camlint len));
    StanE.vd_constraint = StanE.Cidentity;
  };
}


