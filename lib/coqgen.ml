
type identifier = string
type identifiers = identifier list

type constr_expr = Constrexpr.constr_expr
type constr_exprs = constr_expr list
type binder_expr = Constrexpr.local_binder_expr
type branch_expr = Constrexpr.branch_expr

let qualid_ s = Libnames.qualid_of_string s
let reft_ t = Constrexpr_ops.mkRefC t
let ref_ s =  reft_ (qualid_ s)
let id_ s = Names.Id.of_string s
let lident_ s = CAst.make (id_ s)
(* let num_ n = *)
  (* CAst.make (Constrexpr.(CPrim (Numeral (NumTok.(Signed.of_bigint CDec (Bigint.of_int n)))))) *)
  (* Constrexpr.(CPrim (Numeral (NumTok.Signed.of_int_string (Int.to_string n)))) *)
let app_ f xs =
  Constrexpr_ops.mkAppC (f, xs)
let app1_ f x =
  Constrexpr_ops.mkAppC (f, [x])
let appExpl_ n xs =
  CAst.make @@ Constrexpr.CAppExpl ((None, qualid_ n, None), xs)

let ident_decl_ s : Constrexpr.ident_decl  =
  (lident_ s, None)
let eq_ t1 t2 =
  app_ (ref_ "eq") [t1; t2]

let lname_ s = CAst.make (Names.Name (Names.Id.of_string s))
let name_decl_ s = lname_ s, None


type constructor_expr = bool * (Names.lident * Constrexpr.constr_expr)
let constructor_ cname ctype = (false, (lident_ cname, ctype))

let forall_ binders rtype =
  Constrexpr_ops.mkProdCN binders rtype

let arr_ tys tyend =
  ref_ "a"
  (* List.fold_right (fun t1 t2 ->
   *     CAst.make (Constrexpr.CNotation
   *                  (Some (Constrexpr.LastLonelyNotation),
   *                   (Constrexpr.InConstrEntry, "_ -> _"),
   *                   ([ t1; t2 ], [], [], []))))
   *   tys tyend *)
(* let arr1_ ty1 ty2 = arr_ [ty1] ty2 *)
let arr1_ ty1 ty2 =
  CAst.make (Constrexpr.CNotation
               (Some (Constrexpr.LastLonelyNotation),
                (Constrexpr.InConstrEntry, "_ -> _"),
                ([ ty1; ty2 ], [], [], [])))

type inductive_body = Vernacexpr.inductive_expr * Vernacexpr.decl_notation list
let inductiveBody_ iname iparams ?rtype iconstructors =
  (((false, (CAst.make (Names.Id.of_string iname), None)), (* ident decl with coercion *)
    (iparams, None), (* inductive params_expr *)
    rtype, (* type I guess *)
    Vernacexpr.Constructors iconstructors), [])

let inductive_ inductiveBodies =
  Vernacexpr.(VernacInductive (Inductive_kw, inductiveBodies))

let definition_expr_ dbinders ?rtype dbody =
  let open Vernacexpr in
  DefineBody (dbinders, None, dbody, rtype)

let definition_ dname dbinders ?rtype dbody =
  let open Vernacexpr in
  let dname = name_decl_ dname in
  let dexpr = definition_expr_ dbinders ?rtype dbody in
  VernacDefinition ((NoDischarge, Decls.Definition), dname, dexpr)

type fixpoint_expr = Vernacexpr.fixpoint_expr
let fixpointBody_ name binders rtype body =
  let open Vernacexpr in
  let feg = { fname=lident_ name;
              univs=None;
              rec_order=None;
              binders;
              rtype;
              body_def=Some body;
              notations=[]} in
  feg

let fixpoint_ ~is_rec fexprs =
  if is_rec
  then Vernacexpr.(VernacFixpoint (NoDischarge, fexprs))
  else match fexprs with
    | [{ fname={ v=fname; _ }; binders; rtype; body_def=Some body; _}] ->
      definition_ (Names.Id.to_string fname) binders ~rtype body
    | [fexpr] -> failwith "Malformed fixpoint expression"
    | _ -> failwith "A non recursive fixpoint degenerates to a definition so it should only have one body"


let match_ cexpr ?rtype bexprs =
  let open Constrexpr in
  CAst.make (CCases (Constr.MatchStyle, rtype, [(cexpr, None, None)], bexprs))

let binder_ ?(implicit=false) ?btype bnames =
  let open Constrexpr in
  let bk = Default (if implicit then Glob_term.MaxImplicit else Glob_term.Explicit) in
  let btype = Option.default (CAst.make @@ CHole (None, Namegen.IntroAnonymous, None)) btype in
  CLocalAssum (List.map lname_ bnames, bk, btype)

(* let binder_ bnames ?(implicit=false) btype =
 *   let open Constrexpr in
 *   let bk = Default (if implicit then Glob_term.MaxImplicit else Glob_term.Explicit) in
 *   CLocalAssum (List.map ~f:lname_ bnames, bk, btype) *)

let binder1_ ?implicit ?btype bname =
  binder_ ?implicit ?btype [bname]

let branch_ cname cargs_s bcont =
  let open Constrexpr in
  let cargs = List.map (fun s -> CAst.make (CPatAtom (Some (qualid_ s)))) cargs_s in
  let cases_pattern = CAst.make (CPatCstr (qualid_ cname, None, cargs)) in
  CAst.make ([[cases_pattern]], bcont)

let lambda_ binders body =
  Constrexpr_ops.mkLambdaCN binders body

type vernac_expr = Vernacexpr.vernac_expr
let lemma_ lname lbinders ltype lbody =
  let open Vernacexpr in
  let pexpr = (ident_decl_ lname, (lbinders, ltype)) in
  let lbegin = VernacStartTheoremProof (Decls.Lemma, [pexpr]) in
  let lbody = VernacExactProof lbody in
  let lend = VernacEndProof (Proved (Opaque, None)) in
  [lbegin; lbody; lend]

let vernacend = Pp.str ".\n"

let pr_constr_expr cexpr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Ppconstr.pr_lconstr_expr env sigma cexpr

let pr_exact_expr cexpr =
  let open Pp in
  str "exact (" ++ pr_constr_expr cexpr ++ str ")" ++ vernacend

(** I catch the VernacExactProof constructor because the way Coq normally prints it does not
 ** work well with proof general. So I explicitly add an `exact (...)` *)
let pr_vernac_expr =
  let open Vernacexpr in
  let open Pp in
  function
  | VernacExactProof cexpr ->
    str "Proof" ++ vernacend ++ pr_exact_expr cexpr
  | vexpr ->
    Ppvernac.pr_vernac_expr vexpr ++ vernacend

let parse_constr_expr expr_s = Pcoq.parse_string (Pcoq.Constr.lconstr) expr_s

let setup_notations () =
  let () = print_endline "Defining Notations" in
  let scope = "autosubst_scope" in
  let () = Notation.declare_scope scope in
  (* let dummy_eq = app1_ (ref_ "x") (ref_ "y") in *)
  (* let () = Metasyntax.add_notation ~local:false None (Global.env()) dummy_eq (CAst.make "x = y", [Vernacexpr.SetLevel 70]) (Some scope) in *)
  let dummy_arrow = app1_ (ref_ "A") (ref_ "B") in
  let () = Metasyntax.add_notation ~local:false None (Global.env()) dummy_arrow (CAst.make "A -> B", [Vernacexpr.SetLevel 1000]) (Some scope) in
  print_endline "Notations defined"


(* disable unused warning *)
module [@warning "-32"] GenTests = struct
  (* Lemma congr_lam  { s0 : tm   } { t0 : tm   } (H1 : s0 = t0) : lam  s0 = lam  t0 . *)
  let print_utlc_tm () : Pp.t =
    let utlc = inductive_ [inductiveBody_ "tm" [] ~rtype:(ref_ "Type") [
        constructor_ "var_tm" (arr1_ (ref_ "fin") (ref_ "tm"));
        constructor_ "app" (arr_ [ref_ "tm"; ref_ "tm"] (ref_ "tm"));
        constructor_ "lam" (arr1_ (ref_ "tm") (ref_ "tm"))
      ]] in
    pr_vernac_expr utlc

  let print_utlc_fix () : Pp.t =
    let fname = "ren_tm" in
    let binders = [ binder1_ ~btype:(arr1_ (ref_ "fin") (ref_ "fin")) "xitm";
                    binder1_ ~btype:(ref_ "tm") "s" ] in
    let rtype = ref_ "tm" in
    let body_def = match_ (ref_ "s") ~rtype:(ref_ "tm") [
        branch_ "var_tm" ["s"] (app1_ (ref_ "var_tm") (app1_ (ref_ "xitm") (ref_ "s")));
        branch_ "app" ["s0"; "s1"] (app_ (ref_ "app") [
            app_ (ref_ "ren_tm") [(ref_ "xitm"); (ref_ "s0")];
            app_ (ref_ "ren_tm") [(ref_ "xitm"); (ref_ "s1")]
          ]);
        branch_ "lam" ["s0"] (app1_ (ref_ "lam")
                                (app_ (ref_ "ren_tm") [
                                    app1_ (ref_ "upRen_tm_tm") (ref_ "xitm");
                                    ref_ "s0"
                                  ]))
      ]
    in
    let fix = fixpoint_ ~is_rec:true [fixpointBody_ fname binders rtype body_def] in
    pr_vernac_expr fix

  let print_utlc_lemma () : Pp.t =
    let lname = "congr_lam" in
    let tm = ref_ "tm" in
    let lbinders = [ binder_ ~implicit:true ~btype:tm ["s0";"t0"] ;
                     binder1_ ~btype:(eq_ (ref_ "s0") (ref_ "t0")) "H1"  ] in
    let ltype = app_ (ref_ "eq") [
        app1_ (ref_ "lam") (ref_ "s0");
        app1_ (ref_ "lam") (ref_ "t0")
      ] in
    let lbody = ref_ "False" in
    let lemma = lemma_ lname lbinders ltype lbody in
    Pp.seq @@ List.map pr_vernac_expr lemma

  (* This sadly just prints cc_plugin@cc:0 (or similar) which is probably a correct internal representation of the congruence tactic but now what I was looking for. *)
  (* let print_congruence () : Pp.t =
   *   let env = Global.env () in
   *   let sigma = Evd.from_env env in *)
    (* let open Ltac_plugin.Tacexpr in
     * let texpr = TacML (CAst.make ({ mltac_name={ mltac_plugin="cc_plugin"; mltac_tactic="cc"; }; mltac_index=0; }, [])) in
     * Ltac_plugin.Pptactic.pr_raw_tactic env sigma texpr *)
    (* Ltac_plugin.Pptactic.pr_glob_tactic env texpr *)

end
