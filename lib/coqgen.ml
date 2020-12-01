open Base

let reft_ t = Constrexpr_ops.mkRefC t
let ref_ s =
  reft_ (Libnames.qualid_of_string @@ String.strip s)
let id_ s = Names.Id.of_string s
let lident_ s = CAst.make (Names.Id.of_string s)
let num_ n =
  CAst.make (Constrexpr.(CPrim (Numeral (NumTok.(Signed.of_bigint CDec (Bigint.of_int n))))))
  (* Constrexpr.(CPrim (Numeral (NumTok.Signed.of_int_string (Int.to_string n)))) *)
let app_ f xs =
  Constrexpr_ops.mkAppC (f, xs)
let app1_ f x =
  Constrexpr_ops.mkAppC (f, [x])

let ident_decl_ s : Constrexpr.ident_decl  =
  (lident_ s, None)
let eq_ t1 t2 =
  app_ (ref_ "eq") [t1; t2]

let lname_ s = CAst.make (Names.Name (Names.Id.of_string s))
let name_decl_ s = lname_ s, None

let qualid_ s = Libnames.qualid_of_string s

let type_ = ref_ "Type"
let nat_ = ref_ "nat"

let constructor_ cname ctype = (false, (lident_ cname, ctype))

let prod_ binders rtype =
  Constrexpr_ops.mkProdCN binders rtype

let arr_ tys tyend =
  prod_ (List.map ~f:(fun ty ->
      Constrexpr.CLocalAssum ([ CAst.make (Names.Anonymous) ], Default Glob_term.Explicit, ty))
      tys)
    tyend

let inductiveBody_ iname iparams ?rtype iconstructors =
  (((false, (CAst.make (Names.Id.of_string iname), None)), (* ident decl with coercion *)
    (iparams, None), (* inductive params_expr *)
    rtype, (* type I guess *)
    Vernacexpr.Constructors iconstructors), [])

let inductive_ inductiveBodies =
  Vernacexpr.(VernacInductive (Inductive_kw, inductiveBodies))

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

let fixpoint_ fegs =
  Vernacexpr.(VernacFixpoint (NoDischarge, fegs))


let match_ cexpr ?rtype bexprs =
  let open Constrexpr in
  CAst.make (CCases (Constr.MatchStyle, rtype, [(cexpr, None, None)], bexprs))

let binder_ ?(implicit=false) ?btype bnames =
  let open Constrexpr in
  let bk = Default (if implicit then Glob_term.MaxImplicit else Glob_term.Explicit) in
  let btype = Option.value btype ~default: (CAst.make @@ CHole (None, Namegen.IntroAnonymous, None)) in
  CLocalAssum (List.map ~f:lname_ bnames, bk, btype)

(* let binder_ bnames ?(implicit=false) btype =
 *   let open Constrexpr in
 *   let bk = Default (if implicit then Glob_term.MaxImplicit else Glob_term.Explicit) in
 *   CLocalAssum (List.map ~f:lname_ bnames, bk, btype) *)

let binder1_ ?implicit ?btype bname =
  binder_ ?implicit ?btype [bname]

let branch_ cname cargs_s bcont =
  let open Constrexpr in
  (* TODO it might be that when I want an underscore pattern I need the `CPatAtom None` *)
  let cargs = List.map ~f:(fun s -> CAst.make (CPatAtom (Some (qualid_ s)))) cargs_s in
  let cases_pattern = CAst.make (CPatCstr (qualid_ cname, None, cargs)) in
  CAst.make ([[cases_pattern]], bcont)

let lambda_ binders body =
  Constrexpr_ops.mkLambdaCN binders body

let lemma_ lname lbinders ltype lbody =
  let open Vernacexpr in
  let pexpr = (ident_decl_ lname, (lbinders, ltype)) in
  let lbegin = VernacStartTheoremProof (Decls.Lemma, [pexpr]) in
  let lbody = VernacExactProof lbody in
  let lend = VernacEndProof (Proved (Opaque, None)) in
  [lbegin; lbody; lend]

let definition_expr_ dbinders ?rtype dbody =
  let open Vernacexpr in
  DefineBody (dbinders, None, dbody, rtype)

let definition_ dname dbinders ?rtype dbody =
  let open Vernacexpr in
  let dname = name_decl_ dname in
  let dexpr = definition_expr_ dbinders ?rtype dbody in
  VernacDefinition ((DoDischarge, Decls.Definition), dname, dexpr)

let vernacend = Pp.str ".\n"

let pr_exact_expr cexpr =
  let open Pp in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  str "exact (" ++ Ppconstr.pr_lconstr_expr env sigma cexpr ++ str ")" ++ vernacend

(* TODO I could also use pr_vernac which already appends a dot (but no newline I think) *)
let pr_vernac_expr =
  let open Vernacexpr in
  let open Pp in
  function
  | VernacExactProof cexpr ->
    str "Proof" ++ vernacend ++ pr_exact_expr cexpr
  | vexpr ->
    Ppvernac.pr_vernac_expr vexpr ++ vernacend

let section_ name vexprs =
  Vernacexpr.([ VernacBeginSection (lident_ name) ] @ vexprs @ [ VernacEndSegment (lident_ name) ])

module GenTests = struct
  (* Lemma congr_lam  { s0 : tm   } { t0 : tm   } (H1 : s0 = t0) : lam  s0 = lam  t0 . *)
  let print_utlc_tm () : Pp.t =
    let utlc = inductive_ [inductiveBody_ "tm" [] ~rtype:(ref_ "Type") [
        constructor_ "var_tm" (arr_ [ref_ "fin"] (ref_ "tm"));
        constructor_ "app" (arr_ [ref_ "tm"; ref_ "tm"] (ref_ "tm"));
        constructor_ "lam" (arr_ [ref_ "tm"] (ref_ "tm"))
      ]] in
    pr_vernac_expr utlc

  let print_utlc_fix () : Pp.t =
    let fname = "ren_tm" in
    let binders = [ binder1_ ~btype:(arr_ [ ref_ "fin" ] (ref_ "fin")) "xitm";
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
    let fix = fixpoint_ [fixpointBody_ fname binders rtype body_def] in
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
    Pp.seq @@ List.map ~f:pr_vernac_expr lemma

end