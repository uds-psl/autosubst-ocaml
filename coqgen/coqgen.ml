let ref_ s = Constrexpr_ops.mkRefC (Libnames.qualid_of_string s)

let type_ = ref_ "Type"
let nat_ = ref_ "nat"

let constructor_ cname ctype = (false, (CAst.make (Names.Id.of_string cname), ctype))

let prod_ tys tyend =
  Constrexpr_ops.mkProdCN
    (List.map (fun ty ->
         Constrexpr.CLocalAssum ([ CAst.make (Names.Anonymous) ], Default Glob_term.Explicit, ty))
        tys)
    tyend

let inductive_ iname iparams ?itype iconstructors =
  let open Vernacexpr in
  VernacInductive (Inductive_kw, [
      (((false, (CAst.make (Names.Id.of_string iname), None)), (* ident decl with coercion *)
       (iparams, None), (* inductive params_expr *)
       itype, (* type I guess *)
       Vernacexpr.Constructors iconstructors), [])
    ])


let fix_ fname binders rtype body_def =
  let open Vernacexpr in
  let feg = { fname;
              univs=None;
              rec_order=None;
              binders;
              rtype;
              body_def=Some body_def;
              notations=[]} in
  VernacFixpoint (NoDischarge, [feg])

let lident_ s = CAst.make (Names.Id.of_string s)

let lname_ s = CAst.make (Names.Name (Names.Id.of_string s))

let qualid_ s = Libnames.qualid_of_string s

let match_ cexpr ?rtype bexprs =
  let open Constrexpr in
  CAst.make (CCases (Constr.MatchStyle, rtype, [(cexpr, None, None)], bexprs))

let binder_ bname ?(implicit=false) btype =
  let open Constrexpr in
  let bk = Default (if implicit then Glob_term.MaxImplicit else Glob_term.Explicit) in
  CLocalAssum ([lname_ bname], bk, ref_ "tm")

let branch_ cname cargs_s bcont =
  let open Constrexpr in
  let cargs = List.map (fun s -> CAst.make (CPatAtom (Some (qualid_ s)))) cargs_s in
  let cases_pattern = CAst.make (CPatCstr (qualid_ cname, None, cargs)) in
  CAst.make ([[cases_pattern]], bcont)

let app_ f xs =
  Constrexpr_ops.mkAppC (f, xs)
let app1_ f x =
  Constrexpr_ops.mkAppC (f, [x])

let ident_decl_ s : Constrexpr.ident_decl  =
  (lident_ s, None)

let lemma_ lname lbinders ltype lbody =
  let open Vernacexpr in
  let pexpr = (ident_decl_ lname, (lbinders, ltype)) in
  let lbegin = VernacStartTheoremProof (Decls.Lemma, [pexpr]) in
  (* let lbody = VernacExactProof lbody in *)
  let lend = VernacEndProof (Proved (Opaque, None)) in
  lbegin, lbody, lend

let vernacend = Pp.str ".\n"

let pr_vernac_expr vexpr =
  let open Pp in
  Ppvernac.pr_vernac_expr vexpr ++ vernacend

let pr_exact_expr cexpr =
  let open Pp in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  str "exact (" ++ Ppconstr.pr_lconstr_expr env sigma cexpr ++ str ")" ++ vernacend

let print_lemma (lbegin, lbody, lend) =
  let pbegin = pr_vernac_expr lbegin in
  let pbody = pr_exact_expr lbody in
  (* let pbody = pr_vernac_expr lbody in *)
  let pend = pr_vernac_expr lend in
  let open Pp in
  pbegin ++ pbody ++ pend

module GenTests = struct
  (* Lemma congr_lam  { s0 : tm   } { t0 : tm   } (H1 : s0 = t0) : lam  s0 = lam  t0 . *)
  let print_utlc_tm () : Pp.t =
    let utlc = inductive_ "tm" [] ~itype:(ref_ "Type") [
        constructor_ "var_tm" (prod_ [ref_ "fin"] (ref_ "tm"));
        constructor_ "app" (prod_ [ref_ "tm"; ref_ "tm"] (ref_ "tm"));
        constructor_ "lam" (prod_ [ref_ "tm"] (ref_ "tm"))
      ] in
    pr_vernac_expr utlc

  let print_utlc_fix () : Pp.t =
    let fname = lident_ "ren_tm" in
    let binders = [ binder_ "xitm" (prod_ [ ref_ "fin" ] (ref_ "fin"));
                    binder_ "s" (ref_ "tm") ] in
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
    let fix = fix_ fname binders rtype body_def in
    pr_vernac_expr fix

  let print_utlc_lemma () : Pp.t =
    let lname = "congr_lam" in
    let tm = ref_ "tm" in
    let lbinders = [ binder_ "s0" ~implicit:true tm;
                     binder_ "t0" ~implicit:true tm;
                     binder_ "H1" (app_ (ref_ "eq") [ref_ "s0";ref_ "t0"]) ] in
    let ltype = app_ (ref_ "eq") [
        app1_ (ref_ "lam") (ref_ "s0");
        app1_ (ref_ "lam") (ref_ "t0")
      ] in
    let lbody = ref_ "False" in
    let lemma = lemma_ lname lbinders ltype lbody in
    print_lemma lemma

end
