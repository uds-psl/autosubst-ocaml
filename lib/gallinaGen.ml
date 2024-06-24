open Util

type identifier = string
type identifiers = identifier list

type constr_expr = Constrexpr.constr_expr
type constr_exprs = constr_expr list
type binder_expr = Constrexpr.local_binder_expr
type branch_expr = Constrexpr.branch_expr

let qualid_ s = Libnames.qualid_of_string s
let reft_ t = Constrexpr_ops.mkRefC t
let ref_ s =  reft_ (qualid_ s)
let name_id_ s = Names.Id.of_string s
let lident_ s = CAst.make (name_id_ s)
let name_ s = Names.Name.mk_name (name_id_ s)

let underscore_ = CAst.make Constrexpr.(CHole None)
let prop_ = CAst.make Constrexpr.(CSort Constrexpr_ops.expr_Prop_sort)
let type_ = CAst.make Constrexpr.(CSort Constrexpr_ops.expr_Type_sort)

let app_ f xs =
  Constrexpr_ops.mkAppC (f, xs)
let app1_ f x =
  Constrexpr_ops.mkAppC (f, [x])
let appExpl_ n xs =
  CAst.make @@ Constrexpr.CAppExpl ((qualid_ n, None), xs)
let app_ref ?(expl=false) s t =
  if expl then appExpl_ s t
  else app_ (ref_ s) t


let eq_ t1 t2 =
  CAst.make (Constrexpr.CNotation
               (Some (Constrexpr.LastLonelyNotation),
                (Constrexpr.InConstrEntry, "_ = _"),
                ([ t1; t2 ], [], [], [])))

let lname_ s = CAst.make (Names.Name (name_id_ s))
let name_decl_ s = lname_ s, None


type constructor_expr = Vernacexpr.constructor_expr
let constructor_ cname ctype = (([],Vernacexpr.NoCoercion,Vernacexpr.NoInstance), (lident_ cname, ctype))

let forall_ binders rtype =
  Constrexpr_ops.mkProdCN binders rtype

let forall1_ binder rtype =
  forall_ [binder] rtype

let arr_ tys tyend =
  List.fold_right (fun t1 t2 ->
      CAst.make (Constrexpr.CNotation
                   (Some (Constrexpr.LastLonelyNotation),
                    (Constrexpr.InConstrEntry, "_ -> _"),
                    ([ t1; t2 ], [], [], []))))
    tys tyend

let arr1_ ty1 ty2 = arr_ [ty1] ty2

type inductive_body = Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list
let inductiveBody_ iname iparams ?rtype iconstructors =
  (((Vernacexpr.NoCoercion, (CAst.make (name_id_ iname), None)), (* ident decl with coercion *)
    (iparams, None), (* inductive params_expr *)
    rtype, (* type I guess *)
    Vernacexpr.Constructors iconstructors), [])

let definition_expr_ dbinders ?rtype dbody =
  let open Vernacexpr in
  DefineBody (dbinders, None, dbody, rtype)


type fixpoint_expr = Vernacexpr.fixpoint_expr
let fixpointBody_ name binders rtype body struc =
  let open Vernacexpr in
  let feg = { fname=lident_ name;
              univs=None;
              binders;
              rtype;
              body_def=Some body;
              notations=[] } in
  let rec_order = Some (CAst.make (Constrexpr.CStructRec (lident_ struc))) in
  rec_order, feg


let match_ cexpr ?rtype bexprs =
  let open Constrexpr in
  CAst.make (CCases (Constr.MatchStyle, rtype, [(cexpr, None, None)], bexprs))

let binder_ ?(implicit=false) ?btype bnames =
  let open Constrexpr in
  let bk = Default (if implicit then Glob_term.MaxImplicit else Glob_term.Explicit) in
  let btype = Option.default (CAst.make @@ CHole None) btype in
  CLocalAssum (List.map lname_ bnames, None, bk, btype)

let binder1_ ?implicit ?btype bname =
  binder_ ?implicit ?btype [bname]

let branch_ cname cargs_s bcont =
  let open Constrexpr in
  let cargs = List.map (fun s -> CAst.make (CPatAtom (Some (qualid_ s)))) cargs_s in
  let cases_pattern = CAst.make (CPatCstr (qualid_ cname, None, cargs)) in
  CAst.make ([[cases_pattern]], bcont)

let lambda_ binders body =
  Constrexpr_ops.mkLambdaCN binders body

let ident_decl_ s : Constrexpr.ident_decl  =
  (lident_ s, None)


let pr_constr_expr cexpr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Ppconstr.pr_lconstr_expr env sigma cexpr

let pr_exact_expr cexpr =
  let open Pp in
  str "exact (" ++ pr_constr_expr cexpr ++ str ")" ++ vernacend

let parse_constr_expr expr_s = Pcoq.parse_string (Pcoq.Constr.lconstr) expr_s

let setup_coq () =
  (* install a printer for feedback from Coq.
   * Sometimes useful in debugging and it seems to mostly send messages so we only handle those *)
  let _ = Feedback.(add_feeder (function { contents; _ } ->
    match contents with
    | Message (_, _, _, pp) -> print_endline ("Message from Coq: " ^ Pp.string_of_ppcmds pp)
    | _ -> print_endline "Received feedback from Coq. Add cases to the printing function in coqgen.setup_coq if you want to see more.")) in
  let scope = "autosubst_scope" in
  let () = Notation.declare_scope scope in
  (* for both definition we create dummy expressions that will never be used.
   * But according to the documentation the bodies of notations might be typechecked in the
   * future and this should work *)
  let _ = (Flags.in_debugger := true) in
  let dummy_eq =
    app_ (lambda_ [ binder_ [ "a"; "b" ] ] prop_) [ (ref_ "x"); (ref_ "y") ] in
  let () = Metasyntax.add_notation_interpretation ~local:true (Global.env ())
            (Metasyntax.add_notation_syntax ~local:true ~infix:false None
              { ntn_decl_string = CAst.make "x = y" ;
                ntn_decl_interp = dummy_eq ;
                ntn_decl_scope = Some scope ;
                ntn_decl_modifiers = [ CAst.make (Vernacexpr.SetLevel 70)
                ; CAst.make (Vernacexpr.SetOnlyPrinting)
                ; CAst.make (Vernacexpr.SetAssoc Gramlib.Gramext.NonA) ]
              }) in
  let dummy_arrow = forall1_ (binder1_ "A") (ref_ "B") in
  let () = Metasyntax.add_notation_interpretation ~local:true (Global.env ())
  (Metasyntax.add_notation_syntax ~local:true ~infix:false None
    { ntn_decl_string = CAst.make "A -> B" ;
      ntn_decl_interp = dummy_arrow ;
      ntn_decl_scope = Some scope ;
      ntn_decl_modifiers = [ CAst.make (Vernacexpr.SetLevel 70)
      ; CAst.make (Vernacexpr.SetOnlyPrinting)
      ; CAst.make (Vernacexpr.SetAssoc Gramlib.Gramext.RightA) ]
    }) in
  ()
