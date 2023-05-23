open Util
open GallinaGen
open AutomationGen
open Vernacexpr

module TG = TacGen
module AL = AssocList
module S = Settings


type vernac_unit = Vernac of vernac_control list
                 | TacticLtac of string * TacGen.t
                 | TacticNotation of string list * TacGen.t

let control_of_expr vexpr = CAst.make { control = []; attrs = []; expr=vexpr }
let unit_of_vernacs vexprs = Vernac (List.map control_of_expr vexprs)

(** I catch the VernacExactProof constructor because the way Coq normally prints it does not
 ** work well with proof general. So I explicitly add an `exact (...)` *)
let pr_vernac_control =
  let open Pp in
  function
  | CAst.{v = {expr = VernacExactProof cexpr; _}; _} ->
    str "Proof" ++ vernacend ++ pr_exact_expr cexpr
  | vexpr ->
    Ppvernac.pr_vernac vexpr ++ newline

let pr_vernac_unit = function
  | Vernac vs ->
    Pp.seq ((List.map pr_vernac_control vs) @ [ newline ])
  | TacticLtac (name, tac) -> TG.pr_tactic_ltac name tac
  | TacticNotation (names, tac) -> TG.pr_tactic_notation names tac

let pr_vernac_units vunits = Pp.seq (List.map pr_vernac_unit vunits)


let definition_ dname dbinders ?rtype dbody =
  let dname = name_decl_ dname in
  let dexpr = definition_expr_ dbinders ?rtype dbody in
  unit_of_vernacs [ VernacDefinition ((NoDischarge, Decls.Definition), dname, dexpr) ]

let lemma_ ?(opaque=true) lname lbinders ltype lbody =
  let pexpr = (ident_decl_ lname, (lbinders, ltype)) in
  let lbegin = VernacStartTheoremProof (Decls.Lemma, [pexpr]) in
  let lbody = VernacExactProof lbody in
  let lend = VernacEndProof (Proved ((if opaque then Opaque else Transparent), None)) in
  unit_of_vernacs [ lbegin; lbody; lend ]

let fixpoint_ ~is_rec fexprs =
  match fexprs with
  | [] -> failwith "fixpoint called without fixpoint bodies"
  | fexprs_nempty ->
    if is_rec
    then unit_of_vernacs [ VernacFixpoint (NoDischarge, fexprs) ]
    (* if the fixpoint is declared non-recursive we try to turn it into a definition *)
    else match fexprs_nempty with
      | [{ fname={ v=fname; _ }; binders; rtype; body_def=Some body; _}] ->
        definition_ (Names.Id.to_string fname) binders ~rtype body
      | [fexpr] -> failwith "Malformed fixpoint body"
      | _ -> failwith "A non recursive fixpoint degenerates to a definition so it should only have one body"

let inductive_ inductiveBodies =
  unit_of_vernacs [ VernacInductive (Inductive_kw, inductiveBodies) ]

let class_ name binders fields =
  let body = inductiveBody_ name binders fields in
  (* a.d. false argument to Class to make it inductive, not definitional *)
  unit_of_vernacs [ VernacInductive (Class false, [ body ]) ]

let instance_ inst_name cbinders class_type ?(interactive=false) body =
   if interactive
    then
      Vernac [ CAst.make { 
        control=[];
        attrs=[("local", Attributes.VernacFlagEmpty)] ;
        expr=VernacInstance (name_decl_ inst_name, cbinders, class_type, None, Typeclasses.{ hint_priority = None; hint_pattern = None });
      }
      ; control_of_expr (VernacExactProof body)
      ; control_of_expr (VernacEndProof (Proved (Opaque, None))) ]
    else 
      Vernac [CAst.make { 
        control=[];
        attrs=[("local", Attributes.VernacFlagEmpty)] ;
        expr=VernacInstance (name_decl_ inst_name, cbinders, class_type, Some (false, body), Typeclasses.{ hint_priority = None; hint_pattern = None });
      } ]

let notation_ notation modifiers ?scope body =
  unit_of_vernacs [ VernacNotation (body, (CAst.make notation, modifiers), scope) ]

let clear_arguments_ name =
  let qname = CAst.make (Constrexpr.AN (qualid_ name)) in
  unit_of_vernacs [ VernacArguments (qname, [], [], [ `ClearImplicits ]) ]

let impl_arguments_ name args =
  let qname = CAst.make (Constrexpr.AN (qualid_ name)) in
  let impl_args = List.map (fun a ->
      RealArg {
        name = name_ a;
        recarg_like = false;
        notation_scope = None;
        implicit_status = Glob_term.MaxImplicit;
      }) args in
  unit_of_vernacs [ VernacArguments (qname, impl_args, [], []) ]

(* TODO somehow the imported module is printed on a new line. looks like automatic line break issue *)
let import_ name =
  unit_of_vernacs [ VernacImport (false, [ (qualid_ name, ImportAll) ]) ]
let export_ name =
  unit_of_vernacs [ VernacImport (true, [ (qualid_ name, ImportAll) ]) ]

let module_ name contents =
  List.concat [
    [ unit_of_vernacs [ VernacDefineModule (None, lident_ name, [], Declaremods.Check [], []) ] ];
    contents;
    [ unit_of_vernacs [ VernacEndSegment (lident_ name) ] ]
  ]


(** For the opaueness hints we have to add an attribute. 
    We use the export flag so that the hints are only enables upon module import.
    TODO document why necessary. disable and kathrin's case study should fail *)
let setoid_opaque_hint version name =
  let attrs = match version with
    | S.LT813 -> []
    | S.GE813 -> [("local", Attributes.VernacFlagEmpty)] 
  in
  Vernac [ CAst.make { 
      control=[];
      attrs=attrs;
      expr=VernacHints (["rewrite"], HintsTransparency (Hints.HintsReferences [qualid_ name], false));
    } ]


module AutosubstModules = struct
  type module_tag = Core | Fext | Allfv | Extra
  type t = (module_tag * vernac_unit list) list

  let append m0 m1 = List.append m0 m1
  let concat ms = List.concat ms
  let empty = []

  let all_tags = [Core; Fext; Allfv; Extra]
  let string_of_tag = function
    | Core -> "Core"
    | Fext -> "Fext"
    | Allfv -> "Allfv"
    | Extra -> "Extra"

  let add_units tag units = [(tag, units)]

  let from_list l = l

  let list_collect tag l =
    let is_same_tag (tag', units) = if tag = tag' then Some units else None in
    List.(concat (filter_map is_same_tag l))

  (** Import statements that show the dependencies between out modules. *)
  let imports = 
    from_list [
      (Fext, [import_ (string_of_tag Core)]);
      (Allfv, [import_ (string_of_tag Core)]);
      (Extra, [import_ (string_of_tag Core)]);
    ]

  (** Narrow a module collection to the given tag list. *)
  let filter_tags tags m =
    from_list (List.(filter (fun (tag, _) -> mem tag tags) m))

  let remove_tags tags m =
    filter_tags (list_diff all_tags tags) m

  let pr_modules preamble m =
    (* we throw away any empty tags *)
    let present_tags = List.filter (fun tag -> List.mem_assq tag m) all_tags in
    let m_with_imports = filter_tags present_tags (append imports m) in
    (* generate the actual modules *)
    let module_of_tag tag =
      let units = list_collect tag m_with_imports in
      module_ (string_of_tag tag) units
    in
    let modules = List.map module_of_tag present_tags in
    (* print the modules *)
    let pp_modules = List.map pr_vernac_units modules in
    let interface_units = List.map (fun tag -> export_ (string_of_tag tag)) present_tags in
    let interface_module = module_ "interface" (interface_units) in
    let pp_interface = pr_vernac_units interface_module in
    (* we export the interface module so that the user only has to Import the file. *)
    let pp_export = pr_vernac_unit (export_ "interface") in
    let code = Pp.((seq pp_modules) ++ pp_interface ++ pp_export) in
    Pp.(preamble ++ code)
end


(* disable unused warning *)
module [@warning "-32"] GenTests = struct
  (* Lemma congr_lam  { s0 : tm   } { t0 : tm   } (H1 : s0 = t0) : lam  s0 = lam  t0 . *)
  let print_utlc_tm () : Pp.t =
    let utlc = inductive_ [inductiveBody_ "tm" [] ~rtype:(ref_ "Type") [
        constructor_ "var_tm" (arr1_ (ref_ "fin") (ref_ "tm"));
        constructor_ "app" (arr_ [ref_ "tm"; ref_ "tm"] (ref_ "tm"));
        constructor_ "lam" (arr1_ (ref_ "tm") (ref_ "tm"))
      ]] in
    (pr_vernac_unit utlc)

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
    let fix = fixpoint_ ~is_rec:true [fixpointBody_ fname binders rtype body_def "s"] in
    (pr_vernac_unit fix)

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
    let lemma = definition_ lname lbinders ~rtype:ltype lbody in
    (pr_vernac_unit lemma)

  (* This sadly just prints cc_plugin@cc:0 (or similar) which is probably a correct internal representation of the congruence tactic but now what I was looking for. *)
  (* let print_congruence () : Pp.t =
   *   let env = Global.env () in
   *   let sigma = Evd.from_env env in *)
  (* let open Ltac_plugin.Tacexpr in
   * let texpr = TacML (CAst.make ({ mltac_name={ mltac_plugin="cc_plugin"; mltac_tactic="cc"; }; mltac_index=0; }, [])) in
   * Ltac_plugin.Pptactic.pr_raw_tactic env sigma texpr *)
  (* Ltac_plugin.Pptactic.pr_glob_tactic env texpr *)

end

module [@warning "-32"] GenTestsTac = struct
  open TacGen

  let myasimpl' =
    let lemmas = ["foo"; "bar"; "baz"] in
    let rewrites = List.map (fun t -> progress_ (rewrite_ t)) lemmas in
    let tac = repeat_ (first_ (rewrites @ [
        progress_ (unfold_ ["upRen"; "upSubst"]);
        progress_ (cbn_ ["subst_tm"; "ren_tm"]);
        calltac_ "fsimpl" ])) in
    let tac = TacticLtac ("asimpl'", tac) in
    (pr_vernac_unit tac)

  let myasimpl =
    let tac = then1_ (then1_ (repeat_ (try_ (calltac_ "unfold_funcomp")))
                        (calltac_ "asimpl'"))
        (repeat_ (try_ (calltac_ "unfold_funcomp"))) in
    pr_tactic_ltac "asimpl" tac

  let myasimpl_hyp =
    let intro = intros_ [ "J" ] in
    let tac = then1_ (then1_ (calltacArgs_ "revert" [ "J" ])
                        (calltac_ "asimpl"))
        intro in
    pr_tactic_notation [ "\"asimpl\""; "\"in\""; "hyp(J)" ] tac

  let myauto_case =
    let inner_tac = then1_ (then1_ (calltac_ "asimpl") (cbn_ [])) (calltac_ "eauto") in
    let tac = calltacTac_ "auto_case" inner_tac in
    pr_tactic_notation [ "\"auto_case\"" ] tac

  let myrenamify =
    let tac = then1_ (calltac_ "auto_unfold")
        (try_ (repeat_ (rewrite_ ~with_evars:true ~to_left:true ~repeat_star:false "foo"))) in
    pr_tactic_ltac "renamify" tac

  let myrewritestar =
    let tac = rewrite_ ~locus_clause:star_locus_clause "foo" in
    pr_tactic_ltac "rest" tac
end

module [@warning "-32"] GenTestsNotation = struct
  open NotationGen

  let mynotation =
    let n = notation_ "x '__tm'" [ level_ 5; format_ "x __tm" ] ~scope:subst_scope (app1_ (ref_ "var_tm") (ref_ "x")) in
    pr_vernac_unit n

  let mynotation2 =
    let n = notation_ "s [ sigmatm ]" [ level_ 7; assoc_ LeftA; only_print_ ] ~scope:subst_scope (app_ (ref_ "subst_tm") [ ref_ "sigmatm"; ref_ "s" ]) in
    pr_vernac_unit n

end
