open Util
open GallinaGen
open AutomationGen
open Vernacexpr

module TG = TacGen

type vernac_expr = Vernacexpr.vernac_expr

type vernac_unit = Vernac of vernac_expr list
                 | TacticLtac of string * TacGen.t
                 | TacticNotation of string list * TacGen.t

(** I catch the VernacExactProof constructor because the way Coq normally prints it does not
 ** work well with proof general. So I explicitly add an `exact (...)` *)
let pr_vernac_expr =
  let open Pp in
  function
  | VernacExactProof cexpr ->
    str "Proof" ++ vernacend ++ pr_exact_expr cexpr
  | vexpr ->
    Ppvernac.pr_vernac_expr vexpr ++ vernacend

let pr_vernac_unit = function
  | Vernac vs ->
    Pp.seq ((List.map pr_vernac_expr vs) @ [ newline ])
  | TacticLtac (name, tac) -> TacGen.pr_tactic_ltac name tac
  | TacticNotation (names, tac) -> TacGen.pr_tactic_notation names tac

let pr_vernac_units vunits = Pp.seq (List.map pr_vernac_unit vunits)


let definition_ dname dbinders ?rtype dbody =
  let dname = name_decl_ dname in
  let dexpr = definition_expr_ dbinders ?rtype dbody in
  Vernac [ VernacDefinition ((NoDischarge, Decls.Definition), dname, dexpr) ]

let lemma_ ?(opaque=true) lname lbinders ltype lbody =
  let pexpr = (ident_decl_ lname, (lbinders, ltype)) in
  let lbegin = VernacStartTheoremProof (Decls.Lemma, [pexpr]) in
  let lbody = VernacExactProof lbody in
  let lend = VernacEndProof (Proved ((if opaque then Opaque else Transparent), None)) in
  Vernac [ lbegin; lbody; lend ]

let fixpoint_ ~is_rec fexprs =
  match fexprs with
  | [] -> failwith "fixpoint called without fixpoint bodies"
  | fexprs_nempty ->
    if is_rec
    then Vernac [ VernacFixpoint (NoDischarge, fexprs) ]
    (* if the fixpoint is declared non-recursive we try to turn it into a definition *)
    else match fexprs_nempty with
      | [{ fname={ v=fname; _ }; binders; rtype; body_def=Some body; _}] ->
        definition_ (Names.Id.to_string fname) binders ~rtype body
      | [fexpr] -> failwith "Malformed fixpoint body"
      | _ -> failwith "A non recursive fixpoint degenerates to a definition so it should only have one body"

let inductive_ inductiveBodies =
  Vernac [ VernacInductive (Inductive_kw, inductiveBodies) ]

let class_ name binders fields =
  let body = inductiveBody_ name binders fields in
  (* a.d. false argument to Class to make it inductive, not definitional *)
  Vernac [ VernacInductive (Class false, [ body ]) ]

let instance_ inst_name cbinders class_type body =
  definition_ inst_name cbinders ~rtype:class_type body

let instance'_ inst_name cbinders class_type ?(interactive=false) body =
  let vexprs = if interactive
    then
      [ VernacInstance (name_decl_ inst_name, cbinders, class_type, None, Typeclasses.{ hint_priority = None; hint_pattern = None })
      ; VernacExactProof body
      ; VernacEndProof (Proved (Opaque, None)) ]
    else [ VernacInstance (name_decl_ inst_name, cbinders, class_type, Some (false, body), Typeclasses.{ hint_priority = None; hint_pattern = None }) ]
  in
  Vernac vexprs

(* a.d. don't call with multiple names for now b/c printing is wrong *)
let ex_instances_ names =
  Vernac [ VernacExistingInstance
             (List.map (fun s ->
                  (qualid_ s, Typeclasses.{ hint_priority = None; hint_pattern = None }))
                 names) ]

let ex_instance_ name = ex_instances_ [ name ]

let notation_ notation modifiers ?scope body =
  Vernac [ VernacNotation (body, (CAst.make notation, modifiers), scope) ]

let clear_arguments_ name =
  let qname = CAst.make (Constrexpr.AN (qualid_ name)) in
  Vernac [ VernacArguments (qname, [], [], [ `ClearImplicits ]) ]

let impl_arguments_ name args =
  let qname = CAst.make (Constrexpr.AN (qualid_ name)) in
  let impl_args = List.map (fun a ->
      RealArg {
        name = name_ a;
        recarg_like = false;
        notation_scope = None;
        implicit_status = Glob_term.MaxImplicit;
      }) args in
  Vernac [ VernacArguments (qname, impl_args, [], []) ]

(* TODO somehow the imported module is printed on a new line. looks like automatic line break issue *)
let import_ name =
  Vernac [ VernacImport (false, [ (qualid_ name, ImportAll) ]) ]
let export_ name =
  Vernac [ VernacImport (true, [ (qualid_ name, ImportAll) ]) ]

let start_module_ name =
  Vernac [ VernacDefineModule (None, lident_ name, [], Declaremods.Check [], []) ]

let end_module_ name =
  Vernac [ VernacEndSegment (lident_ name) ]

let module_ name ?(imports=[]) contents =
  let imports = List.map import_ imports in
  if list_empty contents
  then []
  else
    [ start_module_ name ]
    @ imports @ contents
    @ [ end_module_ name ]


(* TODO add export flag so coq does not complain (see vernac/vernacexpr.ml::vernac_control)
 * TODO document why necessary. disable and kathrin's case study should fail *)
(** the opaqueness hints for setoid rewriting are put into the "rewrite" db *)
let setoid_opaque_hint name =
  Vernac [ VernacHints (["rewrite"], HintsTransparency (Hints.HintsReferences [qualid_ name], false)) ]


(** Module for the organization of an output file.
 ** Autosubst generates a single file with several modules.
 **
 ** ren_subst_units: the common code (inductive types, renamings, substitutions, lemmas)
 ** allfv_units: allfv lemma
 ** fext_units: lemmas involving functional extensionality
 ** interface_units: the module that exports the other modules. This is what an end-user imports in their code *)
module AutosubstModules = struct
  type t = { ren_subst_units: vernac_unit list
           ; allfv_units : vernac_unit list
           ; fext_units: vernac_unit list
           ; interface_units : vernac_unit list }

  let ren_subst_units m = m.ren_subst_units
  let allfv_units m = m.allfv_units
  let fext_units m = m.fext_units
  let interface_units m = m.interface_units

  let append m0 m1 =
    { ren_subst_units = m0.ren_subst_units @ m1.ren_subst_units
    ; allfv_units = m0.allfv_units @ m1.allfv_units
    ; fext_units = m0.fext_units @ m1.fext_units
    ; interface_units = m0.interface_units @ m1.interface_units }

  let concat ms =
    let open List in
    { ren_subst_units = concat (map ren_subst_units ms)
    ; allfv_units = concat (map allfv_units ms)
    ; fext_units = concat (map fext_units ms)
    ; interface_units = concat (map interface_units ms) }

  let initial_modules =
    { ren_subst_units = []
    ; allfv_units = []
    ; fext_units = []
    ; interface_units = [ export_ "renSubst" ] }
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

module [@warning "-32"] GenTestsClass = struct
  let my_instance =
    let inst = instance_ "fooI" [] (ref_ "foo") (ref_ "bar") in
    (pr_vernac_unit inst)


  let my_ex_instances =
    (pr_vernac_unit (ex_instances_ [ "fooI"; "barI" ]))

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
