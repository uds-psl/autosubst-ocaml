open Ltac_plugin.Tacexpr
open Coqgen
open Util

type tactic = raw_tactic_expr

let default_locus_clause = Locus.{ onhyps = Some []; concl_occs = AllOccurrences}
let star_locus_clause = Locus.{ onhyps = None; concl_occs = AllOccurrences}

let rewrite_ ?(repeat_star=true) ?(with_evars=false) ?(to_left=false) ?(locus_clause=default_locus_clause) name =
  let num_rewrite = if repeat_star
    then Equality.RepeatStar
    else Equality.Precisely 1 in
  let rewrite_term = [ (not to_left, num_rewrite, (None, (ref_ name, Tactypes.NoBindings))) ] in
  TacAtom (CAst.make (TacRewrite (with_evars, rewrite_term, locus_clause, None)))

let repeat_ tactic = TacRepeat tactic
let first_ tactics = TacFirst tactics
let progress_ tactic = TacProgress tactic
let try_ tactic = TacTry tactic
let calltac_ name = TacArg (CAst.make (Reference (qualid_ name)))
let calltacArgs_ name args =
  let args = List.map (fun s -> Reference (qualid_ s)) args in
  TacArg (CAst.make (TacCall (CAst.make (qualid_ name, args))))
let calltacTac_ name tac =
  TacArg (CAst.make (TacCall (CAst.make (qualid_ name, [ Tacexp tac ]))))
let then_ tactic1 tactic2 = TacThen (tactic1, tactic2)
let cbn_ consts =
  let consts = List.map (fun s ->
      CAst.make (Constrexpr.AN (qualid_ s))) consts in
  let delta = list_empty consts in
  let flags : Genredexpr.r_cst Genredexpr.glob_red_flag = {
    rBeta = true;
    rMatch = true;
    rFix = true;
    rCofix = true;
    rZeta = true;
    rDelta = delta;
    rConst = consts;
  } in
  let cbn = Genredexpr.Cbn flags in
  TacAtom (CAst.make (TacReduce (cbn, default_locus_clause)))

let unfold_ lemmas =
  let consts = List.map (fun s ->
      CAst.make (Constrexpr.AN (qualid_ s))) lemmas in
  let occ_list = List.map (fun c -> (Locus.AllOccurrences, c)) consts in
  let unfold = Genredexpr.Unfold occ_list in
  TacAtom (CAst.make (TacReduce (unfold, default_locus_clause)))

let notation_ cexpr =
  TacArg (CAst.make (ConstrMayEval (Genredexpr.ConstrTerm cexpr)))

let pr_tactic name tactic =
  let open Ltac_plugin.Pptactic in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = pr_raw_tactic env sigma tactic in
  Pp.(seq [ str "Ltac "; str name; str " := "; pp; vernacend ])

let pr_tactic_notation names tactic =
  let open Ltac_plugin.Pptactic in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = pr_raw_tactic env sigma tactic in
  Pp.(seq (str "Tactic Notation " :: (List.map (fun n -> str (n ^ " ")) names) @ [ str ":= "; pp; vernacend ]))


module [@warning "-32"] GenTests = struct
  let myasimpl' =
    let lemmas = ["foo"; "bar"; "baz"] in
    let rewrites = List.map (fun t -> progress_ (rewrite_ t)) lemmas in
    let tac = repeat_ (first_ (rewrites @ [
        progress_ (unfold_ ["upRen"; "upSubst"]);
        progress_ (cbn_ ["subst_tm"; "ren_tm"]);
        calltac_ "fsimpl" ])) in
    pr_tactic "asimpl'" tac

  let myasimpl =
    let tac = then_ (then_ (repeat_ (try_ (calltac_ "unfold_funcomp")))
                       (calltac_ "asimpl'"))
           (repeat_ (try_ (calltac_ "unfold_funcomp"))) in
    pr_tactic "asimpl" tac

  let myasimpl_hyp =
    let intro = TacAtom (CAst.make (TacIntroPattern (false, [CAst.make (Tactypes.IntroNaming (Namegen.IntroIdentifier (name_id_ "J")))]))) in
    let tac = then_ (then_ (calltacArgs_ "revert" [ "J" ])
                       (calltac_ "asimpl"))
        intro in
    pr_tactic_notation [ "\"asimpl\""; "\"in\""; "hyp(J)" ] tac

  let myauto_case =
    let inner_tac = then_ (then_ (calltac_ "asimpl") (cbn_ [])) (calltac_ "eauto") in
    let tac = calltacTac_ "auto_case" inner_tac in
    pr_tactic_notation [ "\"auto_case\"" ] tac

  let myrenamify =
    let tac = then_ (calltac_ "auto_unfold")
        (try_ (repeat_ (rewrite_ ~with_evars:true ~to_left:true ~repeat_star:false "foo"))) in
    pr_tactic "renamify" tac

  let myrewritestar =
    let tac = rewrite_ ~locus_clause:star_locus_clause "foo" in
    pr_tactic "rest" tac
end
