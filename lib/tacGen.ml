open Ltac_plugin.Tacexpr
open GallinaGen
open Util

type tactic_expr = raw_tactic_expr
type locus_clause_expr = Names.lident Locus.clause_expr

let default_locus_clause = Locus.{ onhyps = Some []; concl_occs = AllOccurrences}
let star_locus_clause = Locus.{ onhyps = None; concl_occs = AllOccurrences}

let idtac_ = TacId []
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
let then1_ tactic1 tactic2 = TacThen (tactic1, tactic2)
let then_ = function
  | [] -> idtac_
  | tac :: tacs ->
    List.fold_left (fun t1 t2 -> then1_ t1 t2) tac tacs
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

let intros_ names =
  let intro_pats = List.map (fun s ->
      CAst.make (Tactypes.IntroNaming (Namegen.IntroIdentifier (name_id_ s))))
      names in
  let intros = TacAtom (CAst.make (TacIntroPattern (false, intro_pats))) in
  intros

let unfold_ ?(locus_clause=default_locus_clause) lemmas =
  let consts = List.map (fun s ->
      CAst.make (Constrexpr.AN (qualid_ s))) lemmas in
  let occ_list = List.map (fun c -> (Locus.AllOccurrences, c)) consts in
  let unfold = Genredexpr.Unfold occ_list in
  TacAtom (CAst.make (TacReduce (unfold, locus_clause)))

(* let notation_ cexpr =
 *   TacArg (CAst.make (ConstrMayEval (Genredexpr.ConstrTerm cexpr))) *)

let pr_tactic_ltac name tactic =
  let open Ltac_plugin.Pptactic in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = pr_raw_tactic env sigma tactic in
  Pp.(seq [ str "Ltac "; str name; str " := "; pp; vernacend; newline ])

let pr_tactic_notation names tactic =
  let open Ltac_plugin.Pptactic in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pp = pr_raw_tactic env sigma tactic in
  Pp.(seq (str "Tactic Notation " :: (List.map (fun n -> str (n ^ " ")) names) @ [ str ":= "; pp; vernacend; newline ]))

type tactic_info = {
  asimpl_rewrite_lemmas : string list;
  asimpl_cbn_functions : string list;
  asimpl_unfold_functions : string list;
  substify_lemmas : string list;
  auto_unfold_functions : string list;
  classes : (string * binder_expr list * constructor_expr list) list;
  (* instance info probably also needs parameter information *)
  instances : (ClassGen.instance_type * string * constr_expr list) list;
  notations : (NotationGen.notation_type * constr_expr) list;
}
