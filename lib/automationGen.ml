open GallinaGen
open CoqNames
open Util

module TacGen = struct
  open Ltac_plugin.Tacexpr

  type t = raw_tactic_expr
  type locus_clause_expr = Names.lident Locus.clause_expr

  let default_locus_clause = Locus.{ onhyps = Some []; concl_occs = AllOccurrences}
  let star_locus_clause = Locus.{ onhyps = None; concl_occs = AllOccurrences}

  let idtac_ = (CAst.make (TacId []))
  let rewrite_ ?(repeat_star=true) ?(with_evars=false) ?(to_left=false) ?(locus_clause=default_locus_clause) name =
    let num_rewrite = if repeat_star
      then Equality.RepeatStar
      else Equality.Precisely 1 in
    let rewrite_term = [ (not to_left, num_rewrite, (None, (ref_ name, Tactypes.NoBindings))) ] in
    (CAst.make (TacAtom (TacRewrite (with_evars, rewrite_term, locus_clause, None))))


  let repeat_ tactic = (CAst.make (TacRepeat tactic))
  let first_ tactics = (CAst.make (TacFirst tactics))
  let progress_ tactic = (CAst.make (TacProgress tactic))
  let try_ tactic = (CAst.make (TacTry tactic))
  let calltac_ name = (CAst.make (TacArg (Reference (qualid_ name))))
  let calltacArgs_ name args =
    let args = List.map (fun s -> Reference (qualid_ s)) args in
    (CAst.make (TacArg (TacCall (CAst.make (qualid_ name, args)))))
  let calltacTac_ name tac =
    (CAst.make (TacArg (TacCall (CAst.make (qualid_ name, [ Tacexp tac ])))))
  let setoid_rewrite_ ?(to_left=false) name =
    calltacArgs_ ("setoid_rewrite" ^ if to_left then "_left" else "") [ name ]
  let then1_ tactic1 tactic2 = (CAst.make (TacThen (tactic1, tactic2)))
  (* Takes in a list of TacGen.t (= raw_tactic_expr = r_dispatch gen_tactic_expr
 = r_dispatch gen_tactic_expr_r CAst.t), and is supposed to produce a TacGen.t? *)
  let then_ = function
    | [] -> idtac_
    | tac :: tacs ->
      List.fold_left (fun t1 t2 -> then1_ t1 t2) tac tacs
  let cbn_ ?(locus_clause=default_locus_clause) consts =
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
      rStrength = Norm ;
    } in
    let cbn = Genredexpr.Cbn flags in
    (CAst.make (TacAtom (TacReduce (cbn, locus_clause))))

  let intros_ names =
    let intro_pats = List.map (fun s ->
        CAst.make (Tactypes.IntroNaming (Namegen.IntroIdentifier (name_id_ s))))
        names in
    let intros = CAst.make (TacAtom (TacIntroPattern (false, intro_pats))) in
    intros

  let unfold_ ?(locus_clause=default_locus_clause) lemmas =
    let consts = List.map (fun s ->
        CAst.make (Constrexpr.AN (qualid_ s))) lemmas in
    let occ_list = List.map (fun c -> (Locus.AllOccurrences, c)) consts in
    let unfold = Genredexpr.Unfold occ_list in
    CAst.make (TacAtom (TacReduce (unfold, locus_clause)))

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
end

module ClassGen = struct
  type t = Ren of int
         | Subst of int
         | Var
         | Up of string

  let instance_name sort = function
    | Ren _ -> sep "Ren" sort
    | Subst _ -> sep "Subst" sort
    | Var -> sep "VarInstance" sort
    | Up bsort -> sepd [ "Up"; bsort; sort ]

  let class_name sort = function
    | Ren n -> "Ren"^(string_of_int n)
    | Subst n -> "Subst"^(string_of_int n)
    | Var -> "Var"
    | Up _ -> sep "Up" sort

  (* a.d. DONE, maybe directly put constr_expr in the info instead of generating the function name here  *)
  let function_name sort = function
    | Ren _ -> ren_ sort
    | Subst _ -> subst_  sort
    | Var -> var_ sort
    | Up bsort -> up_inst_ bsort sort

  let class_args x =
    let us n = list_of_length underscore_ n in
    match x with
    | Ren n | Subst n -> us (n + 2)
    | Var | Up _ -> us 2

  let class_field sort = function
    | Ren n -> "ren"^(string_of_int n)
    | Subst n -> "subst"^(string_of_int n)
    | Var -> "ids"
    | Up _ -> sep "up" sort

  let instance_unfolds sort x =
    [ instance_name sort x; class_name sort x; class_field sort x ]
end

module NotationGen = struct
  open Vernacexpr
  open GallinaGen

  type g_assoc = Gramlib.Gramext.g_assoc = NonA | RightA | LeftA

  type t = VarConstr
         | VarInst
         | Var
         | Up
         | UpInst of string
         | SubstApply of string list
         | Subst of string list
         | RenApply of string list
         | Ren of string list

  let subst_scope = "subst_scope"
  let fscope = "fscope"

  let level_ l = SetLevel l
  let assoc_ a = SetAssoc a
  let format_ fmt = SetFormat (TextFormat (CAst.make fmt))
  let only_print_ = SetOnlyPrinting

  let to_substs x sorts = List.map (fun s -> sep x s) sorts
  let concat_substs substs = String.concat " ; " substs

  let notation_string sort n =
    let open Printf in
    match n with
    | VarConstr | VarInst ->
      sprintf "x '__%s'" sort
    | Var ->
      "'var'"
    | Up | UpInst _ ->
      sprintf "↑__%s" sort
    | SubstApply substSorts ->
      sprintf "s [ %s ]" (concat_substs (to_substs "sigma" substSorts))
    | Subst substSorts ->
      sprintf "[ %s ]" (concat_substs (to_substs "sigma" substSorts))
    | RenApply substSorts ->
      sprintf "s ⟨ %s ⟩" (concat_substs (to_substs "xi" substSorts))
    | Ren substSorts ->
      sprintf "⟨ %s ⟩" (concat_substs (to_substs "xi" substSorts))

  let notation_modifiers sort n =
    let open Printf in
    match n with
    | VarConstr ->
      let fmt = sprintf "x __%s" sort in
      [ level_ 5; format_ fmt ]
    | VarInst ->
      let fmt = sprintf "x __%s" sort in
      [ level_ 5; format_ fmt; only_print_ ]
    | Var ->
      [ level_ 1; only_print_ ]
    | Up | UpInst _ ->
      [ only_print_ ]
    | SubstApply _ | RenApply _ ->
      [ level_ 7; assoc_ LeftA; only_print_ ]
    | Subst _ | Ren _ ->
      [ level_ 1; assoc_ LeftA; only_print_ ]

  let notation_scope = function
    | VarConstr | VarInst | Var | Up | UpInst _
    | SubstApply _ | RenApply _ ->
      subst_scope
    | Subst _ | Ren _ ->
      fscope

  (* DONE hardcoded strings ersetzen durch die korrekten functionen in CoqNames *)
  let notation_body sort = function
    | VarConstr -> app_ref (var_ sort) [ ref_ "x" ]
    | VarInst ->
      app_ref ~expl:true "ids" [ underscore_; underscore_; ref_ (ClassGen.instance_name sort Var); ref_ "x" ]
    | Var -> ref_ (var_ sort)
    | Up -> ref_ (up_class_ sort)
    | UpInst bsort -> ref_ (up_inst_ bsort sort)
    | SubstApply substSorts -> app_ref (subst_ sort) ((List.map ref_ (to_substs "sigma" substSorts)) @ [ ref_ "s" ])
    | Subst substSorts -> app_ref (subst_ sort) (List.map ref_ (to_substs "sigma" substSorts))
    | RenApply substSorts -> app_ref (ren_ sort) ((List.map ref_ (to_substs "xi" substSorts)) @ [ ref_ "s" ])
    | Ren substSorts -> app_ref (ren_ sort) (List.map ref_ (to_substs "xi" substSorts))
end


type t = {
  asimpl_rewrite_no_fext : string list;
  asimpl_rewrite_fext : string list;
  asimpl_rewrite_base : string list;
  asimpl_cbn_functions : string list;
  asimpl_unfold_functions : string list;
  substify_lemmas_fext : string list;
  substify_lemmas : string list;
  auto_unfold_functions : string list;
  arguments : (string * string list) list;
  classes : (ClassGen.t * string) list;
  proper_instances : (string * string * string) list;
  instances : (ClassGen.t * string * string list) list;
  notations : (NotationGen.t * string) list;
}

let initial = {
  asimpl_rewrite_no_fext = [];
  asimpl_rewrite_fext = [];
  asimpl_rewrite_base = [];
  asimpl_cbn_functions = [];
  asimpl_unfold_functions = ["up_ren"];
  substify_lemmas_fext = [];
  substify_lemmas = [];
  auto_unfold_functions = [];
  arguments = [];
  classes = [];
  proper_instances = [];
  instances = [];
  notations = [];
}

let asimpl_rewrite_no_fext info = info.asimpl_rewrite_no_fext
let asimpl_rewrite_fext info = info.asimpl_rewrite_fext
let asimpl_rewrite_base info = info.asimpl_rewrite_base
let asimpl_cbn_functions info = info.asimpl_cbn_functions
let asimpl_unfold_functions info = info.asimpl_unfold_functions
let substify_lemmas_fext info = info.substify_lemmas_fext
let substify_lemmas info = info.substify_lemmas
let auto_unfold_functions info = info.auto_unfold_functions
let arguments info = info.arguments
let classes info = info.classes
let proper_instances info = info.proper_instances
let instances info = info.instances
let notations info = info.notations
