open Base
open Util
open Coqgen
open CoqNames
open CoqSyntax

module CE = Constrexpr
module H = Hsig

let type_ = ref_ "Type"
let nat_ = ref_ "nat"
let none_ = ref_ "None"
let some_ = ref_ "Some"
let suc_ = ref_ "S"
let plus_ = ref_ "plus"
let shift_ = ref_ "shift"
let cons_ = ref_ "scons"
let var_zero_ = ref_ "var_zero"
let underscore_ = ref_ "_"
let id_ = ref_ "id"

let app_ref ?(expl=false) s t =
  if expl then appExpl_ s t
  else app_ (ref_ s) t

let eq_refl_ = ref_ "eq_refl"
let eqSym_ s = app_ref "eq_sym" [s]
let eqTrans_ s t = app_ref "eq_trans" [s; t]
let ap_ s t = app_ref "ap" [s; t]
let app_id_ s = app_ref "id" [s]
let fin_ n = app_ref "fin" [n]
let fext_ s = app_ref "FunctionalExtensionality.functional_extensionality"
    [underscore_; underscore_; s]

(** Create a list of terms from a list of strings *)
let mk_refs = List.map ~f:ref_

let succ_ n z = function
  | H.Single x -> if String.(z = x) then app1_ suc_ n else n
  | H.BinderList (m, x) -> if String.(z = x) then app_ plus_ [ref_ m; n] else n

let (>>>) s t = app_ref "funcomp" [t; s]
let (<<>>) ss ts = List.map2_exn ~f:(>>>) (sty_terms ss) (sty_terms ts)

(** Build up a proof term for a congruence lemma. It uses eq_trans to swap out one one term for another in
 ** the input list [(s0, t0); ...; (sn; tn)] *)
let repRew s = List.fold_left ~f:(fun s (t, t_eq) -> eqTrans_ s (ap_ t_eq t)) ~init:eq_refl_ s

let matchFin_ s f b =
  match !Settings.scope_type with
  | H.Unscoped ->
    match_ s [ branch_ "S" ["n'"] (f (ref_ "n'"))
             ; branch_ "O" [] b ]
  | H.WellScoped ->
    match_ s [ branch_ "Some" ["fin_n"] (f (ref_ "fin_n"))
             ; branch_ "None" [] b ]

let app_sort cname scope =
  match !Settings.scope_type with
  | H.Unscoped -> ref_ cname
  | H.WellScoped -> app_ref cname (sty_terms scope)
let app_constr cname scope rest =
  let args = match !Settings.scope_type with
    | H.Unscoped -> rest
    | H.WellScoped -> (sty_terms scope) @ rest in
  if List.is_empty args
  then ref_ cname
  else app_ref cname args
let app_var_constr sort scope = app_constr (var_ sort) scope []
let filter_scope_vars = List.filter ~f:(function
  | SubstScope _ -> (match !Settings.scope_type with
      | H.Unscoped -> false
      | H.WellScoped -> true)
  | _ -> true)
let app_fix ?expl cname ?(scopes=[]) rest =
  let scope_ts = List.(scopes
                       |> filter_scope_vars
                       |> map ~f:sty_terms
                       |> concat) in
  app_ref ?expl cname (scope_ts @ rest)
let mk_underscore_pattern scope =
  match !Settings.scope_type with
  | H.Unscoped -> []
  | H.WellScoped -> List.map ~f:(const "_") (sty_terms scope)

let sortType x ns =
  let args = match !Settings.scope_type with
    | H.Unscoped -> []
    | H.WellScoped -> sty_terms ns in
  app_ (ref_ x) args

let (==>) s t = List.fold_right s ~f:(fun s t -> arr1_ s t) ~init:t

(** TODO does the fresh variable here work as I expect? check upExtRen_list_vl_vl *)
let abs_ref x t =
  let x' = VarState.tfresh x in
  lambda_ [binder1_ x'] t

let scons_p_congr_ s t = app_ref "scons_p_congr" [t; s]
let scons_p_comp' x = app_ref "scons_p_comp'" [underscore_; underscore_; underscore_; x]
let scons_p_tail' x = app_ref "scons_p_tail'" [underscore_; underscore_; x]
let scons_p_head' x = app_ref "scons_p_head'" [ underscore_; underscore_; x]

(** Convert an implicit binder to an explicit one *)
let explicitS_ = function
  | CE.CLocalAssum (bnames, _, btype) -> CE.CLocalAssum (bnames, CE.Default Glob_term.Explicit, btype)
  | _ -> failwith "We only use CLocalAssum in autosubst!"

(** Convert a list of binders to explicit binders *)
let explicit_ = List.map ~f:explicitS_

let definitionBody sort binder (singleMatch, singleNoMatch) f_listMatch =
  match binder with
  | H.Single sort' -> if String.(sort = sort') then singleMatch else singleNoMatch
  | H.BinderList (p, sort') ->
    let (listMatch, listNoMatch) = f_listMatch p sort' in
    if String.(sort = sort') then listMatch else listNoMatch