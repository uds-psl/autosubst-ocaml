open Util
open GallinaGen
open CoqNames
open CoqSyntax

module CE = Constrexpr
module L = Language
module S = Settings

let type_ = type_
let nat_ = ref_ "nat"
let true_ = ref_ "True"
let trueProof_ = ref_ "I"
let none_ = ref_ "None"
let some_ = ref_ "Some"
let suc_ = ref_ "S"
let plus_ = ref_ "plus"
let shift_ = ref_ "shift"
let cons_ = ref_ "scons"
let var_zero_ = ref_ "var_zero"
let underscore_ = underscore_
let id_ = ref_ "id"
let shift_p_ = ref_ "shift_p"
let eq_refl_ = ref_ "eq_refl"

let and_ x y = app_ref "and" [x; y]
let eqSym_ s = app_ref "eq_sym" [s]
let eqTrans_ s t = app_ref "eq_trans" [s; t]
let ap_ s t = app_ref "ap" [s; t]
let app_id_ s = app_ref "id" [s]
let fin_ n = app_ref "fin" [n]
let up_ren_ xi = app_ref "up_ren" [xi]
let up_allfv_ p = app_ref "up_allfv" [p]
let fext_ s = app_ref "FunctionalExtensionality.functional_extensionality"
    [underscore_; underscore_; s]

(** Create a list of terms from a list of strings *)
let mk_refs = List.map ref_

let succ_ n z = function
  | L.Single x -> if z = x then app1_ suc_ n else n
  | L.BinderList (m, x) -> if z = x then app_ plus_ [ref_ m; n] else n

let (>>>) s t = app_ref "funcomp" [t; s]
let (<<>>) ss ts = List.map2 (>>>) (sty_terms ss) (sty_terms ts)

(** Build up a proof term for a congruence lemma. It uses eq_trans to swap out one one term for another in
 ** the input list [(s0, t0); ...; (sn; tn)] *)
let repRew s = List.fold_left (fun s (t, t_eq) -> eqTrans_ s (ap_ t_eq t)) eq_refl_ s

let matchFin_ s f b =
  match !Settings.scope_type with
  | S.Unscoped ->
    match_ s [ branch_ "S" ["n'"] (f (ref_ "n'"))
             ; branch_ "O" [] b ]
  | S.WellScoped ->
    match_ s [ branch_ "Some" ["fin_n"] (f (ref_ "fin_n"))
             ; branch_ "None" [] b ]

let app_sort cname scope = app_ref cname (ss_terms scope)
let app_constr cname scope rest = app_ref cname (ss_terms scope @ rest)
let app_var_constr sort scope = app_constr (var_ sort) scope []
(* TODO document. seems to build an application that uses the scope variabes from scoped. But in most uses in the code this seem sunecessary *)
let app_fix ?expl cname ?(sscopes=[]) ?(scopes=[]) rest =
  let sscope_ts = List.(sscopes
                        |> map ss_terms
                        |> concat) in
  let scope_ts = List.(scopes
                       |> map sty_terms
                       |> concat) in
  app_ref ?expl cname (sscope_ts @ scope_ts @ rest)
let mk_underscore_pattern scope = List.map (const "_") (ss_terms scope)

let (==>) s t = List.fold_right (fun s t -> arr1_ s t) s t

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
let explicit_ = List.map explicitS_

(** Construct the body of a definition depending on if the given sort matches the one in the binder *)
let definitionBody sort binder (singleMatch, singleNoMatch) f_listMatch =
  match binder with
  | L.Single sort' -> if sort = sort' then singleMatch else singleNoMatch
  | L.BinderList (p, sort') ->
    let (listMatch, listNoMatch) = f_listMatch p sort' in
    if sort = sort' then listMatch else listNoMatch
