open Base
open Coqgen

module CS = CoqSyntax
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
(* TODO atm I must always insert two underscores at the beginning of the list of argument when I use fext_ in a TermApp *)
let fext_ = ref_ "FunctionalExtensionality.functional_extensionality"
let underscore_ = ref_ "_"
let id_ = ref_ "id"

let refApp s t = app_ (ref_ s) t

let eq_refl_ = ref_ "eq_refl"
let eqSym_ s = refApp "eq_sym" [s]
let eqTrans_ s t = refApp "eq_trans" [s; t]
let ap_ s t = refApp "ap" [s; t]
let idApp_ s = refApp "id" [s]
let fin_ n = refApp "fin" [n]

(** Create a list of terms from a list of strings *)
let mkRefs = List.map ~f:ref_

let succ_ n z = function
  | H.Single x -> if String.(z = x) then app1_ suc_ n else n
  | H.BinderList (m, x) -> if String.(z = x) then app_ plus_ [ref_ m; n] else n

let (>>>) s t = refApp "funcomp" [t; s]
let (<<>>) ss ts = List.map2_exn ~f:(>>>) (CS.sty_terms ss) (CS.sty_terms ts)

(** Build up a proof term for a congruence lemma. It uses eq_trans to swap out one one term for another in
 ** the input list [(s0, t0); ...; (sn; tn)] *)
let repRew s = List.fold_left ~f:(fun s (t, t_eq) -> eqTrans_ s (ap_ t_eq t)) ~init:eq_refl_ s


(* TODO variables for constructor name strings? *)
let matchFin_ s f b = match_ s [
    branch_ "Some" ["fin_n"] (f (ref_ "fin_n"));
    branch_ "None" [] b
  ]

let sortType x ns = app_ (ref_ x) (CS.sty_terms ns)

let (==>) s t = List.fold_right s ~f:(fun s t -> arr1_ s t) ~init:t

let refAbs x t = lambda_ [binder1_ x] t

let scons_p_congr_ s t = refApp "scons_p_congr" [t; s]
let scons_p_comp' x = refApp "scons_p_comp'" [underscore_; underscore_; underscore_; x]
let scons_p_tail' x = refApp "scons_p_tail'" [underscore_; underscore_; x]
let scons_p_head' x = refApp "scons_p_head'" [ underscore_; underscore_; x]

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
