(** This module provides names for definitions/lemmas etc.
 ** The values here are mainly passed to the smart constructors in Coqgen
 ** by the generator functions in CodeGenerator *)

open Util

module L = Language
module AL = AssocList

(** This uses the mutable variable var_fmt to build the name for variable constructors.
 ** format_from_string takes a string and format string (the "%s") and tries to cast the string
 ** to that format. Can error at runtime if user supplied a wrong format string. *)
let var_ x =
  let default_name = Printf.sprintf "var_%s" x in
  AL.assoc_default ~default:default_name x !Settings.var_name_assoc

let congr_ c = sepd ["congr"; c]

let ren_ x = sepd ["ren"; x]
let renRen_ x = sepd ["renRen"; x]
let renRen'_ x = sepd ["renRen'"; x]
let renRenPointwise_ x = sepd ["renRen'"; x; "pointwise"]
let substRen_ x = sepd ["substRen"; x]
let substRenPointwise_ x = sepd ["substRen"; x; "pointwise"]
let substRen'_ x = sepd ["substRen'"; x]
let renSubst_ x = sepd ["renSubst"; x]
let renSubstPointwise_ x = sepd ["renSubst"; x; "pointwise"]
let renSubst'_ x = sepd ["renSubst'"; x]
let substSubst_ x = sepd ["substSubst"; x]
let substSubstPointwise_ x = sepd ["substSubst"; x; "pointwise"]
let substSubst'_ x = sepd ["substSubst'"; x]

let upNameGen name = fun y -> function
  | L.Single x -> sepd [name; x; y]
  | L.BinderList (_, x) -> sepd [name; "list"; x; y]

let up_ren_ren__ = "up_ren_ren"
let up_ren_subst__ = "up_ren_subst"
let up_subst_ren__ = "up_subst_ren"
let up_subst_subst__ = "up_subst_subst"
let up__ = "up"
let upRen__ = "upRen"
let upExtRen__ = "upExtRen"
let upExt__ = "upExt"
let upId__ = "upId"

let up_ren_ren_ = upNameGen up_ren_ren__
let up_ren_subst_ = upNameGen up_ren_subst__
let up_subst_ren_ = upNameGen up_subst_ren__
let up_subst_subst_ = upNameGen up_subst_subst__
let up_ = upNameGen up__
let upRen_ = upNameGen upRen__
let upExtRen_ = upNameGen upExtRen__
let upExt_ = upNameGen upExt__
let upId_ = upNameGen upId__
let up_rinstInst_ = upNameGen "rinstInst_up"

let varLFun_ x = sepd ["varL"; x]
let varL'Fun_ x = sepd ["varL'"; x]
let varL'FunPointwise_ x = sepd ["varL'"; x; "pointwise"]
let varLRenFun_ x = sepd ["varLRen"; x]
let varLRen'Fun_ x = sepd ["varLRen'"; x]
let varLRen'FunPointwise_ x = sepd ["varLRen'"; x; "pointwise"]
let instIdFun_ x = sepd ["instId"; x]
let instId'Fun_ x = sepd ["instId'"; x]
let instId'FunPointwise_ x = sepd ["instId'"; x; "pointwise"]
let rinstInst_ x = sepd ["rinst_inst"; x]
let rinstInstFun_ x = sepd ["rinstInst"; x]
let rinstInst'Fun_ x = sepd ["rinstInst'"; x]
let rinstInst'FunPointwise_ x = sepd ["rinstInst'"; x; "pointwise"]
let rinstIdFun_ x = sepd ["rinstId"; x]
let rinstId'Fun_ x = sepd ["rinstId'"; x]
let rinstId'FunPointwise_ x = sepd ["rinstId'"; x; "pointwise"]
let up_class_ x = sepd ["up"; x]
let up_inst_ y x = sepd ["up"; y; x]

let ext_ x = sepd ["ext"; x]
let extRen_ x = sepd ["extRen"; x]

let compRenRen_ x = sepd ["compRenRen"; x]
let compRenSubst_ x = sepd ["compRenSubst"; x]
let compSubstRen_ x = sepd ["compSubstRen"; x]
let compSubstSubst_ x = sepd ["compSubstSubst"; x]

let idSubst_ x = sepd ["idSubst"; x]
let subst_ x = sepd ["subst"; x]


(** New Names for allfv lemmas. *)
let up_allfv_name = upNameGen "upAllfv"
let allfv_name x = sepd ["allfv"; x]
let congr_allfv_name c = sepd ["congrP"; c]
let up_allfv_triv_name = upNameGen "upAllfvTriv"
let allfv_triv_name x = sepd ["allfvTriv"; x]
let up_allfv_impl_name = upNameGen "upAllfvImpl"
let allfv_impl_name x = sepd ["allfvImpl"; x]
let up_allfv_allfv_impl_name = upNameGen "upAllfvAllfvImpl"
let allfv_allfv_impl_name x = sepd ["allfvAllfvImpl"; x]
let up_allfv_ren_l_name = upNameGen "upAllfvRenL"
let allfv_ren_l_name x = sepd ["allfvRenL"; x]
let up_allfv_ren_r_name = upNameGen "upAllfvRenR"
let allfv_ren_r_name x = sepd ["allfvRenR"; x]
