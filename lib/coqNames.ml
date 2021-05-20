(** This module provides names for definitions/lemmas etc.
 ** The values here are mainly passed to the smart constructors in Coqgen
 ** by the generator functions in Generator *)

open Util

module L = Language

(** This uses the mutable variable var__ to build the name for variable constructors.
 ** format_from_string takes a string and format string (the "%s") and tries to cast the string
 ** to that format. Can error at runtime if user supplied a wrong format string. *)
let var_ x =
  let fmt = Scanf.format_from_string !Settings.var__ "%s" in
  Printf.sprintf fmt x

let funname_ f = f

let congr_ c = sepd ["congr"; c]

let ren_ x = sepd ["ren"; x]
let renRen_ x = sepd ["renRen"; x]
let renRen'_ x = sepd ["renRen'"; x]
let compRen_ x = sepd ["compRen"; x]
let compRen'_ x = sepd ["compRen'"; x]
let renComp_ x = sepd ["renComp"; x]
let renComp'_ x = sepd ["renComp'"; x]
let compComp_ x = sepd ["compComp"; x]
let compComp'_ x = sepd ["compComp'"; x]

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
let varLRenFun_ x = sepd ["varLRen"; x]
let instIdFun_ x = sepd ["instId"; x]
let rinstInst_ x = sepd ["rinst_inst"; x]
let rinstInstFun_ x = sepd ["rinstInst"; x]
let rinstIdFun_ x = sepd ["rinstId"; x]

let ext_ x = sepd ["ext"; x]
let extRen_ x = sepd ["extRen"; x]

let compRenRen_ x = sepd ["compRenRen"; x]
let compRenSubst_ x = sepd ["compRenSubst"; x]
let compSubstRen_ x = sepd ["compSubstRen"; x]
let compSubstSubst_ x = sepd ["compSubstSubst"; x]

let idSubst_ x = sepd ["idSubst"; x]
let subst_ x = sepd ["subst"; x]

let shift_p_ = "shift_p"
