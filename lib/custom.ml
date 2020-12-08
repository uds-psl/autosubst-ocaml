open Base
open Util

module H = Hsig
module CS = CoqSyntax

let var__ = ref "var"
let var_ x = sepd [!var__; x]

let funname_ f = f

let constructor_ c = c

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
  | H.Single x -> sepd [name; x; y]
  | H.BinderList (_, x) -> sepd [name; "list"; x; y]

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

let rinstInst_ x = sepd ["rinst_inst"; x]

let up_rinstInst_ = upNameGen "rinstInst_up"

let varLFun_ x = sepd ["varL"; x]
let varLRenFun_ x = sepd ["varLRen"; x]
let instIdFun_ x = sepd ["instId"; x]
let rinstInstFun_ x = sepd ["rinstInst"; x]
let rinstIdFun_ x = sepd ["rinstId"; x]

let ext_ x = sepd ["ext"; x]
let extRen_ x = sepd ["extRen"; x]

let compRenRen_ x = sepd ["compRenRen"; x]
let compRenSubst_ x = sepd ["compRenSubst"; x]
let compSubstRen_ x = sepd ["compSubstRen"; x]
let compSubstSubst_ x = sepd ["compSubstSubst"; x]

let map_ f ts = CS.idApp (sepd [f; "map"]) ts
let mapId_ f ts = CS.idApp (sepd [f; "id"]) ts
let mapExt_ f ts = CS.idApp (sepd [f; "ext"]) ts
let mapComp_ f ts = CS.idApp (sepd [f; "comp"]) ts

let idSubst_ x = sepd ["idSubst"; x]
let subst_ x = sepd ["subst"; x]

let shift_p_ = "shift_p"
