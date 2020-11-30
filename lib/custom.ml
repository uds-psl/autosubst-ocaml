open Base
module H = Hsig
module CS = CoqSyntax

let sep = "_"
let sepd = String.concat ~sep:sep

let var_ x = sepd ["var"; x]

let funname_ f = f

let constructor_ c = c

let congr_ c = sepd ["congr"; c]

let ren_ x = sepd ["ren"; x]

let up_ren_ren_ = "up_ren_ren"
let up_ren_subst__ = "up_ren_subst"
let up_subst_ren__ = "up_subst_ren"
let up_subst_subst__ = "up_subst_subst"

let up_ren_renName_ y = function
    | H.Single x -> sepd [up_ren_ren_; x; y]
    | H.BinderList (_, x) -> sepd [up_ren_ren_; "list"; x; y]

let up_ren_subst_ y = function
    | H.Single x -> sepd [up_ren_subst__; x; y]
    | H.BinderList (_, x) -> sepd [up_ren_subst__; "list"; x; y]

let up_subst_ren_ y = function
    | H.Single x -> sepd [up_subst_ren__; x; y]
    | H.BinderList (_, x) -> sepd [up_subst_ren__; "list"; x; y]

let up_subst_subst_ y = function
    | H.Single x -> sepd [up_subst_subst__; x; y]
    | H.BinderList (_, x) -> sepd [up_subst_subst__; "list"; x; y]

let up_ y = function
    | H.Single x -> sepd ["up"; x; y]
    | H.BinderList (_, x) -> sepd ["upList"; x; y]

let upRen_ y = H.(function
    | Single x -> sepd ["upRen"; x; y]
    | BinderList (_, x) -> sepd ["upRenList"; x; y]
  )

let upExtRen_ y = function
  | H.Single x -> sepd ["upExtRen"; x; y]
  | H.BinderList (_, x) -> sepd ["upExtRen_list"; x; y]

let upExt_ y = function
  | H.Single x -> sepd ["upExt"; x; y]
  | H.BinderList (_, x) -> sepd ["upExt_list"; x; y]

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

let upId_ y = H.(function
    | Single x -> sepd ["upId"; x; y]
    | BinderList (_, x) -> sepd ["upIdList"; x; y]
  )
