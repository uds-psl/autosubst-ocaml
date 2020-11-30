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

let up_ren_renName_ y = H.(function
    | Single x -> sepd [up_ren_ren_; x; y]
    | BinderList (_, x) -> sepd [up_ren_ren_; "list"; x; y]
  )

let up_ y = H.(function
    | Single x -> sepd ["up"; x; y]
    | BinderList (_, x) -> sepd ["upList"; x; y]
  )

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
