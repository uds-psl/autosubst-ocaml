open Vernacexpr
open Coqgen

let format_ fmt = SetFormat ("text", CAst.make fmt)
let subst_scope = "subst_scope"
let fscope = "fscope"

let notation_ notation ?level ?assoc ?fmt ?(modifiers=[ SetOnlyPrinting ]) ?scope body =
  let modifiers = match fmt with
    | None -> modifiers
    | Some f -> format_ f :: modifiers in
  let modifiers = match assoc with
    | None -> modifiers
    | Some a -> SetAssoc a :: modifiers in
  let modifiers = match level with
    | None -> modifiers
    | Some l -> SetLevel l :: modifiers in
  VernacNotation (body, (CAst.make notation, modifiers), scope)

type g_assoc = Gramlib.Gramext.g_assoc = NonA | RightA | LeftA

module [@warning "-32"] GenTests = struct
  let mynotation =
    let n = notation_ "x '__tm'" ~level:5 ~scope:subst_scope ~fmt:"x __tm" ~modifiers:[] (app1_ (ref_ "var_tm") (ref_ "x")) in
    pr_vernac_expr n

  let mynotation2 =
    let n = notation_ "s [ sigmatm ]" ~level:7 ~assoc:LeftA ~scope:subst_scope (app_ (ref_ "subst_tm") [ ref_ "sigmatm"; ref_ "s" ]) in
    pr_vernac_expr n

end
