open Vernacexpr
open Coqgen

let instance_ inst_name class_name body =
    definition_ inst_name [] ~rtype:(ref_ class_name) body

let ex_instances_ names =
    VernacExistingInstance (List.map (fun s ->
        (qualid_ s, Typeclasses.{ hint_priority = None; hint_pattern = None }))
        names)

module [@warning "-32"] GenTests = struct
  let my_instance =
    let inst = instance_ "fooI" "foo" (ref_ "bar") in
    Pp.seq (pr_vernac_unit inst)


  let my_ex_instances =
    pr_vernac_expr (ex_instances_ [ "fooI"; "barI" ])

end
