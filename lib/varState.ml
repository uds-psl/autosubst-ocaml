open Base

module AL = AssocList

let scope : (string, int) AL.t ref = ref (AL.from_list [])

let lookup = AL.assoc_default ~default:0

let fresh id =
  let n = lookup id !scope in
  scope := (AL.insert id (n+1) !scope);
  if n > 0
  then id ^ (Int.to_string n)
  else id

(** TODO wtf why does this not update the scope. I use it everywhere! *)
let tfresh id =
  let n = lookup id !scope in
  if n > 0
  then id ^ (Int.to_string n)
  else id
