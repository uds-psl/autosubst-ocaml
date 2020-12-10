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

let tfresh id =
  let n = lookup id !scope in
  if n > 0
  then id ^ (Int.to_string n)
  else id

(* TODO what if empty string? *)
let intern tid =
  fresh String.(of_char @@ get (lowercase tid) 0 )
