(** This module is supposed to implement some kind of scope so that we don't accidentally
 ** generate code where variables are shadowed/captured.
 ** The way it is used right now is not correct. Luckily there is only one instance of harmless shadowing that I found in the generated code. But this is something to fix. *)
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
