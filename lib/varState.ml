open Core

module AL = AssocList

let scope : (string * int) list ref = ref []

let lookup = AL.assoc_default ~default:0

let fresh id =
  let n = lookup id !scope in
  scope := (AL.insert id (n+1) !scope);
  if n > 0
  then id ^ (string_of_int n)
  else id

let tfresh id =
  let n = lookup id !scope in
  if n > 0
  then id ^ (string_of_int n)
  else id

(* TODO what if empty string? *)
let intern tid =
  fresh String.(of_char @@ get (lowercase tid) 0 )

(* where is this even used? not sure how to deal with this monadic bind here when using state *)

let withScope m =
  let open GenM.Syntax in
  let open GenM in
  let s = !scope in
  let* v = m in
  scope := s;
  pure v
