open Lib.Types
open Lib.Generate

let generate the_sig =
  (* generate dot graph *)
  let code = genCode the_sig in
  (* write file *)
  print_endline code

let main () =
  (* parse arguments *)
  (* parse input HOAS *)
  let the_sig = mySig in
  (* print_endline the_sig;; *)
  generate the_sig
