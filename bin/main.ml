open Core
open Lib.Types
open Lib.Generate

let generate the_sig =
  (* generate dot graph *)
  let code = genCode the_sig in
  (* write file *)
  code

let main () =
  let open Or_error.Monad_infix in
  (* parse arguments *)
  (* parse input HOAS *)
  let the_sig = Or_error.return mySig in
  let the_code = the_sig >>= generate in
  let result = match the_code with
    | Ok x -> x
    | Error x -> Error.to_string_hum x in
  print_endline result;; (* how do I end this function, when I remove the ;; it thinks the call to main below belongs to the definition -.- *)

main ()
