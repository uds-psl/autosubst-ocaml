open Base
open Autosubst_lib

let main () =
  let open ErrorM in
  let result = match run (Program.main ()) with
    | Ok x -> x
    | Error x -> failwith x in
  Stdio.print_endline result

let () = main ()
