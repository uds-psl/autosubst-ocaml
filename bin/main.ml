open Autosubst_lib


let main () =
  let open ErrorM in
  match run (Program.main Sys.argv) with
  | Ok x -> print_endline x
  | Error x -> print_endline x

let () = main ()
