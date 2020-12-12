open Base
open Autosubst_lib
module H = Hsig

let parse_arguments () =
  let argv = Sys.get_argv () in
  let infile = Array.get argv 1 in
  let outfile = Array.get argv 2 in
  let scope_type = match Array.get argv 3 with
    | "ucoq" -> H.Unscoped
    | "coq" -> H.WellScoped
    | _ -> failwith "scope type must be either \"ucoq\" or \"coq\"" in
  (infile, outfile, scope_type)

let main () =
  let open ErrorM in
  let args = parse_arguments () in
  let result = match run (Program.main args) with
    | Ok x -> x
    | Error x -> failwith x in
  Stdio.print_endline result

let () = main ()
