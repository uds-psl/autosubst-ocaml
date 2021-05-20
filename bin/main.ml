open Autosubst_lib
module L = Language

let parse_arguments () =
  let infile = Sys.argv.(1) in
  let outfile = Sys.argv.(2) in
  let scope_type = match Sys.argv.(3) with
    | "ucoq" -> L.Unscoped
    | "coq" -> L.WellScoped
    | _ -> failwith "scope type must be either \"ucoq\" or \"coq\"" in
  (infile, outfile, scope_type)

let main () =
  let open ErrorM in
  let (infile, outfile, scope_type) = parse_arguments () in
  match run (Program.(main (infile, outfile, scope_type, GE810))) with
    | Ok x -> print_endline x
    | Error x -> print_endline ("Error:\n" ^ x)

let () = main ()
