open Autosubst_lib
module H = Hsig

let parse_arguments () =
  let infile = Sys.argv.(1) in
  let outfile = Sys.argv.(2) in
  let scope_type = match Sys.argv.(3) with
    | "ucoq" -> H.Unscoped
    | "coq" -> H.WellScoped
    | _ -> failwith "scope type must be either \"ucoq\" or \"coq\"" in
  (infile, outfile, scope_type)

let main () =
  let open ErrorM in
  let args = parse_arguments () in
  match run (Program.main args) with
    | Ok x -> print_endline x
    | Error x -> print_endline ("Error:\n" ^ x)

let () = main ()
