open Autosubst_lib
module S = Settings

let print_usage () =
  print_endline "dune exec -- bin/main.exe <signature-file> <output-file> <syntax-style> [coq-version] [axioms-separate] [generate-static-files]\n\nsyntax-style: coq | ucoq -- generate scoped or unscoped code\n\ncoq-version: lt810 | ge810 -- which coq version to target\n\naxioms-separate: true | false -- put all lemmas involving functional extensionality into a different file (names <output-file>_axioms.v)\n\ngenerate-static-files: true | false -- put core.v, unscoped.v, fintype.v, ... into the output directory"

let parse_arguments () =
  let () = if Array.length Sys.argv < 4 then
      let () = print_usage () in
      failwith "Too few arguments"
      else () in
  let infile = Sys.argv.(1) in
  let outfile = Sys.argv.(2) in
  let scope = match Sys.argv.(3) with
    | "ucoq" -> S.Unscoped
    | "coq" -> S.WellScoped
    | _ -> failwith "scope type must be either \"ucoq\" or \"coq\"" in
  let version = if Array.length Sys.argv >= 5 then match Sys.argv.(4) with
      | "lt810" -> S.LT810
      | "ge810" -> S.GE810
      | _ -> failwith "coq verison must be either \"lt810\" or \"ge810\""
    else S.GE810 in
  let axioms_separate = if Array.length Sys.argv >= 6 then bool_of_string Sys.argv.(5) else true in
  let generate_static_files = if Array.length Sys.argv >= 7 then bool_of_string Sys.argv.(6) else true in
  S.{ infile; outfile; scope; axioms_separate; generate_static_files; version }

let main () =
  let open ErrorM in
  match run (Program.(main (parse_arguments ()))) with
    | Ok x -> print_endline x
    | Error x -> print_endline ("Error:\n" ^ x)

let () = main ()
