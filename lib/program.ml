(** This module is basically the entrypoint of the program.
 ** (It's in lib because the ocaml repl cannot open executables, i.e. bin/main.ml) *)

let read_signature infile =
  let open Lwt.Syntax in
  let open Lwt_io in
  Lwt_main.run (
    let* input = open_file ~mode:Input infile in
    read input
  )

let write_file outfile content =
  let open Lwt.Syntax in
  let open Lwt_io in
  Lwt_main.run (
    let* output = open_file ~mode:Output outfile in
    write output content
  )

let main (infile, outfile, scope_type) =
  let open ErrorM.Syntax in
  let open ErrorM in
  let () = Settings.scope_type := scope_type in
  (* parse input HOAS *)
  let* spec = read_signature infile |> SigParser.parse_signature in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate dot graph *)
  (* generate code *)
  let* code = GenCode.run_gen_code signature in
  (* write file *)
  let () = write_file outfile code in
  pure "done"
