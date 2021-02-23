(** This module is basically the entrypoint of the program.
 ** (It's in lib because the ocaml repl cannot open executables, i.e. bin/main.ml) *)

let read_signature infile =
  let input = open_in_bin infile in
  let content = really_input_string input (in_channel_length input) in
  let _ = close_in input in
  content

let write_file outfile content =
  let output = open_out outfile in
  let _ = output_string output content in
  let _ = close_out output in
  ()

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
