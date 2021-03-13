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

let make_filenames outfile =
  let open Filename in
  let outfile_name = remove_extension outfile in
  (* could happen that we don't have an extension *)
  if (outfile = outfile_name)
  then outfile, outfile ^ "_asimpl"
  else
    let ext = extension outfile in
    outfile_name ^ ext, outfile_name ^ "_asimpl" ^ ext

let main (infile, outfile, scope_type) =
  let open ErrorM.Syntax in
  let open ErrorM in
  let outfile, outfile_fext = make_filenames outfile in
  let () = Printexc.record_backtrace true in
  let () = Coqgen.setup_coq () in
  let () = Settings.scope_type := scope_type in
  (* parse input HOAS *)
  let* spec = read_signature infile |> SigParser.parse_signature in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate dot graph *)
  (* generate code *)
  let* code, fext_code = GenCode.run_gen_code signature in
  (* write file *)
  let () = write_file outfile code in
  let () = write_file outfile_fext fext_code in
  pure "done"
