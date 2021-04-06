(** This module is basically the entrypoint of the program.
 ** (It's in lib because the ocaml repl cannot open executables, i.e. bin/main.ml) *)

module H = Hsig

(* before version 8.10 there was no explicit scope declaration so we use a different static file *)
type coq_version = LT810 | GE810

let read_file infile =
  let input = open_in_bin infile in
  let content = really_input_string input (in_channel_length input) in
  let _ = close_in input in
  content

let write_file outfile content =
  let output = open_out outfile in
  let _ = output_string output content in
  let _ = close_out output in
  ()

let copy_file src dst = write_file dst (read_file src)

let copy_static_files dir scope_type coq_version =
  let open Filename in
  let () = copy_file "data/axioms.v" (concat dir "axioms.v") in
  match scope_type, coq_version with
  | H.WellScoped, LT810 ->
    copy_file "data/fintype_809.v" (concat dir "fintype.v")
  | H.Unscoped, LT810 ->
    copy_file "data/unscoped_809.v" (concat dir "unscoped.v")
  | H.WellScoped, GE810 ->
    copy_file "data/fintype.v" (concat dir "fintype.v")
  | H.Unscoped, GE810 ->
    copy_file "data/unscoped.v" (concat dir "unscoped.v")

let make_filenames outfile =
  let open Filename in
  let outfile_name = remove_extension outfile in
  (* could happen that we don't have an extension *)
  if (outfile = outfile_name)
  then outfile, outfile, outfile ^ "_asimpl"
  else
    let ext = extension outfile in
    outfile_name, outfile_name ^ ext, outfile_name ^ "_asimpl" ^ ext


let main (infile, outfile, scope_type, coq_version) =
  let open ErrorM.Syntax in
  let open ErrorM in
  let dir, outfile, outfile_fext = make_filenames outfile in
  let () = Printexc.record_backtrace true in
  let () = Coqgen.setup_coq () in
  let () = Settings.scope_type := scope_type in
  (* setup static files *)
  let () = Unix.mkdir dir 0o755 in
  let () = copy_static_files dir scope_type coq_version in
  (* parse input HOAS *)
  let* spec = read_file infile |> SigParser.parse_signature in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate dot graph *)
  (* generate code *)
  let* code, fext_code = GenCode.run_gen_code signature in
  (* write file *)
  let open Filename in
  let () = write_file (concat dir outfile) code in
  let () = write_file (concat dir outfile_fext) fext_code in
  pure "done"
