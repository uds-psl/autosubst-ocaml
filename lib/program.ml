(** This module is basically the entrypoint of the program.
 ** (It's in lib because the ocaml repl cannot open executables, i.e. bin/main.ml) *)

module S = Settings

let read_file infile =
  let input = open_in_bin infile in
  let content = really_input_string input (in_channel_length input) in
  let () = close_in input in
  content

let really_write_file outfile content =
  let output = open_out outfile in
  let () = output_string output content in
  close_out output

let write_file ?(force_overwrite=false) outfile content =
  let open Unix in
  if force_overwrite then really_write_file outfile content
  else
    try
      let _ = stat outfile in
      let () = print_endline (outfile ^ " exists. Overwrite [y/N]:") in
      let prompt = read_line () in
      if prompt = "y"
      then really_write_file outfile content
      else ()
    with Unix_error (ENOENT, _, _) ->
      really_write_file outfile content

let copy_file ?(force_overwrite=false) src dst = write_file ~force_overwrite dst (read_file src)

let gen_static_files ?(force_overwrite=false) dir scope version outfile outfile_fext =
  let open Filename in
  (* let coq_project_files = ref [outfile; outfile_fext] in *)
  let copy_static_file ?out_name name =
    let out_name = Option.default name out_name in
    (* coq_project_files := out_name :: !coq_project_files; *)
    copy_file ~force_overwrite (concat "data" name) (concat dir out_name)
  in
  let open Settings in
  let () = match scope with
    | WellScoped ->
      let () = copy_static_file "fintype_axioms.v" in
      copy_static_file "fintype.v"
    | Unscoped ->
      let () = copy_static_file "unscoped_axioms.v" in
      copy_static_file "unscoped.v"
  in
  let () = copy_static_file "core_axioms.v" in
  let () = match version with
    | GE810 ->
      copy_static_file "core.v"
    | LT810 ->
      copy_static_file ~out_name:"core.v" "core_809.v" in
  ()
  (* now coq_project files contains all files for the _CoqProject in the correct order. TODO do it without ref? *)
  (* let coq_project = "-Q . \"\"\n\n"
   *   ^ String.concat "\n" !coq_project_files in *)
  (* write_file (concat dir "_CoqProject") coq_project *)

let make_filenames outfile =
  let open Filename in
  let outfile_name = basename (remove_extension outfile) in
  let dir = dirname outfile in
  let ext = extension outfile in
  dir, outfile_name, outfile_name ^ ext, outfile_name ^ "_axioms" ^ ext

let create_outdir dir =
  let open Unix in
  try let _ = opendir dir in ()
  with Unix_error (ENOENT, _, _) ->
    Unix.mkdir dir 0o755

let main S.{ infile; outfile; scope; axioms_separate; generate_static_files; force_overwrite; version } =
  let open ErrorM.Syntax in
  let open ErrorM in
  let () = Printexc.record_backtrace true in
  let () = GallinaGen.setup_coq () in
  let () = Settings.scope_type := scope in
  let dir, outfile_basename, outfile, outfile_fext = make_filenames outfile in
  (* setup static files *)
  let () = create_outdir dir in
  let () = if generate_static_files
    then gen_static_files ~force_overwrite dir scope version outfile outfile_fext
    else () in
  (* parse input HOAS *)
  let* spec = read_file infile |> SigParser.parse_signature in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate dot graph *)
  (* generate code *)
  let* (code, fext_code), _ = FileGenerator.run_gen_code signature outfile_basename axioms_separate in
  (* write file *)
  let open Filename in
  let () = if axioms_separate
    then
      let () = write_file ~force_overwrite (concat dir outfile) code in
      write_file ~force_overwrite (concat dir outfile_fext) fext_code
    else
      write_file ~force_overwrite (concat dir outfile) (code ^ fext_code)
  in
  pure "done"
