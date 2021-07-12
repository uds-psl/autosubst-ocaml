(** This module is basically the entrypoint of the program.
 ** It's in lib because the ocaml repl cannot open executables, i.e. bin/main.ml
 ** so the executable is just a thin wrapper around this *)

module S = Settings

let read_file infile =
  let input = open_in_bin infile in
  let content = really_input_string input (in_channel_length input) in
  let () = close_in input in
  content

(* naming based on the really_input_string from the OCaml stdlib  *)
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
    (* if the file does not exist the stat raises an exception *)
    with Unix_error (ENOENT, _, _) ->
      really_write_file outfile content

let copy_file ?(force_overwrite=false) src dst = write_file ~force_overwrite dst (read_file src)

let gen_static_files ?(force_overwrite=false) dir scope version =
  let open Filename in
  let copy_static_file ?out_name name =
    let out_name = Option.default name out_name in
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

let make_filename outfile =
  let open Filename in
  let outfile_name = basename (remove_extension outfile) in
  let dir = dirname outfile in
  let ext = extension outfile in
  dir, outfile_name, outfile_name ^ ext

let create_outdir dir =
  let open Unix in
  try let _ = opendir dir in ()
  with Unix_error (ENOENT, _, _) ->
    Unix.mkdir dir 0o755

let main S.{ infile; outfile; scope; gen_fext; gen_allfv; generate_static_files; force_overwrite; version } =
  let open ErrorM.Syntax in
  let open ErrorM in
  (* print backtrace when the program crashes *)
  let () = Printexc.record_backtrace true in
  let () = Settings.scope_type := scope in
  let () = GallinaGen.setup_coq () in
  let dir, _, outfile = make_filename outfile in
  (* setup static files *)
  let () = create_outdir dir in
  let () = if generate_static_files
    then gen_static_files ~force_overwrite dir scope version
    else () in
  (* parse input HOAS *)
  let* (_, functors, _) as spec = read_file infile |> SigParser.parse_signature in
  (* check if we use the "cod" functor because then we need fext also in the normal code *)
  let gen_fext = if List.mem "cod" functors then true else gen_fext in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate code *)
  let* code, _ = FileGenerator.run_gen_code signature gen_allfv gen_fext in
  (* write file *)
  let () = write_file ~force_overwrite (Filename.concat dir outfile) code in
  pure "done"
