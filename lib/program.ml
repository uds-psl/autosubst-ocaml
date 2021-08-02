(** This module is basically the entrypoint of the program.
 ** It's in lib because the ocaml repl cannot open executables, i.e. bin/main.ml
 ** so the executable is just a thin wrapper around this *)

module S = Settings


let usage_message = "dune exec -- bin/main.exe [OPTION]... signature-file

signature-file:
  Path to a .sig file containing the signature of your language."


(** Parse the program arguments and return a Settings.args object.
 ** The Arg module from the OCaml stdlib is missing some
 ** features compared to e.g. Python's argparse so we need
 ** to manually check that we only receive a single input
 ** signature and -o flag. *)
let parse_args args =
  (* the signature is the only argument not guarded by a keyword and we only want to set it once *)
  let infile_r = ref "" in
  let anon_fun s =
    if !infile_r = ""
    then infile_r := s
    else raise (Arg.Bad ("no additional arguments expected: " ^ s)) in
  (* we also only allow one -o flag. Technically we could also do it for the other falgs but they are idempotent. *)
  let outfile_r = ref "" in
  let set_outfile s =
    if !outfile_r = ""
    then outfile_r := s
    else raise (Arg.Bad ("only one -o flag expected.")) in
  let scope_r = ref S.Unscoped in
  (* can disable warnings here because the functions will only be called with these arguments by Arg.Symbol *)
  let [@warning "-8"] set_scope = function
    | "coq" -> scope_r := S.WellScoped
    | "ucoq" -> scope_r := S.Unscoped in
  let version_r = ref S.GE810 in
  let [@warning "-8"] set_version = function
    | "lt810" -> version_r := S.LT810
    | "ge810" -> version_r := S.GE810 in
  let gen_static_files_r = ref true in
  let force_overwrite_r = ref false in
  let gen_allfv_r = ref false in
  let gen_fext_r = ref false in
  let arg_spec = Arg.[
      ("-o", String set_outfile, "File to save output to.");
      ("-s", Symbol (["coq"; "ucoq"], set_scope), "Generate scoped or unscoped code.");
      ("-v", Symbol (["lt810"; "ge810"], set_version), "Which coq version to target. Either < 8.10 or >= 8.10.");
      ("-f", Set force_overwrite_r, "Force overwrite files in the output directory.");
      ("-no-static", Clear gen_static_files_r, "Don't put the static files like core.v, unscoped.v, etc. into the output directory.");
      ("-allfv", Set gen_allfv_r, "Generate allfv lemmas.");
      ("-fext", Set gen_fext_r, "Generate lemmas & tactics that use the functional extensionality axiom.")
  ] in
  (* have to pass in a fresh reference (or set the one from the module) to be able to call this multiple times in repl *)
  let () = Arg.parse_argv ~current:(ref 0) args arg_spec anon_fun usage_message in
  let infile = if !infile_r = "" then raise (Arg.Bad "Input signature file is required.") else !infile_r in
  let outfile = if !outfile_r = "" then raise (Arg.Bad "Output file is required.") else !outfile_r in
  S.{ infile; outfile; scope = !scope_r; gen_allfv = !gen_allfv_r; gen_fext = !gen_fext_r; gen_static_files = !gen_static_files_r; force_overwrite = !force_overwrite_r; version = !version_r }


(** Read the contents of the infile and return them. *)
let read_file infile =
  let input = open_in_bin infile in
  let content = really_input_string input (in_channel_length input) in
  let () = close_in input in
  content


(** Write content to outfile without checking if the file already exists.
 ** Naming is based on the really_input_string function from the OCaml stdlib *)
let really_write_file outfile content =
  let output = open_out outfile in
  let () = output_string output content in
  close_out output


(** Write content to outfile but prompt the user if the file already exists, except if force_overwrite is set. *)
let write_file force_overwrite outfile content =
  if (force_overwrite || not (Sys.file_exists outfile))
  then really_write_file outfile content
  else
    let () = print_endline (outfile ^ " exists. Overwrite [y/N]:") in
    let prompt = read_line () in
    if prompt = "y"
    then really_write_file outfile content
    else ()


(** Copy a file. Unfortunately the stdlib does not contain a function like this. *)
let copy_file force_overwrite src dst =
  write_file force_overwrite dst (read_file src)


(** Generate the static files by copying them into the output directory. *)
let gen_static_files force_overwrite dir scope version =
  let open Filename in
  let copy_static_file ?out_name name =
    let out_name = Option.default name out_name in
    copy_file force_overwrite (concat "data" name) (concat dir out_name)
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


(** Create the directory dir.
 ** We check if the directory does not exist by trying to open it. *)
let create_dir dir =
  let open Unix in
  try let _ = opendir dir in ()
  with Unix_error (ENOENT, _, _) ->
    mkdir dir 0o755


(** Main function of the program. Gets called by the real entrypoint in bin/main.ml *)
let main argv =
  let open ErrorM.Syntax in
  let open ErrorM in
  (* print backtrace if the program crashes *)
  let () = Printexc.record_backtrace true in
  let () = GallinaGen.setup_coq () in
  (* parse program arguments *)
  let args = parse_args argv in
  let () = Settings.scope_type := args.scope in
  (* setup static files *)
  let () =
    let dir = Filename.dirname args.outfile in
    let () = create_dir dir in
    if args.gen_static_files
    then gen_static_files args.force_overwrite dir args.scope args.version
    else () in
  (* parse input HOAS *)
  let* (_, functors, _) as spec = read_file args.infile |> SigParser.parse_signature in
  (* check if we use the "cod" functor because then we need fext also in the normal code *)
  let args = if List.mem "cod" functors then {args with gen_fext = true} else args in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate code *)
  let* code, _ = FileGenerator.run_gen_code signature args.gen_allfv args.gen_fext in
  (* write file *)
  let () = write_file args.force_overwrite args.outfile code in
  pure "done"
