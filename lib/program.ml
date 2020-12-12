open Base
module H = Hsig

let readSignature infile =
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

let parse_arguments () =
  let argv = Sys.get_argv () in
  let infile = Array.get argv 1 in
  let outfile = Array.get argv 2 in
  let scope_type = match Array.get argv 3 with
    | "ucoq" -> H.Unscoped
    | "coq" -> H.WellScoped
    | _ -> failwith "scope type must be either \"ucoq\" or \"coq\"" in
  let () = Settings.scope_type := scope_type in
  (infile, outfile)

let main () =
  let open ErrorM.Syntax in
  let open ErrorM in
  (* parse arguments *)
  let (infile, outfile) = parse_arguments () in
  (* parse input HOAS *)
  let* spec = readSignature infile |> SigParser.parse_signature in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate dot graph *)
  (* generate code *)
  let* code = GenCode.runGenCode signature in
  (* write file *)
  let () = write_file outfile code in
  pure "done"
