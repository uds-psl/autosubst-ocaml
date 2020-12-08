open Base
module H = Hsig

let readSignature () =
  let open Lwt.Syntax in
  let open Lwt_io in
  Lwt_main.run (
    let* input = open_file ~mode:Input "./signatures/sysf_cbv.sig" in
    read input
  )

let main () =
  let open ErrorM.Syntax in
  let open ErrorM in
  (* parse arguments *)
  (* parse input HOAS *)
  let* spec = readSignature () |> SigParser.parse_signature in
  let* signature = SigAnalyzer.build_signature spec in
  (* generate dot graph *)
  let* code = GenCode.runGenCode signature in
  (* write file *)
  pure code
  (* pure "" *)
