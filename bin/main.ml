open Base
open Autosubst_lib

module M = Monadic
module H = Hsig

module SError = M.Result.Make(struct type t = string end)

let mainProg () =
  let open SError.Syntax in
  (* parse arguments *)
  (* parse input HOAS *)
  (* let* the_sig = SError.error "failed generating signature" in *)
  let* hsig = SError.pure H.Hsig_example.mySig in
  (* generate dot graph *)
  let* (_, code, _) = GenCode.runGenCode hsig in
  (* write file *)
  SError.pure code

let main () =
  let result = match SError.run (mainProg ()) with
    | Ok x -> x
    | Error x -> x in
  print_endline result

let () = main ()
