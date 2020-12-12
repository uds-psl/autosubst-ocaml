open Base
open Util

module CS = CoqSyntax
module H = Hsig

let unscopedPreamble = "Require Export unscoped.\nRequire Export header_extensible.\n"
let scopedPreamble = "Require Export fintype.\nRequire Export header_extensible.\n"

let get_preamble () =
  match !Settings.scope_type with
  | H.Unscoped -> unscopedPreamble
  | H.WellScoped -> scopedPreamble

let getUps component =
  let open List in
  let cart = cartesian_product component component in
  let singles = cart >>| (fun (x, y) -> (H.Single x, y)) in
  let blists =  cart >>| (fun (x, y) -> (H.BinderList ("p", x), y)) in
  let scope_type = !Settings.scope_type in
  match scope_type with
  | H.WellScoped -> List.append singles blists
  | H.Unscoped -> singles

(* deriving a comparator for a type and packing it in a module
 * from https://stackoverflow.com/a/59266326 *)
module UpsComp = struct
  module T = struct
    type t = H.binder * string [@@deriving compare]
    let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_opaque
  end

  include T
  include Comparable.Make(T)
end

let genCode components =
  let open REM.Syntax in
  let open REM in
  let* (_, code) = m_fold (fun (done_ups, sentences) component ->
      let* substSorts = substOf (List.hd_exn component) in
      (* TODO in pi calculus I generate the uplist wrong. Maybe I need to use the version from autosubst25 to calculate *)
      let new_ups = getUps substSorts in
      let ups = list_diff new_ups done_ups in
      let* code_x = Generator.genCodeT component ups in
      let sentences = sentences @ code_x in
      pure @@ (ups @ done_ups, sentences))
      ([], []) components in
  pure code

let genFile () =
  let open REM.Syntax in
  let open REM in
  let* components = getComponents in
  (* let* subs = asks H.sigSubstOf in *)
  (* let* sign = ask in *)
  (* let () = print_endline (H.show_signature sign) in *)
  (* let () = print_endline (H.show_components components) in *)
  (* let () = print_endline (H.show_tIdMap H.pp_tId_list subs) in *)
  let* code = genCode components in
  let ps = (List.map ~f:Coqgen.pr_vernac_expr code) in
  let preamble = get_preamble () in
  pure @@ (preamble
           ^ String.concat (List.map ~f:Pp.string_of_ppcmds ps))

let runGenCode hsig = REM.run (genFile ()) hsig
