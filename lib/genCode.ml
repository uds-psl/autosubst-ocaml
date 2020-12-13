(** This module is the entry point for code generation.
 ** It dispatches to the actual code generation in the Generator module.
 ** And when we support printing of Tactics/Type classes it would also dispatch to that in here.
 **  *)
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

(** Generate all the liftings (= Up = fatarrow^y_x) for all pairs of sorts in the current component.
 ** So that we can later build the lifting functions "X_ty_ty", "X_ty_vl" etc. *)
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
(* I refactored out the code where I needed the comparator to call stable_dedup on a list but leaving this in for reference *)
module UpsComp = struct
  module T = struct
    type t = H.binder * string [@@deriving compare]
    let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_opaque
  end

  include T
  include Comparable.Make(T)
end

(** Generate the fixpoints/lemmas for all the connected components *)
let genCode components =
  let open REM.Syntax in
  let open REM in
  let* (_, code) = m_fold (fun (done_ups, sentences) component ->
      let* substSorts = substOf (List.hd_exn component) in
      let new_ups = getUps substSorts in
      let ups = list_diff new_ups done_ups in
      let* code_x = Generator.genCodeT component ups in
      let sentences = sentences @ code_x in
      pure @@ (ups @ done_ups, sentences))
      ([], []) components in
  pure code

(** Generate the Coq file. Here we convert the Coq AST to pretty print expressions and then to strings. *)
let genFile () =
  let open REM.Syntax in
  let open REM in
  let* components = getComponents in
  let* code = genCode components in
  let ps = (List.map ~f:Coqgen.pr_vernac_expr code) in
  let preamble = get_preamble () in
  pure @@ (preamble
           ^ String.concat (List.map ~f:Pp.string_of_ppcmds ps))

(** Run the computation constructed by genFile *)
let run_gen_code hsig = REM.run (genFile ()) hsig
