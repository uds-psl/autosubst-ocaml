(** This module is the entry point for code generation.
 ** It dispatches to the actual code generation in the Generator module.
 ** And when we support printing of Tactics/Type classes it would also dispatch to that in here.
 **  *)
open Util

module CS = CoqSyntax
module CG = Coqgen
(* module TG = Tacgen *)
module H = Hsig

let unscoped_preamble = "Require Import core unscoped.\n\n"
let unscoped_preamble_axioms = "Require Import core core_axioms unscoped unscoped_axioms.\n"
let scoped_preamble = "Require Import core fintype.\n\n"
let scoped_preamble_axioms = "Require Import core core_axioms fintype fintype_axioms.\n"
let base_preamble = Scanf.format_from_string "Require Import %s.\n\n" "%s"

let get_preambles outfile_basename =
  let base_preamble = Printf.sprintf base_preamble outfile_basename in
  match !Settings.scope_type with
  | H.Unscoped -> (unscoped_preamble, unscoped_preamble_axioms ^ base_preamble)
  | H.WellScoped -> (scoped_preamble, scoped_preamble_axioms ^ base_preamble)

(** Generate all the liftings (= Up = fatarrow^y_x) for all pairs of sorts in the current component.
 ** So that we can later build the lifting functions "X_ty_ty", "X_ty_vl" etc. *)
let getUps component =
  let open List in
  let cart = cartesian_product component component in
  let singles = map (fun (x, y) -> (H.Single x, y)) cart in
  let blists = map (fun (x, y) -> (H.BinderList ("p", x), y)) cart in
  let scope_type = !Settings.scope_type in
  match scope_type with
  | H.WellScoped -> List.append singles blists
  | H.Unscoped -> singles

(* deriving a comparator for a type and packing it in a module
 * from https://stackoverflow.com/a/59266326 *)
(* I refactored out the code where I needed the comparator to call stable_dedup on a list but leaving this in for reference *)
(* module UpsComp = struct
 *   module T = struct
 *     type t = H.binder * string [@@deriving compare]
 *     let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_opaque
 *   end
 *
 *   include T
 *   include Comparable.Make(T)
 * end *)

(** Generate the fixpoints/lemmas for all the connected components *)
let genCode components =
  let open REM.Syntax in
  let open REM in
  let open CG in
  let* (_, code, fext_code) = m_fold (fun (done_ups, vexprs, fext_exprs) component ->
      let* substSorts = substOf (List.hd component) in
      let new_ups = getUps substSorts in
      let ups = list_diff new_ups done_ups in
      let* { as_exprs; as_fext_exprs } = Generator.genCodeT component ups in
      pure @@ (ups @ done_ups, vexprs @ as_exprs, fext_exprs @ as_fext_exprs))
      ([], [], []) components in
  pure { as_exprs = code; as_fext_exprs = fext_code }

let genTactics () =
  let open REM.Syntax in
  let open REM in
  let* info = failwith "tell from writer monad" in
  pure (TacticGenerator.gen_tactics_T info)

let make_file preamble code tactics =
  let pp_code = List.concat_map Coqgen.pr_vernac_unit code in
  let pp_tactics = List.map Tacgen.pr_tactic tactics in
  let text = List.map Pp.string_of_ppcmds (pp_code @ pp_tactics) in
  preamble ^ (String.concat "" text)

(** Generate the Coq file. Here we convert the Coq AST to pretty print expressions and then to strings. *)
let genFile outfile_basename =
  let open REM.Syntax in
  let open REM in
  let open CG in
  (* let open TG in *)
  let* components = getComponents in
  let* { as_exprs = code; as_fext_exprs = fext_code } = genCode components in
  (* let* { as_tactics = tactics; as_fext_tactics = fext_tactics } = genTactics () in *)
  let preamble, preamble_axioms = get_preambles outfile_basename in
  pure (make_file preamble code [], make_file preamble_axioms fext_code [])

(** Run the computation constructed by genFile *)
let run_gen_code hsig outfile = REM.run (genFile outfile) hsig
