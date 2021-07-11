(** This module is the entry point for code generation.
 ** It dispatches to the actual code generation in the Generator module.
 ** And when we support printing of Tactics/Type classes it would also dispatch to that in here.
 **  *)
open Util

module CS = CoqSyntax
module GG = GallinaGen
module VG = VernacGen
module AG = AutomationGen
module L = Language
module S = Settings

let unscoped_preamble = "Require Import core unscoped.\n\n"
let unscoped_preamble_axioms = "Require Import core core_axioms unscoped unscoped_axioms.\n"
let scoped_preamble = "Require Import core fintype.\n\n"
let scoped_preamble_axioms = "Require Import core core_axioms fintype fintype_axioms.\n"
let base_preamble = Scanf.format_from_string "Require Import %s.\n\n" "%s"
let setoid_preamble = "Require Import Setoid Morphisms Relation_Definitions.\n\n"

let get_preambles outfile_basename axioms_separate =
  let base_preamble = Printf.sprintf base_preamble outfile_basename in
  if axioms_separate then
    match !S.scope_type with
    | S.Unscoped -> (unscoped_preamble ^ setoid_preamble, unscoped_preamble_axioms ^ base_preamble)
    | S.WellScoped -> (scoped_preamble ^ setoid_preamble, scoped_preamble_axioms ^ base_preamble)
  else
    match !S.scope_type with
    | S.Unscoped -> (unscoped_preamble_axioms ^ setoid_preamble, "")
    | S.WellScoped -> (scoped_preamble_axioms ^ setoid_preamble, "")

(** Generate all the liftings (= Up = fatarrow^y_x) for all pairs of sorts in the current component.
 ** So that we can later build the lifting functions "X_ty_ty", "X_ty_vl" etc. *)
let getUps component =
  let open List in
  let cart = cartesian_product component component in
  let singles = map (fun (x, y) -> (L.Single x, y)) cart in
  let blists = map (fun (x, y) -> (L.BinderList ("p", x), y)) cart in
  match !S.scope_type with
  | S.WellScoped -> List.append singles blists
  | S.Unscoped -> singles

(* deriving a comparator for a type and packing it in a module
 * from https://stackoverflow.com/a/59266326 *)
(* I refactored out the code where I needed the comparator to call stable_dedup on a list but leaving this in for reference *)
(* module UpsComp = struct
 *   module T = struct
 *     type t = L.binder * string [@@deriving compare]
 *     let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_opaque
 *   end
 *
 *   include T
 *   include Comparable.Make(T)
 * end *)

(** Generate the fixpoints/lemmas for all the connected components *)
let genCode components =
  let open RWEM.Syntax in
  let open RWEM in
  let open VG in
  let* (_, code, fext_code) = m_fold (fun (done_ups, vexprs, fext_exprs) component ->
      let* substSorts = substOf (List.hd component) in
      let new_ups = getUps substSorts in
      let ups = list_diff new_ups done_ups in
      let* { as_units; as_fext_units } = CodeGenerator.gen_code component ups in
      pure @@ (ups @ done_ups, vexprs @ as_units, fext_exprs @ as_fext_units))
      ([], [], []) components in
  pure { as_units = code; as_fext_units = fext_code }

let make_file preamble code tactics =
  let pp_code = VG.pr_vernac_units code in
  let pp_tactics = VG.pr_vernac_units tactics in
  let text = Pp.(string_of_ppcmds (pp_code ++ pp_tactics)) in
  preamble ^ text

(** Generate the Coq file. Here we convert the Coq AST to pretty print expressions and then to strings. *)
let genFile outfile_basename axioms_separate =
  let open RWEM.Syntax in
  let open RWEM in
  let open VG in
  let* components = getComponents in
  (* I accidentally put the hack args above the call to genCode which does not work b/c the state is not set. Another point why losing referential transparency sucks *)
  let* { as_units = code; as_fext_units = fext_code } = genCode components in
  (* HACK clear implicit arguments so that the fext code works. Either I do this or I will have to use @ in the code *)
  let* hack_args = AutomationGenerator.gen_arguments_clear () in
  let* { as_units = automation; as_fext_units = fext_automation } = AutomationGenerator.gen_automation () in
  let preamble, preamble_axioms = get_preambles outfile_basename axioms_separate in
  pure (make_file preamble code automation, make_file preamble_axioms (hack_args @ fext_code) fext_automation)

(** Run the computation constructed by genFile *)
let run_gen_code hsig outfile axioms_separate = RWEM.rwe_run (genFile outfile axioms_separate) hsig AG.initial
