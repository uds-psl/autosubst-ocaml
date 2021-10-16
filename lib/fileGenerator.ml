(** This module is the entry point for code generation.
 ** It dispatches to the actual code generation in the Generator module.
 ** And when we support printing of Tactics/Type classes it would also dispatch to that in here.
 **  *)
open Util

module CS = CoqSyntax
module GG = GallinaGen
module VG = VernacGen
module AM = VG.AutosubstModules
module AG = AutomationGen
module L = Language
module S = Settings

let unscoped_preamble = "Require Import core unscoped.\n\n"
let unscoped_preamble_axioms = "Require Import core_axioms unscoped_axioms.\n"
let scoped_preamble = "Require Import core fintype.\n\n"
let scoped_preamble_axioms = "Require Import core_axioms fintype_axioms.\n"
let setoid_preamble = "Require Import Setoid Morphisms Relation_Definitions.\n\n"

let get_preamble () =
  let open RWEM.Syntax in
  let open RWEM in
  let* gen_fext = is_gen_fext in
  let preamble = match !S.scope_type with
    | S.Unscoped -> unscoped_preamble ^ (if gen_fext then unscoped_preamble_axioms else "")
    | S.Wellscoped -> scoped_preamble ^ (if gen_fext then scoped_preamble_axioms else "")
  in
  pure (preamble ^ setoid_preamble)

(** Generate all the liftings (= Up = fatarrow^y_x) for all pairs of sorts in the given substitution vector.
 ** So that we can later build the lifting functions "X_ty_ty", "X_ty_vl" etc. *)
let getUps subst_sorts =
  let open List in
  let cart = cartesian_product subst_sorts subst_sorts in
  let singles = map (fun (x, y) -> (L.Single x, y)) cart in
  let blists = map (fun (x, y) -> (L.BinderList ("p", x), y)) cart in
  match !S.scope_type with
  | S.Wellscoped -> List.append singles blists
  | S.Unscoped -> singles

(** Generate pairs of the signature's components with their liftings. *)
let get_ups_by_component () =
  let open RWEM.Syntax in
  let open RWEM in
  let* components = getComponents in
  (* pair up components with the subsitution vector of their first sort
   * the substitution vector is equal between all sorts of a component *)
  let* subst_sorts_by_component = a_map (fun component ->
      let* subst_sorts = substOf (List.hd component) in
      pure (component, subst_sorts))
      components in
  (* components are sorted and we start code generation at the leftmost one *)
  let (_, ups) = List.fold_left
      (fun (done_ups, ups) (component, subst_sorts) ->
         let new_ups = list_diff (getUps subst_sorts) done_ups in
         (done_ups @ new_ups, ups @ [(component, new_ups)]))
      ([], []) subst_sorts_by_component in
  pure ups

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
let genCode () =
  let open RWEM.Syntax in
  let open RWEM in
  let open VG in
  let* components = getComponents in
  (* prepare the exports contained in the interface module *)
  let* gen_allfv = is_gen_allfv in
  let the_initial_modules = if gen_allfv
    then AM.{ initial_modules
              with interface_units = initial_modules.interface_units @ [export_ "allfv"] }
    else AM.initial_modules in
  let* gen_fext = is_gen_fext in
  let the_initial_modules = if gen_fext
    then AM.{ initial_modules
              with interface_units = initial_modules.interface_units @ [export_ "fext"] }
    else the_initial_modules in
  (* generate the code for all component/lifting pairs *)
  let* ups_by_component = get_ups_by_component () in
  let* as_modules = a_map (fun (component, ups) -> CodeGenerator.gen_code component ups) ups_by_component in
  pure (AM.concat (the_initial_modules :: as_modules))

let make_file preamble AM.{ ren_subst_units; allfv_units; fext_units; interface_units } =
  let open VG in
  let pp_code = VG.pr_vernac_units (module_ "renSubst" ren_subst_units) in
  let pp_allfv = VG.pr_vernac_units (module_ "allfv" ~imports:[ "renSubst" ] allfv_units) in
  let pp_fext = VG.pr_vernac_units (module_ "fext" ~imports:[ "renSubst" ] fext_units) in
  let pp_interface = VG.pr_vernac_units (module_ "interface" interface_units) in
  let pp_export = VG.pr_vernac_unit (export_ "interface") in
  let text = Pp.(string_of_ppcmds (pp_code ++ pp_allfv ++ pp_fext ++ pp_interface ++ pp_export)) in
  preamble ^ text

(** Generate the Coq file. Here we convert the Coq AST to pretty print expressions and then to strings. *)
let genFile () =
  let open RWEM.Syntax in
  let open RWEM in
  let* preamble = get_preamble () in
  let* code = genCode () in
  let* automation = AutomationGenerator.gen_automation () in
  pure (make_file preamble (AM.append code automation))


(** Run the computation constructed by genFile *)
let run_gen_code hsig gen_allfv gen_fext = RWEM.rwe_run (genFile ()) (hsig, gen_allfv, gen_fext) AG.initial
