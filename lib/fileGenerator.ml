(** This module is the entry point for code generation.
 ** It dispatches to the actual code generation in the Generator module.
 ** And when we support printing of Tactics/Type classes it would also dispatch to that in here.
 **  *)
open Util

module CS = ScopeTypes
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
  let open RSEM.Syntax in
  let open RSEM in
  let* is_gen_fext = ask_gen_fext in
  let preamble = match !S.scope_type with
    | S.Unscoped -> unscoped_preamble ^ (if is_gen_fext then unscoped_preamble_axioms else "")
    | S.Wellscoped -> scoped_preamble ^ (if is_gen_fext then scoped_preamble_axioms else "")
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
  let open RSEM.Syntax in
  let open RSEM in
  let* components = get_components in
  (* pair up components with the subsitution vector of their first sort
   * the substitution vector is equal between all sorts of a component *)
  let* subst_sorts_by_component = a_map (fun component ->
      let* subst_sorts = get_substv (List.hd component) in
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
  let open RSEM.Syntax in
  let open RSEM in
  let* components = get_components in
  (* generate the code for all component/lifting pairs *)
  let* ups_by_component = get_ups_by_component () in
  let* as_modules = a_map (fun (component, ups) -> CodeGenerator.generate component ups) ups_by_component in
  pure (AM.concat as_modules)

(** We can filter the generated code based on flags.
    At the moment we only remove fext code if necessary. *)
let filter_code code =
  let open RSEM.Syntax in
  let open RSEM in
  let tags_to_remove = [] in
  (* Check the flags if we have to remove Fext lemmas *)
  let* is_gen_fext = ask_gen_fext in
  let tags_to_remove = if not is_gen_fext 
    then AM.Fext :: tags_to_remove
    else tags_to_remove in
  let code_filtered = AM.remove_tags tags_to_remove code in
  pure code_filtered

(** Generate the Coq file. Here we convert the Coq AST to pretty print expressions and then to strings. *)
let genFile () =
  let open RSEM.Syntax in
  let open RSEM in
  let* preamble = get_preamble () in
  let* code = genCode () in
  let* automation = AutomationGenerator.generate () in
  let* gen_filtered = filter_code (AM.append code automation) in
  let pp = AM.pr_modules (Pp.str preamble) gen_filtered in
  pure (Pp.string_of_ppcmds pp)


(** Run the computation constructed by genFile *)
let run_gen_code hsig fl_allfv fl_fext = RSEM.rse_run (genFile ()) (hsig, { fl_allfv; fl_fext }) AG.initial
