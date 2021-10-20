(** This module implements the Reader-State-Error monad.
    It's used pervasively through the code generation so that all the generator functions
    can read the signature. *)
open Util

module M = Monadic
module L = Language
module AG = AutomationGen
module AL = AssocList
module S = Settings


(* The state is AutomationGen.t which contains all necessary information to generate the automation. *)
module SE = M.State.MakeT(ErrorM)(struct type t = AG.t end)
(* We can read a Language.t signature and two flags: if we generate allfv lemmas and if we generate *)
module RSE = M.Reader.MakeT(SE)(struct type t = (L.t * S.flags) end)

include RSE


(** Redefine all the monad functions using functions from the nested monads. *)

let error s = ErrorM.error s |> SE.elevate |> elevate
let ask = peek >>= fun (s, _) -> pure s (* [ask] returns the signature by default *)
let asks f = f <$> ask
let ask_gen_allfv = peek >>= fun (_, { fl_allfv; _ }) -> pure fl_allfv
let ask_gen_fext = peek >>= fun (_, { fl_fext; _}) -> pure fl_fext
let put x = SE.put x |> elevate
let get = SE.get |> elevate
let gets f = f <$> get

let rse_run m r = SE.run (run m r)

(** This module contains all the tell_ functions that get called during code generation 
    to put information in the state to use in the automation generation. *)
module Tells = struct
  open AG
  open Syntax

  let tell_rewrite_no_fext x =
    let* info = get in
    put { info with asimpl_rewrite_no_fext = x :: info.asimpl_rewrite_no_fext }

  let tell_rewrite_fext x =
    let* info = get in
    put { info with asimpl_rewrite_fext = x :: info.asimpl_rewrite_fext }

  let tell_rewrite_base x =
    let* info = get in
    put { info with asimpl_rewrite_base = x :: info.asimpl_rewrite_base }

  let tell_cbn_function x =
    let* info = get in
    put { info with asimpl_cbn_functions = x :: info.asimpl_cbn_functions }

  let tell_unfold_function x =
    let* info = get in
    put { info with asimpl_unfold_functions = x :: info.asimpl_unfold_functions }

  let tell_substify_lemma_fext x =
    let* info = get in
    put { info with substify_lemmas_fext = x :: info.substify_lemmas_fext }

  let tell_substify_lemma x =
    let* info = get in
    put { info with substify_lemmas = x :: info.substify_lemmas }

  let tell_auto_unfold_function x =
    let* info = get in
    put { info with auto_unfold_functions = x :: info.auto_unfold_functions }

  let tell_argument x =
    let* info = get in
    put { info with arguments = x :: info.arguments }

  let tell_class x =
    let* info = get in
    put { info with classes = x :: info.classes }

  let tell_proper_instance x =
    let* info = get in
    put { info with proper_instances = x :: info.proper_instances }

  let tell_instance x =
    let* info = get in
    put { info with instances = x :: info.instances }

  let tell_notation x =
    let* info = get in
    put { info with notations = x :: info.notations }
end
include Tells

include M.Monad.ApplicativeFunctionsList(RSE)
include M.Monad.MonadFunctionsList(RSE)
include Monads.ExtraFunctionsList(RSE)

(** Now we define the common functions that are used in
    code generation or signature graph generation. *)
open RSE.Syntax

(** Get all non-variable constructors of a sort. *)
let get_constructors sort =
  let* spec = asks L.sigSpec in
  match AL.assoc sort spec with
  | Some cs -> pure cs
  | None -> error @@ "get_constructors called with unknown sort: " ^ sort

(** Get the substitution vector for a sort. *)
let get_substv sort =
  let* substs = asks L.sigSubstOf in
  match AL.assoc sort substs with
  | Some substSorts -> pure substSorts
  | None -> error @@ "get_substv called with unknown sort: " ^ sort

(** Check whether a sort has a variable constructor, i.e. is open. *)
let check_open sort =
  let* opens = asks L.sigIsOpen in
  pure @@ L.SSet.mem sort opens

(** Check if a sort is definable. 
    A sort is definable if it has any constructor. *)
let check_definable sort =
  let* is_open = check_open sort in
  let* ctors = get_constructors sort in
  let res = (is_open || list_nempty ctors) in
  pure res

(** Check if a sort has a substitution vector. *)
let check_args sort = (fun l -> list_empty l |> not) <$> get_substv sort

(** Get the arguments (all sorts in head positions) of a sort. *)
let get_arguments sort =
  let* args = asks L.sigArguments in
  match AL.assoc sort args with
  | Some ts -> pure ts
  | None -> error @@ "get_arguments called with unknown sort: " ^ sort

(** Get all components. *)
let get_components = asks L.sigComponents

(** Get all sorts. *)
let get_all_sorts = List.concat <$> get_components

(** Get the component that a sort belongs to *)
let get_component sort =
  let* components = get_components in
  match List.find_opt (fun component -> List.mem sort component) components with
  | None -> error @@ "get_component called with unknown sort: " ^ sort 
  | Some component -> pure component

(** Check if a component is recursive. 
    A component is recursive if the arguments a sort of a component and the component itself overlaps.
    We can only check the first element of the component because they all have the same substitution vector. *)
let isRecursive component =
  if (list_empty component) then error "check_recursive called with empty component."
  else 
    let* args = get_arguments (List.hd component) in
    pure (list_nempty (list_intersection component args))

(** get all the bound sorts that appear in a component *)
let boundBinders component =
  let* ctors = a_concat_map get_constructors component in
  let binders =
    let open Monadic.List.Make.Syntax in
    let* L.{ cpositions; _ } = ctors in
    let* L.{ binders; _ } = cpositions in
    let* binder = binders in
    [ L.get_bound_sort binder ] in
  pure binders

(** A sort needs renamings
 ** either if it is an argument in a sort of a different component that needs renamings
 ** or if any sort of the component appears as a binder in the component
 ** TODO implement in sigAnalysis *)
let rec hasRenamings sort =
  let* component = get_component sort in
  let* boundBinders = boundBinders component in
  let* all_types = get_all_sorts in
  let all_other_types = list_diff all_types component in
  let* occ = a_filter (fun sort' ->
      let* arguments' = get_arguments sort' in
      pure @@ List.mem sort arguments')
      all_other_types in
  (* DONE that is not structural recursion. But it probably terminates. We might have to additionally keep track of all previously visited components.
   * Was able to translate it to Gallina by doing moving this function to the graph analysis stage.
   * It works because we can precompute hasRenamings once for each sort similar to to how we compute strongly connected components without recursion. *)
  let* bs = a_map hasRenamings occ in
  let xs_bb = list_intersection component boundBinders |> list_empty |> not in
  let bs' = list_any bs in
  let res = (xs_bb || bs') in
  (* let () = print_endline ("renaming " ^ sort ^ (string_of_bool res)) in *)
  pure res
