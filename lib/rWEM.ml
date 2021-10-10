(** This module implements the ReaderT(Error) monad for signatures.
 ** It's used pervasively through the code generation so that all the generator functions
 ** can read the signature. *)
open Util

module M = Monadic
module L = Language
module AG = AutomationGen
module AL = AssocList


module WE = M.State.MakeT(ErrorM)(struct type t = AG.t end)
module RWE = M.Reader.MakeT(WE)(struct type t = (L.t * bool * bool) end)

include RWE

let ask = peek >>= fun (s, _, _) -> pure s
let asks f = f <$> ask
let is_gen_allfv = peek >>= fun (_, gen_allfv, _) -> pure gen_allfv
let is_gen_fext = peek >>= fun (_, _, gen_fext) -> pure gen_fext

let put x = WE.put x |> elevate
let get = WE.get |> elevate
let gets f = f <$> get

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

let error s = ErrorM.error s |> WE.elevate |> elevate

let rwe_run m r = WE.run (run m r)

include M.Monad.ApplicativeFunctionsList(RWE)
include M.Monad.MonadFunctionsList(RWE)
include Monads.ExtraFunctionsList(RWE)

(** In the following we collect the functions that are used either in
 ** code generation or signature graph generation.
 ** TODO implement signature graph generation in dot format.
 ** The ocamlgraph library seems to support it ootb *)
open RWE.Syntax

(** return non-variable constructors of a sort *)
let constructors sort =
  let* spec = asks L.sigSpec in
  match AL.assoc sort spec with
  | Some cs -> pure cs
  | None -> error @@ "constructors called with unknown sort " ^ sort

(** return the substitution vector for a sort *)
let substOf sort =
  let* substs = asks L.sigSubstOf in
  match AL.assoc sort substs with
  | Some substSorts -> pure substSorts
  | None -> error @@ "substOf called with unknown sort " ^ sort

(** check whether a sort has a variable constructor *)
let isOpen sort =
  let* opens = asks L.sigIsOpen in
  pure @@ L.SSet.mem sort opens

(** A sort is definable if it has any constructor *)
let isDefinable sort =
  let* b = isOpen sort in
  let* cs = constructors sort in
  let res = (b || not (list_empty cs)) in
  (* if not res
   * then failwith ("sort not definable " ^ sort)
   * else *)
    pure res

(** check if a sort has a substitution vector *)
let hasArgs sort = (fun l -> list_empty l |> not) <$> substOf sort

(** return the arguments (all sorts in head positions) of a sort *)
let getArguments sort =
  let* args = asks L.sigArguments in
  match AL.assoc sort args with
  | Some ts -> pure ts
  | None -> error @@ "arguments called with unknown sort" ^ sort

(** return all components *)
let getComponents = asks L.sigComponents

(** return all known sorts *)
let getAllSorts = List.concat <$> getComponents

(** get the component that a sort belongs to *)
let getComponent s =
  let* components = asks L.sigComponents in
  pure @@ List.(concat @@ filter_map (fun component ->
      if mem s component then Some component else None)
      components)

(** Check if the arguments of the first sort of a component and the component itself overlaps
 ** We can only check the first element of the component because they all have the same
 ** substitution vector. *)
let isRecursive xs =
  if (list_empty xs) then error "Can't determine whether the component is recursive."
  else let* args = getArguments (List.hd xs) in
    list_intersection xs args |> list_empty |> not |> pure

(** get all the bound sorts that appear in a component *)
let boundBinders component =
  let* constructors = a_concat_map constructors component in
  let binders =
    let open Monadic.List.Make.Syntax in
    let* L.{ cpositions; _ } = constructors in
    let* L.{ binders; _ } = cpositions in
    let* binder = binders in
    [ L.get_bound_sort binder ] in
  pure binders

(** A sort needs renamings
 ** either if it is an argument in a sort of a different component that needs renamings
 ** or if any sort of the component appears as a binder in the component *)
let rec hasRenamings sort =
  let* component = getComponent sort in
  let* boundBinders = boundBinders component in
  let* all_types = getAllSorts in
  let all_other_types = list_diff all_types component in
  let* occ = a_filter (fun sort' ->
      let* arguments' = getArguments sort' in
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
