(** This module analyzes the output of the SigParser
 **  and build the signature that we then use during code generation. *)
open Util

module L = Language
module AL = AssocList

module SortsOrdered = struct
  type t = L.tId
  let compare = String.compare
  let hash = Hashtbl.hash
  let equal = String.equal
end

module G = Graph.Persistent.Digraph.Concrete(SortsOrdered)
module Op = Graph.Oper.P(G)
module C = Graph.Components.Make(G)
module SSet = Set.Make(String)

(** Build a graph where the vertices are all the sort from the spec and there
 ** is an edge u->v if v occurs directly in u (i.e. if there is some constructor
 ** of u where v is an argument head. ) *)
let build_graph spec =
  let specl = AL.to_list spec in
  List.fold_left (fun g (t, cs) ->
      let args = List.(concat (map L.getArgs cs)) in
      List.fold_left (fun g arg -> G.add_edge g t arg) g args)
    G.empty specl

(** A sort x needs a binder if it is bound in some sort y and also occurs in y.
 ** A special case happens when x is only bound in some sort in which case the binding
 ** is vacuous and we return an error. *)
let binder_analysis spec occurs_in =
  let open ErrorM in
  let specl = AL.to_list spec in
  let analysis =
    let open Monadic.List.Make.Syntax in
    let* (t, cs) = specl in
    let* L.{ cpositions; cname; _ } = cs in
    let* L.{ binders; head; } = cpositions in
    let* binder = binders in
    let bound_sort = L.get_bound_sort binder in
    let vacuous = not (List.exists (fun arg -> bound_sort |> occurs_in arg) (L.getArgSorts head)) in
    if vacuous then [`Vacuous (t, bound_sort, cname)]
    else [`Binder bound_sort]
  in
  (* I had quite some trouble making an empty set. But in the end it worked like in the
   * documentation for Map https://ocaml.janestreet.com/ocaml-core/latest/doc/core_kernel/Core_kernel/Map/
   * How would I define a specialized StringSet module so I don't have to pass the
   * first order module every time I want to create an empty map? *)
  List.fold_left (fun bs -> function
      | `Vacuous (t, b, cname) ->
        error ("Vacuous binding in sort "^t^" of bound variable "^b^" in constructor "^cname)
      | `Binder b -> bs >>= fun bs' -> SSet.add b bs' |> pure)
    (pure (SSet.empty)) analysis

(** Return the sublist of the canonical order which correspond to the substitution vector
 ** for the sort t.
 ** These are all the open sorts that (reflexively) occur in t *)
let subordination g canonical_order open_sorts t =
  List.filter (fun s ->
      SSet.mem s open_sorts
      && G.mem_edge g t s)
    canonical_order

(** Return the strongly connected components, each ordered according to canonical_order.
 ** I suspect that if I used a first order module for the COMPARABLE of the graph which
 ** implemented compare using canonical_sort, the lists in the scc would already by in the
 ** correct order. But I could not find a guarantee in the documentation.
 ** TODO check in the code and maybe do pull request if it's reasonable *)
let topological_sort g canonical_order =
  List.map (fun component -> list_intersection canonical_order component) (C.scc_list g)

let build_signature (canonical_order, fs, spec, _) =
  let open ErrorM.Syntax in
  let open ErrorM in
  let g = build_graph spec in
  let* open_sorts = binder_analysis spec (G.mem_edge @@ Op.transitive_closure g) in
  let substs = subordination (Op.transitive_closure ~reflexive:true g) canonical_order open_sorts in
  let subst_of = AL.map (fun t _ -> substs t) spec in
  let components = topological_sort g canonical_order in
  let arguments = AL.map (fun t _ -> G.succ g t) spec in
  pure @@ L.{ sigSpec=spec
            ; sigSubstOf=subst_of
            ; sigComponents=components
            ; sigIsOpen=open_sorts
            ; sigArguments=arguments }
