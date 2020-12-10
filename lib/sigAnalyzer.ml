open Base
open Util

module H = Hsig
module AL = AssocList

module SortsOrdered = struct
  type t = H.tId
  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end

module G = Graph.Persistent.Digraph.Concrete(SortsOrdered)
module Op = Graph.Oper.P(G)
module C = Graph.Components.Make(G)
type sort_set = Set.M(String).t

(** Build a graph where the vertices are all the sort from the spec and there
 ** is an edge u->v if v occurs directly in u (i.e. if there is some constructor
 ** of u where v is an argument head. ) *)
let build_graph spec =
  let specl = AL.to_list spec in
  List.fold specl ~init:G.empty ~f:(fun g (t, cs) ->
      let args = List.concat_map cs ~f:H.getArgs in
      List.fold args ~init:g ~f:(fun g arg -> G.add_edge g t arg))

(** A sort x needs a binder if it is bound in some sort y and also occurs in y.
 ** A special case happens when x is only bound in some sort in which case the binding
 ** is vacuous and we return an error. *)
let binder_analysis spec occurs_in =
  let open ErrorM in
  let specl = AL.to_list spec in
  let analysis =
    let open Monadic.List.Make.Syntax in
    let* (t, cs) = specl in
    let* H.{ cpositions; cname; _ } = cs in
    let* H.{ binders; head; } = cpositions in
    let* binder = binders in
    let* bound_sort = H.getBinders binder in
    let vacuous = list_none (fun arg -> bound_sort |> occurs_in arg) (H.getArgSorts head) in
    if vacuous then [`Vacuous (t, bound_sort, cname)]
    else [`Binder bound_sort]
  in
  (* I had quite some trouble making an empty set. But in the end it worked like in the
   * documentation for Map https://ocaml.janestreet.com/ocaml-core/latest/doc/core_kernel/Core_kernel/Map/
   * How would I define a specialized StringSet module so I don't have to pass the
   * first order module every time I want to create an empty map? *)
  List.fold analysis ~init:(pure (Set.empty (module String)))
    ~f:(fun bs -> function
        | `Vacuous (t, b, cname) ->
          error ("Vacuous binding in sort "^t^" of bound variable "^b^" in constructor "^cname)
        | `Binder b -> bs >>= fun bs' -> Set.add bs' b |> pure)

(** Return the sublist of the canonical order which correspond to the substitution vector
 ** for the sort t.
 ** These are all the open sorts that occur in t *)
let subordination g canonical_order open_sorts t =
  List.filter canonical_order ~f:(fun s ->
      Set.mem open_sorts s
      && G.mem_edge g t s)

(** Return the strongly connected components, each ordered according to canonical_order.
 ** I suspect that if I used a first order module for the COMPARABLE of the graph which
 ** implemented compare using canonical_sort, the lists in the scc would already by in the
 ** correct order. But I could not find a guarantee in the documentation.
 ** TODO check in the code and maybe do pull request if it's reasonable *)
let topological_sort g canonical_order =
  List.map (C.scc_list g) ~f:(fun component -> list_intersection canonical_order component)

let build_signature (canonical_order, fs, spec) =
  let open ErrorM.Syntax in
  let open ErrorM in
  let g = build_graph spec in
  let transitive_closure = Op.transitive_closure g in
  let* open_sorts = binder_analysis spec (G.mem_edge transitive_closure) in
  let substs = subordination transitive_closure canonical_order open_sorts in
  let subst_of = AL.map (fun t _ -> substs t) spec in
  let components = topological_sort g canonical_order in
  let arguments = AL.map (fun t _ -> G.succ g t) spec in
  pure @@ H.{ sigSpec=spec
            ; sigSubstOf=subst_of
            ; sigComponents=components
            ; sigIsOpen=open_sorts
            ; sigArguments=arguments }
