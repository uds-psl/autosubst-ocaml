(** My own definitions for reader/writer/state monad
 ***  *)

open Base
open Util

module M = Monadic
module H = Hsig
module AL = AssocList

module type MONAD_READER = sig
  type 'a t
  type r

  include M.Monad.MONAD
    with type 'a t := 'a t

  (* Reader *)
  val ask : r t
  val asks : (r -> 'a) -> 'a t
end

module type MONAD_WRITER = sig
  type 'a t
  type w

  include M.Monad.MONAD
    with type 'a t := 'a t

  val tell : w -> unit t
end

module type MONAD_STATE = sig
  type 'a t
  type s

  include M.Monad.MONAD
    with type 'a t := 'a t

  val get : s t
  val put : s -> unit t
end

module type MONAD_ERROR = sig
  type 'a t
  type e

  include M.Monad.MONAD
    with type 'a t := 'a t

  val error : e -> 'a t
end

(* A combination between reader and writer *)
module type MONAD_RE = sig
  type 'a t
  (* as in Rws.MONAD_RWST I use these two types to include the Monad.MAKE_T signature so that I can have the Syntax signature in MONAD_RE. Then I can use the syntax when defining functions in the RE_Functions functor *)
  type 'a wrapped
  type 'a actual_t

  include MONAD_READER
    with type 'a t := 'a t
  include MONAD_ERROR
    with type 'a t := 'a t

  (* TODO could also abstract over 'a collection *)
  include M.Monad.APPLICATIVE_FUNCTIONS
    with type 'a applicative := 'a t
    with type 'a collection := 'a list

  include M.Monad.MONAD_FUNCTIONS
    with type 'a monad := 'a t
    with type 'a collection := 'a list

  include M.Monad.MAKE_T
    with type 'a t := 'a t
    with type 'a wrapped := 'a wrapped
    with type 'a actual_t := 'a actual_t
end

(* module type MONAD_RWSE = sig
 *   type 'a t
 *
 *   include MONAD_READER
 *     with type 'a t := 'a t
 *   include MONAD_WRITER
 *     with type 'a t := 'a t
 *   include MONAD_STATE
 *     with type 'a t := 'a t
 *   include MONAD_ERROR
 *     with type 'a t := 'a t
 *
 *   include M.Monad.APPLICATIVE_FUNCTIONS
 *     with type 'a applicative := 'a t
 *     with type 'a collection := 'a list
 *   include M.Monad.MONAD_FUNCTIONS
 *     with type 'a monad := 'a t
 *     with type 'a collection := 'a list
 * end *)

(* here I need to instantiate the read and error type
 * it's like
 * (MonadReader Signature m, MonadError String m) => ...
 * in Haskell *)
module RE_Functions (RE: MONAD_RE
                  with type r := H.t
                  with type e := string) =
struct
  open RE.Syntax
  open RE

(* -- Accessing the signature
 * -- These functions work on both GenM and SigM *)

  let constructors id =
    let* spec = asks H.sigSpec in
    match (AL.assoc id spec) with
    | Some cs -> pure cs
    | None -> error @@ "constructors called on invalid type: " ^ id

  let substOf tid =
    let* substs = asks H.sigSubstOf in
    match ListLabels.assoc_opt tid substs with
    | Some cs -> pure cs
    | None -> error @@ "substOf called on invalid type: " ^ tid

  let isOpen id =
    let* opens = asks H.sigIsOpen in
    pure @@ List.mem opens id ~equal:equal_string

  let definable id =
    let* b = isOpen id in
    let* cs = constructors id in
    pure (b || not (List.is_empty cs))

  (* Yields true if at least one variable is contained. *)
  let hasArgs id = (fun l -> List.is_empty l |> not) <$> substOf id

  let arguments id =
    let* args = asks H.sigArguments in
    match AL.assoc id args with
    | Some ts -> pure ts
    | None -> error @@ "arguments called on invalid type: " ^ id

  let successors id =
    let* cs = constructors id in
    pure @@ List.(concat_map cs
                    ~f:(function { positions; _ } ->
                        concat_map positions
                          ~f: (function { arg; _ } -> H.getIds arg )))

  let arguments id =
    let* args = asks H.sigArguments in
    match (AL.assoc id args) with
    | Some ts -> pure ts
    | None -> error @@ "arguments called on invalid type: " ^ id

  let realDeps x =
    let* args = arguments x in
    let* f = asks H.sigExt in
    pure @@ match (AL.assoc x f) with
    | Some y -> if List.mem args y ~equal:Poly.equal then [y] else []
    | None -> []

  let complete_ x =
    let* xs = realDeps x in
    pure @@ x ^ " " ^ String.concat ~sep:" " xs

  (* TODO belongs to modular code *)
  let extend_ x =
    let* f = asks H.sigExt in
    pure @@ match (AL.assoc x f) with
    | Some y -> y
    | None -> x

  let isFeature x =
    let* y = extend_ x in
    (* fun fact Jane Street's core/base library only allows <> for int so you need to open scopes every time you want to compare something else https://stackoverflow.com/questions/61184401/why-my-ocaml-operator-is-only-applied-to-int *)
    pure @@ String.(x <> y)

  let types =
    let* c = asks H.sigComponents in
    pure @@ List.concat_map ~f:fst c

  let getComponent x =
    let* comps = asks H.sigComponents in
    pure @@ List.(concat @@
                  filter_map comps ~f:(fun (l, r) -> if List.mem l x ~equal:equal_string
                                                     || List.mem r x ~equal:equal_string
                                        then Some (List.append l r)
                                        else None))

  let prev_ x =
    let* ts = types in
    a_filter (fun t ->
        let* y = extend_ t in
        pure @@ Poly.(x = y))
      (list_remove ts x)

  let isOpenComponent x =
    let* xs = prev_ x in (* TODO kathrin: all sorts that are features *)
    let* ys = a_filter isOpen xs in
    List.is_empty ys |> not |> pure

  let recursive xs =
    if (List.is_empty xs) then error "Can't determine whether the component is recursive."
    else let* args = successors (List.hd_exn xs) in
      let* zs = a_map prev_ xs in
      let xargs = list_intersection xs args |> List.is_empty |> not in
      let zempty = List.(filter zs ~f:(fun z -> is_empty z |> not) |> is_empty |> not) in
      (* TODO I should not need parentheses here *)
      pure @@ (xargs || zempty)

  (* a lot of binding going on here *)
  let boundBinders xs =
    let* binders = a_map (fun x ->
        constructors x >>= fun cs -> pure @@
        List.(cs >>= function { positions; _ } ->
            positions >>= function { binders; _ } ->
              binders >>= H.getBinders)) xs in
    pure @@ List.concat binders

  let rec hasRenamings x =
    let* y = extend_ x in
    let* xs = getComponent y in
    let* boundBinders = boundBinders xs in
    let* all = types in
    let occursIn = list_diff all xs in
    let* occ = a_filter (fun z ->
        let* zs = successors z in
        pure @@ List.mem zs y ~equal:equal_string)
        occursIn in
    let* bs = a_map hasRenamings occ in
    let xs_bb = list_intersection xs boundBinders |> List.is_empty |> not in
    let bs' = List.filter bs ~f:(fun b -> b) |> List.is_empty |> not in
    pure (xs_bb || bs')
end
