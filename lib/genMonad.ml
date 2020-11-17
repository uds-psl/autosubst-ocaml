open Core
open Util

module M = Monadic
module H = Hsig
module AL = AssocList

module type GENM = sig
  type 'a t

  include Rws.MONAD_RWST
    with type 'a t := 'a t

  include Monads.MONAD_ERROR
    with type 'a t := 'a t
end

module GenM = struct
  module GenError = M.Result.Make(String)
  (* TODO Autosubst uses some Doc type for pretty printing in the writer *)
  module StringMon = struct
    type t = string
    let empty = ""
    let append = (^)
  end
  type scope = (H.vId * int) list
  module RWS = Rws.MakeT(GenError)(struct type t = H.t end)(StringMon)(struct type t = scope end)
  include RWS

  let error s = GenError.error s |> elevate

  include M.Monad.ApplicativeFunctionsList(RWS)
  include M.Monad.MonadFunctionsList(RWS)
end

open GenM.Syntax
open GenM
open MonadReaderError.Functions(GenM)

let lookupScope =
  AL.assoc_default ~default:0

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

let fresh id =
  let* scope = get in
  let n = lookupScope id scope in
  let* () = put @@ (AL.insert id (n+1) scope) in
  if n > 0
  then pure @@ id ^ (string_of_int n)
  else pure id

let tfresh id =
  let* scope = get in
  let n = lookupScope id scope in
  if n > 0
  then pure @@ id ^ (string_of_int n)
  else pure id

(* TODO what if empty string? *)
let intern tid =
  fresh String.(of_char @@ get (lowercase tid) 0 )

let withScope m =
  let* scope = get in
  let* v = m in
  let* () = put scope in
  pure v


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
