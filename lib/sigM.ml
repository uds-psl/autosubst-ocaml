open Base

module M = Monadic
module H = Hsig

type 'a wrapped = 'a M.Result.Make(String).t
type 'a actual_t = H.t -> 'a M.Result.Make(String).t

module GenError = M.Result.Make(String)
module RE = M.Reader.MakeT(GenError)(struct type t = H.t end)

include RE

let ask = peek
let asks f = f <$> ask

let error s = GenError.error s |> elevate

include M.Monad.ApplicativeFunctionsList(RE)
include M.Monad.MonadFunctionsList(RE)

let map2 f a b =
  let open Syntax in
  let* f' = map f a in
  map f' b

let rec invert =
  let open Syntax in function
  | [] -> pure []
  | m :: ms ->
    let* m' = m in
    let* ms' = invert ms in
    pure @@ m' :: ms'

let a_map2_exn f a b =
  invert @@ List.map2_exn ~f a b

(** The m_fold of the monad library I'm using is actually also a fold_left by doing a fold_right on the list and using continuations. So this is unused *)
let rec m_fold_left ~f ~init xs =
  let open Syntax in
  match xs with
  | [] -> pure init
  | x :: xs ->
    let* init = f init x in
    m_fold_left ~f ~init xs

let a_concat_map f xs =
  map List.concat @@ a_map f xs

let m_guard cond m =
  if cond then m else pure []
