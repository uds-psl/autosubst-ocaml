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
