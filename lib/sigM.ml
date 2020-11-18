open Core
open Util
open Monads

module M = Monadic
module H = Hsig

module type SIGM = Monads.MONAD_RE
    with type 'a wrapped = 'a M.Result.Make(String).t
    with type 'a actual_t = H.t -> 'a M.Result.Make(String).t
    with type e := string
    with type r := H.t


module SigM : SIGM = struct
  type 'a wrapped = 'a M.Result.Make(String).t
  type 'a actual_t = H.t -> 'a M.Result.Make(String).t

  module GenError = M.Result.Make(String)
  module MM = M.Reader.MakeT(GenError)(struct type t = H.t end)

  include MM

  let ask = peek
  let asks f = f <$> ask

  let error s = GenError.error s |> elevate

  include M.Monad.ApplicativeFunctionsList(MM)
  include M.Monad.MonadFunctionsList(MM)

end
