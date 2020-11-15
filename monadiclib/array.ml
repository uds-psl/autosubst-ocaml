module MakeT (Wrapped : Monad.MONAD) = struct
  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module ArrayMonadPlus : Monad.MONAD_PLUS with type 'a t = 'a array Wrapped.t =
  struct
    type 'a t = 'a array Wrapped.t

    let pure v = [| v |] |> Wrapped.pure

    let map f x =
      let+ v = x in
      Stdlib.Array.map f v

    let apply fa xa =
      let+ fs = fa and+ xs = xa in
      let accum curr acc =
        let l1 = Stdlib.Array.map curr xs in
        Stdlib.Array.append l1 acc
      in
      Stdlib.Array.fold_right accum fs [||]

    let sequence ms =
      let open Monad.ApplicativeFunctionsArray (Wrapped) in
      sequence ms

    let join v =
      let* (x : 'a t array) = v in
      let+ xs = sequence x in
      Stdlib.Array.to_list xs |> Stdlib.Array.concat

    let bind m f = join (map f m)

    let append xa ya =
      let+ x = xa and+ y = ya in
      Stdlib.Array.append x y

    let empty () = Wrapped.pure [||]
  end

  include ArrayMonadPlus
  include Monad.MonadPlusInfix (ArrayMonadPlus)

  let run m = m [@@inline]

  let create x = x [@@inline]

  let elevate v =
    let+ x = v in
    [| x |]
end

module Make = MakeT (Identity)
