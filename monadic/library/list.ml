module MakeT (Wrapped : Monad.MONAD) = struct
  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module ListMonadPlus : Monad.MONAD_PLUS with type 'a t = 'a list Wrapped.t =
  struct
    type 'a t = 'a list Wrapped.t

    let pure v = [ v ] |> Wrapped.pure

    let map f x =
      let+ v = x in
      Stdlib.List.map f v

    let apply fa xa =
      let+ fs = fa and+ xs = xa in
      let accum curr acc =
        let l1 = Stdlib.List.map curr xs in
        l1 @ acc
      in
      Stdlib.List.fold_right accum fs []

    let sequence ms =
      let open Monad.ApplicativeFunctionsList (Wrapped) in
      sequence ms

    let join v =
      let* (x : 'a t list) = v in
      let+ xs = sequence x in
      Stdlib.List.concat xs

    let bind m f = join (map f m)

    let append xa ya =
      let+ x = xa and+ y = ya in
      x @ y

    let empty () = Wrapped.pure []
  end

  include ListMonadPlus
  include Monad.MonadPlusInfix (ListMonadPlus)

  let run m = m [@@inline]

  let create x = x [@@inline]

  let elevate v =
    let+ x = v in
    [ x ]
end

module Make = MakeT (Identity)
