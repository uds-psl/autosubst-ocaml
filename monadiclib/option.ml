module MakeT (Wrapped : Monad.MONAD) = struct
  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module OptionMonadPlus :
    Monad.MONAD_PLUS with type 'a t = 'a option Wrapped.t = struct
    type 'a t = 'a option Wrapped.t

    let pure v = Some v |> Wrapped.pure

    let map f x =
      let+ v = x in
      Stdlib.Option.map f v

    let apply fa xa =
      let+ f = fa and+ x = xa in
      match (f, x) with Some f', Some x' -> Some (f' x') | _ -> None

    let join v =
      let* x = v in
      match x with Some x' -> x' | _ -> Wrapped.pure None

    let bind m f = join (map f m)

    let empty () = Wrapped.pure None

    let append xa ya =
      let+ x = xa and+ y = ya in
      match x with None -> y | _ -> x
  end

  include OptionMonadPlus

  let elevate v =
    let+ x = v in
    Some x

  include Monad.MonadPlusInfix (OptionMonadPlus)

  let run m = m [@@inline]

  let create x = x [@@inline]

  let none = empty
end

module Make = MakeT (Identity)
