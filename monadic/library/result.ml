module MakeT
    (Wrapped : Monad.MONAD) (E : sig
      type t
    end) =
struct
  type e = E.t

  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module ResultMonad : Monad.MONAD with type 'a t = ('a, e) result Wrapped.t =
  struct
    type 'a t = ('a, e) result Wrapped.t

    let pure v = Ok v |> Wrapped.pure

    let map f x =
      let+ v = x in
      Stdlib.Result.map f v

    let apply fa xa =
      let+ f = fa and+ x = xa in
      match (f, x) with
      | Ok f', Ok x' -> Ok (f' x')
      | Error e, _ | _, Error e -> Error e

    let join v =
      let* x = v in
      match x with Ok x' -> x' | Error e -> Wrapped.pure @@ Error e

    let bind m f = join (map f m)
  end

  include ResultMonad

  let elevate v =
    let+ x = v in
    Ok x

  include Monad.MonadInfix (ResultMonad)

  let run m = m [@@inline]

  let create x = x [@@inline]

  let error x = Error x |> Wrapped.pure

  let ok x = Ok x |> Wrapped.pure
end

module Make = MakeT (Identity)

module MakePlusT (Wrapped : Monad.MONAD) (E : Monad.MONOID) = struct
  module ResultMonad = MakeT (Wrapped) (E)

  type e = E.t

  module AppendAndEmpty = struct
    module WrappedInfix = Monad.MonadInfix (Wrapped)
    open WrappedInfix.Syntax

    type 'a t = 'a ResultMonad.t

    let append : 'a t -> 'a t -> 'a t =
     fun xa ya ->
      let+ x = xa and+ y = ya in
      match (x, y) with
      | Error e1, Error e2 -> Error (E.append e1 e2)
      | Ok a, _ -> Ok a
      | _, b -> b

    let empty () = Wrapped.pure @@ Error E.empty
  end

  module ResultMonadPlus = Monad.CreateMonadPlus (ResultMonad) (AppendAndEmpty)
  include ResultMonadPlus

  let run = ResultMonad.run

  let create = ResultMonad.create

  let elevate = ResultMonad.elevate

  let error = ResultMonad.error

  let ok = ResultMonad.ok
end

module MakePlus = MakePlusT (Identity)
