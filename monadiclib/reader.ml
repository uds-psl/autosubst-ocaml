module MakeT
    (Wrapped : Monad.MONAD) (R : sig
      type t
    end) =
struct
  type r = R.t

  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module ReaderMonad : Monad.MONAD with type 'a t = r -> 'a Wrapped.t = struct
    type 'a t = r -> 'a Wrapped.t

    let pure v _ = Wrapped.pure v

    let map f x r =
      let+ result = x r in
      f result

    let apply fa va r =
      let+ f = fa r and+ v = va r in
      f v

    let bind m k r =
      let* v = m r in
      k v r

    let join m = bind m (fun x -> x)
  end

  include ReaderMonad

  let elevate w _ = w

  include Monad.MonadInfix (ReaderMonad)

  let peek r = Wrapped.pure r

  let run m init = m init

  let create x = x [@@inline]
end

module Make = MakeT (Identity)

module MakePlusT
    (Wrapped : Monad.MONAD_PLUS) (R : sig
      type t
    end) =
struct
  module ReaderMonad = MakeT (Wrapped) (R)

  type r = ReaderMonad.r

  module AppendAndEmpty = struct
    type 'a t = 'a ReaderMonad.t

    let append xa ya r =
      let x = xa r in
      let y = ya r in
      Wrapped.append x y

    let empty () _ = Wrapped.empty ()
  end

  module ReaderMonadPlus = Monad.CreateMonadPlus (ReaderMonad) (AppendAndEmpty)
  include ReaderMonadPlus

  let peek = ReaderMonad.peek

  let run = ReaderMonad.run

  let create = ReaderMonad.create

  let elevate = ReaderMonad.elevate
end
