module MakeT (Wrapped : Monad.MONAD) (W : Monad.MONOID) = struct
  type w = W.t

  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module WriterMonad : Monad.MONAD with type 'a t = ('a * w) Wrapped.t = struct
    type 'a t = ('a * w) Wrapped.t

    let pure v = Wrapped.pure (v, W.empty)

    let map f x =
      let+ v, w = x in
      (f v, w)

    let apply fa xa =
      let+ f, w1 = fa and+ x, w2 = xa in
      (f x, W.append w1 w2)

    let bind m f =
      let* x1, w1 = m in
      let+ x2, w2 = f x1 in
      (x2, W.append w1 w2)

    let join m = bind m (fun x -> x)
  end

  include WriterMonad

  let elevate v =
    let+ x = v in
    (x, W.empty)

  include Monad.MonadInfix (WriterMonad)

  let tell w = Wrapped.pure ((), w)

  let run m = m [@@inline]

  let create x = x [@@inline]
end

module Make = MakeT (Identity)

module MakePlusT (Wrapped : Monad.MONAD_PLUS) (W : Monad.MONOID) = struct
  module WriterMonad = MakeT (Wrapped) (W)

  type w = W.t

  module AppendAndEmpty = struct
    type 'a t = 'a WriterMonad.t

    let append xa ya = Wrapped.append xa ya

    let empty () = Wrapped.empty ()
  end

  module WriterMonadPlus = Monad.CreateMonadPlus (WriterMonad) (AppendAndEmpty)
  include WriterMonadPlus

  let create = WriterMonad.create

  let run = WriterMonad.run

  let tell = WriterMonad.tell

  let elevate = WriterMonad.elevate
end
