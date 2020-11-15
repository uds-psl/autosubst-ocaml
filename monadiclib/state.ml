module MakeT
    (Wrapped : Monad.MONAD) (S : sig
      type t
    end) =
struct
  type s = S.t

  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module StateMonad : Monad.MONAD with type 'a t = s -> ('a * s) Wrapped.t =
  struct
    type 'a t = s -> ('a * s) Wrapped.t

    let pure v s = Wrapped.pure (v, s)

    let map f x s =
      let+ result, s' = x s in
      (f result, s')

    let apply fa sa s =
      let* f, result1 = fa s in
      let+ s', result2 = sa result1 in
      (f s', result2)

    let bind m k s =
      let* result, s' = m s in
      k result s'

    let join m = bind m (fun x -> x)
  end

  (* Adding all the monadic functions to the outer scope *)
  include StateMonad

  let elevate w s =
    let+ x = w in
    (x, s)

  (* Adding the infix functions *)
  include Monad.MonadInfix (StateMonad)

  (* Adding the syntax extensions as an internal module *)

  (* The State functions themselves *)
  let get s = Wrapped.pure (s, s)

  let put s _ = Wrapped.pure ((), s)

  let run m init = m init

  let create x = x [@@inline]
end

module Make = MakeT (Identity)

module MakePlusT
    (Wrapped : Monad.MONAD_PLUS) (S : sig
      type t
    end) =
struct
  module StateMonad = MakeT (Wrapped) (S)

  type s = S.t

  module AppendAndEmpty = struct
    type 'a t = 'a StateMonad.t

    let append xa ya s =
      let x = xa s in
      let y = ya s in
      Wrapped.append x y

    let empty () = StateMonad.create (fun _ -> Wrapped.empty ())
  end

  module StateMonadPlus = Monad.CreateMonadPlus (StateMonad) (AppendAndEmpty)
  include StateMonadPlus

  let create = StateMonad.create

  let run = StateMonad.run

  let get = StateMonad.get

  let put = StateMonad.put

  let elevate = StateMonad.elevate
end
