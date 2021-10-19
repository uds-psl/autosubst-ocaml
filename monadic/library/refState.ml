module MakeT
    (Wrapped : Monad.MONAD) (S : sig
      type t
    end) =
struct
  type s = S.t

  module ReaderMonad =
    Reader.MakeT
      (Wrapped)
      (struct
        type t = S.t ref
      end)

  include ReaderMonad
  open Syntax

  let put v =
    let+ x = peek in
    x := v

  let get =
    let+ x = peek in
    !x

  let run m init =
    let r = ref init in
    let result = run m r in
    (result, !r)

  module WrappedInfix = Monad.MonadInfix (Wrapped)

  let create f =
    create @@ fun r ->
    let result, new_state = f !r in
    r := new_state;
    result
end

module Make = MakeT (Identity)

module MakePlusT
    (Wrapped : Monad.MONAD_PLUS) (S : sig
      type t
    end) =
struct
  module RefStateMonad = MakeT (Wrapped) (S)

  type s = S.t

  module AppendAndEmpty = struct
    type 'a t = 'a RefStateMonad.t

    let append xa ya =
      let open RefStateMonad in
      create @@ fun r ->
      let x, _ = run xa r in
      let y, _ = run ya r in
      (Wrapped.append x y, r)

    let empty () = RefStateMonad.create (fun r -> (Wrapped.empty (), r))
  end

  module RefStateMonadPlus =
    Monad.CreateMonadPlus (RefStateMonad) (AppendAndEmpty)
  include RefStateMonadPlus

  let create = RefStateMonad.create

  let run = RefStateMonad.run

  let get = RefStateMonad.get

  let put = RefStateMonad.put

  let elevate = RefStateMonad.elevate
end
