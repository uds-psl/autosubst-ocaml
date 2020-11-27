module M = Monadic

module type MONAD_RWST = sig
  type 'a t
  type r
  type w
  type s

  (* I can use this sort of like a parameter for the MONAD_RWST signature by substituting it for Wrapped.t. Then I can use 'a wrapped again to pass it to MAKE_T, so that I can get the Syntax module in my RWST signature. TODO seems kind of unnec. I could just make a separate Syntax signature. Also do the same in Monads.MONAD_RE *)
  type 'a wrapped

  include M.Monad.MAKE_T
    with type 'a wrapped := 'a wrapped
    with type 'a t := 'a t
    with type 'a actual_t := r -> s -> ('a * w * s) wrapped

  include Monads.MONAD_READER
    with type 'a t := 'a t
    with type r := r

  include Monads.MONAD_WRITER
    with type 'a t := 'a t
    with type w := w

  include Monads.MONAD_STATE
    with type 'a t := 'a t
    with type s := s

  include M.Monad.APPLICATIVE_FUNCTIONS
    with type 'a applicative := 'a t
    with type 'a collection := 'a list

  include M.Monad.MONAD_FUNCTIONS
    with type 'a monad := 'a t
    with type 'a collection := 'a list
end

module MakeT
    (Wrapped : M.Monad.MONAD) (R: sig type t end) (W: M.Monad.MONOID) (S: sig type t end) :
  MONAD_RWST
  with type 'a wrapped := 'a Wrapped.t
(* these don't need to be replaced, because I want to implement them anyways *)
  with type r = R.t
  with type w = W.t
  with type s = S.t =
struct
  type r = R.t
  type w = W.t
  type s = S.t

  (* also import syntax of wrapped monad so that we can use it in functions later *)
  module WrappedInfix = M.Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module MON : M.Monad.MONAD
    with type 'a t = r -> s -> ('a * w * s) Wrapped.t =
    (* with type 'a t := 'a t = *)
  struct
    type 'a t = r -> s -> ('a * w * s) Wrapped.t

    let pure v _ s = Wrapped.pure (v, W.empty, s)

    let map f m r s =
      let+ result, w, s1 = m r s in
      (f result, w, s1)

    let apply fa xa r s =
      let* f, w1, s1 = fa r s in
      let+ result, w2, s2 = xa r s1 in
      (f result, W.append w1 w2, s2)

    let bind m k r s =
      let* result1, w1, s1 = m r s in
      let+ result2, w2, s2 = k result1 r s1 in
      (result2, W.append w1 w2, s2)

    let join m = bind m (fun x -> x)
  end

  include MON

  let elevate wr _ s =
    let+ result = wr in
    (result, W.empty, s)

  include M.Monad.MonadInfix (MON)

  let ask r s = Wrapped.pure (r, W.empty, s)
  let asks f = f <$> ask

  let tell w _ s = Wrapped.pure ((), w, s)

  let get _ s = Wrapped.pure (s, W.empty, s)
  let put s _ _ = Wrapped.pure ((), W.empty, s)

  let run m r s = m r s
  let create x = x

  include M.Monad.ApplicativeFunctionsList(MON)
  include M.Monad.MonadFunctionsList(MON)
  (* dont do that in a monad transformer I think. only at the end when I instantiate Rws.MakeT *)
  (* include Monad.ApplicativeFunctionsList(MON)
   * include Monad.MonadFunctionsList(MON) *)
end

module Make = MakeT(M.Identity)
