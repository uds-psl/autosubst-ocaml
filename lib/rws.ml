module M = Monadic

module type MONAD_RWST = sig
  type 'a t
  type rws_r
  type rws_w
  type rws_s

  type 'a ww

  include M.Monad.MAKE_T
    with type 'a wrapped := 'a ww
    with type 'a t := 'a t
    with type 'a actual_t := rws_r -> rws_s -> ('a * rws_w * rws_s) ww

  include Monads.MONAD_READER
    with type 'a t := 'a t
    with type r := rws_r

  include Monads.MONAD_WRITER
    with type 'a t := 'a t
    with type w := rws_w

  include Monads.MONAD_STATE
    with type 'a t := 'a t
    with type s := rws_s
end

module MakeT
    (Wrapped : M.Monad.MONAD) (R: sig type t end) (W: M.Monad.MONOID) (S: sig type t end) :
  MONAD_RWST
  with type 'a ww := 'a Wrapped.t
  with type rws_r := R.t
  with type rws_w := W.t
  with type rws_s := S.t =
struct

  type rws_r = R.t
  type rws_w = W.t
  type rws_s = S.t
  type 'a t = rws_r -> rws_s -> ('a * rws_w * rws_s) Wrapped.t
  type 'a myt = 'a t

    (* also import syntax of wrapped monad so that we can use it in functions later *)
  module WrappedInfix = M.Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module MON : M.Monad.MONAD
    with type 'a t := 'a t =
  struct
    (* type 'a t = rws_r -> rws_s -> ('a * rws_w * rws_s) Wrapped.t *)

    let pure v _ s = Wrapped.pure (v, W.empty, s)

    (* val map :
     *   ('a -> 'b) ->
     *   (r -> s -> (('a * w) * s) Wrapped.t) ->
     *   r -> s -> (('b * w) * w) Wrapped.t *)
    let map f m r s =
      let+ result, w, s1 = m r s in
      (f result, w, s1)

    (* val apply :
     *   (r -> s -> ((('a -> 'b) * w) * s) Wrapped.t) ->
     *   (r -> s -> (('a * w) * s) Wrapped.t) ->
     *   r -> s -> (('b * w) * s) Wrapped.t *)
    let apply fa xa r s =
      let* f, w1, s1 = fa r s in
      let+ result, w2, s2 = xa r s1 in
      (f result, W.append w1 w2, s2)

    (* val bind :
     *   (r -> s -> (('a * w) * s) Wrapped.t) ->
     *   ('a -> (r -> s -> (('b * w) * s) Wrapped.t)) ->
     *   r -> s -> (('b * w) * s) Wrapped.t *)
    let bind m k r s =
      let* result1, w1, s1 = m r s in
      let+ result2, w2, s2 = k result1 r s1 in
      (result2, W.append w1 w2, s2)

    let join m = bind m (fun x -> x)
  end

  include MON

  let elevate w _ s =
    let+ x = w in
    (x, W.empty, s)

  include M.Monad.MonadInfix (struct
      type 'a t = 'a myt
      include MON
    end)

  let ask r s = Wrapped.pure (r, W.empty, s)
  let asks f = f <$> ask

  let tell w _ s = Wrapped.pure ((), w, s)

  let get _ s = Wrapped.pure (s, W.empty, s)
  let put s _ _ = Wrapped.pure ((), W.empty, s)

  let run m r s = m r s
  let create x = x

  (* dont do that in a monad transformer I think. only at the end when I instantiate Rws.MakeT *)
  (* include Monad.ApplicativeFunctionsList(MON)
   * include Monad.MonadFunctionsList(MON) *)
end

module Make = MakeT(M.Identity)
