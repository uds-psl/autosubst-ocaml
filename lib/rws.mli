open Monadic

module MakeT : functor
    (Wrapped : Monad.MONAD) (R: sig type t end) (W: Monad.MONOID) (S: sig type t end) ->
sig
  type rws_r
  type rws_w
  type rws_s

  include Monad.MAKE_T
    with type 'a wrapped := 'a Wrapped.t
    with type 'a actual_t := rws_r -> rws_s -> ('a * rws_w * rws_s) Wrapped.t

  module W : Monad.MONAD

  val peek : rws_r t
  val get : rws_s t
  val put : rws_s -> unit t
  val tell : rws_w -> unit t
  val run : 'a t -> r:rws_r -> s:rws_s -> ('a * rws_w * rws_s) Wrapped.t
  val create : (rws_r -> rws_s -> ('a * rws_w * rws_s) Wrapped.t) -> 'a t
end
with type rws_r = R.t
with type rws_w = W.t
with type rws_s = S.t
with module W = Wrapped


module Make : functor
    (R: sig type t end) (W: Monad.MONOID) (S: sig type t end) ->
sig
  type rws_r
  type rws_w
  type rws_s

  include Monad.MAKE_T
    with type 'a wrapped := 'a
    with type 'a actual_t := rws_r -> rws_s -> ('a * rws_w * rws_s)

  val peek : rws_r t
  val get : rws_s t
  val put : rws_s -> unit t
  val tell : rws_w -> unit t
  val run : 'a t -> r:rws_r -> s:rws_s -> ('a * rws_w * rws_s)
  val create : (rws_r -> rws_s -> ('a * rws_w * rws_s)) -> 'a t
end
with type rws_r = R.t
with type rws_w = W.t
with type rws_s = S.t
