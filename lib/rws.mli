open Monadic

module MakeT : functor
    (Wrapped : Monad.MONAD) (R: sig type t end) (W: Monad.MONOID) (S: sig type t end) ->
sig
  module MON : sig
    type rws_r
    type rws_w
    type rws_s

    include Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := rws_r -> rws_s -> ('a * rws_w * rws_s) Wrapped.t

    module Wr : Monad.MONAD
    (* module M3 : Writer.MakeT(State.MakeT(Reader.MakeT(Wrapped)(R))(S))(W) *)

    (* Reader *)
    val ask : rws_r t
    val asks : (rws_r -> 'a) -> 'a t

    (* State *)
    val get : rws_s t
    val gets : (rws_s -> 'a) -> 'a t
    val put : rws_s -> unit t
    val modify : (rws_s -> rws_s) -> unit t

    (* Writer *)
    val tell : rws_w -> unit t


    val run : 'a t -> r:rws_r -> s:rws_s -> ('a * rws_w * rws_s) Wrapped.t
    val create : (rws_r -> rws_s -> ('a * rws_w * rws_s) Wrapped.t) -> 'a t
  end
  with type rws_r = R.t
  with type rws_w = W.t
  with type rws_s = S.t
  with module Wr = Wrapped

  (* declare the internal type of the monad once so that I can override it in M_internal and the applicative functions *)
  type 'a t

  (* now we include the M_internal, which is a Monad, so the whole RWS is a Monad *)
  include (module type of MON with type 'a t := 'a t)

  (* TODO Before I included Monad.ApplicativeFunctionsList(M_internal), but then I was not able to swap out the type 'a M_internal.t with t. Probably because the ApplicativeFunctionsList functor already overrides the 'a applicative with 'a A. t (but even using 'a A.t) did not work *)
  (* so is this the best way? *)
  include Monad.APPLICATIVE_FUNCTIONS
    with type 'a applicative := 'a t
    with type 'a collection := 'a list
  include Monad.MONAD_FUNCTIONS
    with type 'a monad := 'a t
    with type 'a collection := 'a list
end


(* module Make : functor
 *     (R: sig type t end) (W: Monad.MONOID) (S: sig type t end) ->
 * sig
 *   type rws_r
 *   type rws_w
 *   type rws_s
 *
 *   include Monad.MAKE_T
 *     with type 'a wrapped := 'a
 *     with type 'a actual_t := rws_r -> rws_s -> ('a * rws_w * rws_s)
 *
 *   (\* Reader *\)
 *   val ask : rws_r t
 *   val asks : (rws_r -> 'a) -> 'a t
 *
 *   (\* State *\)
 *   val get : rws_s t
 *   val gets : (rws_s -> 'a) -> 'a t
 *   val put : rws_s -> unit t
 *   val modify : (rws_s -> rws_s) -> unit t
 *
 *   (\* Writer *\)
 *   val tell : rws_w -> unit t
 *
 *
 *   val run : 'a t -> r:rws_r -> s:rws_s -> ('a * rws_w * rws_s)
 *   val create : (rws_r -> rws_s -> ('a * rws_w * rws_s)) -> 'a t
 *
 * end
 * with type rws_r = R.t
 * with type rws_w = W.t
 * with type rws_s = S.t *)
