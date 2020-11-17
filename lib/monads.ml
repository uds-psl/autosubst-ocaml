(** My own definitions for reader/writer/state monad
 ***  *)


module M = Monadic

module type MONAD_READER = sig
  type 'a t
  type r

  include M.Monad.MONAD
    with type 'a t := 'a t

  (* Reader *)
  val ask : r t
  val asks : (r -> 'a) -> 'a t
end

module type MONAD_WRITER = sig
  type 'a t
  type w

  include M.Monad.MONAD
    with type 'a t := 'a t

  val tell : w -> unit t
end

module type MONAD_STATE = sig
  type 'a t
  type s

  include M.Monad.MONAD
    with type 'a t := 'a t

  val get : s t
  val put : s -> unit t
end

module type MONAD_ERROR = sig
  type 'a t
  type e

  include M.Monad.MONAD
    with type 'a t := 'a t

  val error : e -> 'a t
end
