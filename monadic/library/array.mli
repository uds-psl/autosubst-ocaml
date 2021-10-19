module MakeT : functor
  (Wrapped : Monad.MONAD)
  -> sig
  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := 'a array Wrapped.t

  val append : 'a t -> 'a t -> 'a t

  val empty : unit -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t
end
with type 'a t = 'a array Wrapped.t

module Make : sig
  include
    Monad.MAKE_T with type 'a wrapped := 'a with type 'a actual_t := 'a array

  val append : 'a t -> 'a t -> 'a t

  val empty : unit -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t
end
with type 'a t = 'a array
