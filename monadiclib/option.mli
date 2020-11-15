module MakeT : functor
  (Wrapped : Monad.MONAD)
  -> sig
  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := 'a option Wrapped.t

  val append : 'a t -> 'a t -> 'a t

  val empty : unit -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t
end
with type 'a t = 'a option Wrapped.t

module Make : sig
  include
    Monad.MAKE_T with type 'a wrapped := 'a with type 'a actual_t := 'a option

  val none : unit -> 'a t

  val append : 'a t -> 'a t -> 'a t

  val empty : unit -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t
end
with type 'a t = 'a option
