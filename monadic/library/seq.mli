module MakeT : functor
  (Wrapped : Monad.MONAD)
  -> sig
  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := 'a Stdlib.Seq.t Wrapped.t

  val append : 'a t -> 'a t -> 'a t

  val empty : unit -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t
end
with type 'a t = 'a Stdlib.Seq.t Wrapped.t

module Make : sig
  include
    Monad.MAKE_T
      with type 'a wrapped := 'a
      with type 'a actual_t := 'a Stdlib.Seq.t

  val append : 'a t -> 'a t -> 'a t

  val empty : unit -> 'a t

  val ( <|> ) : 'a t -> 'a t -> 'a t
end
with type 'a t = 'a Stdlib.Seq.t
