module MakeT : functor
  (Wrapped : Monad.MONAD)
  (E : sig
     type t
   end)
  -> sig
  type e = E.t

  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := ('a, e) result Wrapped.t

  val error : e -> 'a t

  val ok : 'a -> 'a t
end
with type 'a t = ('a, E.t) result Wrapped.t

module Make : functor
  (E : sig
     type t
   end)
  -> sig
  type e = E.t

  include
    Monad.MAKE_T
      with type 'a wrapped := 'a
      with type 'a actual_t := ('a, e) result

  val error : e -> 'a t

  val ok : 'a -> 'a t
end
with type 'a t = ('a, E.t) result

module MakePlusT : functor (Wrapped : Monad.MONAD) (E : Monad.MONOID) -> sig
  type e = E.t

  include
    Monad.MAKE_PLUS_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := ('a, e) result Wrapped.t

  val error : e -> 'a t

  val ok : 'a -> 'a t
end

module MakePlus : functor (E : Monad.MONOID) -> sig
  type e = E.t

  include
    Monad.MAKE_PLUS_T
      with type 'a wrapped := 'a
      with type 'a actual_t := ('a, e) result

  val run : 'a t -> ('a, e) result

  val create : ('a, e) result -> 'a t

  val error : e -> 'a t

  val ok : 'a -> 'a t
end
