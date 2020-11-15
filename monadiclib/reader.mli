module MakeT : functor
  (Wrapped : Monad.MONAD)
  (R : sig
     type t
   end)
  -> sig
  type r

  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := r -> 'a Wrapped.t

  val peek : r t
end
with type r = R.t

module Make : functor
  (R : sig
     type t
   end)
  -> sig
  type r

  include
    Monad.MAKE_T with type 'a wrapped := 'a with type 'a actual_t := r -> 'a

  val peek : r t
end
with type r = R.t

module MakePlusT : functor
  (Wrapped : Monad.MONAD_PLUS)
  (R : sig
     type t
   end)
  -> sig
  type r

  include
    Monad.MAKE_PLUS_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := r -> 'a Wrapped.t

  val peek : r t

  val run : 'a t -> r -> 'a Wrapped.t

  val create : (r -> 'a Wrapped.t) -> 'a t
end
with type r = R.t
