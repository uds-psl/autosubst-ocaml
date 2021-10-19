module MakeT : functor
  (Wrapped : Monad.MONAD)
  (S : sig
     type t
   end)
  -> sig
  type s

  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := s -> 'a Wrapped.t * s

  val get : s t

  val put : s -> unit t
end
with type s = S.t

module Make : functor
  (S : sig
     type t
   end)
  -> sig
  type s

  include
    Monad.MAKE_T with type 'a wrapped := 'a with type 'a actual_t := s -> 'a * s

  val get : s t

  val put : s -> unit t
end
with type s = S.t

module MakePlusT : functor
  (Wrapped : Monad.MONAD_PLUS)
  (S : sig
     type t
   end)
  -> sig
  type s

  include
    Monad.MAKE_PLUS_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := s -> 'a Wrapped.t * s

  val get : s t

  val put : s -> unit t
end
with type s = S.t
