module MakeT : functor
  (Wrapped : Monad.MONAD)
  (S : sig
     type t
   end)
  -> sig
  type s = S.t

  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := s -> ('a * s) Wrapped.t

  val get : s t

  val put : s -> unit t

  val run : 'a t -> s -> ('a * s) Wrapped.t

  val create : (s -> ('a * s) Wrapped.t) -> 'a t
end

module Make : functor
  (S : sig
     type t
   end)
  -> sig
  type s = S.t

  include
    Monad.MAKE_T with type 'a wrapped := 'a with type 'a actual_t := s -> 'a * s

  val get : s t

  val put : s -> unit t

  val run : 'a t -> s -> 'a * s

  val create : (s -> 'a * s) -> 'a t
end

module MakePlusT : functor
  (Wrapped : Monad.MONAD_PLUS)
  (S : sig
     type t
   end)
  -> sig
  type s = S.t

  include
    Monad.MAKE_PLUS_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := s -> ('a * s) Wrapped.t

  val get : s t

  val put : s -> unit t

  val run : 'a t -> s -> ('a * s) Wrapped.t

  val create : (s -> ('a * s) Wrapped.t) -> 'a t
end
