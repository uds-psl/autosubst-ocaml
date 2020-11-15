module MakeT : functor (Wrapped : Monad.MONAD) (W : Monad.MONOID) -> sig
  type w = W.t

  include
    Monad.MAKE_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := ('a * w) Wrapped.t

  val tell : w -> unit t
end

module Make : functor (W : Monad.MONOID) -> sig
  type w = W.t

  include
    Monad.MAKE_T with type 'a wrapped := 'a with type 'a actual_t := 'a * w

  val tell : w -> unit t
end

module MakePlusT : functor
  (Wrapped : Monad.MONAD_PLUS)
  (W : Monad.MONOID)
  -> sig
  type w = W.t

  include
    Monad.MAKE_PLUS_T
      with type 'a wrapped := 'a Wrapped.t
      with type 'a actual_t := ('a * w) Wrapped.t

  val tell : w -> unit t
end
