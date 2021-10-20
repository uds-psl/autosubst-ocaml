
(** Some functions that were not in the monad library yet
    TODO add to the monadic library *)
module ExtraFunctionsList : functor (MON: Monadic.Monad.MONAD) -> sig
  val a_split_map : ('a -> ('b * 'c) MON.t) -> 'a list -> ('b list * 'c list) MON.t
  
  val a_map2 : ('a -> 'b -> 'c MON.t) -> 'a list -> 'b list -> 'c list MON.t

  val liftM2 : ('a -> 'b -> 'c) -> 'a MON.t -> 'b MON.t -> 'c MON.t

  val m_fold_left : f:('a -> 'b -> 'a MON.t) -> init:'a -> 'b list -> 'a MON.t
  val m_fold_right : f:('b -> 'a -> 'a MON.t) -> init:'a -> 'b list -> 'a MON.t

  val a_concat_map : ('a -> 'b list MON.t) -> 'a list -> 'b list MON.t

  val m_guard : bool -> 'a list MON.t -> 'a list MON.t
end