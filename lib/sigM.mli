open Base

module M = Monadic
module H = Hsig

include Monads.MONAD_RE
    with type 'a wrapped = 'a M.Result.Make(String).t
    with type 'a actual_t = H.t -> 'a M.Result.Make(String).t
    with type e := string
    with type r := H.t

val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val a_map2_exn : ('a -> 'b -> 'c t) -> 'a list -> 'b list -> 'c list t

val m_fold_left : f:('a -> 'b -> 'a t) -> init:'a -> 'b list -> 'a t

val a_concat_map : ('a -> 'b list t) -> 'a list -> 'b list t

val m_guard : bool -> 'a list t -> 'a list t
