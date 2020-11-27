open Base

module M = Monadic
module H = Hsig

include Monads.MONAD_RE
    with type 'a wrapped = 'a M.Result.Make(String).t
    with type 'a actual_t = H.t -> 'a M.Result.Make(String).t
    with type e := string
    with type r := H.t

val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
