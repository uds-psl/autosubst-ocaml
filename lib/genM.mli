module M = Monadic
module H = Hsig

type 'a t
type scope = (H.vId * int) list
type 'a wrapped = ('a, string) result
type 'a actual_t = H.t -> scope -> ('a * string * scope) M.Result.Make(String).t

include Rws.MONAD_RWST
        with type 'a t := 'a t
        with type 'a wrapped := 'a wrapped
        with type r = H.t
        with type w = string
        with type s = scope

include Monads.MONAD_ERROR
        with type 'a t := 'a t
        with type e = string
