open Base
open Util

module M = Monadic
module H = Hsig
module AL = AssocList

(* I could actually also build up the signature like this. It's either RWST (including MAKE_T, so the Syntax) or RWSE + MAKE_T. But all in all this just shows that it would be pretty easy to roll it myself and I spent too much time worrying about which Monad library to use. at least now I know better how it works *)
(* module type GENM2 = sig
 *   type 'a t
 *
 *   include Monads.MONAD_RWSE
 *     with type 'a t := 'a t
 *     with type r = H.t
 *     with type w = string
 *     with type s = (H.vId * int) list
 *     with type e = string
 *
 *   include M.Monad.MAKE_T
 *     with type 'a t := 'a t
 *     with type 'a wrapped := 'a M.Result.Make(String).t
 *     with type 'a actual_t := r -> s -> ('a * w * s) M.Result.Make(String).t
 * end *)

type scope = (H.vId * int) list
type 'a wrapped = ('a, string) result
type 'a actual_t = H.t -> scope -> ('a * string * scope) M.Result.Make(String).t
type e = string
module GenError = M.Result.Make(struct type t = e end)
(* TODO Autosubst uses some Doc type for pretty printing in the writer *)
module StringMon = struct
  type t = string
  let empty = ""
  let append = (^)
end
module RWS = Rws.MakeT(GenError)(struct type t = H.t end)(StringMon)(struct type t = scope end)
include RWS

let error s = GenError.error s |> elevate
