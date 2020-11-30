
open CoqSyntax
module V = Vernacexpr

(* val pcount : unit -> string *)

val translate_sentence : sentence -> V.vernac_expr list
