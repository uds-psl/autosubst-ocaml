open Base
open Util
open GenM

module H = Hsig

module type LEMMA_PRE = sig
  type args

  val getName : string
  val getType : args -> Constrexpr.constr_expr
  val getBody : args -> Constrexpr.constr_expr
end


module Lemma (L: LEMMA_PRE) : sig
  include LEMMA_PRE
  val build : args -> Pp.t
end = struct
  include L
  let build x = Pp.str "lemma!"
end


let genCodeT xs dps upList' =
  let open GenM.Syntax in
  let open GenM in
  let _ = print_endline "genCodeT" in
  (* let _ = "varSorts: " ^ (List.to_string ~f:id xs) |> print_endline in
   * let _ = "sorts: " ^ (List.to_string ~f:id dps) |> print_endline in
   * let _ = "ups: " ^ (List.to_string ~f:(showPair H.show_binder id) upList') |> print_endline in *)
  ["code"] |> pure
