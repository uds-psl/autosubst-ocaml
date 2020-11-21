open Core
open Util
open GenM

module H = Hsig


let genCodeT xs dps upList' =
  let open GenM.Syntax in
  let open GenM in
  let _ = print_endline "genCodeT" in
  let _ = "varSorts: " ^ (List.to_string ~f:id xs) |> print_endline in
  let _ = "sorts: " ^ (List.to_string ~f:id dps) |> print_endline in
  let _ = "ups: " ^ (List.to_string ~f:(showPair H.show_binder id) upList') |> print_endline in
  ["code"] |> pure
