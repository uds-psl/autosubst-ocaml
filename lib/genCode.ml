open Core
open Util
open GenMonad
open MonadReaderError.Functions(GenM)
module H = Hsig

let coqPreamble = "preamble"

let getUps con_com =
  let open List in
  let cart = cartesian_product con_com con_com in
  let singles = cart >>| (fun (x, y) -> (H.Single x, y)) in
  let blists =  cart >>| (fun (x, y) -> (H.BinderList ("p", x), y)) in
  List.append singles blists

let genCode ups spec =
  let open GenM.Syntax in
  let open GenM in
  let* (_, code) =
    m_fold (fun (ups, sentences) (x, dps) ->
        let* xs = substOf (List.hd_exn x) in
        (* let* mdps = a_map realDeps x in *)
        let up_x = getUps xs in
        let* code_x = Generator.genCodeT x dps (list_intersection ups up_x) in
        let new_ups = if List.is_empty dps
          then list_diff ups up_x
          else ups in
        let new_sentences = sentences @ [code_x] in
        pure @@ (new_ups, new_sentences))
      (ups, []) spec in
  pure @@ List.concat code

let genAutomation varSorts sorts substSorts ups =
  let open GenM.Syntax in
  let open GenM in
  let _ = print_endline "genAutomation" in
  let _ = "varSorts: " ^ (List.to_string ~f:id varSorts) |> print_endline in
  let _ = "sorts: " ^ (List.to_string ~f:id sorts) |> print_endline in
  let _ = "substSorts: " ^ (List.to_string ~f:id substSorts) |> print_endline in
  let _ = "ups: " ^ (List.to_string ~f:(showPair H.show_binder id) ups) |> print_endline in
  pure "tactics"


(* TODO genFile should also take prover args, like what kind of code it should generate *)
let genFile () =
  let open GenM.Syntax in
  let open GenM in
  (* TODO why is this called spec in autosubst2? *)
  let* spec = asks H.sigComponents in
  let sorts = List.(spec >>| fst |> concat) in
  let* varSorts = asks H.sigIsOpen in
  let* substSorts =
    a_filter (fun srt -> let* sub = substOf srt in
               List.is_empty sub |> not |> pure)
      sorts in
  (* TODO only create BinderList if well scoped coq code. also can the list ever be empty. calling hd_exn can error *)
  let* ups_pre =
    a_map (fun srt -> let* subsorts = substOf srt in
          getUps subsorts |> pure)
      List.(spec >>| fst >>| hd_exn) in
  (* TODO the core library only has a function that also sorts, this should not change the behaviour of the program. Using the polymorphic compare also from the core library *)
  let ups = List.(dedup_and_sort ~compare:Poly.compare @@ concat ups_pre) in
  let* code = genCode ups spec in
  (* let modularCode =  *)
  let* auto = genAutomation varSorts sorts substSorts ups in
  tell (coqPreamble ^ (String.concat code) ^ auto)

let runGenCode hsig = GenM.run (genFile ()) hsig []
