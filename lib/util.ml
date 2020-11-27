open Base

let id x = x

let list_intersection xs ys =
  List.(filter xs ~f:(fun x -> mem ys x ~equal:Poly.equal))

let list_diff xs ys =
  List.(filter xs ~f:(fun x -> not @@ mem ys x ~equal:Poly.equal))

let list_remove xs y =
  List.(filter xs ~f:(fun x -> Poly.(x <> y)))

let showPair f g (x, y) =
  "(" ^ f x ^ ", " ^ g y ^ ")"

let nub l = List.dedup_and_sort ~compare:Poly.compare l

let rec list_zip xs ys =
  match xs, ys with
  | [], [] -> []
  | x::xs, y::ys -> (x,y)::(list_zip xs ys)
  | _, _ -> []
