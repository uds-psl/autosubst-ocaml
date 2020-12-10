open Base

let id x = x

let list_intersection xs ys =
  List.(filter xs ~f:(fun x -> mem ys x ~equal:Poly.equal))

let list_diff xs ys =
  List.(filter xs ~f:(fun x -> not @@ mem ys x ~equal:Poly.equal))

let list_remove xs y =
  List.(filter xs ~f:(fun x -> Poly.(x <> y)))

let list_find_index_exn x xs =
  List.find_mapi_exn ~f:(fun i y -> if Poly.(x = y) then Some i else None) xs

let list_any f xs =
  match List.find ~f xs with
  | Some _ -> true
  | None -> false

let list_none f xs =
  list_any f xs |> not

let showPair f g (x, y) =
  "(" ^ f x ^ ", " ^ g y ^ ")"

let nub cmp l = Set.stable_dedup_list cmp l

(** An implementation of zip that does not throw *)
let rec list_zip xs ys =
  match xs, ys with
  | [], [] -> []
  | x::xs, y::ys -> (x,y)::(list_zip xs ys)
  | _, _ -> []

let const b x = b
let const2 b x y = b

let sep_ = "_"
let sep a b = a^sep_^b
let sepd = String.concat ~sep:sep_
