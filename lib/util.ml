(** General utility functions *)

let id x = x

let list_intersection xs ys =
  List.(filter (fun x -> mem x ys) xs)

let list_diff xs ys =
  List.(filter (fun x -> not @@ mem x ys) xs)

let list_remove xs y =
  List.(filter (fun x -> x <> y) xs)

let list_contains_dup compare xs =
  List.(length xs <> length (sort_uniq compare xs))

let list_empty = function
  | [] -> true
  | _ -> false

(* let list_find_index_exn x xs =
 *   Option.get @@
 *   List.mapi (fun i y -> if x = y then Some i else None) xs *)

let list_any = List.exists

let list_none f xs =
  list_any f xs |> not

let cartesian_product xs ys =
  List.fold_left (fun c x ->
      let pairs = List.map (fun y -> (x, y)) ys in
      c @ pairs)
    [] xs

let rec list_take xs n = match xs with
  | [] -> []
  | x :: xs ->
    if n > 0
    then x :: list_take xs (n - 1)
    else []

let rec list_drop xs n =
  if n <= 0 then xs
  else match xs with
    | [] -> []
    | x :: xs -> list_drop xs (n - 1)

let showPair f g (x, y) =
  "(" ^ f x ^ ", " ^ g y ^ ")"

(* let nub cmp l = Set.stable_dedup_list cmp l *)

let list_zip xs ys = List.combine xs ys

let const b x = b
let const2 b x y = b

let sep_ = "_"
let sep a b = a^sep_^b
let sepd = String.concat sep_

(* Printing *)
let newline = Pp.fnl ()
let vernacend = Pp.((str ".") ++ newline)
