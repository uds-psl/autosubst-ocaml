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

let list_nempty = function
  | [] -> false
  | _ -> true

(* let list_find_index_exn x xs =
 *   Option.get @@
 *   List.mapi (fun i y -> if x = y then Some i else None) xs *)

let rec list_any = function
  | [] -> false
  | b :: bs -> b || list_any bs

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

let list_split3 l =
  let open List in
  let x0 = map (fun (x, _, _) -> x) l in
  let x1 = map (fun (_, y, _) -> y) l in
  let x2 = map (fun (_, _, z) -> z) l in
  (x0, x1, x2)


let list_zip xs ys = List.combine xs ys

let rec list_of_length x = function
  | 0 -> []
  | n -> x :: list_of_length x (n - 1)

let const b x = b
let const2 b x y = b

let sep_ = "_"
let sep a b = a^sep_^b
let sepd = String.concat sep_

(* Printing *)
let newline = Pp.fnl ()
let vernacend = Pp.((str ".") ++ newline)

let guard b l =
  if b then l else []

let string_of_char c = String.make 1 c
