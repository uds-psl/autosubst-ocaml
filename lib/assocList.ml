type ('a, 'b) t = ('a * 'b) list [@@deriving show]

let assoc_exn = List.assoc
let assoc = List.assoc_opt

let assoc_default x l ~default =
  match assoc x l with
  | None -> default
  | Some y -> y

let insert x y l = (x,y)::l

let mem_assoc x l =
  match assoc x l with
  | Some _ -> true
  | None -> false

let update_exn x f l =
  let v = assoc_exn x l in
  insert x (f v) l

let update x f l =
  match assoc x l with
  | None -> l
  | Some v -> insert x (f v) l

let flatten l =
  List.fold_left (fun l (x, y) ->
      if mem_assoc x l then l else insert x y l)
    [] l
  |> List.rev

let from_list l = l
let to_list l = flatten l

let map f l =
  List.map (fun (x, y) -> (x, f x y)) l
