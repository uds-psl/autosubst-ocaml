
let assoc_exn = ListLabels.assoc
let assoc = ListLabels.assoc_opt

let assoc_default x l ~default =
  match assoc x l with
  | None -> default
  | Some y -> y

let insert x y l = (x,y)::l

let mem_assoc x l =
  match assoc x l with
  | Some _ -> true
  | None -> false
