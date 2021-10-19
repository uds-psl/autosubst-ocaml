module ZipSeqAlternative = struct
  type 'a t = 'a Stdlib.Seq.t

  let rec zip xs ys () =
    let open Stdlib.Seq in
    match (xs (), ys ()) with
    | Cons (l1, ls1), Cons (l2, ls2) -> Cons ((l1, l2), zip ls1 ls2)
    | _ -> Nil

  let rec drop i xs =
    let open Stdlib.Seq in
    if i <= 0 then xs
    else match xs () with Nil -> empty | Cons (_, ls) -> drop (i - 1) ls

  let length seq = Stdlib.Seq.fold_left (fun i _ -> i + 1) 0 seq

  let pure = Seq.Make.pure

  let map = Seq.Make.map

  let apply f x =
    let c (x, y) = x y in
    zip f x |> Stdlib.Seq.map c

  let append x y = Seq.Make.append x (drop (length x) y)

  let empty () = Stdlib.Seq.empty
end

include ZipSeqAlternative
include Monad.AlternativeInfix (ZipSeqAlternative)
