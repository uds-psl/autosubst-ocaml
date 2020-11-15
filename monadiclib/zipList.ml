module ZipListAlternative = struct
  type 'a t = 'a list

  let rec zip xs ys =
    match (xs, ys) with
    | l1 :: ls1, l2 :: ls2 -> (l1, l2) :: zip ls1 ls2
    | _ -> []

  let rec drop i xs =
    if i <= 0 then xs
    else match xs with [] -> [] | _ -> drop (i - 1) @@ Stdlib.List.tl xs

  let pure = List.Make.pure

  let map = List.Make.map

  let apply f x =
    let c (x, y) = x y in
    zip f x |> Stdlib.List.map c

  let append x y = x @ drop (Stdlib.List.length x) y

  let empty () = []
end

include ZipListAlternative
include Monad.AlternativeInfix (ZipListAlternative)
