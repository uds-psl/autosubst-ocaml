module ZipArrayAlternative = struct
  type 'a t = 'a array

  let zip xs ys =
    let min_length = min (Stdlib.Array.length xs) (Stdlib.Array.length ys) in
    let zip_at_pos i = (Stdlib.Array.get xs i, Stdlib.Array.get ys i) in
    Stdlib.Array.init min_length zip_at_pos

  let drop i xs =
    let start = Stdlib.Array.length xs |> min i in
    let new_length = Stdlib.Array.length xs - start in
    Stdlib.Array.sub xs start new_length

  let pure = Array.Make.pure

  let map = Array.Make.map

  let apply f x =
    let c (x, y) = x y in
    zip f x |> Stdlib.Array.map c

  let append x y = Stdlib.Array.append x @@ drop (Stdlib.Array.length x) y

  let empty () = [||]
end

include ZipArrayAlternative
include Monad.AlternativeInfix (ZipArrayAlternative)
