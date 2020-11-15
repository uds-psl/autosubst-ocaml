let rec append xs ys () =
  match xs () with
  | Stdlib.Seq.Nil -> ys ()
  | Stdlib.Seq.Cons (x, xs) -> Stdlib.Seq.Cons (x, append xs ys)

let concat s =
  let open Stdlib.Seq in
  let rec aux current rest () =
    match current () with
    | Cons (e, s) -> Cons (e, aux s rest)
    | Nil -> ( match rest () with Cons (e, s) -> aux e s () | Nil -> Nil )
  in
  aux Stdlib.Seq.empty s

module MakeT (Wrapped : Monad.MONAD) = struct
  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module SeqMonadPlus :
    Monad.MONAD_PLUS with type 'a t = 'a Stdlib.Seq.t Wrapped.t = struct
    type 'a t = 'a Stdlib.Seq.t Wrapped.t

    let pure v = Stdlib.Seq.return v |> Wrapped.pure

    let map f x =
      let+ v = x in
      Stdlib.Seq.map f v

    let apply fa xa =
      let+ fs = fa and+ xs = xa in
      let accum curr acc =
        let l1 = Stdlib.Seq.map curr xs in
        append l1 acc
      in
      Monad.SeqCollection.fold_right accum fs Stdlib.Seq.empty

    let sequence ms =
      let open Monad.ApplicativeFunctions (Wrapped) in
      sequence ms

    let join v =
      let* x = v in
      let+ xs = sequence x in
      concat xs

    let bind m f = join (map f m)

    let append xa ya =
      let+ x = xa and+ y = ya in
      append x y

    let empty () = Wrapped.pure Stdlib.Seq.empty
  end

  include SeqMonadPlus
  include Monad.MonadPlusInfix (SeqMonadPlus)

  let run m = m [@@inline]

  let create x = x [@@inline]

  let elevate v =
    let+ x = v in
    Stdlib.Seq.return x
end

module Make = MakeT (Identity)
