(* someone on stackvoerflow once implemented a monadtransformer just form Option which seems to work ok https://stackoverflow.com/questions/48953288/how-does-one-state-that-a-module-implements-an-interface-so-that-a-type-in-the-s *)
module type MONAD = sig
  type 'a m
  val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
  val return : 'a -> 'a m
end

module Identity : MONAD with type 'a m = 'a = struct
  type 'a m = 'a
  let (>>=) m f = f m
  let return x = x
end

module OptionT (M : MONAD) : MONAD
  with type 'a m = ('a option) M.m = struct
  type 'a m = ('a option) M.m

  let (>>=) m f = M.(>>=) m (fun option ->
    match option with
    | Some x -> f x
    | None -> M.return None)
  let return x = M.return @@ Some x
end

module Option = OptionT(Identity)

let _ =
  Option.(>>=) (Some 1) (fun x -> Some (x + 1))
