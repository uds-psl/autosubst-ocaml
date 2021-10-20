module M = Monadic

module ExtraFunctionsList (MON: M.Monad.MONAD) = struct
  module Infix = M.Monad.MonadInfix(MON)
  module Fun = M.Monad.ApplicativeFunctionsList(MON)
  open Fun
  open Infix.Syntax
  open MON

  let a_split_map f a =
    let* bs = a_map f a in
    let (cs, ds) = List.split bs in
    pure (cs, ds)

  let a_map2 f la lb =
    a_map (fun (a, b) -> f a b) (List.combine la lb)

  let liftM2 f ma mb =
    let* a = ma in
    let* b = mb in
    pure (f a b)

  let rec m_fold_left ~f ~init xs =
    match xs with
    | [] -> pure init
    | x :: xs ->
      let* init = f init x in
      m_fold_left ~f ~init xs

  let rec m_fold_right ~f ~init xs =
    match xs with
    | [] -> pure init
    | x :: xs ->
      let* result = m_fold_right ~f ~init xs in
      f x result

  let a_concat_map f xs =
    map List.concat @@ a_map f xs

  let m_guard b m =
    if b then m else pure []
end
