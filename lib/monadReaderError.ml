open Core
open Util

module M = Monadic
module H = Hsig
module AL = AssocList


module type MONAD_RE = sig
  type 'a t

  include Monads.MONAD_READER
    with type 'a t := 'a t
  include Monads.MONAD_ERROR
    with type 'a t := 'a t

  (* TODO could also abstract over 'a collection *)
  include M.Monad.APPLICATIVE_FUNCTIONS
    with type 'a applicative := 'a t
    with type 'a collection := 'a list

  include M.Monad.MONAD_FUNCTIONS
    with type 'a monad := 'a t
    with type 'a collection := 'a list

  (* since the syntax depends on the monad at hand it seems better to leave it our of here and only include it when I actually want to implement the functions so that I can instantiate the Syntax with THIS monad  *)
  (* include module type of M.Monad.MonadInfix(MON) *)
end

(* here I need to instantiate the read and error type
 * it's like
 * (MonadReader Signature m, MonadError String m) => ...
 * in Haskell (I hope) *)
module Functions (RE: MONAD_RE
                  with type r := H.t
                  with type e := string) =
struct
  (* Now I know that the functions should work on the RE monad, so I can generate the syntax for it *)
  module REInfix = M.Monad.MonadInfix(RE)
  open REInfix.Syntax
  open REInfix

  open RE

(* -- Accessing the signature
 * -- These functions work on both GenM and SigM *)

  let constructors id =
    let* spec = asks H.sigSpec in
    match (AL.assoc id spec) with
    | Some cs -> pure cs
    | None -> error @@ "constructors called on invalid type: " ^ id

  let substOf tid =
    let* substs = asks H.sigSubstOf in
    match ListLabels.assoc_opt tid substs with
    | Some cs -> pure cs
    | None -> error @@ "substOf called on invalid type: " ^ tid

  let isOpen id =
    let* opens = asks H.sigIsOpen in
    pure @@ List.mem opens id ~equal:equal_string

  let definable id =
    let* b = isOpen id in
    let* cs = constructors id in
    pure (b || not (List.is_empty cs))

  (* Yields true if at least one variable is contained. *)
  let hasArgs id = (fun l -> List.is_empty l |> not) <$> substOf id

  let arguments id =
    let* args = asks H.sigArguments in
    match AL.assoc id args with
    | Some ts -> pure ts
    | None -> error @@ "arguments called on invalid type: " ^ id

  let successors id =
    let* cs = constructors id in
    pure @@ List.(concat_map cs
                    ~f:(function { positions; _ } ->
                        concat_map positions
                          ~f: (function { arg; _ } -> H.getIds arg )))
end
