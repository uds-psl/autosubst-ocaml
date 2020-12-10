open Base
open Util

module M = Monadic
module H = Hsig
module AL = AssocList

type 'a wrapped = 'a M.Result.Make(String).t
type 'a actual_t = H.t -> 'a M.Result.Make(String).t

module RE = M.Reader.MakeT(ErrorM)(struct type t = H.t end)

include RE

let ask = peek
let asks f = f <$> ask

let error s = ErrorM.error s |> elevate

include M.Monad.ApplicativeFunctionsList(RE)
include M.Monad.MonadFunctionsList(RE)

let map2 f a b =
  let open Syntax in
  let* f' = map f a in
  map f' b

let rec invert =
  let open Syntax in function
  | [] -> pure []
  | m :: ms ->
    let* m' = m in
    let* ms' = invert ms in
    pure @@ m' :: ms'

let a_map2_exn f a b =
  invert @@ List.map2_exn ~f a b

let rec m_fold_left ~f ~init xs =
  let open Syntax in
  match xs with
  | [] -> pure init
  | x :: xs ->
    let* init = f init x in
    m_fold_left ~f ~init xs

let a_concat_map f xs =
  map List.concat @@ a_map f xs

let m_guard cond m =
  if cond then m else pure []

(** In the following module we collect the functions that are used either in
 ** code generation or signature graph generation. *)
module Functions = struct
  open RE.Syntax

  let constructors id =
    let* spec = asks H.sigSpec in
    match (AL.assoc id spec) with
    | Some cs -> pure cs
    | None -> error @@ "constructors called on invalid type: " ^ id

  let substOf tid =
    let* substs = asks H.sigSubstOf in
    match AL.assoc tid substs with
    | Some cs -> pure cs
    | None -> error @@ "substOf called on invalid type: " ^ tid

  let isOpen id =
    let* opens = asks H.sigIsOpen in
    pure @@ Set.mem opens id

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
                    ~f:(function { cpositions; _ } ->
                        concat_map cpositions
                          ~f: (function { head; _ } -> H.getArgSorts head )))

  let arguments id =
    let* args = asks H.sigArguments in
    match (AL.assoc id args) with
    | Some ts -> pure ts
    | None -> error @@ "arguments called on invalid type: " ^ id

  let types =
    let* c = asks H.sigComponents in
    pure @@ List.concat c

  let getComponent x =
    let* comps = asks H.sigComponents in
    pure @@ List.(concat @@
                  filter_map comps ~f:(fun c -> if List.mem c x ~equal:String.equal
                                        then Some c
                                        else None))

  (* TODO this seems to check if a given list of components is recursive but I don't know exactly what that entails *)
  let isRecursive xs =
    if (List.is_empty xs) then error "Can't determine whether the component is recursive."
    else let* args = successors (List.hd_exn xs) in
      list_intersection xs args |> List.is_empty |> not |> pure

  (* TODO  a lot of binding going on here *)
  let boundBinders xs =
    let* binders = a_map (fun x ->
        constructors x >>= fun cs -> pure @@
        List.(cs >>= function { cpositions; _ } ->
            cpositions >>= function { binders; _ } ->
              binders >>= H.getBinders)) xs in
    pure @@ List.concat binders

  let rec hasRenamings x =
    (* let* y = extend_ x
     * TODO what part of this function can be removed? *)
    let y = x in
    let* xs = getComponent y in
    let* boundBinders = boundBinders xs in
    let* all = types in
    let occursIn = list_diff all xs in
    let* occ = a_filter (fun z ->
        let* zs = successors z in
        pure @@ List.mem zs y ~equal:equal_string)
        occursIn in
    let* bs = a_map hasRenamings occ in
    let xs_bb = list_intersection xs boundBinders |> List.is_empty |> not in
    let bs' = List.filter bs ~f:(fun b -> b) |> List.is_empty |> not in
    pure (xs_bb || bs')
end
