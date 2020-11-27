open Base
open Util

module H = Hsig
open Monads.RE_Functions(SigM)
open SigM.Syntax
open SigM
open CoqSyntax
open Tactics
open Custom

let guard cond lst =
  if cond then lst else []

let createBinders = List.map ~f:(fun p -> BinderNameType ([fst p],TermId (snd p)))

let rec genArg sort n bs = function
  (* lift! *)
  | H.Atom y -> map2 idApp (complete_ y) (map sty_terms (castUpSubst sort bs y n))
  | H.FunApp (f, p, xs) ->
    let* xs' = a_map (genArg sort n bs) xs in
    pure @@ idApp (funname_ (f^p)) xs'

let genVar sort n =
  let* open_x = isOpen sort in
  let* s = finT_ sort (sty_terms n) in
  let t = [s] ==> sortType sort n in
  pure @@ guard open_x [InductiveCtor (var_ sort, Some t)]

let genConstr sort n H.{ parameters; name; positions } =
    let* t =
      let* up_n_x = a_map (fun H.{ binders=bs; arg=y } -> genArg sort n bs y) positions in
      pure @@ (up_n_x ==> sortType sort n) in
    pure @@ InductiveCtor (constructor_ name, Some (if List.is_empty parameters then t else TermForall (createBinders parameters, t)))


let genBody sort =
  let* cs = constructors sort in
  let* (n,b) = introScopeVar "n" sort in
  let* varCons = genVar sort n in
  let* constrs = a_map (genConstr sort n) cs in
  pure @@ InductiveBody (sort, explicit_ b, TermSort Type, varCons @ constrs)

let rec genCodeT xs dps upList' =
  (* TODO I suspect the dependencies can only happen with modular code *)
  let upList = if (List.is_empty dps) then upList' else [] in
  let* x_open = isOpen (List.hd_exn xs) in
  (* TODO don't we have a field for that in the signature? *)
  let* varSorts = a_filter isOpen xs in
  let* hasbinders = map (fun l -> l |> List.is_empty |> not) (substOf (List.hd_exn xs)) in
  let substSorts = xs in
  let* ys = a_filter definable xs in
  let* types = a_map genBody ys in
  let* r = recursive xs in
  (* let* congruences = a_map genCongruences xs in *)
  let typesSentence = SentenceInductive (Inductive types) in
  let () = print_endline ("types:" ^ show_sentence typesSentence) in
  (* more let's *)
  pure @@ [SentenceSection (String.concat xs,
      [typesSentence]
  )]
