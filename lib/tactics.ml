open Base
open Monads.RE_Functions(SigM)
open SigM.Syntax
open SigM
open CoqSyntax
open Util


(* TODO what does this function even do!? *)
let toVar sort ts =
  let styt = sty_terms ts in
  (* let () = print_endline ("styt: "^ String.concat ~sep:"| " (List.map ~f:show_term styt)) in *)
  let () = print_endline ("sort:" ^ sort) in
  let* xs = substOf sort in
  let () = print_endline ("xs: " ^ String.concat ~sep:"| " xs) in
  (* TODO what does this do, what are the terms in ts? *)
  let zs = List.filter ~f:(fun (y,_) -> String.(sort = y)) (list_zip xs styt) in
  if List.is_empty zs
  then pure @@ idApp sort [TermId "HERE in toVar."; TermId "true"; TermSubst ts]
  else List.hd_exn zs |> snd |> pure

let introScopeVar name sort =
  let* args = substOf sort in
  let scope = List.map ~f:(fun x -> sort ^ x) args in
  pure @@ (
    SubstScope (List.map ~f:(fun x -> TermId x) scope),
    [BinderImplicitScopeNameType (scope, nat)]
  )

let up x f n b =
  let* xs = substOf x in
  pure @@ List.map (list_zip xs n) ~f:(fun (p, n_i) -> f p b n_i)
let ups x f = m_fold (up x f)

let upScope x bs terms = ups x (fun z b n -> succ_ n z b) terms bs

let up' x f n b =
  let* xs = substOf x in
  a_map (fun (p, n_i) -> f p b n_i) (list_zip xs n)

let upEq x bs xs f = m_fold (up' x f) xs bs

let upSubst x bs = function
  | SubstScope xs -> map (fun xs -> SubstScope xs) (upScope x bs xs)
  | SubstRen xs -> map (fun xs -> SubstRen xs) (upScope x bs xs)
  | SubstSubst xs -> map (fun xs -> SubstSubst xs) (upScope x bs xs)
  | SubstEq (xs, f) -> map2 (fun xs f -> SubstEq (xs, f)) (upEq x bs xs f) (pure f)
  | SubstConst xs -> pure @@ SubstConst xs

let cast x y xs =
  let* arg_x = substOf x in
  let* arg_y = substOf y in
  pure @@ List.(fold_right (list_zip arg_x xs)
                  ~f:(fun (x, v) ws -> if mem arg_y x ~equal:Poly.equal then v::ws else ws)
                  ~init:[])

let castSubst x y = function
  | SubstScope xs -> map (fun xs -> SubstScope xs) (cast x y xs)
  | SubstRen xs -> map (fun xs -> SubstRen xs) (cast x y xs)
  | SubstSubst xs -> map (fun xs -> SubstSubst xs) (cast x y xs)
  | SubstEq (xs, f) -> map2 (fun xs f -> SubstEq (xs, f)) (cast x y xs) (pure f)
  | SubstConst xs -> pure @@ SubstConst xs

let castUpSubst sort bs y arg =
  let* arg' = castSubst sort y arg in
  upSubst y bs arg'

let explicitS_ = function
  | BinderImplicitName s -> BinderName s
  | BinderImplicitNameType (s, t) -> BinderNameType (s, t)
  | BinderImplicitScopeNameType (s, t) -> BinderScopeNameType (s, t)
  | s -> s

let explicit_ = List.map ~f:explicitS_

let finT_ sort n = map fin_ (toVar sort (SubstScope n))
