open Base
open Monads.RE_Functions(SigM)
open SigM.Syntax
open SigM
open CoqSyntax
open Util
open CoqNames
open Termutil
open Coqgen

(** Terminology:
 ** sort: a syntactic sort that is represented by an inductive type. In cbv SystemF ty, tm & vl
 ** scope variable: something of type nat that is used for scoped syntax. Sometimes named after a sort. E.g. m, n, mty, mvl
 ** scope variable vector: A SubstTy that contains multiple scope variables. E.g. sty_terms ms = [mty; mvl]
 ** renaming variable: some function that represents a renaming. E.g. xi : fin m -> fin n
 ** substitution variable: some function that represents a substitution. E.g. sigma : fin m -> vl mty mvl
 **  *)

let varApp sort n = refApp (var_ sort) (sty_terms n)

(** For a given sort create a renaming type
 ** fin m -> fin n *)
let renT m n = arr1_ (fin_ m) (fin_ n)

(** For a given sort create a substitution type.
 ** fin m -> tm nty nvl *)
(** TODO I suspect that here we only get SubstScope variables for n *)
let substT m ns sort = arr1_ (fin_ m) (sortType sort ns)

(** Create an extensional equivalence between unary functions s & t
 ** forall x, s x = t x *)
let equiv_ s t =
  let x = VarState.tfresh "x" in
  forall_ [binder1_ x] (eq_ (app1_ s (ref_ x))
                          (app1_ t (ref_ x)))

(** For a given sort and some SubstTy ts return the component of ts that has the same name as the sort.
 ** E.g. for sort vl and ts being a list of renamings [ xity; xivl ] return xivl
 ** TODO Even though this function has an error case (when the given sort does not substitute
 ** into itself, like tm in cbv system F), the returned term is not used. Probably because there
 ** is a similar kind of filtering logic as is used in this function. It would be preferable if
 ** we would then only call toVar if we really want to use it *)
let toVar sort ts =
  let* substSorts = substOf sort in
  let () = if (List.length substSorts <> List.length @@ sty_terms ts)
    then Stdio.print_endline "toVar unequal"
    else () in
  let zs = List.filter ~f:(fun (substSort,_) -> String.(sort = substSort)) (list_zip substSorts (sty_terms ts)) in
  if List.is_empty zs
  then
    let () = Stdio.print_endline "toVar: list was empty. For some probably brittle reason the resulting term is never used" in
    pure @@ refApp sort @@ [ref_ "HEREintoVar"; ref_ "true"] @ sty_terms ts
  else List.hd_exn zs |> snd |> pure

(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
let getPattern name positions =
  List.mapi ~f:(fun i _ -> name ^ Int.to_string i) positions

(** Extract the extra shifting argument from a BinderList. *)
let binvparameters = function
    | H.Single x -> ([], [])
    | H.BinderList (m, _) -> ([ref_ m], [binder1_ ~implicit:true ~btype:nat_ m])

let bparameters binder =
  let (terms, binders) = binvparameters binder in
  (terms, explicit_ binders)

(* TODO I don't really understand this chain of up functions yet *)
let up x f n b =
  let* xs = substOf x in
  pure @@ List.map (list_zip xs n) ~f:(fun (p, n_i) -> f p b n_i)
let ups x f = m_fold (up x f)

let upRen x bs xs = ups x (fun z b xi -> refApp (upRen_ z b) (fst (bparameters b) @ [xi])) xs bs

let upScope x bs terms = ups x (fun z b n -> succ_ n z b) terms bs

let upSubstS x bs xs = ups x (fun z b xi -> refApp (up_ z b) (fst (bparameters b) @ [xi])) xs bs

let up' x f n b =
  let* xs = substOf x in
  a_map (fun (p, n_i) -> f p b n_i) (list_zip xs n)

let upEq x bs xs f = m_fold (up' x f) xs bs

let upSubst x bs = function
  | SubstScope xs -> map (fun xs -> SubstScope xs) (upScope x bs xs)
  | SubstRen xs -> map (fun xs -> SubstRen xs) (upRen x bs xs)
  | SubstSubst xs -> map (fun xs -> SubstSubst xs) (upSubstS x bs xs)
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


(** Create a scope variable together with a implicit binder
 ** Example: { m : nat } *)
let introScopeVarS name =
  let name = VarState.tfresh name in
  (* TODO for unscoped code I need to filter it out here. was the special binder type before *)
  (ref_ name, [binder1_ ~implicit:true ~btype:nat_ name])

(** Create a renaming variable together with a binder
 ** Example: ( xi : fin m -> fin n ) *)
let genRenS name (m, n) =
  let name = VarState.tfresh name in
  (ref_ name, [binder1_ ~btype:(renT m n) name])

(** Create a substitution variable for the given sort together with a binder
 ** Example: ( sigma: fin m -> tm nty nvl ) *)
let genSubstS name (m, ns) sort =
  let name = VarState.tfresh name in
  (ref_ name, [binder1_ ~btype:(substT m ns sort) name])

(** Create multiple scope variables and their binders. One for each substituting sort of the given sort
 ** Example: { m_ty : nat } { m_vl : nat } *)
let introScopeVar name sort =
  let* substSorts = substOf sort in
  let names = List.map ~f:(sep name) substSorts in
  pure @@ (
    SubstScope (mkRefs names),
    (* Fix for wrong translation of sorts that don't have a substitution vector.
     * Could also filter out in translation but this seems better. *)
    if List.is_empty names then []
        else [binder_ ~implicit:true ~btype:nat_ names]
  )

(** Create multiple renaming variables and their binders. One for each substituting sort of the given sort. The given scope variables vectors ms & ns should also contain one scope variable per substituting sort.
 ** Example: for a renaming variable xi and for a sort tm with substituting sorts ty & vl, create
 ** ( xi_ty : fin m_ty -> fin n_ty) ( xi_vl : fin m_vl -> fin n_vl ) *)
let genRen sort name (ms, ns) =
  let* substSorts = substOf sort in
  let names = List.map ~f:(sep name) substSorts in
  let types = List.map2_exn ~f:renT (sty_terms ms) (sty_terms ns) in
  pure @@ (
    SubstRen (mkRefs names),
    List.map2_exn ~f:(fun x t -> binder1_ ~btype:t x) names types
  )

(** Create multiple substitution variables and their binders. One for each substituting sort of the given sort. The given scope variables vectors ms & ns should also contain one scope variable per substituting sort.
 ** Example: for a substitution variable sigma and for a sort tm with substituting sorts ty & vl, create
 ** ( sigmaty : fin mty -> ty nty ) ( sigmavl : fin mvl -> vl nty nvl ) *)
let genSubst sort name (ms, ns) =
  let* substSorts = substOf sort in
  let names = List.map ~f:(sep name) substSorts in
  let* types = a_map2_exn (fun substSort m ->
      (* Here we filter the vector ns to include only the substitution sorts relevant for substSort *)
      (* TODO ask kathrin: couldn't we just do set_diff ns (substOf SubstSort)? *)
      let* ns' = castSubst sort substSort ns in
      pure @@ substT m ns' substSort)
      substSorts (sty_terms ms) in
  pure @@ (
    SubstSubst (mkRefs names),
    List.map2_exn ~f:(fun n t -> binder1_ ~btype:t n) names types
  )

(** Create an extensional equality between two substitutions and its binder
 ** H: forall x, sigma x = tau x *)
let genEq name sigma tau =
  let name = VarState.tfresh name in
  ( ref_ name,
    [binder1_ ~btype:(equiv_ sigma tau) name] )

(** Create multiple extensional equalities between two substitutions and their binders. One for each of the substituting sorts of the given sort
 ** ( Hty : forall x, sigmaty x = tauty x ) ( Hvl : forall x, sigmavl x = tauvl x ) *)
let genEqs sort name sigmas taus f =
  let* substSorts = substOf sort in
  let names = List.map ~f:(sep name) substSorts in
  let types = List.map2_exn ~f:(equiv_) sigmas taus in
  pure @@ (
    SubstEq (mkRefs names, f),
    List.map2_exn ~f:(fun n t -> binder1_ ~btype:t n) names types
  )

(** Create a finite type for a given sort and the corresponding element of the scope variable vector
 ** For sort vl and ns = [nty; nvl], create fin nvl *)
let finT_ sort ns = map fin_ (toVar sort (SubstScope ns))

(** Construction of patterns, needed for lifting -- yields a fitting pattern of S and id corresponding to the base sort and the binder
 ** TODO I did not implement the noren version which had an application in the else branch instead of underscore directly. Is that relevant?
 ** TODO example *)
let patternSId sort binder =
  let* substSorts = substOf sort in
  let* hasRen = hasRenamings sort in
  let shift y = if hasRen
    then shift_
    else (shift_ >>> refApp (var_ y) (List.map ~f:(const underscore_) substSorts)) in
  let shiftp p y = if hasRen
    then refApp shift_p_ [ref_ p]
    else refApp shift_p_ [ref_ p]
      >>> refApp (var_ y) (List.map ~f:(const underscore_) substSorts) in
  up sort (fun y b _ -> match b with
      | H.Single bsort -> if String.(y = bsort) then shift y else id_
      | H.BinderList (p, bsort) -> if String.(y = bsort) then shiftp p y else id_)
    (mkRefs substSorts) binder

(* Some patterns in the code for which I don't have a name yet. I have to check in the generated code for a fitting name *)
let findName1 sort substSorts ms =
  a_map (fun substSort ->
      map2 refApp (pure @@ var_ substSort)
        (map sty_terms (castSubst sort substSort ms))) substSorts

let map_ f ts = refApp (sepd [f; "map"]) ts
let mapId_ f ts = refApp (sepd [f; "id"]) ts
let mapExt_ f ts = refApp (sepd [f; "ext"]) ts
let mapComp_ f ts = refApp (sepd [f; "comp"]) ts
