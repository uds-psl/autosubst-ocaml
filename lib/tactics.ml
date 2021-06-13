(** This module also implements utility functions for code generation like TermUtil
 ** but they are mostly more complex *)
open RWEM.Syntax
open RWEM
open CoqSyntax
open Util
open CoqNames
open Termutil
open GallinaGen
module S = Settings

(** Terminology:
 ** sort: a syntactic sort that is represented by an inductive type. In cbv SystemF ty, tm & vl
 ** scope variable: something of type nat that is used for scoped syntax. Sometimes named after a sort. E.g. m, n, mty, mvl
 ** scope variable vector: A SubstTy that contains multiple scope variables. E.g. sty_terms ms = [mty; mvl]
 ** renaming variable: some function that represents a renaming. E.g. xi : fin m -> fin n
 ** substitution variable: some function that represents a substitution. E.g. sigma : fin m -> vl mty mvl
 **  *)

(** Create a variable index either of type nat or a finite type *)
let varT m =
  match !Settings.scope_type with
  | S.Unscoped -> nat_
  | S.WellScoped -> fin_ m

(** For a given sort create a renaming type
 ** fin m -> fin n *)
let renT m n =
  match !Settings.scope_type with
  | S.Unscoped -> arr1_ nat_ nat_
  | S.WellScoped -> arr1_ (fin_ m) (fin_ n)

(** For a given sort create a substitution type.
 ** fin m -> tm nty nvl *)
let substT m ns sort =
  match !Settings.scope_type with
  | S.Unscoped -> arr1_ nat_ (sortType sort ns)
  | S.WellScoped -> arr1_ (fin_ m) (sortType sort ns)

(** Create an extensional equivalence between unary functions s & t
 ** forall x, s x = t x *)
let equiv_ s t =
  let x = VarState.tfresh "x" in
  forall_ [binder1_ x] (eq_ (app1_ s (ref_ x))
                          (app1_ t (ref_ x)))

(** For a given sort and some SubstTy ts return the component of ts that has the same name as the sort.
 ** E.g. for sort vl and ts being a list of renamings [ xity; xivl ] return xivl
 ** *)
let toVar sort ts =
  let* substSorts = substOf sort in
  let zs = List.filter (fun (substSort, _) -> sort = substSort) (list_zip substSorts (sty_terms ts)) in
  if list_empty zs
  then error "toVar was called with incompatible sort and substitution vector. The substitution vector must contain the sort!"
  else List.hd zs |> snd |> pure

(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
let getPattern name positions =
  List.mapi (fun i _ -> name ^ string_of_int i) positions

(** Extract the extra shifting argument from a BinderList. *)
let binvparameters = function
  | L.Single x -> ([], [])
  | L.BinderList (m, _) -> ([ref_ m], [binder1_ ~implicit:true ~btype:nat_ m])

let bparameters binder =
  let (terms, binders) = binvparameters binder in
  (terms, explicit_ binders)

(* TODO I don't really understand this chain of up functions yet *)
let up x f n b =
  let* xs = substOf x in
  pure @@ List.map (fun (p, n_i) -> f p b n_i) (list_zip xs n)
let ups x f = m_fold (up x f)

let upRen x bs xs = ups x (fun z b xi -> app_ref (upRen_ z b) (fst (bparameters b) @ [xi])) xs bs

let upScope x bs terms = ups x (fun z b n -> succ_ n z b) terms bs

let upSubstS x bs xs = ups x (fun z b xi -> app_ref (up_ z b) (fst (bparameters b) @ [xi])) xs bs

let up' x f n b =
  let* xs = substOf x in
  a_map (fun (p, n_i) -> f p b n_i) (list_zip xs n)

let upEq x bs xs f = m_fold (up' x f) xs bs

let upSubst x bs = function
  | SubstScope (ns, xs) -> map (fun xs -> SubstScope (ns, xs)) (upScope x bs xs)
  | SubstRen xs -> map (fun xs -> SubstRen xs) (upRen x bs xs)
  | SubstSubst xs -> map (fun xs -> SubstSubst xs) (upSubstS x bs xs)
  | SubstEq (xs, f) -> map2 (fun xs f -> SubstEq (xs, f)) (upEq x bs xs f) (pure f)

let cast x y xs =
  let* arg_x = substOf x in
  let* arg_y = substOf y in
  pure @@ List.(fold_right (fun (x, v) ws ->
      if mem x arg_y then v :: ws else ws)
      (list_zip arg_x xs) [])

(* TODO documentation. iirc it narrows a substitution vector *)
let castSubst x y = function
  | SubstScope (ns, xs) -> map (fun xs -> SubstScope (ns, xs)) (cast x y xs)
  | SubstRen xs -> map (fun xs -> SubstRen xs) (cast x y xs)
  | SubstSubst xs -> map (fun xs -> SubstSubst xs) (cast x y xs)
  | SubstEq (xs, f) -> map2 (fun xs f -> SubstEq (xs, f)) (cast x y xs) (pure f)

let castUpSubst sort bs y arg =
  let* arg' = castSubst sort y arg in
  upSubst y bs arg'


(** Create a scope variable together with a implicit binder
 ** Example: { m : nat } *)
let introScopeVarS name =
  let name = VarState.tfresh name in
  let binders = match !Settings.scope_type with
    | S.Unscoped -> []
    | S.WellScoped -> [binder1_ ~implicit:true ~btype:nat_ name] in
  (ref_ name, binders)


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
  let names = List.map (sep name) substSorts in
  let binders = guard (list_nempty names && Settings.is_wellscoped ())
      [binder_ ~implicit:true ~btype:nat_ names] in
  pure @@ (
    SubstScope (names, mk_refs names),
    (* Fix for wrong translation of sorts that don't have a substitution vector.
     * Could also filter out in translation but this seems better. *)
    binders
  )

(** Create multiple renaming variables and their binders. One for each substituting sort of the given sort. The given scope variables vectors ms & ns should also contain one scope variable per substituting sort.
 ** Example: for a renaming variable xi and for a sort tm with substituting sorts ty & vl, create
 ** ( xi_ty : fin m_ty -> fin n_ty) ( xi_vl : fin m_vl -> fin n_vl ) *)
let genRen sort name (ms, ns) =
  let* substSorts = substOf sort in
  let names = List.map (sep name) substSorts in
  let types = List.map2 renT (sty_terms ms) (sty_terms ns) in
  pure @@ (
    SubstRen (mk_refs names),
    List.map2 (fun x t -> binder1_ ~btype:t x) names types
  )

(** Create multiple substitution variables and their binders. One for each substituting sort of the given sort. The given scope variables vectors ms & ns should also contain one scope variable per substituting sort.
 ** Example: for a substitution variable sigma and for a sort tm with substituting sorts ty & vl, create
 ** ( sigmaty : fin mty -> ty nty ) ( sigmavl : fin mvl -> vl nty nvl ) *)
let genSubst sort name (ms, ns) =
  let* substSorts = substOf sort in
  let names = List.map (sep name) substSorts in
  let* types = a_map2_exn (fun substSort m ->
      (* Here we filter the vector ns to include only the substitution sorts relevant for substSort *)
      let* ns' = castSubst sort substSort ns in
      pure @@ substT m ns' substSort)
      substSorts (sty_terms ms) in
  pure @@ (
    SubstSubst (mk_refs names),
    List.map2 (fun n t -> binder1_ ~btype:t n) names types
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
  let names = List.map (sep name) substSorts in
  let types = List.map2 equiv_ sigmas taus in
  pure @@ (
    SubstEq (mk_refs names, f),
    List.map2 (fun n t -> binder1_ ~btype:t n) names types
  )

(** Create the argument type for the variable constructor of the given sort.
 ** If we create well scoped code fin will be indexed by the element of the scope indices
 ** corresponding to the sort.
 ** For sort vl and ns = [nty; nvl], create fin nvl *)
let gen_var_arg sort ns =
  match !Settings.scope_type with
  | S.Unscoped -> pure @@ nat_
  | S.WellScoped -> map fin_ (toVar sort ns)

(** Construction of patterns, needed for lifting -- yields a fitting pattern of S and id corresponding to the base sort and the binder
 ** TODO example *)
let patternSId sort binder =
  let* substSorts = substOf sort in
  let* hasRen = hasRenamings sort in
  let shift y = if hasRen
    then shift_
    else (shift_ >>> app_var_constr y (SubstScope (List.map (const "_") substSorts, List.map (const underscore_) substSorts))) in
  let shiftp p y = if hasRen
    then app_ref shift_p_ [ref_ p]
    else app_ref shift_p_ [ref_ p]
      >>> app_var_constr y (SubstScope (List.map (const "_") substSorts, List.map (const underscore_) substSorts)) in
  up sort (fun y b _ -> match b with
      | L.Single bsort -> if y = bsort then shift y else id_
      | L.BinderList (p, bsort) -> if y = bsort then shiftp p y else id_)
    (mk_refs substSorts) binder

let patternSIdNoRen sort binder =
  let* substSorts = substOf sort in
  let shift = const shift_ in
  let shiftp p = const @@ app_ref shift_p_ [ ref_ p ] in
  up sort (fun y b _ -> match b with
      | L.Single bsort -> if y = bsort then shift y else app_id_ underscore_
      | L.BinderList (p, bsort) -> if y = bsort then shiftp p y else app_id_ underscore_)
    (mk_refs substSorts) binder

(** Create an application of the var constructor for each element of the substitition vector
 ** of the given sort
 **
 ** e.g. [ var_ty m_ty; var_vl m_ty m_vl ] *)
let mk_var_apps sort ms =
  let* substSorts = substOf sort in
  a_map (fun substSort ->
      map2 app_var_constr (pure substSort) (castSubst sort substSort ms))
    substSorts

(** Convert a renaming to a substitution by postcomposing it with the variable constructor
 ** of the given sort. The domain of xis is the given ns *)
let substify sort ns xis =
  let* substSorts = substOf sort in
  a_map2_exn (fun substSort xi ->
      let* ns' = castSubst sort substSort ns in
      pure (xi >>> app_var_constr substSort ns'))
    substSorts (sty_terms xis)

(** Compose a renaming with a substitution *)
let comp_ren_or_subst sort sty1s sty2s =
  let* substSorts = substOf sort in
  let* ren_or_subst_ = match sty1s with
    | SubstRen _ -> pure ren_
    | SubstSubst _ -> pure subst_
    | _ -> error "comp_ren_or_subst called with wrong subst_ty" in
  a_map2_exn (fun substSort sty2 ->
      let* sty1s' = castSubst sort substSort sty1s in
      pure @@ (sty2 >>> app_ref (ren_or_subst_ substSort) (sty_terms sty1s')))
    substSorts (sty_terms sty2s)

(** Convenience functions that are passed to traversal which it uses when dealing with functors. *)
let map_ f ts = app_ref (sepd [f; "map"]) ts
let mapId_ f ts = app_ref (sepd [f; "id"]) ts
let mapExt_ f ts = app_ref (sepd [f; "ext"]) ts
let mapComp_ f ts = app_ref (sepd [f; "comp"]) ts
