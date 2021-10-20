(** This module also implements utility functions for code generation like TermUtil
 ** but they are mostly more complex *)
open RSEM.Syntax
open RSEM
open ScopeTypes
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
  match !S.scope_type with
  | S.Unscoped -> nat_
  | S.Wellscoped -> fin_ m

(** For a given sort create a renaming type
 ** fin m -> fin n *)
let renT m n = match !S.scope_type with
  | S.Unscoped -> arr1_ nat_ nat_
  | S.Wellscoped -> arr1_ (fin_ m) (fin_ n)

(** For a given sort create a substitution type.
 ** fin m -> tm nty nvl *)
let substT m ns sort = match !S.scope_type with
  | S.Unscoped -> arr1_ nat_ (ref_ sort)
  | S.Wellscoped -> arr1_ (fin_ m) (app_sort sort ns)

let predT = arr1_ nat_ prop_

(** Create an extensional equivalence between unary functions s & t
 ** forall x, s x = t x *)
let equiv_ s t =
  let x = varName "x" in
  forall_ [binder1_ x] (eq_ (app1_ s (ref_ x))
                          (app1_ t (ref_ x)))

(** For a given sort and some SubstTy ts return the component of ts that has the same name as the sort.
 ** E.g. for sort vl and ts being a list of renamings [ xity; xivl ] return xivl
 ** *)
(* DONE I think it would be easier if ts was already a list of pairs where the first component is the corresponding substSort. I would have to change all the genRen/genSubst/... functions for that but then here it would just be a call to AssocList.find
 *
 * No, it was not easier. check the "toVar" feature branch *)
let to_var_helper substSort sort l =
  let* substSorts = get_substv sort in
  let assoc = AL.from_list (List.combine substSorts l) in
  match AL.assoc substSort assoc with
  | None -> error (Printf.sprintf "to_var was called with incompatible sort and substitution vector. The substitution vector must contain the sort! substSort: %s\tsort: %s" substSort sort)
  | Some t -> pure t

let to_var sort st =
  to_var_helper sort sort (sty_terms st)

(** For a substTy [st] which is based on [sort]'s substitution vector this
    projects out the component of [substSort] *)
let to_var_project substSort sort st =
  to_var_helper substSort sort (sty_terms st)

let to_var_scope sort ss =
  to_var_helper sort sort (ss_terms_all ss)

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
let up x f ns b =
  let* xs = get_substv x in
  pure @@ List.map2 (fun p n_i -> f p b n_i) xs ns

(* here evaluation stops ifbs is empty. Is there a better way to do this? *)
let ups x f xs bs = m_fold (up x f) xs bs

let upRen x bs xs = ups x (fun z b xi -> app_ref (upRen_ z b) (fst (bparameters b) @ [xi])) xs bs

let upScope x bs terms = ups x (fun z b n -> succ_ n z b) terms bs

let upPred x bs pred_names = ups x (fun z b p -> app_ref (up_allfv_name z b) [p]) pred_names bs

let upSubstS x bs xs = ups x (fun z b xi -> app_ref (up_ z b) (fst (bparameters b) @ [xi])) xs bs

let up' x f ns b =
  let* xs = get_substv x in
  a_map2 (fun p n_i -> f p b n_i) xs ns

(* this (and the up') is finally responsible for calling the function contained in the SubstEq *)
let upEq x bs xs f = m_fold (up' x f) xs bs
let upAllfvH x bs xs f = m_fold (up' x f) xs bs

let upSubstScope x bs = function
  | SubstScope (ns, xs) -> map (fun xs -> SubstScope (ns, xs)) (upScope x bs xs)
let upSubst x bs = function
  | SubstRen xs -> map (fun xs -> SubstRen xs) (upRen x bs xs)
  | SubstSubst xs -> map (fun xs -> SubstSubst xs) (upSubstS x bs xs)
  | SubstEq (xs, f) -> map (fun xs -> SubstEq (xs, f)) (upEq x bs xs f)
  | SubstPred xs -> map (fun xs -> SubstPred xs) (upPred x bs xs)
  | SubstAllfvH (xs, f) -> map (fun xs -> SubstEq (xs, f)) (upAllfvH x bs xs f)

let cast x y xs =
  let* arg_x = get_substv x in
  let* arg_y = get_substv y in
  pure @@ List.(fold_right (fun (x, v) ws ->
      if mem x arg_y then v :: ws else ws)
      (List.combine arg_x xs) [])

(* TODO documentation. iirc it narrows a substitution vector *)
let castSubstScope x y = function
  | SubstScope (ns, xs) -> map (fun xs -> SubstScope (ns, xs)) (cast x y xs)
let castSubst x y = function
  | SubstRen xs -> map (fun xs -> SubstRen xs) (cast x y xs)
  | SubstSubst xs -> map (fun xs -> SubstSubst xs) (cast x y xs)
  | SubstEq (xs, f) -> map (fun xs -> SubstEq (xs, f)) (cast x y xs)
  | SubstPred xs -> map (fun xs -> SubstPred xs) (cast x y xs)
  | SubstAllfvH (xs, f) -> map (fun xs -> SubstAllfvH (xs, f)) (cast x y xs)

let castUpSubstScope sort bs y arg =
  let* arg' = castSubstScope sort y arg in
  upSubstScope y bs arg'
let castUpSubst sort bs y arg =
  let* arg' = castSubst sort y arg in
  upSubst y bs arg'



(** TODO document *)
let introUntypedVar ?btype name =
  (name, [binder1_ ?btype name])

(** Create a scope variable together with a implicit binder
 ** Example: { m : nat } *)
let genScopeVar name =
  let binders = match !S.scope_type with
    | S.Unscoped -> []
    | S.Wellscoped -> [binder1_ ~implicit:true ~btype:nat_ name] in
  (ref_ name, binders)

(** Create a renaming variable together with a binder
 ** Example: ( xi : fin m -> fin n ) *)
let genRen name (m, n) =
  (ref_ name, [binder1_ ~btype:(renT m n) name])

(** Create a substitution variable for the given sort together with a binder
 ** Example: ( sigma: fin m -> tm nty nvl ) *)
let genSubst name sort (m, ns) =
  (ref_ name, [binder1_ ~btype:(substT m ns sort) name])

let genPred ?implicit name =
  (ref_ name, [binder1_ ?implicit ~btype:predT name])

(** Create an extensional equality between two functions
 ** Example: ( H: forall x, sigma x = tau x ) *)
 let genEq name sigma tau =
  ( ref_ name,
    [binder1_ ~btype:(equiv_ sigma tau) name] )

(** Create multiple scope variables and their binders. One for each substituting sort of the given sort
 ** Example: { m_ty : nat } { m_vl : nat } *)
let genScopeVarVect name sort =
  let* substSorts = get_substv sort in
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
let genRenVect name sort (ms, ns) =
  let* substSorts = get_substv sort in
  let names = List.map (sep name) substSorts in
  let types = List.map2 renT (ss_terms_all ms) (ss_terms_all ns) in
  pure @@ (
    SubstRen (mk_refs names),
    List.map2 (fun x t -> binder1_ ~btype:t x) names types
  )

(** Create multiple substitution variables and their binders. One for each substituting sort of the given sort. The given scope variables vectors ms & ns should also contain one scope variable per substituting sort.
 ** Example: for a substitution variable sigma and for a sort tm with substituting sorts ty & vl, create
 ** ( sigmaty : fin mty -> ty nty ) ( sigmavl : fin mvl -> vl nty nvl ) *)
let genSubstVect name sort (ms, ns) =
  let* substSorts = get_substv sort in
  let names = List.map (sep name) substSorts in
  let* types = a_map2 (fun substSort m ->
      (* Here we filter the vector ns to include only the substitution sorts relevant for substSort *)
      let* ns' = castSubstScope sort substSort ns in
      pure @@ substT m ns' substSort)
      substSorts (ss_terms_all ms) in
  pure @@ (
    SubstSubst (mk_refs names),
    List.map2 (fun n t -> binder1_ ~btype:t n) names types
  )

let genPredVect ?implicit name sort ms =
  let* substSorts = get_substv sort in
  let names = List.map (sep name) substSorts in
  let types = List.map (const predT) substSorts in
  pure @@ (
    SubstPred (mk_refs names),
    List.map2 (fun n t -> binder1_ ?implicit ~btype:t n) names types
  )

(** Create multiple extensional equalities between two substitutions and their binders. One for each of the substituting sorts of the given sort
 ** ( Hty : forall x, sigmaty x = tauty x ) ( Hvl : forall x, sigmavl x = tauvl x ) *)
let genEqVect name sort sigmas taus f =
  let* substSorts = get_substv sort in
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
  match !S.scope_type with
  | S.Unscoped -> pure @@ nat_
  | S.Wellscoped -> map fin_ (to_var_scope sort ns)

(** Construction of patterns, needed for lifting -- yields a fitting pattern of S and id corresponding to the base sort and the binder
 ** TODO example *)
let patternSId sort binder =
  let* substSorts = get_substv sort in
  let* hasRen = hasRenamings sort in
  let shift y = if hasRen
    then shift_
      (* DONE remove app_var_constr and the SubstScope since I'm calling sty_terms right away
       * no I can't remove it b/c I need the filtering behavior of ss_terms so I need to convert it to a SubstScope *)
    else (shift_ >>> app_var_constr y (SubstScope (List.map (const "_") substSorts, List.map (const underscore_) substSorts))) in
  let shiftp p y = if hasRen
    then app1_ shift_p_ (ref_ p)
    else app1_ shift_p_ (ref_ p)
      >>> app_var_constr y (SubstScope (List.map (const "_") substSorts, List.map (const underscore_) substSorts)) in
  up sort (fun y b _ -> match b with
      | L.Single bsort -> if y = bsort then shift y else id_
      | L.BinderList (p, bsort) -> if y = bsort then shiftp p y else id_)
    (mk_refs substSorts) binder

let patternSIdNoRen sort binder =
  let* substSorts = get_substv sort in
  let shift = const shift_ in
  let shiftp p = const @@ app1_ shift_p_ (ref_ p) in
  up sort (fun y b _ -> match b with
      (* TODO what does app_id result in? *)
      | L.Single bsort -> if y = bsort then shift y else app_id_ underscore_
      | L.BinderList (p, bsort) -> if y = bsort then shiftp p y else app_id_ underscore_)
    (mk_refs substSorts) binder

(** Create an application of the var constructor for each element of the substitition vector
 ** of the given sort
 **
 ** e.g. [ var_ty m_ty; var_vl m_ty m_vl ] *)
let mk_var_apps sort ms =
  let* substSorts = get_substv sort in
  a_map (fun substSort ->
      let* ms' = castSubstScope sort substSort ms in
      pure (app_var_constr substSort ms'))
    substSorts

(** Convert a renaming to a substitution by postcomposing it with the variable constructor
 ** of the given sort. The domain of xis is the given ns *)
let substify sort ns xis =
  let* substSorts = get_substv sort in
  a_map2 (fun substSort xi ->
      let* ns' = castSubstScope sort substSort ns in
      pure (xi >>> app_var_constr substSort ns'))
    substSorts (sty_terms xis)

(** Compose a renaming with a substitution *)
let comp_ren_or_subst sort sty1s sty2s =
  let* substSorts = get_substv sort in
  let* ren_or_subst_ = match sty1s with
    | SubstRen _ -> pure ren_
    | SubstSubst _ -> pure subst_
    | _ -> error "comp_ren_or_subst called with wrong subst_ty" in
  a_map2 (fun substSort sty2 ->
      let* sty1s' = castSubst sort substSort sty1s in
      pure @@ (sty2 >>> app_ref (ren_or_subst_ substSort) (sty_terms sty1s')))
    substSorts (sty_terms sty2s)

(** Convenience functions that are passed to traversal which it uses when dealing with functors. *)
let map_ f ts = app_ref (sepd [f; "map"]) ts
let mapId_ f ts = app_ref (sepd [f; "id"]) ts
let mapExt_ f ts = app_ref (sepd [f; "ext"]) ts
let mapComp_ f ts = app_ref (sepd [f; "comp"]) ts

(* TODO move to tactics and make same name as in MetaCoq *)
let genMatchVar (sort: L.tId) (scope: substScope) =
  let s = varName "s" in
  (s, [binder1_ ~btype:(app_sort sort scope) s])

let rec genArg sort ms binders = function
  | L.Atom head_sort ->
    let* ms_up = castUpSubstScope sort binders head_sort ms in
    pure @@ app_sort head_sort ms_up
  | L.FunApp (fname, static_args, args) ->
    let* args' = a_map (genArg sort ms binders) args in
    pure @@ app_ref fname (static_args @ args')

let createBinders = List.map (fun p -> binder1_ ~btype:(ref_ (snd p)) (fst p))

let createImpBinders = List.map (fun p -> binder1_ ~implicit:true ~btype:(ref_ (snd p)) (fst p))
