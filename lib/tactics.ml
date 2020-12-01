open Base
open Monads.RE_Functions(SigM)
open SigM.Syntax
open SigM
open CoqSyntax
open Util
open Custom

(** Terminology:
 ** sort: a syntactic sort that is represented by an inductive type. In cbv SystemF ty, tm & vl
 ** scope variable: something of type nat that is used for scoped syntax. Sometimes named after a sort. E.g. m, n, mty, mvl
 ** scope variable vector: A SubstTy that contains multiple scope variables. E.g. sty_terms ms = [mty; mvl]
 ** renaming variable: some function that represents a renaming. E.g. xi : fin m -> fin n
 ** substitution variable: some function that represents a substitution. E.g. sigma : fin m -> vl mty mvl
 **  *)

let var sort n = idApp (var_ sort) (sty_terms n)

(** For a given sort create a renaming type
 ** fin m -> fin n *)
let renT m n = TermFunction (fin_ m, fin_ n)

(** For a given sort create a substitution type.
 ** fin m -> tm nty nvl *)
(** TODO I suspect that here we only get SubstScope variables for n *)
let substT m ns sort = TermFunction (fin_ m, sortType sort ns)

(** Create an extensional equivality between unary functions s & t
 ** forall x, s x = t x *)
let equiv_ s t =
  let x = VarState.tfresh "x" in
  TermForall ([BinderName x], TermEq (TermApp (s, [TermId x]), (TermApp (t, [TermId x]))))

(** Create a list of terms from a list of strings *)
let mkTermIds = List.map ~f:(fun x -> TermId x)

(** For a given sort and some SubstTy ts return the component of ts that has the same name as the sort.
 ** E.g. for sort vl and ts being a list of renamings [ xity; xivl ] return xivl
 ** TODO Even though this function has an error case (when the given sort does not substitute
 ** into itself, like tm in cbv system F), the returned term is not used. Probably because there
 ** is a similar kind of filtering logic as is used in this function. It would be preferable if
 ** we would then only call toVar if we really want to use it *)
let toVar sort ts =
  let* substSorts = substOf sort in
  let () = if (List.length substSorts <> List.length @@ sty_terms ts)
    then print_endline "toVar unequal"
    else () in
  let zs = List.filter ~f:(fun (substSort,_) -> String.(sort = substSort)) (list_zip substSorts (sty_terms ts)) in
  if List.is_empty zs
  then
    let () = Stdio.print_endline "toVar: list was empty. For some probably brittle reason the resulting term is never used" in
    pure @@ idApp sort [TermId "HERE in toVar."; TermId "true"; TermSubst ts]
  else List.hd_exn zs |> snd |> pure

(** Return a list of variable names for the input list of positions
 ** [s0, s2, ..., sn-1] *)
let getPattern name positions =
  List.mapi ~f:(fun i _ -> name ^ Int.to_string i) positions

(** Convert an implicit binder to an explicit one *)
let explicitS_ = function
  | BinderImplicitName s -> BinderName s
  | BinderImplicitNameType (s, t) -> BinderNameType (s, t)
  | BinderImplicitScopeNameType (s, t) -> BinderScopeNameType (s, t)
  | s -> s

(** Convert a list of binders to explicit binders *)
let explicit_ = List.map ~f:explicitS_

(** Extract the extra shifting argument from a BinderList. *)
let binvparameters = function
    | H.Single x -> ([], [])
    | H.BinderList (m, _) -> ([TermId m], [BinderImplicitNameType ([m], nat)])

let bparameters binder =
  let (terms, binders) = binvparameters binder in
  (terms, explicit_ binders)

(* TODO I don't really understand this chain of up functions yet *)
let up x f n b =
  let* xs = substOf x in
  pure @@ List.map (list_zip xs n) ~f:(fun (p, n_i) -> f p b n_i)
let ups x f = m_fold (up x f)

let upRen x bs xs = ups x (fun z b xi -> idApp (upRen_ z b) (fst (bparameters b) @ [xi])) xs bs

let upScope x bs terms = ups x (fun z b n -> succ_ n z b) terms bs

let upSubstS x bs xs = ups x (fun z b xi -> idApp (up_ z b) (fst (bparameters b) @ [xi])) xs bs

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

let introScopeVar name sort =
  let* args = substOf sort in
  let scope = List.map ~f:(fun x -> name ^ x) args in
  pure @@ (
    SubstScope (List.map ~f:(fun x -> TermId x) scope),
    [BinderImplicitScopeNameType (scope, nat)]
  )


(** This creates a scope variable together with a implicit binder
 ** Example: { m : nat } *)
let introScopeVarS name =
  let name = VarState.tfresh name in
  (TermId name, [BinderImplicitScopeNameType ([name], nat)])

(** This creates a renaming variable together with a binder
 ** Example: ( xi : fin m -> fin n ) *)
let genRenS name (m, n) =
  let name = VarState.tfresh name in
  (TermId name, [BinderNameType ([name], renT m n)])

(** Create a substitution variable for the given sort together with a binder
 ** Example: ( sigma: fin m -> tm nty nvl ) *)
let genSubstS name (m, ns) sort =
  let name = VarState.tfresh name in
  (TermId name, [BinderNameType ([name], substT m ns sort)])

(** Create multiple renaming variables and their binders. One for each substituting sort of the given sort. The given scope variables vectors ms & ns should also contain one scope variable per substituting sort.
 ** Example: for a renaming variable xi and for a sort tm with substituting sorts ty & vl, create
 ** ( xity : fin mty -> fin nty) ( xivl : fin mvl -> fin nvl ) *)
let genRen sort name (ms, ns) =
  let* substSorts = substOf sort in
  let names = List.map ~f:(fun s -> name^s) substSorts in
  let types = List.map2_exn ~f:renT (sty_terms ms) (sty_terms ns) in
  pure @@ (
    SubstRen (mkTermIds names),
    List.map2_exn ~f:(fun x t -> BinderNameType ([x], t)) names types
  )

(** Create multiple substitution variables and their binders. One for each substituting sort of the given sort. The given scope variables vectors ms & ns should also contain one scope variable per substituting sort.
 ** Example: for a substitution variable sigma and for a sort tm with substituting sorts ty & vl, create
 ** ( sigmaty : fin mty -> ty nty ) ( sigmavl : fin mvl -> vl nty nvl ) *)
let genSubst sort name (ms, ns) =
  let* substSorts = substOf sort in
  let names = List.map ~f:(fun x -> name^x) substSorts in
  (* TODO create a_map2 function *)
  let* types = a_map (fun (substSort, m) ->
      (* Here we filter the vector ns to include only the substitution sorts relevant for substSort *)
      (* TODO ask kathrin: couldn't we just do set_diff ns (substOf SubstSort)? *)
      let* ns' = castSubst sort substSort ns in
      pure @@ substT m ns' substSort)
      (list_zip substSorts (sty_terms ms)) in
  pure @@ (
    SubstSubst (mkTermIds names),
    List.map2_exn ~f:(fun x t -> BinderNameType ([x], t)) names types
  )

(** Create an extensional equality between two substitutions and its binder
 ** H: forall x, sigma x = tau x *)
let genEq name sigma tau =
  let name = VarState.tfresh name in
  ( TermId name,
    [BinderNameType ([name], (equiv_ sigma tau))] )

(** Create multiple extensional equalities between two substitutions and their binders. One for each of the substituting sorts of the given sort
 ** ( Hty : forall x, sigmaty x = tauty x ) ( Hvl : forall x, sigmavl x = tauvl x ) *)
let genEqs sort name sigmas taus f =
  let* substSorts = substOf sort in
  let names = List.map ~f:(fun x -> name^x) substSorts in
  let types = List.map2_exn ~f:(fun sigma tau -> equiv_ sigma tau) sigmas taus in
  pure @@ (
    SubstEq (mkTermIds names, f),
    List.map2_exn ~f:(fun s t -> BinderNameType ([s], t)) names types
  )

(** Create a finite type for a given sort and the corresponding element of the scope variable vector
 ** For sort vl and ns = [nty; nvl], create fin nvl *)
let finT_ sort ns = map fin_ (toVar sort (SubstScope ns))

(* TODO: What does this function do? *)
(* Construct S/Id patterns, needed for uping.
 * TODO: kathrin, Generalize the shift. Instead of Single => Up by the number of the list. *)
let patternSId x b' =
  let* xs = substOf x in
  let* hasRen = hasRenamings x in
  let shift y = if hasRen then shift_ else (shift_ >>> idApp (var_ y) (List.map ~f:(const TermUnderscore) xs)) in
  let shiftp p y = if hasRen then idApp "shift_p" [TermId p]
    else (idApp "shift_p" [TermId p]) >>> (idApp (var_ y) (List.map ~f:(const TermUnderscore) xs)) in
  up x (fun y b _ -> match b with
      | H.Single z -> if String.(y = z) then shift y else (TermConst Id)
      | H.BinderList (p, z) -> if String.(y = z) then shiftp p y else (TermConst Id))
    (List.map ~f:(fun x -> TermId x) xs) b'


let scons_p_congr_ s t = idApp "scons_p_congr" [t; s]
let scons_p_comp' x = idApp "scons_p_comp'" [TermUnderscore; TermUnderscore; TermUnderscore; x]
let scons_p_tail' x = idApp "scons_p_tail'" [TermUnderscore; TermUnderscore; x]
let scons_p_head' x = idApp "scons_p_head'" [ TermUnderscore; TermUnderscore; x]
