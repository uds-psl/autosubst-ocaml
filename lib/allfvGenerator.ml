open Util

module L = Language

open ScopeTypes
open Tactics
open CoqNames
open GallinaGen
open VernacGen
module AM = AutosubstModules
open Termutil
open RSEM.Syntax
open RSEM


let mk_abs intros body = 
  List.fold_right abs_ref intros body

(** [mk_ands ps] generates a nested junctions of the given propositions. 

    Example:
    P0 /\ P1 /\ True *)
let rec mk_ands = function
  | [] -> true_
  | p::ps -> and_ p (mk_ands ps)

(** [mk_conjs ps] generates a proof of a nested conjunction. 

    Example:
    conj p0 (conj p1 I) *)
let rec mk_conjs = function 
  | [] -> trueI_
  | p::ps -> conj_ p (mk_conjs ps)

(** Create a projection out of a nested conjunction.

    Example:
    match name with conj _ (conj name _) => name *)
let rec mk_proj n name =
  if n > 0
  then
    let inner_proj = mk_proj (n-1) name in
    match_ (ref_ name) [ branch_ "conj" ["_"; name] inner_proj ]
  else
    match_ (ref_ name) [ branch_ "conj" [name; "_"] (ref_ name) ]



let traversal_intro (* no_args should be just True? *)
    sort nameF ?(no_args=fun s -> app1_ eq_refl_ s) args intros
    var_case_body ?(sem=fun _ cname positions -> mk_conjs positions) 
    ?(positionF=fun _ _ _ _ f rest -> pure (f rest)) s =
  let open L in
  let* substSorts = get_substv sort in
  (* the underscore pattern is used when constructing the branches to ignore the scope variables. Could also construct a dummy SusbtScope instead of matching the scope_type *)
  let underscore_pattern = List.map (const "_") (match !S.scope_type with | S.Unscoped -> [] | S.Wellscoped -> substSorts) in
  let* ctors = get_constructors sort in
  let* open_x = check_open sort in
  (* Only create the variable branch if the sort is open *)
  let* var_pattern = m_guard open_x (
      (** TODO make scope state work correctly *)
      let s0 = "s0" in
      let* var_body = var_case_body (mk_refs intros) (ref_ s0) in
      (* we add the intro here *)
      pure [ branch_ (var_ sort) (underscore_pattern @ [s0]) (mk_abs intros var_body) ]
    )
  in
  (* Computes the branch for a constructor *)
  let mk_constr_pattern { cparameters; cname; cpositions; } =
    let extra_arg_list = function
      | None -> []
      | Some s -> [s] in
    let arg_map i bs extra_arg head = match head with
      | Atom head_sort ->
        (* TODO I think I can also use hasArgs in genAllfvType *)
        let* has_args = check_args head_sort in
        let* args_up = a_map (castUpSubst sort bs head_sort) args in
        if has_args
        then
          let extra_args = extra_arg_list extra_arg in
          positionF bs head_sort args extra_args
            (fun rest -> app_ref (nameF head_sort)
                (List.(concat (map sty_terms args_up))
                 @ extra_args
                 @ rest))
            (* TODO this should be user-controllable *)
            (List.map (mk_proj i) intros)
        else
          (* In the case there are no args we have to take extra care. TODO better documentation. need this because of recursion in the FunApp case. Otherwise we would have nothing to apply the no_args function to *)
          pure (match extra_arg with 
              | None -> abs_ref "x" (no_args (ref_ "x"))
              | Some s -> no_args s)
      (* TODO really ignore static args here? *)
      | FunApp (fname, _, args) ->
        error "functors not supported with allfv" 
    in
    let ss = getPattern "s" cpositions in
    (* monadic library does not have mapi so we enumerate the constructors to get an index *)
    let* positions = a_map2
        (fun s (i, { binders; head; }) ->
           arg_map i binders (Some (ref_ s)) head)
        ss (list_enumerate cpositions) in
    pure (branch_ cname
            (underscore_pattern @ List.map fst cparameters @ ss)
            (mk_abs intros (sem (List.map fst cparameters) cname positions)))
  in
  let* constr_pattern = a_map mk_constr_pattern ctors in
  let body = match_ (ref_ s) (var_pattern @ constr_pattern) in
  pure body

(** Dummy argument for definitionBody.
      TODO write custom definitionBody that errors on a BinderList instead of this. *)
let allfv_def_body_functor =
  (fun m _ -> ref_ "unimplemented", ref_ "unimplemented")

(** [gen_up_allfv (binder, sort)] generates the lifting for an allfv predicate. *)
let gen_up_allfv (binder, sort) =
  let (p, bps) = genPred "p" in
  let defBody = definitionBody sort binder
      (up_allfv_ p, p)
      allfv_def_body_functor in
  pure @@ lemma_ ~opaque:false (up_allfv_name sort binder) bps predT defBody


(** [gen_allfv sort] generates the allfv operation for the given [sort]. *)
let gen_allfv sort =
  (* arguments *)
  let* (ms, bms) = genScopeVarVect "m" sort in
  let* (ps, bps) = genPredVect "p" sort ms in
  let (s, bs) = genMatchVar sort ms in
  (* type *)
  let type_ = prop_ in
  (* body *)
  let* body = traversal_intro sort allfv_name ~no_args:(fun _ -> true_) [ps] []
      (fun _ s ->
         let* toVarT = to_var sort ps in
         pure (app1_ toVarT s))
      ~sem:(fun pms cname positions -> mk_ands positions)
      s in
  pure @@ fixpointBody_ (allfv_name sort) (bms @ bps @ bs) type_ body s


(** Generate lifting for the allfvTriv lemma. *)
let gen_up_allfv_triv (binder, sort) =
  (* arguments *)
  let (p, bps) = genPred ~implicit:true "p" in
  let (x, bxs) = introUntypedVar "x" in
  let (h, bhs) = introUntypedVar ~btype:(forall_ bxs (app1_ p (ref_ x))) "H" in
  (* type *)
  let type_ = forall_ bxs (app1_ (app_ref (up_allfv_name sort binder) [p]) (ref_ x)) in
  (* body *)
  let body = definitionBody sort binder
      (matchFin_ (ref_ x) (fun x -> app1_ (ref_ h) x) trueI_, app1_ (ref_ h) (ref_ x))
      allfv_def_body_functor in
  pure @@ lemma_ (up_allfv_triv_name sort binder) (bps @ bhs) type_ (lambda_ bxs body)

(** TODO move to tactics and document. *)
let genAllfvH name sort ps typeF f =
  let* substSorts = get_substv sort in
  let names = List.map (sep name) substSorts in
  let types = List.map typeF (sty_terms ps) in
  pure (
    SubstAllfvH (mk_refs names, f),
    List.map2 (fun n t -> binder1_ ~btype:t n) names types
  )

(** Generate the allfvTriv lemma. *)
let gen_allfv_triv sort =
  let* (ms, bms) = genScopeVarVect "m" sort in
  let* (ps, bps) = genPredVect "p" sort ms in
  let (x, bxs) = introUntypedVar "x" in
  let* (hs, bhs) = genAllfvH "H" sort ps
      (fun p -> forall_ bxs (app1_ p (ref_ x)))
      (fun substSort binder h_subst ->
         pure (app_ref (up_allfv_triv_name substSort binder) [h_subst]))
  in
  let (s, bs) = genMatchVar sort ms in
  (** type *)
  let type_ = app_ref (allfv_name sort) (sty_terms ps @ [ref_ s]) in
  (** body *)
  let* body = traversal_intro sort allfv_triv_name ~no_args:(fun _ -> trueI_) [ps; hs] []
      (fun _ s ->
         let* toVarT = to_var sort hs in
         pure (app1_ toVarT s))
      s in
  pure @@ fixpointBody_ (allfv_triv_name sort) (bps @ bhs @ bs) type_ body s

let genAllfvH2 name sort types f =
  let* substSorts = get_substv sort in
  let names = List.map (sep name) substSorts in
  pure (
    SubstAllfvH (mk_refs names, f),
    List.map2 (fun n t -> binder1_ ~btype:t n) names types
  )


let gen_up_allfv_impl (binder, sort) =
  (* arguments *)
  let (p, bps) = genPred ~implicit:true "p" in
  let (q, bqs) = genPred ~implicit:true "q" in
  let (x, bxs) = introUntypedVar "x" in
  let (h, bhs) = introUntypedVar ~btype:(forall_ bxs (arr1_ (app1_ p (ref_ x)) (app1_ q (ref_ x)))) "H" in
  (* type *)
  let type_ = forall_ bxs (arr1_ (app1_ (app_ref (up_allfv_name sort binder) [p]) (ref_ x)) 
                             (app1_ (app_ref (up_allfv_name sort binder) [q]) (ref_ x))) in
  (* body *)
  let body = definitionBody sort binder
      (matchFin_ (ref_ x) (fun x -> app1_ (ref_ h) x) (abs_ref "Hp" (ref_ "Hp")), app1_ (ref_ h) (ref_ x))
      allfv_def_body_functor in
  pure @@ lemma_ (up_allfv_impl_name sort binder) (bps @ bqs @ bhs) type_ (lambda_ bxs body)


let gen_allfv_impl sort =
  let* (ms, bms) = genScopeVarVect "m" sort in
  let* (ps, bps) = genPredVect "p" sort ms in
  let* (qs, bqs) = genPredVect "q" sort ms in
  let (x, bxs) = introUntypedVar "x" in
  let* (hs, bhs) = genAllfvH2 "H" sort
      (List.map2 (fun p q -> forall_ bxs (arr1_ (app1_ p (ref_ x)) (app1_ q (ref_ x))))
         (sty_terms ps) (sty_terms qs))
      (fun substSort binder h_subst -> 
         pure (app_ref (up_allfv_impl_name substSort binder) [h_subst]))
  in
  let (s, bs) = genMatchVar sort ms in
  (* type *)
  let type_ = arr1_ 
      (app_fix (allfv_name sort) ~scopes:[ps] [ref_ s])
      (app_fix (allfv_name sort) ~scopes:[qs] [ref_ s]) in
  (* body *)
  let* body = traversal_intro sort allfv_impl_name ~no_args:(fun _ -> trueI_) [ps; qs; hs] ["HP"]
      (fun [@warning "-8"] [h] s -> 
         let* toVarT = to_var sort hs in
         pure @@ app_ toVarT [s; h])
      s in
  pure @@ fixpointBody_ (allfv_impl_name sort) (bps @ bqs @ bhs @ bs) type_ body s


(** I was not able to properly generate the allfvAllfvImpl lemma. 
    Comment out for now. *)
(* let gen_up_allfv_allfv_impl (binder, sort) =
  (* arguments *)
  let (p, bps) = genPred ~implicit:true "p" in
  let (q, bqs) = genPred ~implicit:true "q" in
  let (x, bxs) = introUntypedVar "x" in
  (* type *)
  let type_ = forall_ bxs (arr1_ 
                             (app_ref (up_allfv_name sort binder) [
                                 abs_ref x (arr1_ (app1_ p (ref_ x)) (app1_ q (ref_ x)));
                                 ref_ x
                               ])
                             (arr1_ (app1_ (app_ref (up_allfv_name sort binder) [p]) (ref_ x)) 
                                (app1_ (app_ref (up_allfv_name sort binder) [q]) (ref_ x)))) in
  (* body *)
  let body = definitionBody sort binder
      (matchFin_ (ref_ x) 
         (fun x -> abs_ref "H" (abs_ref "H'" (app1_ (ref_ "H") (ref_ "H'")))) 
         (abs_ref "H" (abs_ref "H'" (ref_ "H'"))), 
       app1_ (ref_ "H") (ref_ x)) (* TODO app1 h x probably needs to be changed *)
      allfv_def_body_functor in
  pure @@ lemma_ (up_allfv_allfv_impl_name sort binder) (bps @ bqs) type_ (lambda_ bxs body)

let gen_allfv_allfv_impl sort = 
  let* (ms, bms) = genScopeVarVect "m" sort in
  let* (ps, bps) = genPredVect "p" sort ms in
  let* (qs, bqs) = genPredVect "q" sort ms in
  let (x, bxs) = introUntypedVar "x" in
  let* (hs, bhs) = genAllfvH2 "H" sort
      (List.map2 (fun p q -> forall_ bxs (arr1_ (app1_ p (ref_ x)) (app1_ q (ref_ x))))
         (sty_terms ps) (sty_terms qs))
      (fun substSort binder h_subst -> 
         pure (app_ref (up_allfv_allfv_impl_name substSort binder) [h_subst]))
  in
  let (s, bs) = genMatchVar sort ms in
  (* type *)
  let type_ = arr1_ 
      (app_fix (allfv_name sort) ~scopes:[ps] [ref_ s])
      (app_fix (allfv_name sort) ~scopes:[qs] [ref_ s]) in
  (* body *)
  (* TODO this is hard because the intros are special. Can I add a function? *)
  let* body = traversal_intro sort allfv_allfv_impl_name ~no_args:(fun _ -> trueI_) [ps; qs; hs] ["H"; "Hp1"]
      (fun [@warning "-8"] [_; hp1] s -> 
         let* toVarT = to_var sort hs in
         pure @@ app_ toVarT [s; hp1])
      s in
  pure @@ fixpointBody_ (allfv_impl_name sort) (bps @ bqs @ bhs @ bs) type_ body s *)


let gen_up_allfv_ren_l (binder, sort) = 
  (* arguments *)
  let (m, bms) = genScopeVar "m" in
  let (n, bms) = genScopeVar "n" in
  let (p, bps) = genPred "p" in
  let (xi, bxis) = genRen "xi" (m, n) in
  let xi_p = xi >>> p in
  let (x, bxs) = introUntypedVar "x" in
  (* type *)
  let type_ = forall_ bxs 
      (arr1_ (app_fix (up_allfv_name sort binder) [p; app_fix (upRen_ sort binder) [xi; ref_ x]])
         (app_fix (up_allfv_name sort binder) [xi_p; ref_ x])) in
  (* body *)
  let body = definitionBody sort binder
      (matchFin_ (ref_ x) 
         (fun x -> abs_ref "i" (ref_ "i")) 
         (abs_ref "H" (ref_ "H")), 
       abs_ref "H" (ref_ "H"))
      allfv_def_body_functor in
  pure @@ lemma_ (up_allfv_ren_l_name sort binder) (bps @ bxis) type_ (lambda_ bxs body)


let gen_allfv_ren_l sort =
  let* (ms, bms) = genScopeVarVect "m" sort in
  let* (ns, bns) = genScopeVarVect "n" sort in
  let* (ps, bps) = genPredVect "p" sort ns in
  let* (xis, bxis) = genRenVect "xi" sort (ms, ns) in
  let xis_ps = xis <<>> ps in (* composition of ps and xis *)
  let (s, bs) = genMatchVar sort ms in
  (* type *)
  let type_ = arr1_
      (app_fix (allfv_name sort) ~scopes:[ps] 
         [app_fix (ren_ sort) ~scopes:[xis] [ref_ s]])
      (app_fix (allfv_name sort) (List.append xis_ps [ref_ s])) in
  (* body *)
  let* body = traversal_intro sort allfv_ren_l_name ~no_args:(fun _ -> trueI_) [ps; xis] ["H"]
      (fun [@warning "-8"] [h] s -> pure h)
      ~positionF:(fun binders head_sort args s f rest -> 
          match binders with
          | [] -> pure (f rest)
          | b::_ -> (* TODO this only works for a single binder. *)
            let* substSorts = get_substv sort in
            let underscores = List.map (const underscore_) (List.concat [substSorts; substSorts]) in
            let* ups = a_map (fun (substSort, (p, xi)) -> (* TODO the correct way should be to map this over the binder list *)
                pure (app_ref (up_allfv_ren_l_name substSort b) [p; xi])
              ) List.(combine substSorts (combine (sty_terms ps) (sty_terms xis))) in
            pure (app_ref (allfv_impl_name head_sort) 
                    (List.concat [underscores; ups; s; [f rest]]))
        )
      s in
  pure @@ fixpointBody_ (allfv_ren_l_name sort) (bps @ bxis @ bs) type_ body s

let gen_up_allfv_ren_r (binder, sort) = 
  (* arguments *)
  let (m, bms) = genScopeVar "m" in
  let (n, bms) = genScopeVar "n" in
  let (p, bps) = genPred "p" in
  let (xi, bxis) = genRen "xi" (m, n) in
  let xi_p = xi >>> p in
  let (x, bxs) = introUntypedVar "x" in
  (* type *)
  let type_ = forall_ bxs 
      (arr1_ (app_fix (up_allfv_name sort binder) [xi_p; ref_ x])
         (app_fix (up_allfv_name sort binder) [p; app_fix (upRen_ sort binder) [xi; ref_ x]])) in
  (* body *)
  let body = definitionBody sort binder
      (matchFin_ (ref_ x) 
         (fun x -> abs_ref "i" (ref_ "i")) 
         (abs_ref "H" (ref_ "H")), 
       abs_ref "H" (ref_ "H"))
      allfv_def_body_functor in
  pure @@ lemma_ (up_allfv_ren_r_name sort binder) (bps @ bxis) type_ (lambda_ bxs body)

let gen_allfv_ren_r sort =
  let* (ms, bms) = genScopeVarVect "m" sort in
  let* (ns, bns) = genScopeVarVect "n" sort in
  let* (ps, bps) = genPredVect "p" sort ns in
  let* (xis, bxis) = genRenVect "xi" sort (ms, ns) in
  let xis_ps = xis <<>> ps in (* composition of ps and xis *)
  let (s, bs) = genMatchVar sort ms in
  (* type *)
  let type_ = arr1_
      (app_fix (allfv_name sort) (List.append xis_ps [ref_ s])) 
      (app_fix (allfv_name sort) ~scopes:[ps] 
         [app_fix (ren_ sort) ~scopes:[xis] [ref_ s]]) in
  (* body *)
  let* body = traversal_intro sort allfv_ren_r_name ~no_args:(fun _ -> trueI_) [ps; xis] ["H"]
      (fun [@warning "-8"] [h] s -> pure h)
      ~positionF:(fun binders head_sort args s f rest -> 
          match binders with
          | [] -> pure (f rest)
          | b::_ -> (* TODO this only works for a single binder. *)
            let* substSorts = get_substv sort in
            let underscores = List.map (const underscore_) (List.concat [substSorts; substSorts]) in
            let* ups = a_map (fun (substSort, (p, xi)) -> (* TODO the correct way should be to map this over the binder list *)
                pure (app_ref (up_allfv_ren_r_name substSort b) [p; xi])
              ) List.(combine substSorts (combine (sty_terms ps) (sty_terms xis))) in
            pure (f [app_ref (allfv_impl_name head_sort) 
                       (List.concat [underscores; ups; s; rest])])
        )
      s in
  pure @@ fixpointBody_ (allfv_ren_r_name sort) (bps @ bxis @ bs) type_ body s


let gen_ren_lemmas sorts up_list = 
  let* is_rec = check_recursive sorts in
  let mk_fixpoint = fixpoint_ ~is_rec in
  (* ren *)
  let* up_allfv_ren_l = a_map gen_up_allfv_ren_l up_list in
  let* allfv_ren_l = a_map gen_allfv_ren_l sorts in
  let* up_allfv_ren_r = a_map gen_up_allfv_ren_r up_list in
  let* allfv_ren_r = a_map gen_allfv_ren_r sorts in
  pure (up_allfv_ren_l @ [mk_fixpoint allfv_ren_l]
        @ up_allfv_ren_r @ [mk_fixpoint allfv_ren_r])

let generate component up_list =
  let* is_rec = check_recursive component in
  let mk_fixpoint = fixpoint_ ~is_rec in
  (* Code for Allfv *)
  let* up_allfv = a_map gen_up_allfv up_list in
  let* allfv = a_map gen_allfv component in
  (* trivial lemma *)
  let* up_allfv_triv = a_map gen_up_allfv_triv up_list in
  let* allfv_triv = a_map gen_allfv_triv component in
  (* implication lemmas *)
  let* up_allfv_impl = a_map gen_up_allfv_impl up_list in
  let* allfv_impl = a_map gen_allfv_impl component in
  (* let* up_allfv_allfv_impl = a_map gen_up_allfv_allfv_impl up_list in
     let* allfv_allfv_impl = a_map gen_allfv_allfv_impl sorts in *)
  (* put the code in the respective modules *)
  let* has_ren = hasRenamings (List.hd component) in
  let* ren_lemmas = if has_ren 
    then gen_ren_lemmas component up_list
    else pure [] in
  pure AM.(add_units Allfv (up_allfv @ [mk_fixpoint allfv]
                            @ up_allfv_triv @ [mk_fixpoint allfv_triv]
                            @ up_allfv_impl @ [mk_fixpoint allfv_impl]
                            (* @ up_allfv_allfv_impl @ [mk_fixpoint allfv_allfv_impl] *)
                            @ ren_lemmas
                           ))