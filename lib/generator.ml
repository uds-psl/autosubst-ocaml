open Base
open Util

module H = Hsig
module V = Variables

open Monads.RE_Functions(SigM)
open SigM.Syntax
open SigM
open CoqSyntax
open Tactics
open Custom

let guard cond lst =
  if cond then lst else []

let createBinders = List.map ~f:(fun p -> BinderNameType ([fst p],TermId (snd p)))

let createImpBinders = List.map ~f:(fun p -> BinderImplicitNameType ([fst p], TermId (snd p)))

let rec genArg sort n bs = function
  | H.Atom y -> map2 idApp (pure y) (map sty_terms (castUpSubst sort bs y n))
  | H.FunApp (f, p, xs) ->
    let* xs' = a_map (genArg sort n bs) xs in
    pure @@ idApp (funname_ (f^p)) xs'

let genVar sort n =
  let* open_x = isOpen sort in
  let* s = finT_ sort (sty_terms n) in
  let t = [s] ==> sortType sort n in
  pure @@ guard open_x [InductiveCtor (var_ sort, Some t)]

let genConstr sort n H.{ cparameters; cname; cpositions } =
    let* t =
      let* up_n_x = a_map (fun H.{ binders=bs; head=y } -> genArg sort n bs y) cpositions in
      pure @@ (up_n_x ==> sortType sort n) in
    pure @@ InductiveCtor (constructor_ cname, Some (if List.is_empty cparameters then t else TermForall (createBinders cparameters, t)))


let genBody sort =
  let* cs = constructors sort in
  let* (ns,bns) = introScopeVar "n" sort in
  let* varCons = genVar sort ns in
  let* constrs = a_map (genConstr sort ns) cs in
  pure @@ InductiveBody (sort, explicit_ bns, TermSort Type, varCons @ constrs)

let genCongruence sort H.{ cparameters; cname; cpositions } =
  let* (ms, bms) = introScopeVar "m" sort in
  let ss = getPattern "s" cpositions in
  let ts = getPattern "t" cpositions in
  let mkBinders xs = a_map2_exn (fun x H.{binders; head} ->
      let* arg_type = genArg sort ms binders head in
      pure @@ BinderImplicitNameType ([x], arg_type))
      xs cpositions in
  let* bss = mkBinders ss in
  let* bts = mkBinders ts in
  let bparameters = createImpBinders cparameters in
  let parameters' = List.(mkTermIds (map ~f:fst cparameters)) in
  let eqs = List.map2_exn ~f:(fun x y -> TermEq (TermId x, TermId y)) ss ts in
  let ss = mkTermIds ss in
  let ts = mkTermIds ts in
  let eq = TermEq (
      idApp cname (sty_terms ms @ parameters' @ ss),
      idApp cname (sty_terms ms @ parameters' @ ts)
    ) in
  let beqs = List.mapi ~f:(fun n s -> BinderNameType (["H" ^ Int.to_string n], s)) eqs in
  (* the proof term is just n-1 eq_trans and n ap's where n is the length of cpositions.
   * The pattern is that with each f_equal we swap out one s_n for one t_n
   * and the eq_trans chain all those together
   * e.g. C s0 s1 s2 = C t0 s1 s2 = C t0 t1 s2 = C t0 t1 t2
   * So this should be possible by a fold *)
  let x = VarState.tfresh "x" in
  let proof' = ProofExact (List.foldi cpositions ~init:(eq_refl_) ~f:(fun i t _ ->
      let ss' = List.take ts i @ [TermId x] @ (List.drop ss (i + 1)) in
      eqTrans_ t (f_equal_ (idAbs "x" (idApp cname (sty_terms ms @ parameters' @ ss')))
                    (TermId ("H"^Int.to_string i))
                 ))) in
  pure @@ Lemma (congr_ cname, bparameters @ bms @ bss @ bts @ beqs, eq, proof')

let genCongruences sort =
  let* ctrs = constructors sort in
  a_map (genCongruence sort) ctrs

(* TODO this function seems to be the main function that generates the proof term for all the lemmas which traverse one of our inductive types. How does it work *)
(* TODO make the var_case_body implicit with default value and also return a monadic value so that I can call toVar inside *)
let traversal sort scope name no_args ret bargs args var_case_body (sem: string list -> H.cId -> term list -> term) funsem =
  let open H in
  let s = "s" in
  let* cs = constructors sort in
  let* open_x = isOpen sort in
  (* let underscore_pattern = TermSubst (SubstScope (List.map ~f:(const TermUnderscore) (sty_terms scope))) in *)
  let underscore_pattern = List.map ~f:(const "_") (sty_terms scope) in
  (* This only create this pattern if the sort is open *)
  let var_pattern = guard open_x [Equation (var_ sort, underscore_pattern @ [s],
                                            var_case_body (TermId s))] in
  (* computes the result for a constructor *)
  let cons_pattern { cparameters; cname; cpositions; } =
    let ss = getPattern "s" cpositions in
    let rec arg_map bs arg = match arg with
      | Atom y ->
        let* b = hasArgs y in
        let* arg = a_map (castUpSubst sort bs y) args in
        pure @@ if b then idApp (name y) (List.map ~f:(fun x -> TermSubst x) arg)
        else TermAbs ([BinderName "x"], no_args (TermId "x"))
      | FunApp (f, p, xs) ->
        let* res = a_map (arg_map bs) xs in
        pure @@ (funsem f res) in
    (* TODO this can surely be simplified *)
    let* positions = a_map (fun (s, { binders; head; }) -> map2 (fun a b -> TermApp (a, b))
                               (* TODO I know ss and cpositions are the same length how do I call the other function with that knowledge? *)
                               (arg_map binders head) (pure @@ [TermId s])) (list_zip ss cpositions) in
    pure @@ Equation (cname, underscore_pattern @ (List.map ~f:fst cparameters) @ ss,
      sem (List.map ~f:fst cparameters) cname positions
    ) in
  let* cons_pat = a_map cons_pattern cs in
  let t = TermMatch (MatchItem (TermId s, None), Some (ret (TermId s)), var_pattern @ cons_pat) in
  pure @@ FixpointBody (name sort, bargs @ [BinderNameType ([s], idApp sort (sty_terms scope))], ret (TermId s), t)

(* UpRen in sort x by the binder *)
let genUpRenS (binder, sort) =
  let* v = V.genVariables sort [ `M; `N; `XI (`M, `N) ] in
  let [@warning "-8"] [ m; n; xi ], scopeBinders = v in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let n' = succ_ n sort binder in
  pure @@ Definition (upRen_ sort binder, bpms @ scopeBinders, Some (renT m' n'), up_ren_ sort xi binder)

let genRenaming sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst xis ], scopeBinders = v in
  (* DONE what is the result of toVar here?\
   * when I call it with sort=tm, xi=[xity;xivl] I get this weird error term that toVar constructs. This is then probably ignored by some similar login in the traversal. Seems brittle.
   * When I call it instead with sort=vl I get xivl. So it seems get the renaming of the sort that I'm currently inspecting *)
  let* toVarT = toVar sort xis in
  traversal sort ms ren_ id (const @@ idApp sort (sty_terms ns)) scopeBinders [xis]
    (fun s -> TermApp (varApp sort ns, [TermApp (toVarT, [s])]))
    (fun pms c s -> idApp c (sty_terms ns @ List.map ~f:(fun x -> TermId x) pms @ s))
    map_

let genRenamings sorts =
  let* fs = a_map genRenaming sorts in
  let* r = isRecursive sorts in
  pure @@ Fixpoint (r, fs)

(* TODO find a better name and place for these 2 functions *)
let zero_ x b m =
  let open H in
  match b with
  | Single y -> TermApp (varApp x m, [varZero_])
  | BinderList (p, y) -> idApp "zero_p" [TermId p] >>> varApp x m

let cons__ z b sigma m =
  let open H in
  match b with
  | Single y -> if String.(z = y) then TermApp (cons_, [zero_ z (Single y) m; sigma]) else sigma
  | BinderList (p, y) -> if String.(z = y) then idApp "scons_p" [TermId p; zero_ z (BinderList (p, y)) m; sigma] else sigma

(* TODO kathrin: change according to whether this is a renaming *)
let upSubstT b z m sigma =
  let* pat = patternSId z b in
  let* m = upSubst z [b] m in
  let* hasRen = hasRenamings z in
  let sigma' = sigma >>> idApp (if hasRen then (ren_ z) else (subst_ z)) pat in
  pure @@ cons__ z b sigma' m

let genUpS (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS) ] in
  let [@warning "-8"] [ m; TermSubst ns; sigma ], scopeBinders = v in
(* TODO what does upSubstT do here? *)
  let* sigma = upSubstT binder sort ns sigma in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let* n' = upSubst sort [binder] ns in
  pure @@ Definition (up_ sort binder, bpms @ scopeBinders, Some (substT m' n' sort), sigma)

let genSubstitution sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst sigmas ], scopeBinders = v in
  let* toVarT = toVar sort sigmas in
  traversal sort ms subst_ id (const @@ idApp sort (sty_terms ns)) scopeBinders [sigmas]
    (fun s -> TermApp (toVarT, [s]))
    (fun pms c s -> idApp c (sty_terms ns @ List.map ~f:(fun x -> TermId x) pms @ s)) map_

let genSubstitutions sorts =
  let* fs = a_map genSubstitution sorts in
  let* r = isRecursive [List.hd_exn sorts] in
  pure @@ Fixpoint (r, fs)

(* TODO move this somewhere else and also use in other definitions *)
let definitionBody sort binder (singleMatch, singleNoMatch) f_listMatch =
  match binder with
  | H.Single sort' -> if String.(sort = sort') then singleMatch else singleNoMatch
  | H.BinderList (p, sort') ->
    let (listMatch, listNoMatch) = f_listMatch p sort' in
    if String.(sort = sort') then listMatch else listNoMatch

let genUpId (binder, sort) =
  let* (ms, bms) = introScopeVar "m" sort in
  let* m_var = toVar sort ms in
  let (sigma, bsigma) = genSubstS "sigma" (m_var, ms) sort in
  let (eq, beq) = genEq "Eq" sigma (varApp sort ms) in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (up_ sort binder) (pms @ [sigma]))
      (varApp sort ms) in
  let* shift = patternSId sort binder in
  let* hasRen = hasRenamings sort in
  let t n = ap_ [ idApp (if hasRen then ren_ sort else subst_ sort) shift
                ; TermApp (eq, [n]) ] in
  let defBody = definitionBody sort binder
      (matchFin_ (TermId n) t eq_refl_, t (TermId n))
      (const2 (idApp "scons_p_eta" [varApp sort ms; idAbs n (t (TermId n)); idAbs n eq_refl_], t (TermId n))) in
  pure @@ Definition (upId_ sort binder, bpms @ bms @ bsigma @ beq, Some ret, idAbs n defBody)

let genIdLemma sort =
  let* v = V.genVariables sort [ `MS; `SIGMAS (`MS, `MS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst sigmas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* eqs' = findName1 sort substSorts ms in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) eqs'
      (fun x y s -> pure @@ idApp (upId_ x y) [TermUnderscore; s]) (* TODO kathrin, generate ID in a sensible way *) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (idApp (subst_ sort) (sty_terms sigmas @ [s]), s) in
  traversal sort ms idSubst_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [sigmas; eqs]
    (fun s -> TermApp (toVarT, [s]))
    (fun _ c cs -> idApp (congr_ c) cs)
    mapId_

let genUpExtRen (binder, sort) =
  let* v = V.genVariables sort [ `M; `N; `XI (`M, `N); `ZETA (`M, `N) ] in
  let [@warning "-8"] [ m; n; xi; zeta ], scopeBinders = v in
  let (eq, b_eq) = genEq "Eq" xi zeta in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (upRen_ sort binder) (pms @ [xi]))
      (idApp (upRen_ sort binder) (pms @ [zeta])) in
  let n = VarState.tfresh "n" in
  let t n = TermApp (eq, [n]) in
  let s = matchFin_ (TermId n) (fun n -> ap_ [shift_; t n]) eq_refl_ in
  let defBody = definitionBody sort binder
      (s, t (TermId n))
      (fun p _ -> (idApp "scons_p_congr" [
           (* TODO shouldn't I use the n variable here instead of a string literal? *)
           idAbs "n" eq_refl_;
           idAbs "n" @@ ap_ [ idApp "shift_p" [TermId p]; t (TermId "n")]
      ], t (TermId n))) in
  pure @@ Definition (upExtRen_ sort binder, bpms @ scopeBinders @ b_eq, Some ret, idAbs "n" defBody)

let genExtRen sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `ZETAS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst xis; TermSubst zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms xis) (sty_terms zetas)
      (fun x y s -> pure @@ idApp (upExtRen_ x y) [TermUnderscore; TermUnderscore; s]) in
  let ret s = TermEq (
      idApp (ren_ sort) (sty_terms xis @ [s]),
      idApp (ren_ sort) (sty_terms zetas @ [s])) in
  let* toVarT = toVar sort eqs in
  traversal sort ms extRen_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [xis; zetas; eqs]
    (fun z -> ap_ [varApp sort ns; TermApp (toVarT, [z])])
    (fun _ c cs -> idApp (congr_ c) cs)
    mapExt_

let genUpExt (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS); `TAU (`M, `NS) ] in
  let [@warning "-8"] [ m; TermSubst ns; sigma; tau ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" sigma tau in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (up_ sort binder) (pms @ [sigma]))
      (idApp (up_ sort binder) (pms @ [tau])) in
  let* shift = patternSId sort binder in
  let n = VarState.tfresh "n" in
  let* hasRen = hasRenamings sort in
  let t n = ap_ [ idApp (if hasRen then ren_ sort else subst_ sort) shift
                ; TermApp (eq, [n])] in
  let defBody = definitionBody sort binder
      (matchFin_ (TermId n) t eq_refl_, t (TermId n))
      (const2 @@ (idApp "scons_p_congr" [ idAbs "n" eq_refl_;
                                          idAbs "n" (t (TermId "n")) ],
                  t (TermId n))) in
  pure @@ Definition (upExt_ sort binder, bpms @ scopeBinders @ beq, Some ret, idAbs "n" defBody)

(* TODO this and genExtRen could be one function *)
let genExt sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS); `TAUS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst sigmas; TermSubst taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) (sty_terms taus)
      (fun x y s -> pure @@ idApp (upExt_ x y) [TermUnderscore; TermUnderscore; s]) in
  let ret s = TermEq (
      idApp (subst_ sort) (sty_terms sigmas @ [s]),
      idApp (subst_ sort) (sty_terms taus @ [s])
    ) in
  let* toVarT = toVar sort eqs in
  traversal sort ms ext_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [sigmas; taus; eqs]
    (fun z -> TermApp (toVarT, [z]))
    (fun _ c cs -> idApp (congr_ c) cs)
    mapExt_

let genUpRenRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `L; `M; `XI (`K, `L); `ZETA (`L, `M); `RHO (`K, `M) ] in
  let [@warning "-8"] [ k; l; m; xi; zeta; rho ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (xi >>> zeta) rho in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (upRen_ sort binder) (pms @ [xi])
       >>> idApp (upRen_ sort binder) (pms @ [zeta]))
      (idApp (upRen_ sort binder) (pms @ [rho])) in
  let defBody = definitionBody sort binder
      (idApp up_ren_ren__ [xi; zeta; rho; eq], eq)
      (const2 @@ (idApp "up_ren_ren_p" [eq], eq)) in
  pure @@ Definition (up_ren_ren_ sort binder, bpms @ scopeBinders @ beq, Some ret, defBody)

let genCompRenRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS;
                                 `XIS (`MS, `KS); `ZETAS (`KS, `LS); `RHOS (`MS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms
                      ; TermSubst xis; TermSubst zetas; TermSubst rhos ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2_exn ~f:(>>>) (sty_terms xis) (sty_terms zetas)) (sty_terms rhos)
      (fun x y s -> pure @@ match y with
         | H.Single z -> if String.(z = x)
           then idApp up_ren_ren__ [TermUnderscore; TermUnderscore; TermUnderscore; s]
           else s
         | H.BinderList (_, z) -> if String.(z = x)
           then idApp "up_ren_ren_p" [s]
           else s) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (
      idApp (ren_ sort) (sty_terms zetas
                         @ [ idApp (ren_ sort) @@ sty_terms xis @ [s] ]),
      idApp (ren_ sort) (sty_terms rhos @ [s])) in
  traversal sort ms compRenRen_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [xis; zetas; rhos; eqs]
    (fun n -> ap_ [varApp sort ls; TermApp (toVarT, [n])])
    (fun _ c xs -> idApp (congr_ c) xs)
    mapComp_

let genUpRenSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `L; `MS;
                                 `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; l; TermSubst ms; xi; tau; theta ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (xi >>> tau) theta in
  let n = VarState.tfresh "n" in
  (* TODO here I might understand what upSubst does *)
  let* ms = upSubst sort [binder] ms in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (upRen_ sort binder) (pms @ [xi])
       >>> idApp (up_ sort binder) (pms @ [tau]))
      (idApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let t n = ap_ [idApp (ren_ sort) shift; TermApp (eq, [n])] in
  let s = eqTrans_
      (scons_p_comp' (TermId n))
      (scons_p_congr_ (idAbs "z" (eqTrans_
                                    (scons_p_tail' (TermApp (xi, [TermId "z"])))
                                    (t (TermId "z"))))
         (idAbs "z" @@ scons_p_head' (TermId "z"))) in
  let defBody = definitionBody sort binder
      (matchFin_ (TermId n) t eq_refl_, t (TermId n))
      (const2 (s, t (TermId n))) in
  pure @@ Definition (up_ren_subst_ sort binder, bpms @ scopeBinders @ beq, Some ret, idAbs "n" defBody)

let genCompRenSubst sort =
  let* v = V.genVariables sort
      [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms;
         TermSubst xis; TermSubst taus; TermSubst thetas ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2_exn ~f:(>>>) (sty_terms xis) (sty_terms taus))
      (sty_terms thetas)
      (fun x y s -> pure @@ idApp (up_ren_subst_ x y) [TermUnderscore; TermUnderscore; TermUnderscore; s]) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (
      idApp (subst_ sort) (sty_terms taus @ [idApp (ren_ sort) (sty_terms xis @ [s])]),
      idApp (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compRenSubst_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [xis; taus; thetas; eqs]
    (fun n -> TermApp (toVarT, [n]))
    (fun _ c xs -> idApp (congr_ c) xs)
    mapComp_

let genUpSubstRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `ZETAS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; TermSubst ls; TermSubst ms;
                      sigma; TermSubst zetas; theta ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> idApp (ren_ sort) (sty_terms zetas)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* substSorts = substOf sort in
  let* zetas' = upSubst sort [binder] zetas in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (up_ sort binder) (pms @ [sigma])
       >>> idApp (ren_ sort) (sty_terms zetas'))
      (idApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  (* TODO t and t' can probably be one function. and they also appear in other functions *)
  let t n = eqTrans_
      (idApp (compRenRen_ sort) (pat @ sty_terms zetas'
                                 @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                 @ List.map ~f:(const (idAbs "x" eq_refl_)) pat
                                 @ [ TermApp (sigma, [n])]))
      (eqTrans_
         (eqSym_ (idApp (compRenRen_ sort) (sty_terms zetas @ pat
                                            @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                            @ List.map ~f:(const (idAbs "x" eq_refl_)) pat
                                            @ [ TermApp (sigma, [n])])))
         (ap_ [idApp (ren_ sort) pat; TermApp (eq, [n])])) in
  let t' n z' = eqTrans_
      (idApp (compRenRen_ sort) (pat @ sty_terms zetas'
                                 @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                 @ List.map ~f:(fun x ->
                                     (idAbs "x" (if String.(x = z')
                                                 then scons_p_tail' (TermId "x")
                                                 else eq_refl_))) substSorts
                                 @ [ TermApp (sigma, [n])]))
      (eqTrans_
         (eqSym_ (idApp (compRenRen_ sort) (sty_terms zetas @ pat
                                            @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                            @ List.map ~f:(const (idAbs "x" eq_refl_)) pat
                                            @ [ TermApp (sigma, [n])])))
         (ap_ [idApp (ren_ sort) pat; TermApp (eq, [n])])) in
  let hd = idAbs "x" (ap_ [ varApp sort ms; scons_p_head' (TermId "x") ]) in
  let defBody = definitionBody sort binder
      (matchFin_ (TermId n) t eq_refl_, t (TermId n))
      (fun _ sort' -> (eqTrans_
                         (scons_p_comp' (TermId "n"))
                         (scons_p_congr_ (idAbs "n" (t' (TermId "n") sort')) hd),
                      t' (TermId n) sort')) in
  pure @@ Definition (up_subst_ren_ sort binder, bpms @ scopeBinders @ beq, Some ret, idAbs "n" defBody)

let genCompSubstRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                               ; `ZETAS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms;
                      TermSubst sigmas; TermSubst zetas; TermSubst thetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* sigmazeta = a_map2_exn (fun substSort sigma ->
      let* zetas' = castSubst sort substSort zetas in
      pure (sigma >>> idApp (ren_ substSort) (sty_terms zetas')))
      substSorts (sty_terms sigmas) in
  let* (eqs, beqs) = genEqs sort "Eq" sigmazeta (sty_terms thetas)
      (fun z y s ->
         let* zetas' = castSubst sort z zetas in
         pure @@ idApp (up_subst_ren_ z y) ([TermUnderscore]
                                            @ List.map ~f:(const TermUnderscore) (sty_terms zetas')
                                            @ [TermUnderscore; s])) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (
      idApp (ren_ sort) (sty_terms zetas
                         @ [idApp (subst_ sort) (sty_terms sigmas @ [s])]),
      idApp (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstRen_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [sigmas; zetas; thetas; eqs]
    (fun n -> TermApp (toVarT, [n]))
    (fun _ c xs -> idApp (congr_ c) xs)
    mapComp_

let genUpSubstSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; TermSubst ls; TermSubst ms;
                      sigma; TermSubst taus; theta ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> idApp (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* ls' = upSubst sort [binder] ls in
  let* taus' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (up_ sort binder) (pms @ [sigma])
       >>> idApp (subst_ sort) (sty_terms taus'))
      (idApp (up_ sort binder) (pms @ [theta])) in
  (* TODO why is this the same as pat? *)
  let* shift = patternSId sort binder in
  let* substSorts = substOf sort in
  let* pat' = a_map2_exn (fun substSort tau ->
      let* p' = castSubst sort substSort (SubstSubst pat) in
      pure (tau >>> (idApp (ren_ substSort) (sty_terms p'))))
      substSorts (sty_terms taus) in
  let t n = eqTrans_
      (idApp (compRenSubst_ sort) (pat @ sty_terms taus'
                                   @ List.map2_exn ~f:(>>>) pat (sty_terms taus')
                                   @ List.map ~f:(const (idAbs "x" eq_refl_)) pat
                                   @ [TermApp (sigma, [n])]))
      (eqTrans_
         (eqSym_ (idApp (compSubstRen_ sort) (sty_terms taus @ pat @ pat'
                                              @ List.map ~f:(const (idAbs "x" eq_refl_)) pat
                                              @ [TermApp (sigma, [n])])))
         (ap_ [ idApp (ren_ sort) pat; TermApp (eq, [n]) ])) in
  let t' n z' = eqTrans_
      (idApp (compRenSubst_ sort) (pat @ sty_terms taus'
                                   @ List.map2_exn ~f:(>>>) pat (sty_terms taus')
                                   @ List.map ~f:(const (idAbs "x" eq_refl_)) pat
                                   @ [TermApp (sigma, [n])]))
      (eqTrans_
         (eqSym_ (idApp (compSubstRen_ sort)
                    (sty_terms taus @ pat
                     @ List.map ~f:(const TermUnderscore) pat'
                     @ List.map ~f:(fun substSort ->
                         idAbs "x" @@ eqSym_ (if String.(substSort = z')
                                              then scons_p_tail' (TermId "x")
                                              else eq_refl_)) substSorts
                     @ [TermApp (sigma, [n])])))
         (ap_ [ idApp (ren_ sort) pat; TermApp (eq, [n]) ])) in
  let hd = idAbs "x" (idApp "scons_p_head'" [ TermUnderscore
                                            ; idAbs "z" (idApp (ren_ sort)
                                                           (shift @ [TermUnderscore]))
                                            ; TermId "x" ]) in
  let defBody = definitionBody sort binder
      (matchFin_ (TermId n) t eq_refl_ , t (TermId n))
      (fun p sort' -> (eqTrans_
          (idApp "scons_p_comp'" [ idApp "zero_p" [TermId p]
                                   >>> varApp sort ls'
                                 ; TermUnderscore; TermUnderscore
                                 ; TermId "n" ])
          (scons_p_congr_ (idAbs "n" (t' (TermId "n") sort')) hd),
                       t' (TermId n) sort')) in
  pure @@ Definition (up_subst_subst_ sort binder, bpms @ scopeBinders @ beq, Some ret, idAbs "n" defBody)

let genCompSubstSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                               ; `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms;
                      TermSubst sigmas; TermSubst taus; TermSubst thetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* sigmatau = a_map2_exn (fun substSort sigma ->
      let* taus' = castSubst sort substSort taus in
      pure (sigma >>> idApp (subst_ substSort) (sty_terms taus')))
      substSorts (sty_terms sigmas) in
  let* (eqs, beqs) = genEqs sort "Eq" sigmatau (sty_terms thetas) (fun z y s ->
      let* taus' = castSubst sort z taus in
      pure @@ idApp (up_subst_subst_ z y) ([TermUnderscore]
                                           @ List.map ~f:(const TermUnderscore) (sty_terms taus')
                                           @ [TermUnderscore; s])) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (
      idApp (subst_ sort) (sty_terms taus
                           @ [idApp (subst_ sort) (sty_terms sigmas @ [s])]),
      idApp (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstSubst_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [sigmas; taus; thetas; eqs]
    (fun n -> TermApp (toVarT, [n]))
    (fun _ c xs -> idApp (congr_ c) xs)
    mapComp_

let genUpSubstSubstNoRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS); `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; TermSubst ls; TermSubst ms; sigma; TermSubst taus; theta ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> idApp (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* ls' = upSubst sort [binder] ls in
  let* zeta' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (up_ sort binder) (pms @ [sigma])
       >>> idApp (subst_ sort) (sty_terms zeta'))
      (idApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let* substSorts = substOf sort in
  let* pat' = a_map2_exn (fun tau substSort ->
      let* p' = castSubst sort substSort (SubstSubst pat) in
      pure (tau >>> (idApp (subst_ substSort) (sty_terms p'))))
      (sty_terms taus) substSorts in
  let t n = eqTrans_
      (idApp (compSubstSubst_ sort)
         (pat @ sty_terms zeta'
          @ List.map2_exn ~f:(>>>) shift (sty_terms zeta')
          @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat
          @ [ TermApp (sigma, [n])]))
      (eqTrans_
         (eqSym_ (idApp (compSubstSubst_ sort)
                    (sty_terms taus @ pat @ pat'
                     @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat
                     @ [ TermApp (sigma, [n])])))
         (ap_ [(idApp (subst_ sort) pat); TermApp (eq, [n])])) in
  let t' n z' = eqTrans_
      (idApp (compSubstSubst_ sort)
         (pat @ sty_terms zeta'
          @ List.map2_exn ~f:(>>>) shift (sty_terms zeta')
          @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat
          @ [ TermApp (sigma, [n])]))
      (eqTrans_
         (eqSym_ (idApp (compSubstSubst_ sort)
                    (sty_terms taus @ pat
                     @ List.map ~f:(const TermUnderscore) pat'
                     @ List.map ~f:(fun substSort ->
                         TermAbs ([BinderName "x"],
                                  (eqSym_ (if String.(substSort = z')
                                           then scons_p_tail' (TermId "x")
                                           else eq_refl_))))
                       substSorts
                     @ [ TermApp (sigma, [n])])))
         (ap_ [idApp (subst_ sort) pat; TermApp (eq, [n])])) in
  let hd = idAbs "x" (idApp "scons_p_head'"
                        [ TermUnderscore
                        ; TermAbs ([BinderName "z"],
                                   (idApp (subst_ sort) (pat @ [TermUnderscore])))
                        ; TermId "x"]) in
  let defBody = definitionBody sort binder
      (matchFin_ (TermId n) t eq_refl_, t (TermId n))
      (fun p z' -> (eqTrans_
         (idApp "scons_p_comp'"
            [ idApp "zero_p" [TermId p] >>> (varApp sort ls')
            ; TermUnderscore
            ; TermUnderscore
            ; TermId "n"])
         (scons_p_congr_  (idAbs "n" (t' (TermId "n") z')) hd),
                   t' (TermId n) z')) in
  pure @@ Definition (up_subst_subst_ sort binder, bpms @ scopeBinders @ beq, Some ret, idAbs "n" defBody)

let genUpRinstInst (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS ] in
  let [@warning "-8"] [ m; TermSubst ns ], scopeBinders = v in
  (* TODO because of the toVar here I cannot create the xi & sigma with the other variables. Could I add something like `N_VAR to the poly variant? *)
  let* n_var = toVar sort ns in
  let (xi, bxi) = genRenS "xi" (m, n_var) in
  let (sigma, bsigma) = genSubstS "sigma" (m, ns) sort in
  let (eq, beq) = genEq "Eq" (xi >>> varApp sort ns) sigma in
  let* ns' = upSubst sort [binder] ns in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (idApp (upRen_ sort binder) (pms @ [xi]) >>> varApp sort ns')
      (idApp (up_ sort binder) (pms @ [sigma])) in
  let* shift = patternSId sort binder in
  let t n = ap_ [idApp (ren_ sort) shift; TermApp (eq, [n])] in
  let n = VarState.tfresh "n" in
  let s = eqTrans_
      (idApp "scons_p_comp'" [TermUnderscore; TermUnderscore; varApp sort ns'; TermId n])
      (scons_p_congr_ (idAbs n (t (TermId n))) (idAbs "z" eq_refl_)) in
  let defBody = definitionBody sort binder
      (matchFin_ (TermId n) t eq_refl_, t (TermId n))
      (const2 (s, t (TermId n))) in
  pure @@ Definition (up_rinstInst_ sort binder, bpms @ scopeBinders @ bxi @ bsigma @ beq, Some ret, idAbs "n" defBody)

let genRinstInst sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst xis; TermSubst sigmas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* xis' = a_map2_exn (fun substSort xi ->
      let* n' = castSubst sort substSort ns in
      pure (xi >>> varApp substSort n'))
      substSorts (sty_terms xis) in
  let* (eqs, beqs) = genEqs sort "Eq" xis' (sty_terms sigmas)
      (fun x y s -> pure (idApp (up_rinstInst_ x y) [TermUnderscore; TermUnderscore; s])) in
  let ret s = TermEq (
      idApp (ren_ sort) (sty_terms xis @ [s]),
      idApp (subst_ sort) (sty_terms sigmas @ [s])
    ) in
  let* toVarT = toVar sort eqs in
  traversal sort ms rinstInst_ (fun s -> TermApp (eq_refl_, [s])) ret (scopeBinders @ beqs) [xis; sigmas; eqs]
    (fun n -> TermApp (toVarT, [n]))
    (fun _ c xs -> idApp (congr_ c) xs)
    mapExt_

(* TODO this is very similar to genRinstInst *)
let genLemmaRinstInst sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst xis ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* xis' = a_map2_exn (fun substSort xi ->
      let* n' = castSubst sort substSort ns in
      pure (xi >>> varApp substSort n'))
      substSorts (sty_terms xis) in
  let ret = TermEq (
      idApp (ren_ sort) (sty_terms xis),
      idApp (subst_ sort) xis'
    ) in
  let proof = TermApp (fext_, [ TermUnderscore; TermUnderscore
                              ; idAbs "x"
                                  (idApp (rinstInst_ sort)
                                     (sty_terms xis
                                      @ List.map ~f:(const TermUnderscore) substSorts
                                      @ List.map ~f:(const (idAbs "n" eq_refl_)) substSorts
                                      @ [TermId "x"])) ]) in
  pure @@ Lemma (rinstInstFun_ sort, scopeBinders, ret, ProofExact proof)

let genLemmaVarL sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst sigmas ], scopeBinders = v in
  let* sigma' = toVar sort sigmas in
  let ret = TermEq (
      varApp sort ms >>> idApp (subst_ sort) (sty_terms sigmas),
      sigma') in
  let proof = TermApp (fext_, [ TermUnderscore; TermUnderscore
                              ; idAbs "x" eq_refl_ ]) in
    pure @@ Lemma (varLFun_ sort, scopeBinders, ret, ProofExact proof)

let genLemmaVarLRen sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [ TermSubst ms; TermSubst ns; TermSubst xis ], scopeBinders = v in
  let* xi' = toVar sort xis in
  let ret = TermEq (
      varApp sort ms >>> idApp (ren_ sort) (sty_terms xis),
      xi' >>> (varApp sort ns)
    ) in
  let proof = TermApp (fext_, [ TermUnderscore; TermUnderscore
                              ; idAbs "x" eq_refl_ ]) in
  pure @@ Lemma (varLRenFun_ sort, scopeBinders, ret, ProofExact proof)

let genLemmaInstId sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* substSorts = substOf sort in
  let* vars = a_map (fun substSort ->
      map2 idApp (pure @@ var_ substSort)
        (map sty_terms (castSubst sort substSort ms)))
      substSorts in
  let ret = TermEq (idApp (subst_ sort) vars, TermConst Id) in
  let proof = TermApp (
      fext_, [ TermUnderscore; TermUnderscore
             ; idAbs "x" (idApp (idSubst_ sort)
                            (vars
                             @ (List.map ~f:(const (idAbs "n" eq_refl_)) substSorts)
                             @ [ TermApp (TermConst Id, [TermId "x"]) ])) ] ) in
  pure @@ Lemma (instIdFun_ sort, bms, ret, ProofExact proof)

let genLemmaRinstId sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* substSorts = substOf sort in
  let* vars = a_map (fun substSorts ->
      map2 idApp (pure @@ var_ substSorts)
        (map sty_terms (castSubst sort substSorts ms)))
      substSorts in
  let ret = TermEq (
      (* DONE the explicit @ here probably needs a special ast node for constr_expr.
       * TODO also why do we have the sty_terms ms here twice? *)
      TermAppExpl (ren_ sort, sty_terms ms
                              @ sty_terms ms
                              @ List.map ~f:(const (TermConst Id)) substSorts),
      TermConst Id) in
  let proof = eqTrans_
    (* TODO why do we have id_ Underscore here? *)
      (idApp (rinstInstFun_ sort) (List.map ~f:(const (id_ TermUnderscore)) substSorts))
      (TermId (instIdFun_ sort)) in
  pure @@ Lemma (rinstIdFun_ sort, bms, ret, ProofExact proof)

let genLemmaRenRenComp sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms;
                      TermSubst xis; TermSubst zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let sigmazeta = xis <<>> zetas in
  let s = VarState.tfresh "s" in
  let ret = TermEq (
      (* TODO the first sort here was an sort' (= extend_ sort) in modular code. Is that still needed without? *)
      idApp (ren_ sort) (sty_terms zetas
                         @ [ idApp (ren_ sort) (sty_terms xis
                                                @ [ TermId s ]) ]),
      idApp (ren_ sort) (sigmazeta @ [ TermId s ])) in
  let proof = idApp (compRenRen_ sort) (sty_terms xis
                                        @ sty_terms zetas
                                        @ List.map ~f:(const TermUnderscore) substSorts
                                        @ List.map ~f:(const (idAbs "n" eq_refl_)) substSorts
                                        @ [ TermId s ]) in
  let ret2 = TermEq (
      idApp (ren_ sort) (sty_terms xis) >>> idApp (ren_ sort) (sty_terms zetas),
      idApp (ren_ sort) sigmazeta) in
  let proof2 = TermApp (fext_, [ TermUnderscore; TermUnderscore
                               ; idAbs "n" (idApp (renRen_ sort)
                                              (sty_terms xis
                                               @ sty_terms zetas
                                               @ [ TermId "n" ])) ]) in
  pure [ Lemma (renRen_ sort, scopeBinders
                             @ [BinderNameType ([s], (idApp sort (sty_terms ms)))],
               ret, ProofExact proof)
       ; Lemma (renRen'_ sort, scopeBinders, ret2, ProofExact proof2) ]

let genLemmaCompRenSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms;
                      TermSubst sigmas; TermSubst zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let s = VarState.tfresh "s" in
  let* sigmazeta = a_map2_exn (fun substSort sigma ->
      let* zeta' = castSubst sort substSort zetas in
      pure @@ (sigma >>> idApp (ren_ substSort) (sty_terms zeta')))
      substSorts (sty_terms sigmas) in
  let ret = TermEq (
      idApp (ren_ sort) (sty_terms zetas
                         @ [ idApp (subst_ sort) (sty_terms sigmas
                                                  @ [ TermId s ]) ]),
      idApp (subst_ sort) (sigmazeta @ [ TermId s ])) in
  let proof = idApp (compSubstRen_ sort) (sty_terms sigmas
                                          @ sty_terms zetas
                                          @ List.map ~f:(const TermUnderscore) substSorts
                                          @ List.map ~f:(const (idAbs "n" eq_refl_)) substSorts
                                          @ [ TermId s ]) in
  let ret2 = TermEq (
      idApp (subst_ sort) (sty_terms sigmas) >>> idApp (ren_ sort) (sty_terms zetas),
      idApp (subst_ sort) sigmazeta) in
  let proof2 = TermApp (fext_, [ TermUnderscore; TermUnderscore
                               ; idAbs "n" (idApp (compRen_ sort)
                                              (sty_terms sigmas
                                               @ sty_terms zetas
                                               @ [ TermId "n" ])) ]) in
  pure [ Lemma (compRen_ sort, scopeBinders
                               @ [BinderNameType ([s], idApp sort (sty_terms ms))],
                ret, (ProofExact proof))
       ; Lemma (compRen'_ sort, scopeBinders, ret2, ProofExact proof2) ]

let genLemmaCompSubstRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms;
                      TermSubst xis; TermSubst taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let sigmazeta =  xis <<>> taus in
  let s = VarState.tfresh "s" in
  let ret = TermEq (
      idApp (subst_ sort) (sty_terms taus
                           @ [ idApp (ren_ sort) (sty_terms xis
                                                  @ [TermId s])]),
      idApp (subst_ sort) (sigmazeta @ [TermId s])) in
  let proof = idApp (compRenSubst_ sort) (sty_terms xis
                                          @ sty_terms taus
                                          @ List.map ~f:(const TermUnderscore) substSorts
                                          @ List.map ~f:(const (idAbs "n" eq_refl_)) substSorts
                                          @ [TermId s]) in
  let ret' = TermEq (
      idApp (ren_ sort) (sty_terms xis) >>> (idApp (subst_ sort) (sty_terms taus)),
      idApp (subst_ sort) sigmazeta) in
  let proof' = TermApp (fext_, [ TermUnderscore; TermUnderscore
                               ; idAbs "n" (idApp (renComp_ sort)
                                              (sty_terms xis
                                               @ sty_terms taus
                                               @ [TermId "n"]))]) in
  pure [ Lemma (renComp_ sort, scopeBinders
                              @ [BinderNameType ([s], idApp sort (sty_terms ms))],
                ret, ProofExact proof)
       ; Lemma (renComp'_ sort, scopeBinders, ret', ProofExact proof') ]

let genLemmaCompSubstSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [ TermSubst ks; TermSubst ls; TermSubst ms;
                      TermSubst sigmas; TermSubst taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let s = VarState.tfresh "s" in
  let* sigmatau = a_map2_exn (fun substSort sigma ->
                let* tau' = castSubst sort substSort taus in
                pure (sigma >>> idApp (subst_ substSort) (sty_terms tau')))
      substSorts (sty_terms sigmas) in
  let ret = TermEq (
      idApp (subst_ sort) (sty_terms taus
                           @ [ idApp (subst_ sort) (sty_terms sigmas
                                                    @ [TermId s])]),
      idApp (subst_ sort) (sigmatau @ [TermId s])) in
  let proof = idApp (compSubstSubst_ sort) (sty_terms sigmas
                                            @ sty_terms taus
                                            @ List.map ~f:(const TermUnderscore) substSorts
                                            @ List.map ~f:(const (idAbs "n" eq_refl_)) substSorts
                                            @ [TermId s]) in
  let ret' = TermEq (
      idApp (subst_ sort) (sty_terms sigmas) >>> idApp (subst_ sort) (sty_terms taus),
      idApp (subst_ sort) sigmatau) in
  let proof' = TermApp (fext_, [ TermUnderscore; TermUnderscore
                               ; idAbs "n" (idApp (compComp_ sort)
                                              (sty_terms sigmas
                                               @ sty_terms taus
                                               @ [TermId "n"]))]) in
  pure [ Lemma (compComp_ sort, scopeBinders @ [BinderNameType ([s], (idApp sort (sty_terms ms)))],
                ret, ProofExact proof)
         ; Lemma (compComp'_ sort, scopeBinders, ret', ProofExact proof') ]

let genCodeT sorts upList =
  (* TODO I suspect the dependencies can only happen with modular code *)
  let* x_open = isOpen (List.hd_exn sorts) in
  (* TODO don't we have a field for that in the signature? *)
  let* varSorts = a_filter isOpen sorts in
  let* hasbinders = map (fun l -> l |> List.is_empty |> not) (substOf (List.hd_exn sorts)) in
  (* GENERATE INDUCTIVE TYPES *)
  (* TODO which types are not definable? *)
  let* ys = a_filter definable sorts in
  let* types = a_map genBody ys in
  let* r = isRecursive sorts in
  (* GENERATE CONGRUENCE LEMMAS *)
  let* congruences = a_map genCongruences sorts in
  (* GENERATE RENAMINGS *)
  let* isRen = hasRenamings (List.hd_exn sorts) in
  let guard_map ?(invert=false) f input =
    m_guard Bool.(invert <> isRen) @@ a_map f input in
  let guard_concat_map f input =
    m_guard isRen @@ a_concat_map f input in
  let* upRen = guard_map genUpRenS upList in
  let* renamings = genRenamings sorts in
  (* GENERATE UPs *)
  let* ups = guard_map genUpS upList in
  (* TODO upsNoRen is the same as ups! I should be able to just remove it and the guard from ups *)
  let* upsNoRen = guard_map ~invert:true genUpS upList in
  (* GENERATE SUBSTITUTIONS *)
  let* substitutions = genSubstitutions sorts in
  let* upId = a_map genUpId upList in
  let* idLemmas = a_map genIdLemma sorts in
  (* GENERATE EXTENSIONALITY LEMMAS *)
  let* extUpRen = guard_map genUpExtRen upList in
  let* extRen = guard_map genExtRen sorts in
  let* extUp = a_map genUpExt upList in
  let* ext = a_map genExt sorts in
  (* GENERATE COMPOSITIONALITY LEMMAS *)
  let* upRenRen = guard_map genUpRenRen upList in
  let* compRenRen = guard_map genCompRenRen sorts in
  let* upRenSubst = guard_map genUpRenSubst upList in
  let* compRenSubst = guard_map genCompRenSubst sorts in
  let* upSubstRen = guard_map genUpSubstRen upList in
  let* compSubstRen = guard_map genCompSubstRen sorts in
  let* upSubstSubst = guard_map genUpSubstSubst upList in
  let* compSubstSubst = a_map genCompSubstSubst sorts in
  let* upSubstSubstNoRen = guard_map ~invert:true genUpSubstSubstNoRen upList in
  (* Coincidence of Instantiation *)
  let* upRinstInst = guard_map genUpRinstInst upList in
  let* rinstInst = guard_map genRinstInst sorts in
  (* Lemmas for the rewriting system *)
  let* lemmaRinstId = guard_map genLemmaRinstId sorts in
  let* lemmaInstId = a_map genLemmaInstId sorts in
  let* lemmaVarL = a_map genLemmaVarL varSorts in
  let* lemmaVarLRen = guard_map genLemmaVarLRen varSorts in
  let* lemmaRenSubst = guard_map genLemmaRinstInst sorts in
  let* lemmaSubstRenRen = guard_concat_map genLemmaRenRenComp sorts in
  let* lemmaSubstCompRen = guard_concat_map genLemmaCompRenSubst sorts in
  let* lemmaSubstRenComp = guard_concat_map genLemmaCompSubstRen sorts in
  let* lemmaSubstComp = guard_concat_map genLemmaCompSubstSubst sorts in
  (* generation of the actual sentences *)
  pure @@ [SentenceInductive (Inductive types)] @
          List.(map ~f:sentencelemma (concat congruences)) @
          (if not hasbinders then [] else
             List.map ~f:sentencedefinition upRen @
             guard isRen [SentenceFixpoint renamings] @

             List.map ~f:sentencedefinition ups @
             [SentenceFixpoint substitutions] @
             List.map ~f:sentencedefinition upsNoRen @

             List.map ~f:sentencedefinition upId @
             [SentenceFixpoint (Fixpoint (r, idLemmas))] @

             List.map ~f:sentencedefinition extUpRen @
             [SentenceFixpoint (Fixpoint (r, extRen))] @

             List.map ~f:sentencedefinition extUp @
             [SentenceFixpoint (Fixpoint (r, ext))] @

             List.map ~f:sentencedefinition upRenRen @
             [SentenceFixpoint (Fixpoint (r, compRenRen))] @

             List.map ~f:sentencedefinition upRenSubst @
             [SentenceFixpoint (Fixpoint (r, compRenSubst))] @

             List.map ~f:sentencedefinition upSubstRen @
             [SentenceFixpoint (Fixpoint (r, compSubstRen))] @

             List.map ~f:sentencedefinition upSubstSubst @
             [SentenceFixpoint (Fixpoint (r, compSubstSubst))] @
             List.map ~f:sentencedefinition upSubstSubstNoRen @

             List.map ~f:sentencedefinition upRinstInst @
             [SentenceFixpoint (Fixpoint (r, rinstInst))] @

             List.map ~f:sentencelemma (lemmaRenSubst @ lemmaInstId @ lemmaRinstId @ lemmaVarL @ lemmaVarLRen @ lemmaSubstRenRen @ lemmaSubstCompRen @ lemmaSubstRenComp @ lemmaSubstComp)
             (* TODO tbd *))
