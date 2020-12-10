open Base
open Util

module H = Hsig
module V = Variables

open REM.Functions
open REM.Syntax
open REM
open CoqSyntax
open Tactics
open CoqNames
open Coqgen
open Termutil

let guard cond lst =
  if cond then lst else []

let createBinders = List.map ~f:(fun p -> binder1_ ~btype:(ref_ (snd p)) (fst p))

let createImpBinders = List.map ~f:(fun p -> binder1_ ~implicit:true ~btype:(ref_ (snd p)) (fst p))

let rec genArg sort n bs = function
  | H.Atom y -> map2 refApp (pure y) (map sty_terms (castUpSubst sort bs y n))
  | H.FunApp (f, p, xs) ->
    let* xs' = a_map (genArg sort n bs) xs in
    pure @@ refApp (funname_ (f^p)) xs'

let genVar sort n =
  let* open_x = isOpen sort in
  let* s = finT_ sort (sty_terms n) in
  let t = [s] ==> sortType sort n in
  pure @@ guard open_x [constructor_ (var_ sort) t]

let genConstr sort n H.{ cparameters; cname; cpositions } =
    let* t =
      let* up_n_x = a_map (fun H.{ binders=bs; head=y } -> genArg sort n bs y) cpositions in
      pure @@ (up_n_x ==> sortType sort n) in
    pure @@ constructor_ cname (if List.is_empty cparameters then t else forall_ (createBinders cparameters) t)


let genBody sort =
  let* cs = constructors sort in
  let* (ns,bns) = introScopeVar "n" sort in
  let* varCons = genVar sort ns in
  let* constrs = a_map (genConstr sort ns) cs in
  pure @@ inductiveBody_ sort (explicit_ bns) ~rtype:type_ (varCons @ constrs)

let genCongruence sort H.{ cparameters; cname; cpositions } =
  let* (ms, bms) = introScopeVar "m" sort in
  let ss = getPattern "s" cpositions in
  let ts = getPattern "t" cpositions in
  let mkBinders xs = a_map2_exn (fun x H.{binders; head} ->
      let* arg_type = genArg sort ms binders head in
      pure @@ binder1_ ~implicit:true ~btype:arg_type x)
      xs cpositions in
  let* bss = mkBinders ss in
  let* bts = mkBinders ts in
  let bparameters = createImpBinders cparameters in
  let parameters' = List.(mkRefs (map ~f:fst cparameters)) in
  let eqs = List.map2_exn ~f:(fun x y -> eq_ (ref_ x) (ref_ y)) ss ts in
  let ss = mkRefs ss in
  let ts = mkRefs ts in
  let eq = eq_ (refApp cname (sty_terms ms @ parameters' @ ss))
      (refApp cname (sty_terms ms @ parameters' @ ts)) in
  let beqs = List.mapi ~f:(fun n s -> binder1_ ~btype:s ("H" ^ Int.to_string n)) eqs in
  (* the proof term is just n-1 eq_trans and n ap's where n is the length of cpositions.
   * The pattern is that with each f_equal we swap out one s_n for one t_n
   * and the eq_trans chain all those together
   * e.g. C s0 s1 s2 = C t0 s1 s2 = C t0 t1 s2 = C t0 t1 t2
   * So this should be possible by a fold *)
  let x = VarState.tfresh "x" in
  let proof' = List.foldi cpositions ~init:(eq_refl_) ~f:(fun i t _ ->
      let ss' = List.take ts i @ [ref_ x] @ (List.drop ss (i + 1)) in
      eqTrans_ t (ap_ (refAbs "x" (refApp cname (sty_terms ms @ parameters' @ ss')))
                    (ref_ ("H"^Int.to_string i)))) in
  pure @@ lemma_ (congr_ cname) (bparameters @ bms @ bss @ bts @ beqs) eq proof'

let genCongruences sort =
  let* ctrs = constructors sort in
  a_concat_map (genCongruence sort) ctrs

(* TODO this function seems to be the main function that generates the proof term for all the lemmas which traverse one of our inductive types. How does it work *)
(* TODO make the var_case_body implicit with default value and also return a monadic value so that I can call toVar inside *)
let traversal
    sort scope name ?(no_args=fun s -> app1_ eq_refl_ s) ret
    bargs args var_case_body ?(sem=fun _ c cs -> refApp (congr_ c) cs) funsem =
  let open H in
  let s = "s" in
  let* cs = constructors sort in
  let* open_x = isOpen sort in
  (* let underscore_pattern = TermSubst (SubstScope (List.map ~f:(const TermUnderscore) (sty_terms scope))) in *)
  let underscore_pattern = List.map ~f:(const "_") (sty_terms scope) in
  (* This only create this pattern if the sort is open *)
  let* var_pattern = m_guard open_x (
      let* var_body = var_case_body (ref_ s) in
      pure [ branch_ (var_ sort) (underscore_pattern @ [s]) var_body ]
    ) in
  (* computes the result for a constructor *)
  let cons_pattern { cparameters; cname; cpositions; } =
    let ss = getPattern "s" cpositions in
    let rec arg_map bs arg = match arg with
      | Atom y ->
        let* b = hasArgs y in
        let* arg = a_map (castUpSubst sort bs y) args in
        pure @@ if b then refApp (name y) (List.concat_map ~f:sty_terms arg)
        else refAbs "x" (no_args (ref_ "x"))
      | FunApp (f, p, xs) ->
        let* res = a_map (arg_map bs) xs in
        pure @@ (funsem f res) in
    (* TODO this can surely be simplified *)
    let* positions = a_map2_exn (fun s { binders; head; } -> map2 app_
                               (* TODO I know ss and cpositions are the same length how do I call the other function with that knowledge? *)
                                    (arg_map binders head) (pure @@ [ref_ s]))
        ss cpositions in
    pure @@ branch_ cname (underscore_pattern @ List.map ~f:fst cparameters @ ss)
      (sem (List.map ~f:fst cparameters) cname positions) in
  let* cons_pat = a_map cons_pattern cs in
  let t = match_ (ref_ s) (var_pattern @ cons_pat) in
  pure @@ fixpointBody_ (name sort) (bargs @ [binder1_ ~btype:(refApp sort (sty_terms scope)) s]) (ret (ref_ s)) t

(* UpRen in sort x by the binder *)
let genUpRen (binder, sort) =
  let* v = V.genVariables sort [ `M; `N; `XI (`M, `N) ] in
  let [@warning "-8"] [ m; n; xi ], [], scopeBinders = v in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let n' = succ_ n sort binder in
  let defBody = definitionBody sort binder
      (refApp "up_ren" [xi], xi)
      (fun m _ -> refApp "upRen_p" [ref_ m; xi], xi) in
  pure @@ definition_ (upRen_ sort binder) (bpms @ scopeBinders) ~rtype:(renT m' n') defBody

let genRenaming sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] _, [ ms; ns; xis ], scopeBinders = v in
  (* DONE what is the result of toVar here?\
   * when I call it with sort=tm, xi=[xity;xivl] I get this weird error term that toVar constructs. This is then probably ignored by some similar login in the traversal. Seems brittle.
   * When I call it instead with sort=vl I get xivl. So it seems get the renaming of the sort that I'm currently inspecting *)
  traversal sort ms ren_ ~no_args:id (const @@ refApp sort (sty_terms ns)) scopeBinders [xis]
    (fun s ->
       let* toVarT = toVar sort xis in
       pure @@ app1_ (varApp sort ns) (app1_ toVarT s))
    ~sem:(fun pms c s -> refApp c (sty_terms ns @ List.map ~f:(fun x -> ref_ x) pms @ s))
    map_

let genRenamings sorts =
  let* fs = a_map genRenaming sorts in
  let* is_rec = isRecursive sorts in
  pure @@ fixpoint_ ~is_rec fs

(* TODO find a better name and place for these 2 functions *)
let zero_ x b m =
  let open H in
  match b with
  | Single y -> app1_ (varApp x m) var_zero_
  | BinderList (p, y) -> refApp "zero_p" [ref_ p] >>> varApp x m

let cons__ z b sigma m =
  let open H in
  match b with
  | Single y -> if String.(z = y) then app_ cons_ [zero_ z (Single y) m; sigma] else sigma
  | BinderList (p, y) -> if String.(z = y) then refApp "scons_p" [ref_ p; zero_ z (BinderList (p, y)) m; sigma] else sigma

(* TODO kathrin: change according to whether this is a renaming *)
let upSubstT b z m sigma =
  let* pat = patternSId z b in
  let* m = upSubst z [b] m in
  let* hasRen = hasRenamings z in
  let sigma' = sigma >>> refApp (if hasRen then (ren_ z) else (subst_ z)) pat in
  pure @@ cons__ z b sigma' m

let genUpS (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS) ] in
  let [@warning "-8"] [ m; sigma ], [ ns ], scopeBinders = v in
(* TODO what does upSubstT do here? *)
  let* sigma = upSubstT binder sort ns sigma in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let* n' = upSubst sort [binder] ns in
  pure @@ definition_ (up_ sort binder) (bpms @ scopeBinders) ~rtype:(substT m' n' sort) sigma

let genSubstitution sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; sigmas ], scopeBinders = v in
  traversal sort ms subst_ ~no_args:id (const @@ refApp sort (sty_terms ns)) scopeBinders [sigmas]
    (fun s ->
       let* toVarT = toVar sort sigmas in
       pure @@ app1_ toVarT s)
    ~sem:(fun pms c s -> refApp c (sty_terms ns @ List.map ~f:(fun x -> ref_ x) pms @ s)) map_

let genSubstitutions sorts =
  let* fs = a_map genSubstitution sorts in
  let* is_rec = isRecursive [List.hd_exn sorts] in
  pure @@ fixpoint_ ~is_rec fs

let genUpId (binder, sort) =
  let* (ms, bms) = introScopeVar "m" sort in
  let* m_var = toVar sort ms in
  let (sigma, bsigma) = genSubstS "sigma" (m_var, ms) sort in
  let (eq, beq) = genEq "Eq" sigma (varApp sort ms) in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (up_ sort binder) (pms @ [sigma]))
      (varApp sort ms) in
  let* shift = patternSId sort binder in
  let* hasRen = hasRenamings sort in
  let t n = ap_
      (refApp (if hasRen then ren_ sort else subst_ sort) shift)
      (app1_ eq n) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 (refApp "scons_p_eta" [varApp sort ms; refAbs n (t (ref_ n)); refAbs n eq_refl_], t (ref_ n))) in
  pure @@ definition_ (upId_ sort binder) (bpms @ bms @ bsigma @ beq) ~rtype:ret (refAbs n defBody)

let genIdLemma sort =
  let* v = V.genVariables sort [ `MS; `SIGMAS (`MS, `MS) ] in
  let [@warning "-8"] [], [ ms; sigmas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* eqs' = findName1 sort substSorts ms in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) eqs'
      (fun x y s -> pure @@ refApp (upId_ x y) [underscore_; s]) (* TODO kathrin, generate ID in a sensible way *) in
  let ret s = eq_ (refApp (subst_ sort) (sty_terms sigmas @ [s])) s in
  traversal sort ms idSubst_ ret (scopeBinders @ beqs) [sigmas; eqs]
    (fun s ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT s)
    mapId_

let genUpExtRen (binder, sort) =
  let* v = V.genVariables sort [ `M; `N; `XI (`M, `N); `ZETA (`M, `N) ] in
  let [@warning "-8"] [ m; n; xi; zeta ], [], scopeBinders = v in
  let (eq, b_eq) = genEq "Eq" xi zeta in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (upRen_ sort binder) (pms @ [xi]))
      (refApp (upRen_ sort binder) (pms @ [zeta])) in
  let n = VarState.tfresh "n" in
  let t n = app1_ eq n in
  let s = matchFin_ (ref_ n) (fun n -> ap_ shift_ (t n)) eq_refl_ in
  let defBody = definitionBody sort binder
      (s, t (ref_ n))
      (fun p _ -> (refApp "scons_p_congr" [
           (* TODO shouldn't I use the n variable here instead of a string literal? *)
           refAbs "n" eq_refl_;
           refAbs "n" @@ ap_ (refApp "shift_p" [ref_ p]) (t (ref_ "n"))
      ], t (ref_ n))) in
  pure @@ definition_ (upExtRen_ sort binder) (bpms @ scopeBinders @ b_eq) ~rtype:ret (refAbs "n" defBody)

let genExtRen sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `ZETAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis; zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms xis) (sty_terms zetas)
      (fun x y s -> pure @@ refApp (upExtRen_ x y) [underscore_; underscore_; s]) in
  let ret s = eq_
      (refApp (ren_ sort) (sty_terms xis @ [s]))
      (refApp (ren_ sort) (sty_terms zetas @ [s])) in
  traversal sort ms extRen_ ret (scopeBinders @ beqs) [xis; zetas; eqs]
    (fun z ->
       let* toVarT = toVar sort eqs in
       pure @@ ap_ (varApp sort ns) (app1_ toVarT z))
    mapExt_

let genUpExt (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS); `TAU (`M, `NS) ] in
  let [@warning "-8"] [ m; sigma; tau ], [ ns ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" sigma tau in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (up_ sort binder) (pms @ [sigma]))
      (refApp (up_ sort binder) (pms @ [tau])) in
  let* shift = patternSId sort binder in
  let n = VarState.tfresh "n" in
  let* hasRen = hasRenamings sort in
  let t n = ap_
      (refApp (if hasRen then ren_ sort else subst_ sort) shift)
      (app1_ eq n) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 @@ (refApp "scons_p_congr" [ refAbs "n" eq_refl_
                                         ; refAbs "n" (t (ref_ "n")) ],
                  t (ref_ n))) in
  pure @@ definition_ (upExt_ sort binder) (bpms @ scopeBinders @ beq) ~rtype:ret (refAbs "n" defBody)

 let genExt sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS); `TAUS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; sigmas; taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) (sty_terms taus)
      (fun x y s -> pure @@ refApp (upExt_ x y) [underscore_; underscore_; s]) in
  let ret s = eq_
      (refApp (subst_ sort) (sty_terms sigmas @ [s]))
      (refApp (subst_ sort) (sty_terms taus @ [s])) in
  traversal sort ms ext_ ret (scopeBinders @ beqs) [sigmas; taus; eqs]
    (fun z ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT z)
    mapExt_

 let genUpRenRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `L; `M; `XI (`K, `L); `ZETA (`L, `M); `RHO (`K, `M) ] in
  let [@warning "-8"] [ k; l; m; xi; zeta; rho ], [], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (xi >>> zeta) rho in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (upRen_ sort binder) (pms @ [xi])
       >>> refApp (upRen_ sort binder) (pms @ [zeta]))
      (refApp (upRen_ sort binder) (pms @ [rho])) in
  let defBody = definitionBody sort binder
      (refApp up_ren_ren__ [xi; zeta; rho; eq], eq)
      (const2 @@ (refApp "up_ren_ren_p" [eq], eq)) in
  pure @@ definition_ (up_ren_ren_ sort binder) (bpms @ scopeBinders @ beq) ~rtype:ret defBody

 let genCompRenRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS;
                                 `XIS (`MS, `KS); `ZETAS (`KS, `LS); `RHOS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; zetas; rhos ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2_exn ~f:(>>>) (sty_terms xis) (sty_terms zetas)) (sty_terms rhos)
      (fun x y s -> pure @@ match y with
         | H.Single z -> if String.(z = x)
           then refApp up_ren_ren__ [underscore_; underscore_; underscore_; s]
           else s
         | H.BinderList (_, z) -> if String.(z = x)
           then refApp "up_ren_ren_p" [s]
           else s) in
  let ret s = eq_
      (refApp (ren_ sort) (sty_terms zetas
                           @ [ refApp (ren_ sort) @@ sty_terms xis @ [s] ]))
      (refApp (ren_ sort) (sty_terms rhos @ [s])) in
  traversal sort ms compRenRen_ ret (scopeBinders @ beqs) [xis; zetas; rhos; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ ap_ (varApp sort ls) (app1_ toVarT n))
    mapComp_

 let genUpRenSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `L; `MS;
                                 `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; l; xi; tau; theta ], [ ms ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (xi >>> tau) theta in
  let n = VarState.tfresh "n" in
  (* TODO here I might understand what upSubst does *)
  let* ms = upSubst sort [binder] ms in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (upRen_ sort binder) (pms @ [xi])
       >>> refApp (up_ sort binder) (pms @ [tau]))
      (refApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let t n = ap_ (refApp (ren_ sort) shift) (app1_ eq n) in
  let s = eqTrans_
      (scons_p_comp' (ref_ n))
      (scons_p_congr_ (refAbs "z" (eqTrans_
                                    (scons_p_tail' (app1_ xi (ref_ "z")))
                                    (t (ref_ "z"))))
         (refAbs "z" @@ scons_p_head' (ref_ "z"))) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 (s, t (ref_ n))) in
  pure @@ definition_ (up_ren_subst_ sort binder) (bpms @ scopeBinders @ beq) ~rtype:ret (refAbs "n" defBody)

 let genCompRenSubst sort =
  let* v = V.genVariables sort
      [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; taus; thetas ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2_exn ~f:(>>>) (sty_terms xis) (sty_terms taus))
      (sty_terms thetas)
      (fun x y s -> pure @@ refApp (up_ren_subst_ x y) [underscore_; underscore_; underscore_; s]) in
  let ret s = eq_
      (refApp (subst_ sort) (sty_terms taus @ [refApp (ren_ sort) (sty_terms xis @ [s])]))
      (refApp (subst_ sort) (sty_terms thetas @ [s])) in
  (* TODO make pattern for app1_ erq_refl s *)
  traversal sort ms compRenSubst_ ret (scopeBinders @ beqs) [xis; taus; thetas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapComp_

 let genUpSubstRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `ZETAS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms; zetas ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> refApp (ren_ sort) (sty_terms zetas)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* substSorts = substOf sort in
  let* zetas' = upSubst sort [binder] zetas in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (up_ sort binder) (pms @ [sigma])
       >>> refApp (ren_ sort) (sty_terms zetas'))
      (refApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  (* TODO t and t' can probably be one function. and they also appear in other functions *)
  let t n = eqTrans_
      (refApp (compRenRen_ sort) (pat @ sty_terms zetas'
                                 @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                 @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
                                 @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (refApp (compRenRen_ sort) (sty_terms zetas @ pat
                                            @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                            @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
                                            @ [ app1_ sigma n ])))
         (ap_ (refApp (ren_ sort) pat) (app1_ eq n))) in
  let t' n z' = eqTrans_
      (refApp (compRenRen_ sort) (pat @ sty_terms zetas'
                                 @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                 @ List.map ~f:(fun x ->
                                     (refAbs "x" (if String.(x = z')
                                                 then scons_p_tail' (ref_ "x")
                                                 else eq_refl_))) substSorts
                                 @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (refApp (compRenRen_ sort) (sty_terms zetas @ pat
                                            @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat
                                            @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
                                            @ [ app1_ sigma n ])))
         (ap_ (refApp (ren_ sort) pat) (app1_ eq n))) in
  let hd = refAbs "x" (ap_ (varApp sort ms) (scons_p_head' (ref_ "x"))) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (fun _ sort' -> (eqTrans_
                         (scons_p_comp' (ref_ "n"))
                         (scons_p_congr_ (refAbs "n" (t' (ref_ "n") sort')) hd),
                      t' (ref_ n) sort')) in
  pure @@ definition_ (up_subst_ren_ sort binder) (bpms @ scopeBinders @ beq) ~rtype:ret (refAbs "n" defBody)

 let genCompSubstRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                               ; `ZETAS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; zetas; thetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* sigmazeta = a_map2_exn (fun substSort sigma ->
      let* zetas' = castSubst sort substSort zetas in
      pure (sigma >>> refApp (ren_ substSort) (sty_terms zetas')))
      substSorts (sty_terms sigmas) in
  let* (eqs, beqs) = genEqs sort "Eq" sigmazeta (sty_terms thetas)
      (fun z y s ->
         let* zetas' = castSubst sort z zetas in
         pure @@ refApp (up_subst_ren_ z y) ([underscore_]
                                            @ List.map ~f:(const underscore_) (sty_terms zetas')
                                            @ [underscore_; s])) in
  let ret s = eq_
      (refApp (ren_ sort) (sty_terms zetas
                           @ [refApp (subst_ sort) (sty_terms sigmas @ [s])]))
      (refApp (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstRen_ ret (scopeBinders @ beqs) [sigmas; zetas; thetas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapComp_

let genUpSubstSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms; taus ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> refApp (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* ls' = upSubst sort [binder] ls in
  let* taus' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (up_ sort binder) (pms @ [sigma])
       >>> refApp (subst_ sort) (sty_terms taus'))
      (refApp (up_ sort binder) (pms @ [theta])) in
  (* TODO why is this the same as pat? *)
  let* shift = patternSId sort binder in
  let* substSorts = substOf sort in
  let* pat' = a_map2_exn (fun substSort tau ->
      let* p' = castSubst sort substSort (SubstSubst pat) in
      pure (tau >>> (refApp (ren_ substSort) (sty_terms p'))))
      substSorts (sty_terms taus) in
  let t n = eqTrans_
      (refApp (compRenSubst_ sort) (pat @ sty_terms taus'
                                   @ List.map2_exn ~f:(>>>) pat (sty_terms taus')
                                   @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
                                   @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (refApp (compSubstRen_ sort) (sty_terms taus @ pat @ pat'
                                              @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
                                              @ [ app1_ sigma n ])))
         (ap_ (refApp (ren_ sort) pat) (app1_ eq n))) in
  let t' n z' = eqTrans_
      (refApp (compRenSubst_ sort) (pat @ sty_terms taus'
                                   @ List.map2_exn ~f:(>>>) pat (sty_terms taus')
                                   @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
                                   @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (refApp (compSubstRen_ sort)
                    (sty_terms taus @ pat
                     @ List.map ~f:(const underscore_) pat'
                     @ List.map ~f:(fun substSort ->
                         refAbs "x" @@ eqSym_ (if String.(substSort = z')
                                              then scons_p_tail' (ref_ "x")
                                              else eq_refl_)) substSorts
                     @ [ app1_ sigma n ])))
         (ap_ (refApp (ren_ sort) pat) (app1_ eq n))) in
  let hd = refAbs "x" (refApp "scons_p_head'" [ underscore_
                                            ; refAbs "z" (refApp (ren_ sort)
                                                           (shift @ [underscore_]))
                                            ; ref_ "x" ]) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_ , t (ref_ n))
      (fun p sort' -> (eqTrans_
          (refApp "scons_p_comp'" [ refApp "zero_p" [ref_ p]
                                   >>> varApp sort ls'
                                 ; underscore_; underscore_
                                 ; ref_ "n" ])
          (scons_p_congr_ (refAbs "n" (t' (ref_ "n") sort')) hd),
                       t' (ref_ n) sort')) in
  pure @@ definition_ (up_subst_subst_ sort binder) (bpms @ scopeBinders @ beq) ~rtype:ret (refAbs "n" defBody)

 let genCompSubstSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                               ; `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; taus; thetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* sigmatau = a_map2_exn (fun substSort sigma ->
      let* taus' = castSubst sort substSort taus in
      pure (sigma >>> refApp (subst_ substSort) (sty_terms taus')))
      substSorts (sty_terms sigmas) in
  let* (eqs, beqs) = genEqs sort "Eq" sigmatau (sty_terms thetas) (fun z y s ->
      let* taus' = castSubst sort z taus in
      pure @@ refApp (up_subst_subst_ z y) ([underscore_]
                                           @ List.map ~f:(const underscore_) (sty_terms taus')
                                           @ [underscore_; s])) in
  let ret s = eq_
      (refApp (subst_ sort) (sty_terms taus
                           @ [refApp (subst_ sort) (sty_terms sigmas @ [s])]))
      (refApp (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstSubst_ ret (scopeBinders @ beqs) [sigmas; taus; thetas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapComp_

 let genUpSubstSubstNoRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS); `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms; taus ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> refApp (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* ls' = upSubst sort [binder] ls in
  let* zeta' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (up_ sort binder) (pms @ [sigma])
       >>> refApp (subst_ sort) (sty_terms zeta'))
      (refApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let* substSorts = substOf sort in
  let* pat' = a_map2_exn (fun tau substSort ->
      let* p' = castSubst sort substSort (SubstSubst pat) in
      pure (tau >>> (refApp (subst_ substSort) (sty_terms p'))))
      (sty_terms taus) substSorts in
  let t n = eqTrans_
      (refApp (compSubstSubst_ sort)
         (pat @ sty_terms zeta'
          @ List.map2_exn ~f:(>>>) shift (sty_terms zeta')
          @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
          @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (refApp (compSubstSubst_ sort)
                    (sty_terms taus @ pat @ pat'
                     @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
                     @ [ app1_ sigma n ])))
         (ap_ (refApp (subst_ sort) pat) (app1_ eq n))) in
  let t' n z' = eqTrans_
      (refApp (compSubstSubst_ sort)
         (pat @ sty_terms zeta'
          @ List.map2_exn ~f:(>>>) shift (sty_terms zeta')
          @ List.map ~f:(const (refAbs "x" eq_refl_)) pat
          @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (refApp (compSubstSubst_ sort)
                    (sty_terms taus @ pat
                     @ List.map ~f:(const underscore_) pat'
                     @ List.map ~f:(fun substSort ->
                         refAbs "x" (eqSym_ (if String.(substSort = z')
                                             then scons_p_tail' (ref_ "x")
                                             else eq_refl_)))
                       substSorts
                     @ [ app1_ sigma n ])))
         (ap_ (refApp (subst_ sort) pat) (app1_ eq n))) in
  let hd = refAbs "x" (refApp "scons_p_head'"
                        [ underscore_
                        ; refAbs "z" (refApp (subst_ sort) (pat @ [underscore_]))
                        ; ref_ "x" ]) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (fun p z' -> (eqTrans_
         (refApp "scons_p_comp'"
            [ refApp "zero_p" [ref_ p] >>> (varApp sort ls')
            ; underscore_
            ; underscore_
            ; ref_ "n" ])
         (scons_p_congr_  (refAbs "n" (t' (ref_ "n") z')) hd),
                   t' (ref_ n) z')) in
  pure @@ definition_ (up_subst_subst_ sort binder) (bpms @ scopeBinders @ beq) ~rtype:ret (refAbs "n" defBody)

 let genUpRinstInst (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS ] in
  let [@warning "-8"] [ m ], [ ns ], scopeBinders = v in
  (* TODO because of the toVar here I cannot create the xi & sigma with the other variables. Could I add something like `N_VAR to the poly variant? *)
  let* n_var = toVar sort ns in
  let (xi, bxi) = genRenS "xi" (m, n_var) in
  let (sigma, bsigma) = genSubstS "sigma" (m, ns) sort in
  let (eq, beq) = genEq "Eq" (xi >>> varApp sort ns) sigma in
  let* ns' = upSubst sort [binder] ns in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (refApp (upRen_ sort binder) (pms @ [xi]) >>> varApp sort ns')
      (refApp (up_ sort binder) (pms @ [sigma])) in
  let* shift = patternSId sort binder in
  let t n = ap_ (refApp (ren_ sort) shift) (app1_ eq n) in
  let n = VarState.tfresh "n" in
  let s = eqTrans_
      (refApp "scons_p_comp'" [underscore_; underscore_; varApp sort ns'; ref_ n])
      (scons_p_congr_ (refAbs n (t (ref_ n))) (refAbs "z" eq_refl_)) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 (s, t (ref_ n))) in
  pure @@ definition_ (up_rinstInst_ sort binder) (bpms @ scopeBinders @ bxi @ bsigma @ beq)
    ~rtype:ret (refAbs "n" defBody)

 let genRinstInst sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis; sigmas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* xis' = a_map2_exn (fun substSort xi ->
      let* n' = castSubst sort substSort ns in
      pure (xi >>> varApp substSort n'))
      substSorts (sty_terms xis) in
  let* (eqs, beqs) = genEqs sort "Eq" xis' (sty_terms sigmas)
      (fun x y s -> pure (refApp (up_rinstInst_ x y) [underscore_; underscore_; s])) in
  let ret s = eq_
      (refApp (ren_ sort) (sty_terms xis @ [s]))
      (refApp (subst_ sort) (sty_terms sigmas @ [s])) in
  traversal sort ms rinstInst_ ret (scopeBinders @ beqs) [xis; sigmas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapExt_

(* TODO this is very similar to genRinstInst *)
 let genLemmaRinstInst sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* xis' = a_map2_exn (fun substSort xi ->
      let* n' = castSubst sort substSort ns in
      pure (xi >>> varApp substSort n'))
      substSorts (sty_terms xis) in
  let ret = eq_
      (refApp (ren_ sort) (sty_terms xis))
      (refApp (subst_ sort) xis') in
  let proof = fext_ (refAbs "x"
                       (refApp (rinstInst_ sort)
                          (sty_terms xis
                           @ List.map ~f:(const underscore_) substSorts
                           @ List.map ~f:(const (refAbs "n" eq_refl_)) substSorts
                           @ [ ref_ "x" ]))) in
  pure @@ lemma_ (rinstInstFun_ sort) scopeBinders ret proof

 let genLemmaVarL sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; sigmas ], scopeBinders = v in
  let* sigma' = toVar sort sigmas in
  let ret = eq_ (varApp sort ms >>> refApp (subst_ sort) (sty_terms sigmas)) sigma' in
  let proof = fext_ (refAbs "x" eq_refl_) in
    pure @@ lemma_ (varLFun_ sort) scopeBinders ret proof

 let genLemmaVarLRen sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis ], scopeBinders = v in
  let* xi' = toVar sort xis in
  let ret = eq_
      (varApp sort ms >>> refApp (ren_ sort) (sty_terms xis))
      (xi' >>> (varApp sort ns)) in
  let proof = fext_ (refAbs "x" eq_refl_) in
  pure @@ lemma_ (varLRenFun_ sort) scopeBinders ret proof

let genLemmaInstId sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* substSorts = substOf sort in
  let* vars = a_map (fun substSort ->
      map2 refApp (pure @@ var_ substSort)
        (map sty_terms (castSubst sort substSort ms)))
      substSorts in
  let ret = eq_ (refApp (subst_ sort) vars) id_ in
  let proof = fext_ (refAbs "x"
                       (refApp (idSubst_ sort)
                          (vars
                           @ List.map ~f:(const (refAbs "n" eq_refl_)) substSorts
                           @ [ idApp_ (ref_ "x") ]))) in
  pure @@ lemma_ (instIdFun_ sort) bms ret proof

let genLemmaRinstId sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* substSorts = substOf sort in
  let* vars = a_map (fun substSorts ->
      map2 refApp (pure @@ var_ substSorts)
        (map sty_terms (castSubst sort substSorts ms)))
      substSorts in
  let ret = eq_ (* TODO also why do we have the sty_terms ms here twice? *)
      (appExpl_ (ren_ sort) (sty_terms ms
                            @ sty_terms ms
                            @ List.map ~f:(const id_) substSorts))
      id_ in
  let proof = eqTrans_
    (* TODO why do we have id_ Underscore here? *)
      (refApp (rinstInstFun_ sort) (List.map ~f:(const (idApp_ underscore_)) substSorts))
      (ref_ (instIdFun_ sort)) in
  pure @@ lemma_ (rinstIdFun_ sort) bms ret proof

 let genLemmaRenRenComp sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let sigmazeta = xis <<>> zetas in
  let s = VarState.tfresh "s" in
  let ret = eq_ (* TODO the first sort here was an sort' (= extend_ sort) in modular code. Is that still needed without? *)
      (refApp (ren_ sort) (sty_terms zetas
                           @ [ refApp (ren_ sort) (sty_terms xis
                                                   @ [ ref_ s ]) ]))
      (refApp (ren_ sort) (sigmazeta @ [ ref_ s ])) in
  let proof = refApp (compRenRen_ sort) (sty_terms xis
                                        @ sty_terms zetas
                                        @ List.map ~f:(const underscore_) substSorts
                                        @ List.map ~f:(const (refAbs "n" eq_refl_)) substSorts
                                        @ [ ref_ s ]) in
  let ret' = eq_
      (refApp (ren_ sort) (sty_terms xis) >>> refApp (ren_ sort) (sty_terms zetas))
      (refApp (ren_ sort) sigmazeta) in
  let proof' = fext_ (refAbs "n"
                        (refApp (renRen_ sort)
                           (sty_terms xis
                            @ sty_terms zetas
                            @ [ ref_ "n" ]))) in
  pure [ lemma_ (renRen_ sort) (scopeBinders
                                @ [ binder1_ ~btype:(refApp sort (sty_terms ms)) s ])
           ret proof
       ; lemma_ (renRen'_ sort) scopeBinders ret' proof' ]

let genLemmaCompRenSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let s = VarState.tfresh "s" in
  let* sigmazeta = a_map2_exn (fun substSort sigma ->
      let* zeta' = castSubst sort substSort zetas in
      pure @@ (sigma >>> refApp (ren_ substSort) (sty_terms zeta')))
      substSorts (sty_terms sigmas) in
  let ret = eq_
      (refApp (ren_ sort) (sty_terms zetas
                           @ [ refApp (subst_ sort) (sty_terms sigmas
                                                     @ [ ref_ s ]) ]))
      (refApp (subst_ sort) (sigmazeta @ [ ref_ s ])) in
  let proof = refApp (compSubstRen_ sort) (sty_terms sigmas
                                          @ sty_terms zetas
                                          @ List.map ~f:(const underscore_) substSorts
                                          @ List.map ~f:(const (refAbs "n" eq_refl_)) substSorts
                                          @ [ ref_ s ]) in
  let ret' = eq_
      (refApp (subst_ sort) (sty_terms sigmas) >>> refApp (ren_ sort) (sty_terms zetas))
      (refApp (subst_ sort) sigmazeta) in
  let proof' = fext_ (refAbs "n"
                        (refApp (compRen_ sort)
                           (sty_terms sigmas
                            @ sty_terms zetas
                            @ [ ref_ "n" ]))) in
  pure [ lemma_ (compRen_ sort) (scopeBinders
                                 @ [ binder1_ ~btype:(refApp sort (sty_terms ms)) s ])
                ret proof
       ; lemma_ (compRen'_ sort) scopeBinders ret' proof' ]

 let genLemmaCompSubstRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let sigmazeta =  xis <<>> taus in
  let s = VarState.tfresh "s" in
  let ret = eq_
      (refApp (subst_ sort) (sty_terms taus
                             @ [ refApp (ren_ sort) (sty_terms xis
                                                     @ [ref_ s])]))
      (refApp (subst_ sort) (sigmazeta @ [ref_ s])) in
  let proof = refApp (compRenSubst_ sort) (sty_terms xis
                                          @ sty_terms taus
                                          @ List.map ~f:(const underscore_) substSorts
                                          @ List.map ~f:(const (refAbs "n" eq_refl_)) substSorts
                                          @ [ref_ s]) in
  let ret' = eq_
      (refApp (ren_ sort) (sty_terms xis) >>> (refApp (subst_ sort) (sty_terms taus)))
      (refApp (subst_ sort) sigmazeta) in
  let proof' = fext_ (refAbs "n"
                        (refApp (renComp_ sort)
                           (sty_terms xis
                            @ sty_terms taus
                            @ [ref_ "n"]))) in
  pure [ lemma_ (renComp_ sort) (scopeBinders
                                 @ [ binder1_ ~btype:(refApp sort (sty_terms ms)) s ])
                ret proof
       ; lemma_ (renComp'_ sort) scopeBinders ret' proof' ]

let genLemmaCompSubstSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let s = VarState.tfresh "s" in
  let* sigmatau = a_map2_exn (fun substSort sigma ->
                let* tau' = castSubst sort substSort taus in
                pure (sigma >>> refApp (subst_ substSort) (sty_terms tau')))
      substSorts (sty_terms sigmas) in
  let ret = eq_
      (refApp (subst_ sort) (sty_terms taus
                              @ [ refApp (subst_ sort) (sty_terms sigmas
                                                        @ [ref_ s])]))
      (refApp (subst_ sort) (sigmatau @ [ref_ s])) in
  let proof = refApp (compSubstSubst_ sort) (sty_terms sigmas
                                            @ sty_terms taus
                                            @ List.map ~f:(const underscore_) substSorts
                                            @ List.map ~f:(const (refAbs "n" eq_refl_)) substSorts
                                            @ [ref_ s]) in
  let ret' = eq_
      (refApp (subst_ sort) (sty_terms sigmas) >>> refApp (subst_ sort) (sty_terms taus))
      (refApp (subst_ sort) sigmatau) in
  let proof' = fext_ (refAbs "n"
                        (refApp (compComp_ sort)
                           (sty_terms sigmas
                            @ sty_terms taus
                            @ [ref_ "n"]))) in
  pure [ lemma_ (compComp_ sort) (scopeBinders
                                  @ [ binder1_ ~btype:(refApp sort (sty_terms ms)) s ])
                ret proof
         ; lemma_ (compComp'_ sort) scopeBinders ret' proof' ]

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
  let* is_rec = isRecursive sorts in
  (* GENERATE CONGRUENCE LEMMAS *)
  let* congruences = a_map genCongruences sorts in
  (* GENERATE RENAMINGS *)
  let* isRen = hasRenamings (List.hd_exn sorts) in
  let guard_map ?(invert=false) f input =
    m_guard Bool.(invert <> isRen) @@ a_map f input in
  let guard_concat_map f input =
    m_guard isRen @@ a_concat_map f input in
  let* upRen = guard_map genUpRen upList in
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
  pure @@ [inductive_ types] @
           (List.concat congruences) @
          (if not hasbinders then [] else
             upRen @ guard isRen [renamings] @
             ups @ [substitutions] @ upsNoRen @
             upId @ [fixpoint_ ~is_rec idLemmas] @
             extUpRen @ [fixpoint_ ~is_rec extRen] @
             extUp @ [fixpoint_ ~is_rec ext] @
             upRenRen @ [fixpoint_ ~is_rec compRenRen] @
             upRenSubst @ [fixpoint_ ~is_rec compRenSubst] @
             upSubstRen @ [fixpoint_ ~is_rec compSubstRen] @
             upSubstSubst @ [fixpoint_ ~is_rec compSubstSubst] @ upSubstSubstNoRen @
             upRinstInst @ [fixpoint_ ~is_rec rinstInst] @
             List.concat (lemmaRenSubst @ lemmaInstId @ lemmaRinstId @ lemmaVarL @ lemmaVarLRen @ lemmaSubstRenRen @ lemmaSubstCompRen @ lemmaSubstRenComp @ lemmaSubstComp)
          )
