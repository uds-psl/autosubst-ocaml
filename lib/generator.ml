(** Most of the genX functions in this module follow the same pattern.
 **  - declare some scope/renaming/substitution variables and their binders
 **  - build the type of the statement
 **  - build the proof term of the statement
 **
 ** Fixpoints call traversal which generates the match on the principal argument.
 ** Definitions and Lemmas directly call the smart constructor with the type, binders and proof.
 ** *)
open Util

module H = Hsig
module V = Variables

open REM.Syntax
open REM
open CoqSyntax
open Tactics
open CoqNames
open Coqgen
open Termutil

let guard cond lst =
  if cond then lst else []

let createBinders = List.map (fun p -> binder1_ ~btype:(ref_ (snd p)) (fst p))

let createImpBinders = List.map (fun p -> binder1_ ~implicit:true ~btype:(ref_ (snd p)) (fst p))

let rec genArg sort n bs = function
  | H.Atom y ->
    let* up_scopes = castUpSubst sort bs y n in
    pure @@ app_ref y (List.(concat (map sty_terms (filter_scope_vars [up_scopes]))))
  | H.FunApp (f, p, xs) ->
    let* xs' = a_map (genArg sort n bs) xs in
    let p' = Option.default [] (Option.map (fun x -> [x]) p) in
    pure @@ app_ref (funname_ f) (p' @ xs')


let genVar sort ns =
  let* is_open = isOpen sort in
  if not is_open then pure []
  else
    let* s = gen_var_arg sort ns in
    let t = [s] ==> sortType sort ns in
    pure @@ [constructor_ (var_ sort) t]

let genConstr sort n H.{ cparameters; cname; cpositions } =
    let* t =
      let* up_n_x = a_map (fun H.{ binders; head } -> genArg sort n binders head) cpositions in
      pure @@ (up_n_x ==> sortType sort n) in
    pure @@ constructor_ cname (if list_empty cparameters then t else forall_ (createBinders cparameters) t)


let genBody sort =
  let* cs = constructors sort in
  let* (ns, bns) = introScopeVar "n" sort in
  let* varCons = genVar sort ns in
  let* constrs = a_map (genConstr sort ns) cs in
  pure @@ inductiveBody_ sort (explicit_ bns) ~rtype:type_ (varCons @ constrs)

(** the proof term is just n-1 eq_trans and n ap's where n is the length of cpositions.
 ** The pattern is that with each f_equal we swap out one s_n for one t_n
 ** and the eq_trans chain all those together
 ** e.g. C s0 s1 s2 = C t0 s1 s2 = C t0 t1 s2 = C t0 t1 t2 *)
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
  let parameters' = List.(mk_refs (map fst cparameters)) in
  let eqs = List.map2 (fun x y -> eq_ (ref_ x) (ref_ y)) ss ts in
  let ss = mk_refs ss in
  let ts = mk_refs ts in
  let eq = eq_
      (app_constr cname ms (parameters' @ ss))
      (app_constr cname ms (parameters' @ ts)) in
  let beqs = List.mapi (fun n s -> binder1_ ~btype:s ("H" ^ string_of_int n)) eqs in
  let x = VarState.tfresh "x" in
  let (_, proof') = List.fold_left (fun (i, t) _ ->
      let ss' = list_take ts i @ [ref_ x] @ (list_drop ss (i + 1)) in
      let t' = eqTrans_ t (ap_ (abs_ref "x" (app_constr cname ms (parameters' @ ss')))
                             (ref_ ("H"^string_of_int i))) in
      (i + 1, t'))
      (0, eq_refl_) cpositions in
  pure @@ lemma_ (congr_ cname) (bparameters @ bms @ bss @ bts @ beqs) eq proof'

let genCongruences sort =
  let* ctrs = constructors sort in
  a_concat_map (genCongruence sort) ctrs

let traversal
    sort scope name ?(no_args=fun s -> app1_ eq_refl_ s) ~ret
    bargs args var_case_body ?(sem=fun _ cname positions -> app_fix (congr_ cname) positions) funsem =
  let open H in
  let s = "s" in
  let* cs = constructors sort in
  let* open_x = isOpen sort in
  let underscore_pattern = mk_underscore_pattern scope in
  (* This only create this pattern if the sort is open *)
  let* var_pattern = m_guard open_x (
      (** TODO make scope state work correctly *)
      let s0 = "s0" in
      let* var_body = var_case_body (ref_ s0) in
      pure [ branch_ (var_ sort) (underscore_pattern @ [s0]) var_body ]
    ) in
  (* computes the result for a constructor *)
  let mk_constr_pattern { cparameters; cname; cpositions; } =
    let ss = getPattern "s" cpositions in
    let rec arg_map bs arg = match arg with
      | Atom y ->
        let* b = hasArgs y in
        let* arg = a_map (castUpSubst sort bs y) args in
        pure @@ if b then app_ref (name y) (List.(concat (map sty_terms arg)))
        else abs_ref "x" (no_args (ref_ "x"))
      | FunApp (f, p, xs) ->
        let* res = a_map (arg_map bs) xs in
        pure @@ (funsem f res) in
    let* positions = a_map2_exn (fun s { binders; head; } -> map2 app_
                                    (arg_map binders head) (pure @@ [ref_ s]))
        ss cpositions in
    pure @@ branch_ cname (underscore_pattern @ List.map fst cparameters @ ss)
      (sem (List.map fst cparameters) cname positions) in
  let* constr_pattern = a_map mk_constr_pattern cs in
  let t = match_ (ref_ s) (var_pattern @ constr_pattern) in
  pure @@ fixpointBody_ (name sort) (bargs @ [binder1_ ~btype:(app_sort sort scope) s]) (ret (ref_ s)) t

(* UpRen in sort x by the binder *)
let genUpRen (binder, sort) =
  let* v = V.genVariables sort [ `M; `N; `XI (`M, `N) ] in
  let [@warning "-8"] [ m; n; xi ], [], scopeBinders = v in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let n' = succ_ n sort binder in
  let defBody = definitionBody sort binder
      (app_ref "up_ren" [xi], xi)
      (fun m _ -> app_ref "upRen_p" [ref_ m; xi], xi) in
  pure @@ lemma_ ~opaque:false (upRen_ sort binder) (bpms @ scopeBinders) (renT m' n') defBody

let genRenaming sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] _, [ ms; ns; xis ], scopeBinders = v in
  (* DONE what is the result of toVar here?\
   * when I call it with sort=tm, xi=[xity;xivl] I get this weird error term that toVar constructs. This is then probably ignored by some similar login in the traversal. Seems brittle.
   * When I call it instead with sort=vl I get xivl. So it seems get the renaming of the sort that I'm currently inspecting *)
  let ret _ = app_sort sort ns in
  traversal sort ms ren_ ~no_args:id ~ret scopeBinders [xis]
    (fun s ->
       let* toVarT = toVar sort xis in
       pure @@ app1_ (app_var_constr sort ns) (app1_ toVarT s))
    ~sem:(fun pms cname positions -> app_constr cname ns (mk_refs pms @ positions))
    map_

let genRenamings sorts =
  let* fs = a_map genRenaming sorts in
  let* is_rec = isRecursive sorts in
  pure @@ fixpoint_ ~is_rec fs

let zero_ sort binder ms =
  let open H in
  match binder with
  | Single y -> app1_ (app_var_constr sort ms) var_zero_
  | BinderList (p, y) -> app_ref "zero_p" [ref_ p] >>> app_var_constr sort ms

let mk_scons sort binder sigma ms =
  let open H in
  match binder with
  | Single y -> if sort = y then app_ cons_ [zero_ sort (Single y) ms; sigma] else sigma
  | BinderList (p, y) -> if sort = y then app_ref "scons_p" [ref_ p; zero_ sort (BinderList (p, y)) ms; sigma] else sigma

let upSubstT binder sort ms sigma =
  let* pat = patternSId sort binder in
  let* ms' = upSubst sort [binder] ms in
  let* hasRen = hasRenamings sort in
  let sigma' = sigma >>> app_fix (if hasRen then (ren_ sort) else (subst_ sort)) pat in
  pure @@ mk_scons sort binder sigma' ms'

let genUpS (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS) ] in
  let [@warning "-8"] [ m; sigma ], [ ns ], scopeBinders = v in
(* TODO what does upSubstT do here? *)
  let* sigma = upSubstT binder sort ns sigma in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let* n' = upSubst sort [binder] ns in
  pure @@ lemma_ ~opaque:false (up_ sort binder) (bpms @ scopeBinders) (substT m' n' sort) sigma

let genSubstitution sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; sigmas ], scopeBinders = v in
  let ret _ = app_sort sort ns in
  traversal sort ms subst_ ~no_args:id ~ret scopeBinders [sigmas]
    (fun s ->
       let* toVarT = toVar sort sigmas in
       pure @@ app1_ toVarT s)
    ~sem:(fun pms cname positions -> app_constr cname ns (mk_refs pms @ positions))
    map_

let genSubstitutions sorts =
  let* fs = a_map genSubstitution sorts in
  let* is_rec = isRecursive [List.hd sorts] in
  pure @@ fixpoint_ ~is_rec fs

let genUpId (binder, sort) =
  let* (ms, bms) = introScopeVar "m" sort in
  let* m_var = toVar sort ms in
  let (sigma, bsigma) = genSubstS "sigma" (m_var, ms) sort in
  let (eq, beq) = genEq "Eq" sigma (app_var_constr sort ms) in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (up_ sort binder) (pms @ [sigma]))
      (app_var_constr sort ms) in
  let* shift = patternSId sort binder in
  let* hasRen = hasRenamings sort in
  let t n = ap_
      (app_ref (if hasRen then ren_ sort else subst_ sort) shift)
      (app1_ eq n) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 (app_ref "scons_p_eta" [app_var_constr sort ms; abs_ref n (t (ref_ n)); abs_ref n eq_refl_], t (ref_ n))) in
  pure @@ lemma_ (upId_ sort binder) (bpms @ bms @ bsigma @ beq) ret (abs_ref n defBody)

let genIdLemma sort =
  let* v = V.genVariables sort [ `MS; `SIGMAS (`MS, `MS) ] in
  let [@warning "-8"] [], [ ms; sigmas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* eqs' = mk_var_apps sort ms in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) eqs'
      (fun x y s -> pure @@ app_ref (upId_ x y) [underscore_; s]) in
  let ret s = eq_ (app_fix (subst_ sort) ~scopes:[sigmas] [s]) s in
  traversal sort ms idSubst_ ~ret (scopeBinders @ beqs) [sigmas; eqs]
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
      (app_ref (upRen_ sort binder) (pms @ [xi]))
      (app_ref (upRen_ sort binder) (pms @ [zeta])) in
  let n = VarState.tfresh "n" in
  let t n = app1_ eq n in
  let s = matchFin_ (ref_ n) (fun n -> ap_ shift_ (t n)) eq_refl_ in
  let defBody = definitionBody sort binder
      (s, t (ref_ n))
      (fun p _ -> (app_ref "scons_p_congr" [
           abs_ref "n" eq_refl_;
           abs_ref "n" @@ ap_ (app_ref "shift_p" [ref_ p]) (t (ref_ "n"))
      ], t (ref_ n))) in
  pure @@ lemma_ (upExtRen_ sort binder) (bpms @ scopeBinders @ b_eq) ret (abs_ref "n" defBody)

let genExtRen sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `ZETAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis; zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms xis) (sty_terms zetas)
      (fun x y s -> pure @@ app_ref (upExtRen_ x y) [underscore_; underscore_; s]) in
  let ret s = eq_
      (app_fix (ren_ sort) ~scopes:[xis] [s])
      (app_fix (ren_ sort) ~scopes:[zetas] [s]) in
  traversal sort ms extRen_ ~ret (scopeBinders @ beqs) [xis; zetas; eqs]
    (fun z ->
       let* toVarT = toVar sort eqs in
       pure @@ ap_ (app_var_constr sort ns) (app1_ toVarT z))
    mapExt_

let genUpExt (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS); `TAU (`M, `NS) ] in
  let [@warning "-8"] [ m; sigma; tau ], [ ns ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" sigma tau in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (up_ sort binder) (pms @ [sigma]))
      (app_ref (up_ sort binder) (pms @ [tau])) in
  let* shift = patternSId sort binder in
  let n = VarState.tfresh "n" in
  let* hasRen = hasRenamings sort in
  let t n = ap_
      (app_ref (if hasRen then ren_ sort else subst_ sort) shift)
      (app1_ eq n) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 @@ (app_ref "scons_p_congr" [ abs_ref "n" eq_refl_
                                         ; abs_ref "n" (t (ref_ "n")) ],
                  t (ref_ n))) in
  pure @@ lemma_ (upExt_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)

 let genExt sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS); `TAUS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; sigmas; taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) (sty_terms taus)
      (fun x y s -> pure @@ app_ref (upExt_ x y) [underscore_; underscore_; s]) in
  let ret s = eq_
      (app_fix (subst_ sort) ~scopes:[sigmas] [s])
      (app_fix (subst_ sort) ~scopes:[taus] [s]) in
  traversal sort ms ext_ ~ret (scopeBinders @ beqs) [sigmas; taus; eqs]
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
      (app_ref (upRen_ sort binder) (pms @ [xi])
       >>> app_ref (upRen_ sort binder) (pms @ [zeta]))
      (app_ref (upRen_ sort binder) (pms @ [rho])) in
  let defBody = definitionBody sort binder
      (app_ref up_ren_ren__ [xi; zeta; rho; eq], eq)
      (const2 @@ (app_ref "up_ren_ren_p" [eq], eq)) in
  pure @@ lemma_ (up_ren_ren_ sort binder) (bpms @ scopeBinders @ beq) ret defBody

 let genCompRenRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS;
                                 `XIS (`MS, `KS); `ZETAS (`KS, `LS); `RHOS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; zetas; rhos ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2 (>>>) (sty_terms xis) (sty_terms zetas)) (sty_terms rhos)
      (fun x y s -> pure @@ match y with
         | H.Single z -> if z = x
           then app_ref up_ren_ren__ [underscore_; underscore_; underscore_; s]
           else s
         | H.BinderList (_, z) -> if z = x
           then app_ref "up_ren_ren_p" [s]
           else s) in
  let ret s = eq_
      (app_fix (ren_ sort) (sty_terms zetas
                           @ [ app_ref (ren_ sort) @@ sty_terms xis @ [s] ]))
      (app_ref (ren_ sort) (sty_terms rhos @ [s])) in
  traversal sort ms compRenRen_ ~ret (scopeBinders @ beqs) [xis; zetas; rhos; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ ap_ (app_var_constr sort ls) (app1_ toVarT n))
    mapComp_

 let genUpRenSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `L; `MS;
                                 `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; l; xi; tau; theta ], [ ms ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (xi >>> tau) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (upRen_ sort binder) (pms @ [xi])
       >>> app_ref (up_ sort binder) (pms @ [tau]))
      (app_ref (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let t n = ap_ (app_ref (ren_ sort) shift) (app1_ eq n) in
  let s = eqTrans_
      (scons_p_comp' (ref_ n))
      (scons_p_congr_ (abs_ref "z" (eqTrans_
                                    (scons_p_tail' (app1_ xi (ref_ "z")))
                                    (t (ref_ "z"))))
         (abs_ref "z" @@ scons_p_head' (ref_ "z"))) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 (s, t (ref_ n))) in
  pure @@ lemma_ (up_ren_subst_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)

 let genCompRenSubst sort =
  let* v = V.genVariables sort
      [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; taus; thetas ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2 (>>>) (sty_terms xis) (sty_terms taus))
      (sty_terms thetas)
      (fun x y s -> pure @@ app_ref (up_ren_subst_ x y) [underscore_; underscore_; underscore_; s]) in
  let ret s = eq_
      (app_ref (subst_ sort) (sty_terms taus @ [app_ref (ren_ sort) (sty_terms xis @ [s])]))
      (app_ref (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compRenSubst_ ~ret (scopeBinders @ beqs) [xis; taus; thetas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapComp_

 let genUpSubstRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `ZETAS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms; zetas ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> app_ref (ren_ sort) (sty_terms zetas)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* substSorts = substOf sort in
  let* zetas' = upSubst sort [binder] zetas in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (up_ sort binder) (pms @ [sigma])
       >>> app_ref (ren_ sort) (sty_terms zetas'))
      (app_ref (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let t n = eqTrans_
      (app_ref (compRenRen_ sort) (pat @ sty_terms zetas'
                                 @ List.map2 (>>>) (sty_terms zetas) pat
                                 @ List.map (const (abs_ref "x" eq_refl_)) pat
                                 @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (app_ref (compRenRen_ sort) (sty_terms zetas @ pat
                                            @ List.map2 (>>>) (sty_terms zetas) pat
                                            @ List.map (const (abs_ref "x" eq_refl_)) pat
                                            @ [ app1_ sigma n ])))
         (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
  let t' n z' = eqTrans_
      (app_ref (compRenRen_ sort) (pat @ sty_terms zetas'
                                 @ List.map2 (>>>) (sty_terms zetas) pat
                                 @ List.map (fun x ->
                                     (abs_ref "x" (if x = z'
                                                 then scons_p_tail' (ref_ "x")
                                                 else eq_refl_))) substSorts
                                 @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (app_ref (compRenRen_ sort) (sty_terms zetas @ pat
                                            @ List.map2 (>>>) (sty_terms zetas) pat
                                            @ List.map (const (abs_ref "x" eq_refl_)) pat
                                            @ [ app1_ sigma n ])))
         (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
  let hd = abs_ref "x" (ap_ (app_var_constr sort ms) (scons_p_head' (ref_ "x"))) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (fun _ sort' -> (eqTrans_
                         (scons_p_comp' (ref_ "n"))
                         (scons_p_congr_ (abs_ref "n" (t' (ref_ "n") sort')) hd),
                      t' (ref_ n) sort')) in
  pure @@ lemma_ (up_subst_ren_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)

 let genCompSubstRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                               ; `ZETAS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; zetas; thetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* sigmazeta = comp_ren_or_subst sort zetas sigmas in
  let* (eqs, beqs) = genEqs sort "Eq" sigmazeta (sty_terms thetas)
      (fun z y s ->
         let* zetas' = castSubst sort z zetas in
         pure @@ app_ref (up_subst_ren_ z y) ([underscore_]
                                            @ List.map (const underscore_) (sty_terms zetas')
                                            @ [underscore_; s])) in
  let ret s = eq_
      (app_ref (ren_ sort) (sty_terms zetas
                           @ [app_ref (subst_ sort) (sty_terms sigmas @ [s])]))
      (app_ref (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstRen_ ~ret (scopeBinders @ beqs) [sigmas; zetas; thetas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapComp_

let genUpSubstSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms; taus ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> app_ref (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* ls' = upSubst sort [binder] ls in
  let* taus' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (up_ sort binder) (pms @ [sigma])
       >>> app_ref (subst_ sort) (sty_terms taus'))
      (app_ref (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let* substSorts = substOf sort in
  let* pat' = comp_ren_or_subst sort (SubstRen pat) taus in
  let t n = eqTrans_
      (app_ref (compRenSubst_ sort) (pat @ sty_terms taus'
                                   @ List.map2 (>>>) pat (sty_terms taus')
                                   @ List.map (const (abs_ref "x" eq_refl_)) pat
                                   @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (app_ref (compSubstRen_ sort) (sty_terms taus @ pat @ pat'
                                              @ List.map (const (abs_ref "x" eq_refl_)) pat
                                              @ [ app1_ sigma n ])))
         (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
  let t' n z' = eqTrans_
      (app_ref (compRenSubst_ sort) (pat @ sty_terms taus'
                                   @ List.map2 (>>>) pat (sty_terms taus')
                                   @ List.map (const (abs_ref "x" eq_refl_)) pat
                                   @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (app_ref (compSubstRen_ sort)
                    (sty_terms taus @ pat
                     @ List.map (const underscore_) pat'
                     @ List.map (fun substSort ->
                         abs_ref "x" @@ eqSym_ (if substSort = z'
                                              then scons_p_tail' (ref_ "x")
                                              else eq_refl_)) substSorts
                     @ [ app1_ sigma n ])))
         (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
  let hd = abs_ref "x" (app_ref "scons_p_head'" [ underscore_
                                            ; abs_ref "z" (app_ref (ren_ sort)
                                                           (shift @ [underscore_]))
                                            ; ref_ "x" ]) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_ , t (ref_ n))
      (fun p sort' -> (eqTrans_
          (app_ref "scons_p_comp'" [ app_ref "zero_p" [ref_ p]
                                   >>> app_var_constr sort ls'
                                 ; underscore_; underscore_
                                 ; ref_ "n" ])
          (scons_p_congr_ (abs_ref "n" (t' (ref_ "n") sort')) hd),
                       t' (ref_ n) sort')) in
  pure @@ lemma_ (up_subst_subst_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)

 let genCompSubstSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                               ; `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; taus; thetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* sigmatau = comp_ren_or_subst sort taus sigmas in
  let* (eqs, beqs) = genEqs sort "Eq" sigmatau (sty_terms thetas) (fun z y s ->
      let* taus' = castSubst sort z taus in
      pure @@ app_ref (up_subst_subst_ z y) ([underscore_]
                                           @ List.map (const underscore_) (sty_terms taus')
                                           @ [underscore_; s])) in
  let ret s = eq_
      (app_ref (subst_ sort) (sty_terms taus
                           @ [app_ref (subst_ sort) (sty_terms sigmas @ [s])]))
      (app_ref (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstSubst_ ~ret (scopeBinders @ beqs) [sigmas; taus; thetas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapComp_

 let genUpSubstSubstNoRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS); `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms; taus ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> app_ref (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* ls' = upSubst sort [binder] ls in
  let* zeta' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (up_ sort binder) (pms @ [sigma])
       >>> app_ref (subst_ sort) (sty_terms zeta'))
      (app_ref (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSIdNoRen sort binder in
  let* substSorts = substOf sort in
  let* pat' = comp_ren_or_subst sort (SubstSubst pat) taus in
  let t n = eqTrans_
      (app_ref (compSubstSubst_ sort)
         (pat @ sty_terms zeta'
          @ List.map2 (>>>) shift (sty_terms zeta')
          @ List.map (const (abs_ref "x" eq_refl_)) pat
          @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (app_ref (compSubstSubst_ sort)
                    (sty_terms taus @ pat @ pat'
                     @ List.map (const (abs_ref "x" eq_refl_)) pat
                     @ [ app1_ sigma n ])))
         (ap_ (app_ref (subst_ sort) pat) (app1_ eq n))) in
  let t' n z' = eqTrans_
      (app_ref (compSubstSubst_ sort)
         (pat @ sty_terms zeta'
          @ List.map2 (>>>) shift (sty_terms zeta')
          @ List.map (const (abs_ref "x" eq_refl_)) pat
          @ [ app1_ sigma n ]))
      (eqTrans_
         (eqSym_ (app_ref (compSubstSubst_ sort)
                    (sty_terms taus @ pat
                     @ List.map (const underscore_) pat'
                     @ List.map (fun substSort ->
                         abs_ref "x" (eqSym_ (if substSort = z'
                                             then scons_p_tail' (ref_ "x")
                                             else eq_refl_)))
                       substSorts
                     @ [ app1_ sigma n ])))
         (ap_ (app_ref (subst_ sort) pat) (app1_ eq n))) in
  let hd = abs_ref "x" (app_ref "scons_p_head'"
                        [ underscore_
                        ; abs_ref "z" (app_ref (subst_ sort) (pat @ [underscore_]))
                        ; ref_ "x" ]) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (fun p z' -> (eqTrans_
         (app_ref "scons_p_comp'"
            [ app_ref "zero_p" [ref_ p] >>> (app_var_constr sort ls')
            ; underscore_
            ; underscore_
            ; ref_ "n" ])
         (scons_p_congr_  (abs_ref "n" (t' (ref_ "n") z')) hd),
                   t' (ref_ n) z')) in
  pure @@ lemma_ (up_subst_subst_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)

 let genUpRinstInst (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS ] in
  let [@warning "-8"] [ m ], [ ns ], scopeBinders = v in
  let* n_var = toVar sort ns in
  let (xi, bxi) = genRenS "xi" (m, n_var) in
  let (sigma, bsigma) = genSubstS "sigma" (m, ns) sort in
  let (eq, beq) = genEq "Eq" (xi >>> app_var_constr sort ns) sigma in
  let* ns' = upSubst sort [binder] ns in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (upRen_ sort binder) (pms @ [xi]) >>> app_var_constr sort ns')
      (app_ref (up_ sort binder) (pms @ [sigma])) in
  let* shift = patternSId sort binder in
  let t n = ap_ (app_ref (ren_ sort) shift) (app1_ eq n) in
  let n = VarState.tfresh "n" in
  let s = eqTrans_
      (app_ref "scons_p_comp'" [underscore_; underscore_; app_var_constr sort ns'; ref_ n])
      (scons_p_congr_ (abs_ref n (t (ref_ n))) (abs_ref "z" eq_refl_)) in
  let defBody = definitionBody sort binder
      (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
      (const2 (s, t (ref_ n))) in
  pure @@ lemma_ (up_rinstInst_ sort binder) (bpms @ scopeBinders @ bxi @ bsigma @ beq)
    ret (abs_ref "n" defBody)

 let genRinstInst sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis; sigmas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* xis' = substify sort ns xis in
  let* (eqs, beqs) = genEqs sort "Eq" xis' (sty_terms sigmas)
      (fun x y s -> pure (app_ref (up_rinstInst_ x y) [underscore_; underscore_; s])) in
  let ret s = eq_
      (app_ref (ren_ sort) (sty_terms xis @ [s]))
      (app_ref (subst_ sort) (sty_terms sigmas @ [s])) in
  traversal sort ms rinstInst_ ~ret (scopeBinders @ beqs) [xis; sigmas; eqs]
    (fun n ->
       let* toVarT = toVar sort eqs in
       pure @@ app1_ toVarT n)
    mapExt_

 let genLemmaRinstInst sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* xis_subst = substify sort ns xis in
  let ret = eq_
      (app_ref (ren_ sort) (sty_terms xis))
      (app_ref (subst_ sort) xis_subst) in
  let proof = fext_ (abs_ref "x"
                       (app_ref (rinstInst_ sort)
                          (sty_terms xis
                           @ List.map (const underscore_) substSorts
                           @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                           @ [ ref_ "x" ]))) in
  pure @@ lemma_ (rinstInstFun_ sort) scopeBinders ret proof

 let genLemmaVarL sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; sigmas ], scopeBinders = v in
  let* sigma' = toVar sort sigmas in
  let ret = eq_ (app_var_constr sort ms >>> app_ref (subst_ sort) (sty_terms sigmas)) sigma' in
  let proof = fext_ (abs_ref "x" eq_refl_) in
    pure @@ lemma_ (varLFun_ sort) scopeBinders ret proof

 let genLemmaVarLRen sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns; xis ], scopeBinders = v in
  let* xi' = toVar sort xis in
  let ret = eq_
      (app_var_constr sort ms >>> app_ref (ren_ sort) (sty_terms xis))
      (xi' >>> (app_var_constr sort ns)) in
  let proof = fext_ (abs_ref "x" eq_refl_) in
  pure @@ lemma_ (varLRenFun_ sort) scopeBinders ret proof

let genLemmaInstId sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* substSorts = substOf sort in
  let* vars = mk_var_apps sort ms in
  let ret = eq_ (app_fix (subst_ sort) vars) id_ in
  let proof = fext_ (abs_ref "x"
                       (app_ref (idSubst_ sort)
                          (vars
                           @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                           @ [ app_id_ (ref_ "x") ]))) in
  pure @@ lemma_ (instIdFun_ sort) bms ret proof

let genLemmaRinstId sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* substSorts = substOf sort in
  let* vars = a_map (fun substSorts ->
      map2 app_ref (pure @@ var_ substSorts)
        (map sty_terms (castSubst sort substSorts ms)))
      substSorts in
  let ret = eq_
      (app_fix ~expl:true (ren_ sort) ~scopes:[ms; ms] (List.map (const id_) substSorts))
      id_ in
  let proof = eqTrans_
      (app_ref (rinstInstFun_ sort) (List.map (const (app_id_ underscore_)) substSorts))
      (ref_ (instIdFun_ sort)) in
  pure @@ lemma_ (rinstIdFun_ sort) bms ret proof

 let genLemmaRenRenComp sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let sigmazeta = xis <<>> zetas in
  let s = VarState.tfresh "s" in
  let ret = eq_
      (app_ref (ren_ sort) (sty_terms zetas
                           @ [ app_ref (ren_ sort) (sty_terms xis
                                                   @ [ ref_ s ]) ]))
      (app_ref (ren_ sort) (sigmazeta @ [ ref_ s ])) in
  let proof = app_ref (compRenRen_ sort) (sty_terms xis
                                        @ sty_terms zetas
                                        @ List.map (const underscore_) substSorts
                                        @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                        @ [ ref_ s ]) in
  let ret' = eq_
      (app_ref (ren_ sort) (sty_terms xis) >>> app_ref (ren_ sort) (sty_terms zetas))
      (app_ref (ren_ sort) sigmazeta) in
  let proof' = fext_ (abs_ref "n"
                        (app_ref (renRen_ sort)
                           (sty_terms xis
                            @ sty_terms zetas
                            @ [ ref_ "n" ]))) in
  pure (lemma_ (renRen_ sort) (scopeBinders
                                @ [ binder1_ ~btype:(app_sort sort ms) s ])
           ret proof,
        lemma_ (renRen'_ sort) scopeBinders ret' proof')

let genLemmaCompRenSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; zetas ], scopeBinders = v in
  let* substSorts = substOf sort in
  let s = VarState.tfresh "s" in
  let* sigmazeta = comp_ren_or_subst sort zetas sigmas in
  let ret = eq_
      (app_ref (ren_ sort) (sty_terms zetas
                           @ [ app_ref (subst_ sort) (sty_terms sigmas
                                                     @ [ ref_ s ]) ]))
      (app_ref (subst_ sort) (sigmazeta @ [ ref_ s ])) in
  let proof = app_ref (compSubstRen_ sort) (sty_terms sigmas
                                          @ sty_terms zetas
                                          @ List.map (const underscore_) substSorts
                                          @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                          @ [ ref_ s ]) in
  let ret' = eq_
      (app_ref (subst_ sort) (sty_terms sigmas) >>> app_ref (ren_ sort) (sty_terms zetas))
      (app_ref (subst_ sort) sigmazeta) in
  let proof' = fext_ (abs_ref "n"
                        (app_ref (compRen_ sort)
                           (sty_terms sigmas
                            @ sty_terms zetas
                            @ [ ref_ "n" ]))) in
  pure (lemma_ (compRen_ sort) (scopeBinders
                                 @ [ binder1_ ~btype:(app_sort sort ms) s ])
                ret proof,
        lemma_ (compRen'_ sort) scopeBinders ret' proof')

 let genLemmaCompSubstRen sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; xis; taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let sigmazeta =  xis <<>> taus in
  let s = VarState.tfresh "s" in
  let ret = eq_
      (app_ref (subst_ sort) (sty_terms taus
                             @ [ app_ref (ren_ sort) (sty_terms xis
                                                     @ [ref_ s])]))
      (app_ref (subst_ sort) (sigmazeta @ [ref_ s])) in
  let proof = app_ref (compRenSubst_ sort) (sty_terms xis
                                          @ sty_terms taus
                                          @ List.map (const underscore_) substSorts
                                          @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                          @ [ref_ s]) in
  let ret' = eq_
      (app_ref (ren_ sort) (sty_terms xis) >>> (app_ref (subst_ sort) (sty_terms taus)))
      (app_ref (subst_ sort) sigmazeta) in
  let proof' = fext_ (abs_ref "n"
                        (app_ref (renComp_ sort)
                           (sty_terms xis
                            @ sty_terms taus
                            @ [ref_ "n"]))) in
  pure (lemma_ (renComp_ sort) (scopeBinders
                                 @ [ binder1_ ~btype:(app_sort sort ms) s ])
                ret proof,
        lemma_ (renComp'_ sort) scopeBinders ret' proof')

let genLemmaCompSubstSubst sort =
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms; sigmas; taus ], scopeBinders = v in
  let* substSorts = substOf sort in
  let s = VarState.tfresh "s" in
  let* sigmatau = comp_ren_or_subst sort taus sigmas in
  let ret = eq_
      (app_ref (subst_ sort) (sty_terms taus
                              @ [ app_ref (subst_ sort) (sty_terms sigmas
                                                        @ [ref_ s])]))
      (app_ref (subst_ sort) (sigmatau @ [ref_ s])) in
  let proof = app_ref (compSubstSubst_ sort) (sty_terms sigmas
                                            @ sty_terms taus
                                            @ List.map (const underscore_) substSorts
                                            @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                            @ [ref_ s]) in
  let ret' = eq_
      (app_ref (subst_ sort) (sty_terms sigmas) >>> app_ref (subst_ sort) (sty_terms taus))
      (app_ref (subst_ sort) sigmatau) in
  let proof' = fext_ (abs_ref "n"
                        (app_ref (compComp_ sort)
                           (sty_terms sigmas
                            @ sty_terms taus
                            @ [ref_ "n"]))) in
  pure (lemma_ (compComp_ sort) (scopeBinders
                                  @ [ binder1_ ~btype:(app_sort sort ms) s ])
                ret proof,
        lemma_ (compComp'_ sort) scopeBinders ret' proof')

(** This function delegates to all the different code generation functions and in the end
 ** aggregates all the returned vernacular expressions. *)
let genCodeT sorts upList =
  let* varSorts = a_filter isOpen sorts in
  let* hasbinders = map (fun l -> l |> list_empty |> not) (substOf (List.hd sorts)) in
  (* GENERATE INDUCTIVE TYPES *)
  let* def_sorts = a_filter definable sorts in
  let* types = a_map genBody def_sorts in
  let* is_rec = isRecursive sorts in
  (* GENERATE CONGRUENCE LEMMAS *)
  let* congruences = a_map genCongruences sorts in
  (* GENERATE RENAMINGS *)
  let* isRen = hasRenamings (List.hd sorts) in
  let guard_map ?(invert=false) f input =
    m_guard (invert <> isRen) @@ a_map f input in
  let guard_split_map f input =
    let* l = a_map f input in
    let l1, l2 = List.split l in
    if isRen then pure (l1, l2) else pure ([], []) in
  let* upRen = guard_map genUpRen upList in
  let* renamings = genRenamings sorts in
  (* GENERATE UPs *)
  let* ups = guard_map genUpS upList in
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
  let* lemmaInstId_fext = a_map genLemmaInstId sorts in
  let* lemmaRinstId_fext = guard_map genLemmaRinstId sorts in
  let* lemmaVarL_fext = a_map genLemmaVarL varSorts in
  let* lemmaVarLRen_fext = guard_map genLemmaVarLRen varSorts in
  let* lemmaRenSubst_fext = guard_map genLemmaRinstInst sorts in
  let* lemmaSubstRenRen, lemma_subst_ren_ren_fext = guard_split_map genLemmaRenRenComp sorts in
  let* lemmaSubstCompRen, lemma_subst_comp_ren_fext = guard_split_map genLemmaCompRenSubst sorts in
  let* lemmaSubstRenComp, lemma_subst_ren_comp_fext = guard_split_map genLemmaCompSubstRen sorts in
  let* lemmaSubstComp, lemma_subst_comp_fext = guard_split_map genLemmaCompSubstSubst sorts in
  let mk_inductive = function
    | [] -> []
    | ind_exprs -> [inductive_ ind_exprs] in
  let mk_fixpoint = function
    | [] -> []
    | fix_exprs -> [fixpoint_ ~is_rec fix_exprs] in
  (* generation of the actual sentences *)
  pure { as_exprs = mk_inductive types @
                     (List.concat congruences) @
                     (if not hasbinders then [] else
                        (List.concat upRen) @ guard isRen [renamings] @
                        (List.concat ups) @ [substitutions] @ (List.concat upsNoRen) @
                        (List.concat upId) @ mk_fixpoint idLemmas @
                        (List.concat extUpRen) @ mk_fixpoint extRen @
                        (List.concat extUp) @ mk_fixpoint ext @
                        (List.concat upRenRen) @ mk_fixpoint compRenRen @
                        (List.concat upRenSubst) @ mk_fixpoint compRenSubst @
                        (List.concat upSubstRen) @ mk_fixpoint compSubstRen @
                        (List.concat upSubstSubst) @ mk_fixpoint compSubstSubst @ (List.concat upSubstSubstNoRen) @
                        (List.concat upRinstInst) @ mk_fixpoint rinstInst @
                        (List.concat lemmaSubstRenRen) @ (List.concat lemmaSubstCompRen) @
                        (List.concat lemmaSubstRenComp) @ (List.concat lemmaSubstComp));
         as_fext_exprs =
           List.concat (lemmaRenSubst_fext @
                        lemmaInstId_fext @ lemmaRinstId_fext @
                        lemmaVarL_fext @ lemmaVarLRen_fext @
                        lemma_subst_ren_ren_fext @
                        lemma_subst_comp_ren_fext @
                        lemma_subst_ren_comp_fext @
                        lemma_subst_comp_fext) }
