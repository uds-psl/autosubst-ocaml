(** Most of the genX functions in this module follow the same pattern.
 **  - declare some scope/renaming/substitution variables and their binders
 **  - build the type of the statement
 **  - build the proof term of the statement
 **
 ** Fixpoints call traversal which generates the match on the principal argument.
 ** Definitions and Lemmas directly call the smart constructor with the type, binders and proof.
 ** *)
open Util

module L = Language
module V = Variables

open CoqSyntax
open Tactics
open CoqNames
open GallinaGen
open VernacGen
open Termutil
open AutomationGen
open RWEM.Syntax
open RWEM

let createBinders = List.map (fun p -> binder1_ ~btype:(ref_ (snd p)) (fst p))

let createImpBinders = List.map (fun p -> binder1_ ~implicit:true ~btype:(ref_ (snd p)) (fst p))

let rec genArg sort n bs = function
  | L.Atom y ->
    let* up_scopes = castUpSubstScope sort bs y n in
    pure (app_ref y (ss_terms up_scopes))
  | L.FunApp (f, p, xs) ->
    let* xs' = a_map (genArg sort n bs) xs in
    let p' = Option.default [] (Option.map (fun x -> [x]) p) in
    pure @@ app_ref f (p' @ xs')


let genVar sort ns =
  let* is_open = isOpen sort in
  if not is_open then pure []
  else
    (* register variable constructor instance *)
    let* () = tell_instance (ClassGen.Var, sort, ss_names ns) in
    let* () = tell_notation (NotationGen.VarConstr, sort) in
    let* () = tell_notation (NotationGen.VarInst, sort) in
    let* () = tell_notation (NotationGen.Var, sort) in
    let* () = tell_argument (var_ sort, ss_names ns) in
    let* s = gen_var_arg sort ns in
    let t = [s] ==> app_sort sort ns in
    pure @@ [constructor_ (var_ sort) t]

let genConstr sort ns L.{ cparameters; cname; cpositions } =
  let* t =
    let* up_n_x = a_map (fun L.{ binders; head } -> genArg sort ns binders head) cpositions in
    pure @@ (up_n_x ==> app_sort sort ns) in
  let* () = tell_argument (cname, ss_names ns) in
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
let genCongruence sort L.{ cparameters; cname; cpositions } =
  let* (ms, bms) = introScopeVar "m" sort in
  let ss = getPattern "s" cpositions in
  let ts = getPattern "t" cpositions in
  let hs = getPattern "H" cpositions in
  let mkBinders xs = a_map2_exn (fun x L.{binders; head} ->
      let* arg_type = genArg sort ms binders head in
      pure @@ binder1_ ~implicit:true ~btype:arg_type x)
      xs cpositions in
  let* bss = mkBinders ss in
  let* bts = mkBinders ts in
  let bparameters = createImpBinders cparameters in
  let parameters' = List.(mk_refs (map fst cparameters)) in
  let ss = mk_refs ss in
  let ts = mk_refs ts in
  let eqs = List.map2 eq_ ss ts in
  let beqs = List.map2 (fun h ty -> binder1_ ~btype:ty h) hs eqs in
  let eq = eq_
      (app_constr cname ms (parameters' @ ss))
      (app_constr cname ms (parameters' @ ts)) in
  let x = VarState.tfresh "x" in
  let (_, proof') = List.fold_left (fun (i, t) h ->
      let ss' = list_take ts i @ [ref_ x] @ (list_drop ss (i + 1)) in
      let t' = eqTrans_ t (ap_ (abs_ref "x" (app_constr cname ms (parameters' @ ss')))
                             (ref_ h)) in
      (i + 1, t'))
      (0, eq_refl_) hs in
  pure @@ lemma_ (congr_ cname) (bparameters @ bms @ bss @ bts @ beqs) eq proof'

let genCongruences sort =
  let* ctrs = constructors sort in
  a_map (genCongruence sort) ctrs

(** Constructs the body of a fixpoint.
 **
 ** no_args: used when an argument of a constructor does not have a substitution vector. E.g. ty in stlc does not have a substitution vector.
 ** sem: used to calculate the branch of a non-variable constructor. Most lemmas use the constructor's congruence lemma in the head position but other things like the subsitution operation use other terms in head position *)
let traversal
    s sort nameF underscore_pattern ?(no_args=fun s -> app1_ eq_refl_ s) args
    var_case_body ?(sem=fun _ cname positions -> app_fix (congr_ cname) positions) funsem =
  let open L in
  let* cs = constructors sort in
  let* open_x = isOpen sort in
  (* Only create the variable branch if the sort is open *)
  let* var_pattern = m_guard open_x (
      (** TODO make scope state work correctly *)
      let s0 = "s0" in
      let* var_body = var_case_body (ref_ s0) in
      pure [ branch_ (var_ sort) (underscore_pattern @ [s0]) var_body ]
    )
  in
  (* Computes the branch for a constructor *)
  let mk_constr_pattern { cparameters; cname; cpositions; } =
    let extra_arg_list = function
      | None -> []
      | Some s -> [s] in
    let rec arg_map bs extra_arg head = match head with
      | Atom y ->
        let* b = hasArgs y in
        let* args = a_map (castUpSubst sort bs y) args in
        if b
        then pure (app_ref (nameF y)
                     (List.(concat (map sty_terms args))
                      @ extra_arg_list extra_arg))
        else
          (* In the case there are no args we have to take extra care. TODO better documentation. need this because of recursion in the FunApp case. Otherwise we would have nothing to apply the no_args function to *)
          pure (match extra_arg with
              | None -> abs_ref "x" (no_args (ref_ "x"))
              | Some s -> no_args s)
      | FunApp (f, p, xs) ->
        let* res = a_map (arg_map bs None) xs in
        pure (funsem f (res @ extra_arg_list extra_arg)) in
    let ss = getPattern "s" cpositions in
    let* positions = a_map2_exn
        (fun s { binders; head; } ->
           arg_map binders (Some (ref_ s)) head)
        ss cpositions in
    pure (branch_ cname
            (underscore_pattern @ List.map fst cparameters @ ss)
            (sem (List.map fst cparameters) cname positions))
  in
  let* constr_pattern = a_map mk_constr_pattern cs in
  let body = match_ (ref_ s) (var_pattern @ constr_pattern) in
  pure body

(* UpRen in sort x by the binder *)
let genUpRen (binder, sort) =
  let* v = V.genVariables sort [ `M; `N; `XI (`M, `N) ] in
  let [@warning "-8"] [ m; n; xi ], [], [], scopeBinders = v in
  (** register upRen for unfolding *)
  let* () = tell_unfold_function (upRen_ sort binder) in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let n' = succ_ n sort binder in
  let defBody = definitionBody sort binder
      (up_ren_ xi, xi)
      (fun m _ -> app_ref "upRen_p" [ref_ m; xi], xi) in
  pure @@ lemma_ ~opaque:false (upRen_ sort binder) (bpms @ scopeBinders) (renT m' n') defBody

(* TODO move to tactics and make same name as in MetaCoq *)
let genMatchVar (sort: L.tId) (scope: substScope) =
  let s = VarState.tfresh "s" in
  (s, [binder1_ ~btype:(app_sort sort scope) s])

let genRenaming sort =
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] _, [ ms; ns ], [ xis ], scopeBinders = v in
  (** automation *)
  let* substSorts = substOf sort in
  let* () = tell_instance (ClassGen.Ren (List.length substSorts), sort, ss_names ms @ ss_names ns) in
  let* () = tell_cbn_function (ren_ sort) in
  let* () = tell_notation (NotationGen.RenApply substSorts, sort) in
  let* () = tell_notation (NotationGen.Ren substSorts, sort) in
  let* () = tell_proper_instance (sort, ren_ sort, extRen_ sort) in
  (* DONE what is the result of toVar here?\
   * when I call it with sort=tm, xi=[xity;xivl] I get this weird error term that toVar constructs. This is then probably ignored by some similar logic in the traversal. Seems brittle.
   * When I call it instead with sort=vl I get xivl. So it seems get the renaming of the sort that I'm currently inspecting *)
  (* register renaming instance & and unfolding *)
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = app_sort sort ns in
  (** body *)
  let* body = traversal s sort ren_ (mk_underscore_pattern ms) ~no_args:id [xis]
      (fun s ->
         let* toVarT = toVar sort xis in
         pure @@ app1_ (app_var_constr sort ns) (app1_ toVarT s))
      ~sem:(fun pms cname positions -> app_constr cname ns (mk_refs pms @ positions))
      map_ in
  pure @@ fixpointBody_ (ren_ sort) (scopeBinders @ bs) type_ body s

let mk_scons sort binder sigma ms =
  match binder with
  | L.Single y ->
    if sort = y
    then
      let zero_ = app1_ (app_var_constr sort ms) var_zero_ in
      app_ cons_ [zero_; sigma]
    else sigma
  | L.BinderList (p, y) ->
    if sort = y
    then
      let zero_ = app_ref "zero_p" [ref_ p] >>> app_var_constr sort ms in
      app_ref "scons_p" [ref_ p; zero_; sigma]
    else sigma

let upSubstT binder sort ms sigma =
  let* pat = patternSId sort binder in
  let* ms' = upSubstScope sort [binder] ms in
  let* hasRen = hasRenamings sort in
  let sigma' = sigma >>> app_fix (if hasRen then (ren_ sort) else (subst_ sort)) pat in
  pure @@ mk_scons sort binder sigma' ms'

let genUpS (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS) ] in
  let [@warning "-8"] [ m; sigma ], [ ns ], [], scopeBinders = v in
  (* TODO hack so that I only tell the instance when it's a single binder *)
  let* () = match binder with
    | L.Single x ->
      (* register up instance *)
      let* () = tell_instance (ClassGen.Up x, sort, "m" :: ss_names ns) in
      tell_notation (NotationGen.UpInst x, sort)
    | L.BinderList _ -> pure ()
  in
  (* register up for unfolding *)
  let* () = tell_unfold_function (up_ sort binder) in
  (* TODO what does upSubstT do here? *)
  let* sigma = upSubstT binder sort ns sigma in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let* n' = upSubstScope sort [binder] ns in
  pure @@ lemma_ ~opaque:false (up_ sort binder) (bpms @ scopeBinders) (substT m' n' sort) sigma

(** make the default var_case_body *)
let mk_var_case_body (sort: L.tId) (sty: substTy) = fun (s: constr_expr) ->
  let* toVarT = toVar sort sty in
  pure @@ app1_ toVarT s

(** Generate the substitution function
 ** e.g. Fixpoint subst_tm ... *)
let genSubstitution sort =
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns ], [ sigmas ], scopeBinders = v in
  (** automation *)
  (* register subst instance & unfolding & up class *)
  let* substSorts = substOf sort in
  let* () = tell_instance (ClassGen.Subst (List.length substSorts), sort, ss_names ms @ ss_names ns) in
  let* () = tell_cbn_function (subst_ sort) in
  let* () = tell_class (ClassGen.Up "", sort) in
  let* () = tell_notation (NotationGen.Up, sort) in
  let* () = tell_notation (NotationGen.SubstApply substSorts, sort) in
  let* () = tell_notation (NotationGen.Subst substSorts, sort) in
  let* () = tell_proper_instance (sort, subst_ sort, ext_ sort) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = app_sort sort ns in
  (** body *)
  let* body = traversal s sort subst_ (mk_underscore_pattern ms) ~no_args:id [sigmas]
      (mk_var_case_body sort sigmas)
      ~sem:(fun pms cname positions -> app_constr cname ns (mk_refs pms @ positions))
      map_ in
  pure @@ fixpointBody_ (subst_ sort) (scopeBinders @ bs) type_ body s

(* let genSubstitutions sorts =
 *   let* fs = a_map genSubstitution sorts in
 *   (\* a.d. DONE is the isRecursive still from modular syntax?
 *    * No, it's not. Assitionally, I think I found a bug in the Haskell implementation. I should not check isRecursive for the head of the component but rather for the whole component.
 *    * If we just check the head we can force wrong code generation if the head sort is not an argument of itself (e.g. if we move vl to be the first defined sort in SysF_cbv) *\)
 *   let* is_rec = isRecursive sorts in
 *   pure @@ fixpoint_ ~is_rec fs *)

(* UpAllfv in sort x by the binder *)
let genUpAllfv (binder, sort) =
  let (p, bps) = genPredS "p" sort in
  (** register upRen for unfolding *)
  let defBody = definitionBody sort binder
      (up_allfv_ p, p)
      (* TODO nto used atm *)
      (fun m _ -> ref_ "unimplemented", ref_ "unimplemented") in
  pure @@ lemma_ ~opaque:false (upAllfvName sort binder) bps predT defBody

let rec mk_conjs = function
  | [] -> true_
  | [p] -> p
  | p::ps -> and_ p (mk_conjs ps)

let genAllfv sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* (ps, bps) = genPred "p" sort ms in
  let (s, bs) = genMatchVar sort ms in
  let type_ = prop_ in
  (** body *)
  let* body = traversal s sort allfvName (mk_underscore_pattern ms) ~no_args:(fun s -> true_) [ps]
      (fun s ->
         let* toVarT = toVar sort ps in
         pure (app1_ toVarT s))
      ~sem:(fun pms cname positions -> mk_conjs positions)
      map_ in
  pure @@ fixpointBody_ (allfvName sort) (bms @ bps @ bs) type_ body s

let genUpId (binder, sort) =
  let* (ms, bms) = introScopeVar "m" sort in
  let* m_var = toVarScope sort ms in
  let (sigma, bsigma) = genSubstS "sigma" (m_var, ms) sort in
  let (eq, beq) = genEq "Eq" sigma (app_var_constr sort ms) in
  let n = VarState.tfresh "n" in
  let* ms = upSubstScope sort [binder] ms in
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
  let [@warning "-8"] [], [ ms ], [ sigmas ], scopeBinders = v in
  let* eqs' = mk_var_apps sort ms in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) eqs'
      (fun x y s -> pure @@ app_ref (upId_ x y) [underscore_; s]) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_ (app_fix (subst_ sort) ~scopes:[sigmas] [ref_ s]) (ref_ s) in
  (** body *)
  let* body = traversal s sort idSubst_ (mk_underscore_pattern ms) [sigmas; eqs]
      (mk_var_case_body sort eqs)
      mapId_ in
  pure @@ fixpointBody_ (idSubst_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genUpExtRen (binder, sort) =
  let* v = V.genVariables sort [ `M; `N; `XI (`M, `N); `ZETA (`M, `N) ] in
  let [@warning "-8"] [ m; n; xi; zeta ], [], [], scopeBinders = v in
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
  let [@warning "-8"] [], [ ms; ns ], [ xis; zetas ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms xis) (sty_terms zetas)
      (fun sort binder s -> pure @@ app_ref (upExtRen_ sort binder) [underscore_; underscore_; s]) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_
      (app_fix (ren_ sort) ~scopes:[xis] [ref_ s])
      (app_fix (ren_ sort) ~scopes:[zetas] [ref_ s]) in
  (** body *)
  let* body = traversal s sort extRen_ (mk_underscore_pattern ms) [xis; zetas; eqs]
      (fun s ->
         let* toVarT = toVar sort eqs in
         pure @@ ap_ (app_var_constr sort ns) (app1_ toVarT s))
      mapExt_ in
  pure @@ fixpointBody_ (extRen_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genUpExt (binder, sort) =
  let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS); `TAU (`M, `NS) ] in
  let [@warning "-8"] [ m; sigma; tau ], [ ns ], [], scopeBinders = v in
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
  let [@warning "-8"] [], [ ms; ns ], [ sigmas; taus ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) (sty_terms taus)
      (fun x y s -> pure @@ app_ref (upExt_ x y) [underscore_; underscore_; s]) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_
      (app_fix (subst_ sort) ~scopes:[sigmas] [ref_ s])
      (app_fix (subst_ sort) ~scopes:[taus] [ref_ s]) in
  (** body *)
  let* body = traversal s sort ext_ (mk_underscore_pattern ms) [sigmas; taus; eqs]
      (mk_var_case_body sort eqs)
      mapExt_ in
  pure @@ fixpointBody_ (ext_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genUpRenRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `L; `M; `XI (`K, `L); `ZETA (`L, `M); `RHO (`K, `M) ] in
  let [@warning "-8"] [ k; l; m; xi; zeta; rho ], [], [], scopeBinders = v in
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
  let [@warning "-8"] [], [ ks; ls; ms ], [ xis; zetas; rhos ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2 (>>>) (sty_terms xis) (sty_terms zetas)) (sty_terms rhos)
      (fun x y s -> pure @@ match y with
         | L.Single z -> if z = x
           then app_ref up_ren_ren__ [underscore_; underscore_; underscore_; s]
           else s
         | L.BinderList (_, z) -> if z = x
           then app_ref "up_ren_ren_p" [s]
           else s) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_
      (app_fix (ren_ sort) (sty_terms zetas
                            @ [ app_ref (ren_ sort) (sty_terms xis @ [ref_ s]) ]))
      (app_ref (ren_ sort) (sty_terms rhos @ [ref_ s])) in
  (** body *)
  let* body = traversal s sort compRenRen_ (mk_underscore_pattern ms) [xis; zetas; rhos; eqs]
      (fun s ->
         let* toVarT = toVar sort eqs in
         pure (ap_ (app_var_constr sort ls) (app1_ toVarT s)))
      mapComp_ in
  pure @@ fixpointBody_ (compRenRen_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genUpRenSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `L; `MS;
                                 `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; l; xi; tau; theta ], [ ms ], [], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (xi >>> tau) theta in
  let n = VarState.tfresh "n" in
  (* TODO is this really not used? *)
  (* let* ms = upSubstScope sort [binder] ms in *)
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
  let [@warning "-8"] [], [ ks; ls; ms ], [ xis; taus; thetas ], scopeBinders = v in
  let* (eqs, beqs) = genEqs sort "Eq"
      (List.map2 (>>>) (sty_terms xis) (sty_terms taus))
      (sty_terms thetas)
      (fun x y s -> pure @@ app_ref (up_ren_subst_ x y) [underscore_; underscore_; underscore_; s]) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_
      (app_ref (subst_ sort) (sty_terms taus @ [app_ref (ren_ sort) (sty_terms xis @ [ref_ s])]))
      (app_ref (subst_ sort) (sty_terms thetas @ [ref_ s])) in
  (** body *)
  let* body = traversal s sort compRenSubst_ (mk_underscore_pattern ms) [xis; taus; thetas; eqs]
      (mk_var_case_body sort eqs)
      mapComp_ in
  pure @@ fixpointBody_ (compRenSubst_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genUpSubstRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `ZETAS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms ], [ zetas ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> app_ref (ren_ sort) (sty_terms zetas)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubstScope sort [binder] ms in
  let* substSorts = substOf sort in
  (* TODO document *)
  let* zetas' = upSubst sort [binder] zetas in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_
      (app_ref (up_ sort binder) (pms @ [sigma])
       >>> app_ref (ren_ sort) (sty_terms zetas'))
      (app_ref (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  (* TODO refactor these a bit *)
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
  let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; zetas; thetas ], scopeBinders = v in
  let* sigmazeta = comp_ren_or_subst sort zetas sigmas in
  let* (eqs, beqs) = genEqs sort "Eq" sigmazeta (sty_terms thetas)
      (fun z y s ->
         let* zetas' = castSubst sort z zetas in
         pure @@ app_ref (up_subst_ren_ z y) ([underscore_]
                                              @ List.map (const underscore_) (sty_terms zetas')
                                              @ [underscore_; s])) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_
      (app_ref (ren_ sort) (sty_terms zetas
                            @ [app_ref (subst_ sort) (sty_terms sigmas @ [ref_ s])]))
      (app_ref (subst_ sort) (sty_terms thetas @ [ref_ s])) in
  (** body *)
  let* body = traversal s sort compSubstRen_ (mk_underscore_pattern ms) [sigmas; zetas; thetas; eqs]
      (mk_var_case_body sort eqs)
      mapComp_ in
  pure @@ fixpointBody_ (compSubstRen_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genUpSubstSubst (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                               ; `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms ], [ taus ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> app_ref (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubstScope sort [binder] ms in
  let* ls' = upSubstScope sort [binder] ls in
  let* taus' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  (* TODO document *)
  let ret = equiv_
      (app_ref (up_ sort binder) (pms @ [sigma])
       >>> app_ref (subst_ sort) (sty_terms taus'))
      (app_ref (up_ sort binder) (pms @ [theta])) in
  let* substSorts = substOf sort in
  (* TODO document *)
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
                                                                 (pat @ [underscore_]))
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
  let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; taus; thetas ], scopeBinders = v in
  let* sigmatau = comp_ren_or_subst sort taus sigmas in
  let* (eqs, beqs) = genEqs sort "Eq" sigmatau (sty_terms thetas) (fun z y s ->
      let* taus' = castSubst sort z taus in
      pure @@ app_ref (up_subst_subst_ z y) ([underscore_]
                                             @ List.map (const underscore_) (sty_terms taus')
                                             @ [underscore_; s])) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_
      (app_ref (subst_ sort) (sty_terms taus
                              @ [app_ref (subst_ sort) (sty_terms sigmas @ [ref_ s])]))
      (app_ref (subst_ sort) (sty_terms thetas @ [ref_ s])) in
  (** body *)
  let* body = traversal s sort compSubstSubst_ (mk_underscore_pattern ms) [sigmas; taus; thetas; eqs]
      (mk_var_case_body sort eqs)
      mapComp_ in
  pure @@ fixpointBody_ (compSubstSubst_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genUpSubstSubstNoRen (binder, sort) =
  let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS); `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
  let [@warning "-8"] [ k; sigma; theta ], [ ls; ms ], [ taus ], scopeBinders = v in
  let (eq, beq) = genEq "Eq" (sigma >>> app_ref (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubstScope sort [binder] ms in
  let* ls' = upSubstScope sort [binder] ls in
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
  let [@warning "-8"] [ m ], [ ns ], [], scopeBinders = v in
  let* n_var = toVarScope sort ns in
  let (xi, bxi) = genRenS "xi" (m, n_var) in
  let (sigma, bsigma) = genSubstS "sigma" (m, ns) sort in
  let (eq, beq) = genEq "Eq" (xi >>> app_var_constr sort ns) sigma in
  let* ns' = upSubstScope sort [binder] ns in
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
  let [@warning "-8"] [], [ ms; ns ], [ xis; sigmas ], scopeBinders = v in
  let* xis' = substify sort ns xis in
  let* (eqs, beqs) = genEqs sort "Eq" xis' (sty_terms sigmas)
      (fun x y s -> pure (app_ref (up_rinstInst_ x y) [underscore_; underscore_; s])) in
  (** type *)
  let (s, bs) = genMatchVar sort ms in
  let type_ = eq_
      (app_ref (ren_ sort) (sty_terms xis @ [ref_ s]))
      (app_ref (subst_ sort) (sty_terms sigmas @ [ref_ s])) in
  (** body *)
  let* body = traversal s sort rinstInst_ (mk_underscore_pattern ms) [xis; sigmas; eqs]
      (mk_var_case_body sort eqs)
      mapExt_ in
  pure @@ fixpointBody_ (rinstInst_ sort) (scopeBinders @ beqs @ bs) type_ body s

let genLemmaRinstInst sort =
  (* register substify lemma *)
  let* () = tell_substify_lemma_fext (rinstInstFun_ sort) in
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
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

let genLemmaRinstInst' sort =
  (* register substify lemma *)
  let* () = tell_substify_lemma (rinstInst'Fun_ sort) in
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
  let* substSorts = substOf sort in
  let* xis_subst = substify sort ns xis in
  let s = VarState.tfresh "s" in
  let ret = eq_
      (app_ref (ren_ sort) (sty_terms xis @ [ ref_ s ]))
      (app_ref (subst_ sort) (xis_subst @ [ ref_ s ])) in
  let proof = app_ref (rinstInst_ sort) (sty_terms xis
                                         @ List.map (const underscore_) substSorts
                                         @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                         @ [ ref_ s ]) in
  pure @@ lemma_ (rinstInst'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(app_sort sort ms) s ]) ret proof

let genLemmaVarL sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_fext (varLFun_ sort) in
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns ], [ sigmas ], scopeBinders = v in
  let* sigma' = toVar sort sigmas in
  let ret = eq_ (app_var_constr sort ms >>> app_ref (subst_ sort) (sty_terms sigmas)) sigma' in
  let proof = fext_ (abs_ref "x" eq_refl_) in
  pure @@ lemma_ (varLFun_ sort) scopeBinders ret proof

(* varL' the extensional variant of varL *)
let genLemmaVarL' sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_no_fext (varL'Fun_ sort) in
  let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns ], [ sigmas ], scopeBinders = v in
  (* generate type *)
  (* on the right hand side we only need the sigma for the current sort *)
  let* sigma' = toVar sort sigmas in
  let* m' = toVarScope sort ms in
  let x = VarState.tfresh "x" in
  let ret = eq_
      (app_ref (subst_ sort) (sty_terms sigmas
                              @ [ app_constr (var_ sort) ms [ ref_ x ] ]))
      (app1_ sigma' (ref_ x)) in
  let proof = eq_refl_ in
  pure @@ lemma_ (varL'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(varT m') x ]) ret proof

let genLemmaVarLRen sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_fext (varLRenFun_ sort) in
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
  let* xi' = toVar sort xis in
  let ret = eq_
      (app_var_constr sort ms >>> app_ref (ren_ sort) (sty_terms xis))
      (xi' >>> (app_var_constr sort ns)) in
  let proof = fext_ (abs_ref "x" eq_refl_) in
  pure @@ lemma_ (varLRenFun_ sort) scopeBinders ret proof

(* varLRen' the extensional variant of varLRen *)
let genLemmaVarLRen' sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_no_fext (varLRen'Fun_ sort) in
  let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
  let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
  let* xi' = toVar sort xis in
  let* m' = toVarScope sort ms in
  let x = VarState.tfresh "x" in
  let ret = eq_
      (app_ref (ren_ sort) (sty_terms xis
                            @ [ app_constr (var_ sort) ms [ ref_ x ] ]))
      (app_constr (var_ sort) ns [ app1_ xi' (ref_ x) ]) in
  let proof = eq_refl_ in
  pure @@ lemma_ (varLRen'Fun_ sort) (scopeBinders @ [binder1_ ~btype:(varT m') x ]) ret proof

let genLemmaInstId sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_fext (instIdFun_ sort) in
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

let genLemmaInstId' sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_no_fext (instId'Fun_ sort) in
  let* v = V.genVariables sort [ `MS ] in
  let [@warning "-8"] [], [ ms ], [], scopeBinders = v in
  let* substSorts = substOf sort in
  let* vars = mk_var_apps sort ms in
  let s = VarState.tfresh "s" in
  let ret = eq_ (app_ref (subst_ sort) (vars @ [ ref_ s ])) (ref_ s) in
  let proof = app_ref (idSubst_ sort) (vars
                                       @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                       @ [ ref_ "s" ]) in
  pure @@ lemma_ (instId'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(app_sort sort ms) s ]) ret proof

let genLemmaRinstId sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_fext (rinstIdFun_ sort) in
  let* (ms, bms) = introScopeVar "m" sort in
  let* substSorts = substOf sort in
  let* vars = mk_var_apps sort ms in
  let ret = eq_
      (app_fix ~expl:true (ren_ sort) ~sscopes:[ms; ms] (List.map (const id_) substSorts))
      id_ in
  let proof = eqTrans_
      (app_ref (rinstInstFun_ sort) (List.map (const (app_id_ underscore_)) substSorts))
      (ref_ (instIdFun_ sort)) in
  pure @@ lemma_ (rinstIdFun_ sort) bms ret proof

let genLemmaRinstId' sort =
  (* register lemma for asimpl *)
  let* () = tell_rewrite_no_fext (rinstId'Fun_ sort) in
  let* v = V.genVariables sort [ `MS ] in
  let [@warning "-8"] [], [ ms ], [], scopeBinders = v in
  let* substSorts = substOf sort in
  let* vars = mk_var_apps sort ms in
  let ids = List.map (const id_) substSorts in
  let s = VarState.tfresh "s" in
  let t = VarState.tfresh "t" in
  let ret = eq_ (app_ref (ren_ sort) (ids @ [ ref_ s ])) (ref_ s) in
  (* a.d. I think this is the only instance of rewriting used. Can probably also be done without but it makes it much easier. *)
  let proof = app_ref "eq_ind_r" [ abs_ref t (eq_ (ref_ t) (ref_ s))
                                 ; app_ref (instId'Fun_ sort) [ ref_ s ]
                                 ; app_ref (rinstInst'Fun_ sort) (ids @ [ ref_ s ]) ] in
  pure @@ lemma_ (rinstId'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(app_sort sort ms) s ]) ret proof


let genLemmaCompRenRen sort =
  (* register lemmas for asimpl *)
  let* () = tell_rewrite_base (renRen_ sort) in
  let* () = tell_rewrite_fext (renRen'_ sort) in
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms ], [ xis; zetas ], scopeBinders = v in
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

let genLemmaCompSubstRen sort =
  (* register lemmas for asimpl *)
  let* () = tell_rewrite_base (substRen_ sort) in
  let* () = tell_rewrite_fext (substRen'_ sort) in
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `ZETAS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; zetas ], scopeBinders = v in
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
                        (app_ref (substRen_ sort)
                           (sty_terms sigmas
                            @ sty_terms zetas
                            @ [ ref_ "n" ]))) in
  pure (lemma_ (substRen_ sort) (scopeBinders
                                @ [ binder1_ ~btype:(app_sort sort ms) s ])
          ret proof,
        lemma_ (substRen'_ sort) scopeBinders ret' proof')

let genLemmaCompRenSubst sort =
  (* register lemmas for asimpl *)
  let* () = tell_rewrite_base (renSubst_ sort) in
  let* () = tell_rewrite_fext (renSubst'_ sort) in
  let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms ], [ xis; taus ], scopeBinders = v in
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
                        (app_ref (renSubst_ sort)
                           (sty_terms xis
                            @ sty_terms taus
                            @ [ref_ "n"]))) in
  pure (lemma_ (renSubst_ sort) (scopeBinders
                                @ [ binder1_ ~btype:(app_sort sort ms) s ])
          ret proof,
        lemma_ (renSubst'_ sort) scopeBinders ret' proof')

let genLemmaCompSubstSubst sort =
  (* register lemmas for asimpl *)
  let* () = tell_rewrite_base (substSubst_ sort) in
  let* () = tell_rewrite_fext (substSubst'_ sort) in
  let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `TAUS (`KS, `LS) ] in
  let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; taus ], scopeBinders = v in
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
                        (app_ref (substSubst_ sort)
                           (sty_terms sigmas
                            @ sty_terms taus
                            @ [ref_ "n"]))) in
  pure (lemma_ (substSubst_ sort) (scopeBinders
                                 @ [ binder1_ ~btype:(app_sort sort ms) s ])
          ret proof,
        lemma_ (substSubst'_ sort) scopeBinders ret' proof')

(** This function delegates to all the different code generation functions and in the end
 ** aggregates all the returned vernacular commands. *)
let gen_code sorts upList =
  (* GENERATE INDUCTIVE TYPES *)
  let* def_sorts = a_filter isDefinable sorts in
  let* inductive = match def_sorts with
    | [] -> pure (Vernac [])
    | l -> map inductive_ (a_map genBody def_sorts) in
  (* GENERATE CONGRUENCE LEMMAS *)
  let* congruences = a_concat_map genCongruences sorts in
  (* a.d. DONE if one sort in a component has a non-zero substitution vector, all of them have?
   * Yes, if the component has only one sort, the statement is trivial
   * if the component has two or more sorts, then each sort's subsitution vector contains at least the other sorts fo the component. *)
  let* has_binders = map list_nempty (substOf (List.hd sorts)) in
  if not has_binders
  (* return early and don't generate anything else *)
  then pure { ren_subst_units = inductive :: congruences
            ; allfv_units = []
            ; fext_units = []
            ; interface_units = [] }
  else
    (*  *)
    let* is_rec = isRecursive sorts in
    let mk_fixpoint = function
      | [] -> []
      | fix_exprs -> [fixpoint_ ~is_rec fix_exprs] in
    (* specialized monadic mapping functions
     * there are lemmas that we only generate if the component is recursive (or only if it's not recursive)
     * and there are lemmas we generte in both cases.
     * So this seems like the best way. *)
    let* is_ren = hasRenamings (List.hd sorts) in
    let guard_map ?(invert=false) f input =
      if (invert <> is_ren)
      then a_map f input
      else pure [] in
    let guard_split_map f input =
      if is_ren
      then a_split_map f input
      else pure ([], []) in
    (* GENERATE RENAMINGS *)
    let* upRen = guard_map genUpRen upList in
    let* renamings = guard_map genRenaming sorts in
    (* GENERATE UPs *)
    let* ups = guard_map genUpS upList in
    let* upsNoRen = guard_map ~invert:true genUpS upList in
    (* GENERATE SUBSTITUTIONS *)
    let* substitutions = a_map genSubstitution sorts in
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
    (* TODO should this really come after compSubstSubst? *)
    let* upSubstSubstNoRen = guard_map ~invert:true genUpSubstSubstNoRen upList in
    let* compSubstSubst = a_map genCompSubstSubst sorts in
    (* Coincidence of Instantiation *)
    let* upRinstInst = guard_map genUpRinstInst upList in
    let* rinstInst = guard_map genRinstInst sorts in
    (* Lemmas for the rewriting system *)
    let* lemmaInstId_fext = a_map genLemmaInstId sorts in
    let* lemmaInstId = a_map genLemmaInstId' sorts in
    let* lemmaRinstId_fext = guard_map genLemmaRinstId sorts in
    let* lemmaRinstId = guard_map genLemmaRinstId' sorts in
    let* varSorts = a_filter isOpen sorts in
    let* lemmaVarL_fext = a_map genLemmaVarL varSorts in
    let* lemmaVarL = a_map genLemmaVarL' varSorts in
    let* lemmaVarLRen_fext = guard_map genLemmaVarLRen varSorts in
    let* lemmaVarLRen = guard_map genLemmaVarLRen' varSorts in
    let* lemmaRenSubst_fext = guard_map genLemmaRinstInst sorts in
    let* lemmaRenSubst = guard_map genLemmaRinstInst' sorts in
    let* lemmaCompRenRen, lemmaCompRenRenFext = guard_split_map genLemmaCompRenRen sorts in
    let* lemmaCompSubstRen, lemmaCompSubstRenFext = guard_split_map genLemmaCompSubstRen sorts in
    let* lemmaCompRenSubst, lemmaCompRenSubstFext = guard_split_map genLemmaCompRenSubst sorts in
    let* lemmaCompSubstSubst, lemmaCompSubstSubstFext = guard_split_map genLemmaCompSubstSubst sorts in
    (* Code for Allfv *)
    let* upAllfv = a_map genUpAllfv upList in
    let* allfvs = a_map genAllfv sorts in
    (* put the code in the respective modules *)
    let* gen_allfv = is_gen_allfv in
    let* gen_fext = is_gen_fext in
    pure { ren_subst_units = inductive :: congruences @
                             upRen @ mk_fixpoint renamings @
                             ups @ mk_fixpoint substitutions @ upsNoRen @
                             upId @ mk_fixpoint idLemmas @
                             extUpRen @ mk_fixpoint extRen @
                             extUp @ mk_fixpoint ext @
                             upRenRen @ mk_fixpoint compRenRen @
                             upRenSubst @ mk_fixpoint compRenSubst @
                             upSubstRen @ mk_fixpoint compSubstRen @
                             upSubstSubst @ mk_fixpoint compSubstSubst @ upSubstSubstNoRen @
                             upRinstInst @ mk_fixpoint rinstInst @
                             lemmaCompRenRen @ lemmaCompSubstRen @
                             lemmaCompRenSubst @ lemmaCompSubstSubst @
                             lemmaRenSubst @
                             lemmaInstId @ lemmaRinstId @
                             lemmaVarL @ lemmaVarLRen;
           allfv_units = guard gen_allfv (upAllfv @ mk_fixpoint allfvs);
           fext_units = guard gen_fext (lemmaRenSubst_fext @
                                        lemmaInstId_fext @ lemmaRinstId_fext @
                                        lemmaVarL_fext @ lemmaVarLRen_fext @
                                        lemmaCompRenRenFext @ lemmaCompSubstRenFext @
                                        lemmaCompRenSubstFext @ lemmaCompSubstSubstFext);
           interface_units = [] }
