open Base
open Util

module H = Hsig
open Monads.RE_Functions(SigM)
open SigM.Syntax
open SigM
open CoqSyntax
open Tactics
open Custom

let guard cond lst =
  if cond then lst else []
let m_guard cond mlst =
  if cond then mlst else pure []

let createBinders = List.map ~f:(fun p -> BinderNameType ([fst p],TermId (snd p)))

let createImpBinders = List.map ~f:(fun p -> BinderImplicitNameType ([fst p], TermId (snd p)))

let rec genArg sort n bs = function
  (* lift! *)
  | H.Atom y -> map2 idApp (complete_ y) (map sty_terms (castUpSubst sort bs y n))
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
  let* (n,b) = introScopeVar "n" sort in
  let* varCons = genVar sort n in
  let* constrs = a_map (genConstr sort n) cs in
  pure @@ InductiveBody (sort, explicit_ b, TermSort Type, varCons @ constrs)

let genCongruence sort H.{ cparameters; cname; cpositions } =
  let* (m, bm) = introScopeVar "m" sort in
  let s = getPattern "s" cpositions in
  let t = getPattern "t" cpositions in
  let bs s = a_map (fun (s, H.{binders; head}) ->
                         let* arg_type = genArg sort m binders head in
                         pure @@ BinderImplicitNameType ([s], arg_type))
      (list_zip s cpositions) in
  let* bes = bs s in
  let* bt = bs t in
  let bparameters = createImpBinders cparameters in
  let parameters' = List.(map ~f:(fun x -> TermId x) (map ~f:fst cparameters)) in
  let eqs = List.map2_exn ~f:(fun x f -> TermEq (x, f)) (List.map ~f:(fun x -> TermId x) s) (List.map ~f:(fun x -> TermId x) t) in
  let eq = TermEq (idApp cname (sty_terms m @ parameters' @ List.map ~f:(fun x -> TermId x) s), idApp cname (sty_terms m @ parameters' @ List.map ~f:(fun x -> TermId x) t)) in
  let beqs = List.mapi ~f:(fun n s -> BinderNameType (["H" ^ Int.to_string n], s)) eqs in
  pure @@ Lemma (congr_ cname, bparameters @ bm @ bes @ bt @ beqs, eq, ProofString "congruence")

let genCongruences x =
  let* ctrs = constructors x in
  a_map (genCongruence x) ctrs

(* TODO this function seems to be the main function that generates the proof term for all the lemmas which traverse one of our inductive types. How does it work *)
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
  let (m, bm) = introScopeVarS "m" in
  let (n, bn) = introScopeVarS "n" in
  let (xi, bxi) = genRenS "xi" (m, n) in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let n' = succ_ n sort binder in
  pure @@ Definition (upRen_ sort binder, bpms @ bm @ bn @ bxi, Some (renT m' n'), up_ren_ sort xi binder)

let genRenaming sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* (ns, bns) = introScopeVar "n" sort in
  let* (xis, bxis) = genRen sort "xi" (ms, ns) in
  (* DONE what is the result of toVar here?\
   * when I call it with sort=tm, xi=[xity;xivl] I get this weird error term that toVar constructs. This is then probably ignored by some similar login in the traversal. Seems brittle.
   * When I call it instead with sort=vl I get xivl. So it seems get the renaming of the sort that I'm currently inspecting *)
  let* toVarT = toVar sort xis in
  traversal sort ms ren_ id (const @@ idApp sort (sty_terms ns)) (bms @ bns @ bxis) [xis]
    (fun s -> TermApp (var sort ns, [TermApp (toVarT, [s])]))
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
  | Single y -> TermApp (var x m, [varZero_])
  | BinderList (p, y) -> idApp "zero_p" [TermId p] >>> var x m

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
  let (m, bm) = introScopeVarS "m" in
  let* (ns, bns) = introScopeVar "n" sort in
  let (sigma, b_sigma) = genSubstS "sigma" (m, ns) sort in
  let* sigma = upSubstT binder sort ns sigma in
  let (_, bpms) = bparameters binder in
  let m' = succ_ m sort binder in
  let* n' = upSubst sort [binder] ns in
  pure @@ Definition (up_ sort binder, bpms @ bm @ bns @ b_sigma, Some (substT m' n' sort), sigma)

let genSubstitution sort =
  let* (m, bm) = introScopeVar "m" sort in
  let* (n, bn) = introScopeVar "n" sort in
  let* (sigma, bs) = genSubst sort "sigma" (m, n) in
  let* toVarT = toVar sort sigma in
  traversal sort m subst_ id (const @@ idApp sort (sty_terms n)) (bm @ bn @ bs) [sigma]
    (fun s -> TermApp (toVarT, [s]))
    (fun pms c s -> idApp c (sty_terms n @ List.map ~f:(fun x -> TermId x) pms @ s)) map_

let genSubstitutions sorts =
  let* fs = a_map genSubstitution sorts in
  let* r = isRecursive [List.hd_exn sorts] in
  pure @@ Fixpoint (r, fs)

let genUpId (binder, sort) =
  let* (m, bm) = introScopeVar "m" sort in
  (* TODO why is m converted to a variable here? *)
  let* m_var = toVar sort m in
  let (sigma, b_sigma) = genSubstS "sigma" (m_var, m) sort in
  let (eq, b_eq) = genEq "Eq" sigma (var sort m) in
  let n = VarState.tfresh "n" in
  let* m = upSubst sort [binder] m in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_ (idApp (up_ sort binder) (pms @ [sigma])) (var sort m) in
  let* shift = patternSId sort binder in
  (* TODO when does something with substitions not have renamings (ask kathrin) *)
  let* hasRen = hasRenamings sort in
  let t n = ap_ [idApp (if hasRen then ren_ sort else subst_ sort) shift; TermApp (eq, [n])] in
  let u = match binder with
    | H.Single z' -> if String.(sort = z') then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
    | Hsig.BinderList (_, z') -> if String.(sort = z') then idApp "scons_p_eta" [var sort m; TermAbs ([BinderName n], t (TermId n)); TermAbs ([BinderName n], eq_refl_)] else t (TermId n) in
  pure @@ Definition (upId_ sort binder, bpms @ bm @ b_sigma @ b_eq, Some ret, TermAbs ([BinderName n], u))

let genIdLemma sort =
  let* (m, bm) = introScopeVar "m" sort in
  let* (sigma, bs) = genSubst sort "sigma" (m, m) in
  let* susbstSorts = substOf sort in
  let* eqs' = a_map (fun y -> map2 idApp (pure @@ var_ y) (map sty_terms (castSubst sort y m))) susbstSorts in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigma) eqs' (fun x y s -> pure @@ idApp (upId_ x y) [TermUnderscore; s]) (* TODO kathrin, generate ID in a sensible way *) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (idApp (subst_ sort) (sty_terms sigma @ [s]), s) in
  traversal sort m idSubst_ (fun s -> TermApp (eq_refl_, [s])) ret (bm @ bs @ beqs) [sigma; eqs]
    (fun s -> TermApp (toVarT, [s]))
    (fun pms c cs -> idApp (congr_ c) cs) mapId_

(* let genUpExt binder sort xi_sigma zeta_tau
 *   let* (m, bm) = introScopeVarS "m" in
 *   let* (n, bn) = introScopeVarS "n" in *)

let genUpExtRen (binder, sort) =
  let (m, bm) = introScopeVarS "m" in
  let (n, bn) = introScopeVarS "n" in
  let (xi, bxi) = genRenS "xi" (m, n) in
  let (zeta, bzeta) = genRenS "zeta" (m, n) in
  let (eq, b_eq) = genEq "Eq" xi zeta in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_ (idApp (upRen_ sort binder) (pms @ [xi])) (idApp (upRen_ sort binder) (pms @ [zeta])) in
  let n = VarState.tfresh "n" in
  let t n = TermApp (eq, [n]) in
  let s = matchFin_ (TermId n) (fun n -> ap_ [shift_; t n]) eq_refl_ in
  let u = match binder with
    | H.Single z' -> if String.(sort = z') then s else t (TermId n)
    | H.BinderList (p, z') -> if String.(sort = z') then idApp "scons_p_congr" [
        TermAbs ([BinderName "n"], eq_refl_);
        TermAbs ([BinderName "n"], ap_ [idApp "shift_p" [TermId p]; t (TermId "n")])
      ]
      else t (TermId n) in
  pure @@ Definition (upExtRen_ sort binder, bpms @ bm @ bn @ bxi @ bzeta @ b_eq, Some ret, TermAbs ([BinderName "n"], u))

let genExtRen sort =
  let* (m, bm) = introScopeVar "m" sort in
  let* (n, bn) = introScopeVar "n" sort in
  let* (xi, bxi) = genRen sort "xi" (m, n) in
  let* (zeta, bzeta) = genRen sort "zeta" (m, n) in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms xi) (sty_terms zeta) (fun x y s -> pure @@ idApp (upExtRen_ x y) [TermUnderscore; TermUnderscore; s]) (* TODO kathrin Shouldn't this want SubsttTy instead of Terms? *) in
  let ret s = TermEq (idApp (ren_ sort) (sty_terms xi @ [s]), idApp (ren_ sort) (sty_terms zeta @ [s])) in
  let* toVarT = toVar sort eqs in
  traversal sort m extRen_ (fun s -> TermApp (eq_refl_, [s])) ret (bm @ bn @ bxi @ bzeta @ beqs) [xi; zeta; eqs]
    (fun z -> ap_ [var sort n; TermApp (toVarT, [z])])
    (fun _ c cs -> idApp (congr_ c) cs)
    mapExt_

let genUpExt (binder, sort) =
  let (m, bm) = introScopeVarS "m" in
  let* (ns, bns) = introScopeVar "n" sort in
  let (sigma, bsigma) = genSubstS "sigma" (m, ns) sort in
  let (tau, btau) = genSubstS "tau" (m, ns) sort in
  let (eq, b_eq) = genEq "Eq" sigma tau in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_ (idApp (up_ sort binder) (pms @ [sigma])) (idApp (up_ sort binder) (pms @ [tau])) in
  let* shift = patternSId sort binder in
  let n = VarState.tfresh "n" in
  let* hasRen = hasRenamings sort in
  let t n = ap_ [idApp (if hasRen then ren_ sort else subst_ sort) shift; TermApp (eq, [n])] in
  let u = match binder with
    | H.Single z' -> if String.(sort = z') then matchFin_ (TermId n) t eq_refl_ else t (TermId n)
    | H.BinderList (_, z') -> if String.(sort = z') then idApp "scons_p_congr" [
        TermAbs ([BinderName "n"], eq_refl_);
        TermAbs ([BinderName "n"], (t (TermId "n")))
      ] else t (TermId n) in
  pure @@ Definition (upExt_ sort binder, bpms @ bm @ bns @ bsigma @ btau @ b_eq, Some ret, TermAbs ([BinderName "n"], u))

(* TODO this and genExtRen could be one function *)
let genExt sort =
  let* (ms, bms) = introScopeVar "m" sort in
  let* (ns, bns) = introScopeVar "n" sort in
  let* (sigmas, bsigmas) = genSubst sort "sigma" (ms, ns) in
  let* (taus, btaus) = genSubst sort "tau" (ms, ns) in
  let* substSorts = substOf sort in
  let* (eqs, beqs) = genEqs sort "Eq" (sty_terms sigmas) (sty_terms taus) (fun x y s -> pure @@ idApp (upExt_ x y) [TermUnderscore; TermUnderscore; s]) (* TODO kathrin Shouldn't this want SubsttTy instead of Terms? *) in
  let ret s = TermEq (idApp (subst_ sort) (sty_terms sigmas @ [s]), idApp (subst_ sort) (sty_terms taus @ [s])) in
  let* toVarT = toVar sort eqs in
  traversal sort ms ext_ (fun s -> TermApp (eq_refl_, [s])) ret (bms @ bns @ bsigmas @ btaus @ beqs) [sigmas; taus; eqs]
    (* The following line is the only one structurally different from genExtRen. It also had this TODO from kathrin:  I didn't need the renaming case for Up. Dive into that.*)
    (fun z -> TermApp (toVarT, [z]))
    (fun _ c cs -> idApp (congr_ c) cs)
    mapExt_

let genUpRenRen (binder, sort) =
  let (k, bk) = introScopeVarS "k" in
  let (l, bl) = introScopeVarS "l" in
  let (m, bm) = introScopeVarS "m" in
  let (xi, bxi) = genRenS "xi" (k, l) in
  let (tau, btau) = genRenS "tau" (l, m) in
  let (theta, btheta) = genRenS "theta" (k, m) in
  let (eq, beq) = genEq "Eq" (xi >>> tau) theta in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_ (idApp (upRen_ sort binder) (pms @ [xi]) >>> idApp (upRen_ sort binder) (pms @ [tau])) (idApp (upRen_ sort binder) (pms @ [theta])) in
  let u = match binder with
    | H.Single z' -> if String.(sort = z') then idApp up_ren_ren_ [xi; tau; theta; eq] else eq
    | H.BinderList (_, z') -> if String.(sort = z') then idApp "up_ren_ren_p" [eq] else eq in
  pure @@ Definition (up_ren_renName_ sort binder, bpms @ bk @ bl @ bm @ bxi @ btau @ btheta @ beq, Some ret, u)

let genCompRenRen sort =
  let* (ks, bks) = introScopeVar "k" sort in
  let* (ls, bls) = introScopeVar "l" sort in
  let* (ms, bms) = introScopeVar "m" sort in
  let* (xi, bxi) = genRen sort "xi" (ms, ks) in
  let* (zeta, bzeta) = genRen sort "zeta" (ks, ls) in
  let* (rho, brho) = genRen sort "rho" (ms, ls) in
  let* (eqs, beqs) = genEqs sort "Eq" (List.map2_exn ~f:(>>>) (sty_terms xi) (sty_terms zeta)) (sty_terms rho) (fun x y s -> pure @@ match y with
    | H.Single z -> if String.(z = x) then idApp up_ren_ren_ [TermUnderscore; TermUnderscore; TermUnderscore; s] else s
    | H.BinderList (_, z) -> if String.(z = x) then idApp "up_ren_ren_p" [s] else s) in
  (* TODO in cases like this where we pass the toVarT to something in the traversal we should really rather do that in the function below where it's used. So that we don't call toVarT on the wrong arguments *)
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (idApp (ren_ sort) (sty_terms zeta @ [idApp (ren_ sort) @@ sty_terms xi @ [s]]), idApp (ren_ sort) (sty_terms rho @ [s])) in
  traversal sort ms compRenRen_ (fun s -> TermApp (eq_refl_, [s])) ret (bks @ bls @ bms @ bxi @ bzeta @ brho @ beqs) [xi; zeta; rho; eqs]
    (fun n -> ap_ [var sort ls; TermApp (toVarT, [n])])
    (fun _ c xs -> idApp (congr_ c) xs)
    mapComp_

(* TODO move this somewhere else and also use in other definitions *)
let definitionBody (singleMatch, singleNoMatch) f_listMatch sort = function
  | H.Single sort' -> if String.(sort = sort') then singleMatch else singleNoMatch
  | H.BinderList (p, sort') ->
    let (listMatch, listNoMatch) = f_listMatch p sort' in
    if String.(sort = sort') then listMatch else listNoMatch

let genUpRenSubst (binder, sort) =
  let (k, bk) = introScopeVarS "k" in
  let (l, bl) = introScopeVarS "l" in
  let* (ms, bms) = introScopeVar "m" sort in
  let (xi, bxi) = genRenS "xi" (k, l) in
  let (tau, btau) = genSubstS "tau" (l, ms) sort in
  let (theta, btheta) = genSubstS "theta" (k, ms) sort in
  (* TODO was this also unused in Haskell? *)
  (* let* m_var = toVar sort ms in *)
  let (eq, beq) = genEq "Eq" (xi >>> tau) theta in
  let n = VarState.tfresh "n" in
  (* TODO here I might understand what upSubst does *)
  let* ms = upSubst sort [binder] ms in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_ (idApp (upRen_ sort binder) (pms @ [xi]) >>> idApp (up_ sort binder) (pms @ [tau])) (idApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let t n = ap_ [idApp (ren_ sort) shift; TermApp (eq, [n])] in
  let s = eqTrans_ (scons_p_comp' (TermId n))
      (scons_p_congr_ (TermAbs ([BinderName "z"],
                                eqTrans_ (scons_p_tail' (TermApp (xi, [TermId "z"])))
                                  (t (TermId "z"))))
         (TermAbs ([BinderName "z"], scons_p_head' (TermId "z")) )) in
  let defBody = definitionBody (matchFin_ (TermId n) t eq_refl_, t (TermId n)) (fun _ _ -> (s, t (TermId n))) sort binder in
  pure @@ Definition (up_ren_subst_ sort binder, bpms @ bk @ bl @ bms @ bxi @ btau @ btheta @ beq, Some ret, TermAbs ([BinderName "n"], defBody))

let genCompRenSubst sort =
  let* (ks, bks) = introScopeVar "k" sort in
  let* (ls, bls) = introScopeVar "l" sort in
  let* (ms, bms) = introScopeVar "m" sort in
  let* (xis, bxis) = genRen sort "xi" (ms, ks) in
  let* (zetas, bzetas) = genRen sort "zeta" (ks, ls) in
  let* (rhos, brhos) = genRen sort "rho" (ms, ls) in
  let* (eqs, beqs) = genEqs sort "Eq" (List.map2_exn ~f:(>>>) (sty_terms xis) (sty_terms zetas)) (sty_terms rhos) (fun x y s -> pure @@ idApp (up_ren_subst_ x y) [TermUnderscore; TermUnderscore; TermUnderscore; s]) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (
      idApp (subst_ sort) (sty_terms zetas @ [idApp (ren_ sort) (sty_terms xis @ [s])]),
      idApp (subst_ sort) (sty_terms rhos @ [s])) in
  traversal sort ms compRenSubst_ (fun s -> TermApp (eq_refl_, [s])) ret (bks @ bls @ bms @ bxis @ bzetas @ brhos @ beqs) [xis; zetas; rhos; eqs]
    (fun n -> TermApp (toVarT, [n]))
    (fun _ c xs -> idApp (congr_ c) xs)
    mapComp_

let genUpSubstRen (binder, sort) =
  let (k, bk) = introScopeVarS "k" in
  let* (ls, bls) = introScopeVar "l" sort in
  let* (ms, bms) = introScopeVar "m" sort in
  let (sigma, bsigma) = genSubstS "sigma" (k, ls) sort in
  let* (zetas, bzetas) = genRen sort "zeta" (ls, ms) in
  let (theta, btheta) = genSubstS "theta" (k, ms) sort in
  let (eq, beq) = genEq "Eq" (sigma >>> idApp (ren_ sort) (sty_terms zetas)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* substSorts = substOf sort in
  let* zetas' = upSubst sort [binder] zetas in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_ (idApp (up_ sort binder) (pms @ [sigma]) >>> idApp (ren_ sort) (sty_terms zetas')) (idApp (up_ sort binder) (pms @ [theta])) in
  let* shift = patternSId sort binder in
  let t n = eqTrans_ (idApp (compRenRen_ sort) (pat @ sty_terms zetas' @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat @ [ TermApp (sigma, [n])]))
                (eqTrans_ (eqSym_ (idApp (compRenRen_ sort) (sty_terms zetas @ pat @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat @ [ TermApp (sigma, [n])])))
                   (ap_ [idApp (ren_ sort) pat; TermApp (eq, [n])])) in
  let t' n z' = eqTrans_ (idApp (compRenRen_ sort) (pat @ sty_terms zetas' @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat @ List.map ~f:(fun x -> (TermAbs ([BinderName "x"], (if String.(x = z') then  scons_p_tail' (TermId "x") else eq_refl_)))) substSorts @ [ TermApp (sigma, [n])]))
                (eqTrans_ (eqSym_ (idApp (compRenRen_ sort) (sty_terms zetas @ pat @ List.map2_exn ~f:(>>>) (sty_terms zetas) pat @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat @ [ TermApp (sigma, [n])])))
                (ap_ [idApp (ren_ sort) pat; TermApp (eq, [n])])) in
  let hd = TermAbs ([BinderName "x"], (ap_ [var sort ms; scons_p_head' (TermId "x")])) in
  let defBody = definitionBody (matchFin_ (TermId n) t eq_refl_, t (TermId n))
      (fun _ sort' -> (eqTrans_ (scons_p_comp' (TermId "n")) (scons_p_congr_  (TermAbs ([BinderName "n"], (t' (TermId "n") sort'))) hd), t' (TermId n) sort')) sort binder in
  pure @@ Definition (up_subst_ren_ sort binder, bpms @ bk @ bls @ bms @ bsigma @ bzetas @ btheta @ beq, Some ret, TermAbs ([BinderName "n"], defBody))

let genCompSubstRen sort =
  let* (ks, bks) = introScopeVar "k" sort in
  let* (ls, bls) = introScopeVar "l" sort in
  let* (ms, bms) = introScopeVar "m" sort in
  let* (sigmas, bsigmas) = genSubst sort "sigma" (ms,ks) in
  let* (zetas, bzetas) = genRen sort "zeta" (ks,ls) in
  let* (thetas, bthetas) = genSubst sort "theta" (ms, ls) in
  let* substSorts = substOf sort in
  let* sigmazeta = a_map (fun (substSort, sigma) ->
      let* zetas' = castSubst sort substSort zetas in
      pure (sigma >>> idApp (ren_ substSort) (sty_terms zetas'))) (list_zip substSorts (sty_terms sigmas)) in
  let* (eqs, beqs) = genEqs sort "Eq" sigmazeta (sty_terms thetas) (fun z y s ->
      (* let* sigmas' = toVar z sigmas in *)
      let* zetas' = castSubst sort z zetas in
      (* let* thetas' = toVar z thetas in *)
      pure @@ idApp (up_subst_ren_ z y) ([TermUnderscore] @ List.map ~f:(const TermUnderscore) (sty_terms zetas') @ [TermUnderscore; s])) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (idApp (ren_ sort) (sty_terms zetas @ [idApp (subst_ sort) (sty_terms sigmas @ [s])]), idApp (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstRen_ (fun s -> TermApp (eq_refl_, [s])) ret (bks @ bls @ bms @ bsigmas @ bzetas @ bthetas @ beqs) [sigmas; zetas; thetas; eqs]
                  (fun n -> TermApp (toVarT, [n]))
                  (fun _ c xs -> idApp (congr_ c) xs)
                  mapComp_

let genUpSubstSubst (binder, sort) =
  let (k, bk) = introScopeVarS "k" in
  let* (ls, bls) = introScopeVar "l" sort in
  let* (ms, bms) = introScopeVar "m" sort in
  let (sigma, bsigma) = genSubstS "sigma" (k, ls) sort in
  let* (taus, btaus) = genSubst sort "tau" (ls, ms) in
  let (theta, btheta) = genSubstS "theta" (k, ms) sort in
  let (eq, beq) = genEq "Eq" (sigma >>> idApp (subst_ sort) (sty_terms taus)) theta in
  let n = VarState.tfresh "n" in
  let* ms = upSubst sort [binder] ms in
  let* ls' = upSubst sort [binder] ls in
  let* taus' = upSubst sort [binder] taus in
  let* pat = patternSId sort binder in
  let (pms, bpms) = binvparameters binder in
  let ret = equiv_ (idApp (up_ sort binder) (pms @ [sigma]) >>> idApp (subst_ sort) (sty_terms taus'))
      (idApp (up_ sort binder) (pms @ [theta])) in
  (* TODO why is this the same as pat? *)
  let* shift = patternSId sort binder in
  let* substSorts = substOf sort in
  let* pat' = a_map (fun (substSort, tau) ->
      let* p' = castSubst sort substSort (SubstSubst pat) in
      pure (tau >>> (idApp (ren_ substSort) (sty_terms p')))) (list_zip substSorts (sty_terms taus)) in
  let t n = eqTrans_ (idApp (compRenSubst_ sort) (pat @ sty_terms taus' @ List.map2_exn ~f:(>>>) pat (sty_terms taus') @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat @ [TermApp (sigma, [n])]))
      (eqTrans_ (eqSym_ (idApp (compSubstRen_ sort) (sty_terms taus @ pat @ pat' @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat @ [TermApp (sigma, [n])])))
                (ap_ [(idApp (ren_ sort) pat); TermApp (eq, [n])])) in
  let t' n z' = eqTrans_ (idApp (compRenSubst_ sort) (pat @ sty_terms taus' @ List.map2_exn ~f:(>>>) pat (sty_terms taus') @ List.map ~f:(const (TermAbs ([BinderName "x"], eq_refl_))) pat @ [TermApp (sigma, [n])]))
      (eqTrans_ (eqSym_ (idApp (compSubstRen_ sort) (sty_terms taus @ pat @ List.map ~f:(const TermUnderscore) pat' @ List.map ~f:(fun substSort -> TermAbs ([BinderName "x"], eqSym_ (if String.(substSort = z') then scons_p_tail' (TermId "x") else eq_refl_))) substSorts @ [TermApp (sigma, [n])])))
         (ap_ [idApp (ren_ sort) pat; TermApp (eq, [n])])) in
  let hd = TermAbs ([BinderName "x"], idApp "scons_p_head'" [TermUnderscore; TermAbs ([BinderName "z"], idApp (ren_ sort) (shift @ [TermUnderscore])); TermId "x"]) in
  let defBody = definitionBody (matchFin_ (TermId n) t eq_refl_ , t (TermId n))
      (fun p sort' -> (eqTrans_ (idApp "scons_p_comp'" [idApp "zero_p" [TermId p] >>> (var sort ls'); TermUnderscore; TermUnderscore; TermId "n"]) (scons_p_congr_  (TermAbs ([BinderName "n"], (t' (TermId "n") sort'))) hd), t' (TermId n) sort')) sort binder in
  pure @@ Definition (up_subst_subst_ sort binder, bpms @ bk @ bls @ bms @ bsigma @ btaus @ btheta @ beq, Some ret, TermAbs ([BinderName "n"], defBody))

let genCompSubstSubst sort =
  let* (ks, bks) = introScopeVar "k" sort in
  let* (ls, bls) = introScopeVar "l" sort in
  let* (ms, bms) = introScopeVar "m" sort in
  let* (sigmas, bsigmas) = genSubst sort "sigma" (ms, ks) in
  let* (taus, btaus) = genSubst sort "tau" (ks, ls) in
  let* (thetas, bthetas) = genSubst sort "theta" (ms, ls) in
  let* substSorts = substOf sort in
  let* sigmatau = a_map (fun (substSort, sigma) ->
      let* taus' = castSubst sort substSort taus in
      pure (sigma >>> idApp (subst_ substSort) (sty_terms taus'))) (list_zip substSorts (sty_terms sigmas)) in
  let* (eqs, beqs) = genEqs sort "Eq" sigmatau (sty_terms thetas) (fun z y s ->
      (* let* sigmas' = toVar z sigmas in *)
      let* taus' = castSubst sort z taus in
      (* let* theta' = toVar z thetas in *)
      pure @@ idApp (up_subst_subst_ z y) ([TermUnderscore] @ List.map ~f:(const TermUnderscore) (sty_terms taus') @ [TermUnderscore; s])) in
  let* toVarT = toVar sort eqs in
  let ret s = TermEq (idApp (subst_ sort) (sty_terms taus @ [idApp (subst_ sort) (sty_terms sigmas @ [s])]), idApp (subst_ sort) (sty_terms thetas @ [s])) in
  traversal sort ms compSubstSubst_ (fun s -> TermApp (eq_refl_, [s])) ret (bks @ bls @ bms @ bsigmas @ btaus @ bthetas @ beqs) [sigmas; taus; thetas; eqs]
    (fun n -> TermApp (toVarT, [n]))
    (fun _ c xs -> idApp (congr_ c) xs)
    mapComp_

let genCodeT xs dps upList' =
  (* TODO I suspect the dependencies can only happen with modular code *)
  let upList = if (List.is_empty dps) then upList' else [] in
  let* x_open = isOpen (List.hd_exn xs) in
  (* TODO don't we have a field for that in the signature? *)
  let* varSorts = a_filter isOpen xs in
  let* hasbinders = map (fun l -> l |> List.is_empty |> not) (substOf (List.hd_exn xs)) in
  let substSorts = xs in
  (* GENERATE INDUCTIVE TYPES *)
  (* TODO which types are not definable? *)
  let* ys = a_filter definable xs in
  let* types = a_map genBody ys in
  let* r = isRecursive xs in
  (* GENERATE CONGRUENCE LEMMAS *)
  let* congruences = a_map genCongruences xs in
  (* GENERATE RENAMINGS *)
  let* isRen = hasRenamings (List.hd_exn xs) in
  let* upRen = m_guard isRen @@ a_map genUpRenS upList in
  let* renamings = genRenamings substSorts in
  (* GENERATE UPs *)
  let* ups = m_guard isRen @@ a_map genUpS upList in
  (* TODO upsNoRen is the same as ups! I should be able to just remove it and the guard from ups *)
  let* upsNoRen = m_guard (not isRen) @@ a_map genUpS upList in
  (* GENERATE SUBSTITUTIONS *)
  let* substitutions = genSubstitutions substSorts in
  let* upId = a_map genUpId upList in
  let* idLemmas = a_map genIdLemma substSorts in
  (* GENERATE EXTENSIONALITY LEMMAS *)
  let* extUpRen = m_guard isRen @@ a_map genUpExtRen upList in
  let* extRen = m_guard isRen @@ a_map genExtRen substSorts in
  let* extUp = a_map genUpExt upList in
  let* ext = a_map genExt substSorts in
  (* GENERATE COMPOSITIONALITY LEMMAS *)
  let* upRenRen = m_guard isRen @@ a_map genUpRenRen upList in
  let* compRenRen = m_guard isRen  @@ a_map genCompRenRen substSorts in
  let* upRenSubst = m_guard isRen @@ a_map genUpRenSubst upList in
  let* compRenSubst = m_guard isRen @@ a_map genCompRenSubst substSorts in
  let* upSubstRen = m_guard isRen @@ a_map genUpSubstRen upList in
  let* compSubstRen = m_guard isRen @@ a_map genCompSubstRen substSorts in
  let* upSubstSubst = m_guard isRen @@ a_map genUpSubstSubst upList in
  let* compSubstSubst = a_map genCompSubstSubst substSorts in
  (* let* upSubstSubstNoRen = m_guard (not isRen) @@ a_map genUpSubstSubstNoRen upList in *)
  (* generation of the actual sentences *)
  pure @@ SentenceSection (String.concat xs,
                           [SentenceInductive (Inductive types)] @
                           List.(map ~f:sentencelemma (concat congruences)) @
                             (if not hasbinders then [] else
                                List.map ~f:sentencedefinition upRen @
                                (* List.map ~f:(fun x -> SentenceDefinition x) upRen @ *)
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
                                [SentenceFixpoint (Fixpoint (r, compSubstSubst))]
                             (* TODO tbd *))
  )
