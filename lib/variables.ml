open Base
open Tactics
open CoqSyntax
open Coqgen

module AL = AssocList

type scopeVar = [ `K | `L | `M | `N ]
type scopeVars = [ `KS | `LS | `MS | `NS ]
type renVar = [ `XI of scopeVar * scopeVar | `ZETA of scopeVar * scopeVar | `RHO of scopeVar * scopeVar ]
type renVars = [ `XIS of scopeVars * scopeVars | `ZETAS of scopeVars * scopeVars | `RHOS of scopeVars * scopeVars ]
type substVar = [ `SIGMA of scopeVar * scopeVars  | `TAU of scopeVar * scopeVars  | `THETA of scopeVar * scopeVars ]
type substVars = [ `SIGMAS of scopeVars * scopeVars  | `TAUS of scopeVars * scopeVars  | `THETAS of scopeVars * scopeVars ]

(* Polymorphic Variants are a nice way of specifying that all of `K, `KS, `XI (`K, `L) are
 * variables but that inside `XI, `SIGMA, ... I can only use the scope variables `K, `KS, ...
 * without having to resort to extra constructors. *)
type vars = [ scopeVar | scopeVars | renVar | renVars | substVar | substVars ]

let showVar = function
  | `K | `KS -> "k" | `L | `LS -> "l" | `M | `MS -> "m" | `N | `NS -> "n"
  | `XI _ | `XIS _ -> "xi"
  | `ZETA _ | `ZETAS _ -> "zeta"
  | `RHO _ | `RHOS _ -> "rho"
  | `SIGMA _ | `SIGMAS _ -> "sigma"
  | `TAU _ | `TAUS _ -> "tau"
  | `THETA _ | `THETAS _ -> "theta"

(** Mini DSL to generate scope/renaming/substitution variables
 ** the var_declaration list contains elements of the polymorphic variants *)
let [@warning "-8"] genVariables sort (var_declarations: vars list) =
  let open SigM.Syntax in
  let open SigM in
  let genVariable ((simple_vars : (identifier, constr_expr) AL.t), (stys : (identifier, substTy) AL.t), binders) =
    function
    (`K | `L | `M | `N as s) ->
      let sn = showVar s in
      let (m, bm) = introScopeVarS sn in
      (* let () = print_endline ("putting in (" ^ sn ^ "->" ^ (show_term m) ^ ")") in *)
      pure (AL.insert sn m simple_vars, stys, binders @ bm)
    | (`KS | `LS | `MS | `NS as s) ->
      let sn = showVar s in
      let* (ms, bms) = introScopeVar sn sort in
      (* let () = print_endline ("putting in (" ^ sn ^ "->" ^ (show_term (TermSubst ms)) ^ ")") in *)
      pure (simple_vars, AL.insert sn ms stys, binders @ bms)
    | (`XI (m, n) | `ZETA (m, n) | `RHO (m, n) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar m) ^ " and " ^ showVar n) in *)
      let m = AL.assoc_exn (showVar m) simple_vars in
      let n = AL.assoc_exn (showVar n) simple_vars in
      let (xi, bxi) = genRenS sn (m, n) in
      pure (AL.insert sn xi simple_vars, stys, binders @ bxi)
    | (`XIS (ms, ns) | `ZETAS (ms, ns) | `RHOS (ms, ns) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar ms) ^ " and " ^ showVar ns) in *)
      let ms = AL.assoc_exn (showVar ms) stys in
      let ns = AL.assoc_exn (showVar ns) stys in
      let* (xis, bxis) = genRen sort sn (ms, ns) in
      pure (simple_vars, AL.insert sn xis stys, binders @ bxis)
    | (`SIGMA (m, ns) | `TAU (m, ns) | `THETA (m, ns) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar m) ^ " and " ^ showVar ns) in *)
      let m = AL.assoc_exn (showVar m) simple_vars in
      let ns = AL.assoc_exn (showVar ns) stys in
      let (sigma, bsigma) = genSubstS sn (m, ns) sort in
      pure (AL.insert sn sigma simple_vars, stys, binders @ bsigma)
    | (`SIGMAS (ms, ns) | `TAUS (ms, ns) | `THETAS (ms, ns) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar ms) ^ " and " ^ showVar ns) in *)
      let ms = AL.assoc_exn (showVar ms) stys in
      let ns = AL.assoc_exn (showVar ns) stys in
      let* (sigmas, bsigmas) = genSubst sort sn (ms, ns) in
      pure (simple_vars, AL.insert sn sigmas stys, binders @ bsigmas)
  in
  let* (simple_vars, stys, binders) = m_fold_left ~f:genVariable ~init:(AL.from_list [], AL.from_list [], []) var_declarations in
  pure (List.rev_map ~f:snd (AL.to_list simple_vars),
        List.rev_map ~f:snd (AL.to_list stys),
        binders)

(* let test () =
 *   let open SigM.Syntax in
 *   let open SigM in
 *   let v = [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `ZETAS (`KS, `LS); `THETAS (`MS, `LS) ] in
 *   let* [ ks; ls; ms; sigmas; zetas; thetas ], varBinders as sdf = genVariables "tm" v in
 *   pure sdf
 *
 * let test2 () =
 *   let open SigM.Syntax in
 *   let open SigM in
 *   let v2 = [ `K; `LS; `MS; `SIGMA (`K, `LS); `ZETAS (`LS, `MS); `THETA (`K, `MS) ] in
 *   let* [ k; TermSubst ls; TermSubst ms; sigma; TermSubst zetas; theta ], varBinders as sdf = genVariables "vl" v2 in
 *   pure sdf *)


(* I want to call it like this
 * let v = [ `K; `L; `MS; `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ]
 * e.g. in genUpRenSubst. Since I return a variable number of terms I would need to use a list. Is this bad style? since it's static it seems to be not much of a problem because when it runs once it runs everytime. Since the generating functions for the scope variables sometimes return only SubstTy I would need to match on that, too. One more reason to abandon it. But when I use lists of terms instead of SubstTy I would also need to return a singleton list in the other cases and then I would need to match on those too.
 * let v = [ `K; `L; `MS; `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ]
 * let [ k; l; (TermSubst ms); xi; tau; theta ], varBinders = genVariables sort v
 *  *)
