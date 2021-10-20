open Tactics
open GallinaGen

module AL = AssocList

type scopeVar = [ `K | `L | `M | `N ]
type scopeVars = [ `KS | `LS | `MS | `NS ]
type renVar = [ `XI of scopeVar * scopeVar | `ZETA of scopeVar * scopeVar | `RHO of scopeVar * scopeVar ]
type renVars = [ `XIS of scopeVars * scopeVars | `ZETAS of scopeVars * scopeVars | `RHOS of scopeVars * scopeVars ]
type substVar = [ `SIGMA of scopeVar * scopeVars  | `TAU of scopeVar * scopeVars  | `THETA of scopeVar * scopeVars ]
type substVars = [ `SIGMAS of scopeVars * scopeVars  | `TAUS of scopeVars * scopeVars  | `THETAS of scopeVars * scopeVars ]

(** Polymorphic Variants are a nice way of specifying that all of `K, `KS, `XI (`K, `L) are
 ** variables but that inside `XI, `SIGMA, ... I can only use the scope variables `K, `KS, ...
 ** without having to resort to extra constructors. *)
type vars = [ scopeVar | scopeVars | renVar | renVars | substVar | substVars ]

let showVar = function
  | `K | `KS -> "k" | `L | `LS -> "l" | `M | `MS -> "m" | `N | `NS -> "n"
  | `XI _ | `XIS _ -> "xi"
  | `ZETA _ | `ZETAS _ -> "zeta"
  | `RHO _ | `RHOS _ -> "rho"
  | `SIGMA _ | `SIGMAS _ -> "sigma"
  | `TAU _ | `TAUS _ -> "tau"
  | `THETA _ | `THETAS _ -> "theta"

(** The var_declaration list contains elements of the polymorphic variants.
 ** We then fold over the list and aggregate the generated scope variables.
 ** In general singular variables (like `K, `SIGMA) are represented as constr_expr values.
 ** And those written in plural (like `KS, `SIGMAS) are represented as substTy values. *)
let [@warning "-8"] genVariables sort (var_declarations: vars list) =
  let open RSEM.Syntax in
  let open RSEM in
  let genVariable ((simple_vars : (identifier, constr_expr) AL.t),
                   (sss: (identifier, ScopeTypes.substScope) AL.t),
                   (stys : (identifier, ScopeTypes.substTy) AL.t),
                   (binders : binder_expr list)) =
    function
      (`K | `L | `M | `N as s) ->
      let sn = showVar s in
      let (m, bm) = genScopeVar sn in
      (* let () = print_endline ("putting in (" ^ sn ^ "->" ^ (show_term m) ^ ")") in *)
      pure (AL.insert sn m simple_vars, sss, stys, binders @ bm)
    | (`KS | `LS | `MS | `NS as s) ->
      let sn = showVar s in
      let* (ms, bms) = genScopeVarVect sn sort in
      (* let () = print_endline ("putting in (" ^ sn ^ "->" ^ (show_term (TermSubst ms)) ^ ")") in *)
      pure (simple_vars, AL.insert sn ms sss, stys, binders @ bms)
    | (`XI (m, n) | `ZETA (m, n) | `RHO (m, n) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar m) ^ " and " ^ showVar n) in *)
      let m = AL.assoc_exn (showVar m) simple_vars in
      let n = AL.assoc_exn (showVar n) simple_vars in
      let (xi, bxi) = genRen sn (m, n) in
      pure (AL.insert sn xi simple_vars, sss, stys, binders @ bxi)
    | (`XIS (ms, ns) | `ZETAS (ms, ns) | `RHOS (ms, ns) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar ms) ^ " and " ^ showVar ns) in *)
      let ms = AL.assoc_exn (showVar ms) sss in
      let ns = AL.assoc_exn (showVar ns) sss in
      let* (xis, bxis) = genRenVect sn sort (ms, ns) in
      pure (simple_vars, sss, AL.insert sn xis stys, binders @ bxis)
    | (`SIGMA (m, ns) | `TAU (m, ns) | `THETA (m, ns) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar m) ^ " and " ^ showVar ns) in *)
      let m = AL.assoc_exn (showVar m) simple_vars in
      let ns = AL.assoc_exn (showVar ns) sss in
      let (sigma, bsigma) = genSubst sn sort (m, ns) in
      pure (AL.insert sn sigma simple_vars, sss, stys, binders @ bsigma)
    | (`SIGMAS (ms, ns) | `TAUS (ms, ns) | `THETAS (ms, ns) as s) ->
      let sn = showVar s in
      (* let () = print_endline ("retrieving " ^ (showVar ms) ^ " and " ^ showVar ns) in *)
      let ms = AL.assoc_exn (showVar ms) sss in
      let ns = AL.assoc_exn (showVar ns) sss in
      let* (sigmas, bsigmas) = genSubstVect sn sort (ms, ns) in
      pure (simple_vars, sss, AL.insert sn sigmas stys, binders @ bsigmas)
  in
  let* (simple_vars, sss, stys, binders) = m_fold_left ~f:genVariable ~init:(AL.from_list [], AL.from_list [], AL.from_list [], []) var_declarations in
  pure (List.rev_map snd (AL.to_list simple_vars),
        List.rev_map snd (AL.to_list sss),
        List.rev_map snd (AL.to_list stys),
        binders)
