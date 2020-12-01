open Base
open Tactics
open CoqSyntax
module AL = AssocList

type scopeVar = [ `K | `L | `M | `N ]
type scopeVars = [ `KS | `LS | `MS | `NS ]
type renVar = [ `XI of scopeVar * scopeVar | `ZETA of scopeVar * scopeVar | `RHO of scopeVar * scopeVar ]
type renVars = [ `XIS of scopeVars * scopeVars | `ZETAS of scopeVars * scopeVars | `RHOS of scopeVars * scopeVars ]
type substVar = [ `SIGMA of scopeVar * scopeVars  | `TAU of scopeVar * scopeVars  | `THETA of scopeVar * scopeVars ]
type substVars = [ `SIGMAS of scopeVars * scopeVars  | `TAUS of scopeVars * scopeVars  | `THETAS of scopeVars * scopeVars ]

type vars = [ scopeVar | scopeVars | renVar | renVars | substVar | substVars ]


let showVar = function
  | `K -> "k" | `L -> "l" | `M -> "m" | `N -> "n"
  | `KS -> "ks" | `LS -> "ls" | `MS -> "ms" | `NS -> "ns"
  | `XI _ -> "xi" | `ZETA _ -> "zeta" | `RHO _ -> "rho"
  | `XIS _ -> "xis" | `ZETAS _ -> "zetas" | `RHOS _ -> "rhos"
  | `SIGMA _ -> "sigma" | `TAU _ -> "tau" | `THETA _ -> "theta"
  | `SIGMAS _ -> "sigmas" | `TAUS _ -> "taus" | `THETAS _ -> "thetas"

(** Mini DSL to generate scope/renaming/substitution variables
 ** the var_declaration list contains elements of the polymorphic variants *)
let rec genVariables sort (var_declaration: vars list) =
  let open SigM.Syntax in
  let open SigM in
  let genVariable ((vars : (string * term) list), binders) =
    function
    (`K | `L | `M | `N as s) ->
      let sn = showVar s in
      let (m, bm) = introScopeVarS sn in
      (* let () = print_endline ("putting in (" ^ sn ^ "->" ^ (show_term x) ^ ")") in *)
      pure ((sn, m) :: vars, binders @ bm)
    | (`KS | `LS | `MS | `NS as s) ->
      let sn = showVar s in
      let* (ms, bms) = introScopeVar sn sort in
      pure ((sn, TermSubst ms) :: vars, binders @ bms)
    | (`XI (m, n) | `ZETA (m, n) | `RHO (m, n) as s) ->
      (* let () = print_endline ("retrieving " ^ (showVar x)) in *)
      let sn = showVar s in
      let m = AL.assoc_exn (showVar m) vars in
      let n = AL.assoc_exn (showVar n) vars in
      let (xi, bxi) = genRenS sn (m, n) in
      pure ((sn, xi) :: vars, binders @ bxi)
    | (`XIS (ms, ns) | `ZETAS (ms, ns) | `RHOS (ms, ns) as s) ->
      let sn = showVar s in
      let TermSubst ms = AL.assoc_exn (showVar ms) vars in
      let TermSubst ns = AL.assoc_exn (showVar ns) vars in
      let* (xis, bxis) = genRen sort sn (ms, ns) in
      pure ((sn, TermSubst xis) :: vars, binders @ bxis)
    | (`SIGMA (m, ns) | `TAU (m, ns) | `THETA (m, ns) as s) ->
      let sn = showVar s in
      let m = AL.assoc_exn (showVar m) vars in
      let TermSubst ns = AL.assoc_exn (showVar ns) vars in
      let (sigma, bsigma) = genSubstS sn (m, ns) sort in
      pure ((sn, sigma) :: vars, binders @ bsigma)
    | (`SIGMAS (ms, ns) | `TAUS (ms, ns) | `THETAS (ms, ns) as s) ->
      let sn = showVar s in
      let TermSubst ms = AL.assoc_exn (showVar ms) vars in
      let TermSubst ns = AL.assoc_exn (showVar ns) vars in
      let* (sigmas, bsigmas) = genSubst sort sn (ms, ns) in
      pure ((sn, TermSubst sigmas) :: vars, binders @ bsigmas) in

  let* (assoc_vars, binders) = m_fold_left ~f:genVariable ~init:([], []) var_declaration in
  pure (List.rev_map ~f:snd assoc_vars, binders)

(* TODO atm there is still a bug. Since m_fold is fold_right, it traverses the list in the wrong direction. But when I reverse the list it still somehow traverses it in the wrong direction.
 * If I remove the monad it works. That might be a readon to abandon it alltogether. The reader can be just a global variable for the signature and the error might as well be a real error. But I'm wondering if a m_mold_left would work
 * normal -> fails in sigM.run
 * reversed -> fails already when calling test *)
let test () =
  let open SigM.Syntax in
  let open SigM in
  let v = [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `ZETAS (`KS, `LS); `THETAS (`MS, `LS) ] in
  let* [ ks; ls; ms; sigmas; zetas; thetas ], varBinders as sdf = genVariables "tm" v in
  pure sdf

let test2 () =
  let open SigM.Syntax in
  let open SigM in
  let v2 = [ `K; `LS; `MS; `SIGMA (`K, `LS); `ZETAS (`LS, `MS); `THETA (`K, `MS) ] in
  let* [ k; TermSubst ls; TermSubst ms; sigma; TermSubst zetas; TermSubst theta ], varBinders as sdf = genVariables "vl" v2 in
  pure sdf

(* let v = [ `K; `L; `MS; `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ] *)

(* I want to call it like this
 * e.g. in genUpRenSubst. Since I return a variable number of terms I would need to use a list. Is this bad style? since it's static it seems to be not much of a problem because when it runs one it runs everytime. Since the genXXX functions sometimes return only SubstTy I would need to match on that, too
 * let v = [ `K; `L; `MS; `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ]
 * let [ k; l; (TermSubst ms); xi; tau; theta ], varBinders = genVariables sort v
 *  *)
