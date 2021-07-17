(** This module originally contained another Coq AST. Now it just has the substTy type
 ** which is used to represent vectors of scope variables (n_ty, n_vl : nat),
 ** renamings (zeta_ty, zeta_vl), substitutions (sigma_ty, sigma_vl),
 ** and equalities (that two renamings/substitutions are extensionally equal etc.) *)

module CG = GallinaGen
module L = Language
module S = Settings

type substScope = SubstScope of string list * CG.constr_exprs
type substTy = SubstRen of CG.constr_exprs
             | SubstSubst of CG.constr_exprs
             | SubstEq of CG.constr_exprs * (L.tId -> L.binder -> CG.constr_expr -> CG.constr_expr RWEM.t)
             | SubstPred of CG.constr_exprs
             | SubstAllfvH of CG.constr_exprs * (L.tId -> L.binder -> CG.constr_expr -> CG.constr_expr RWEM.t)

let ss_terms = function
  | SubstScope (_, xs) ->
    match !S.scope_type with
    | S.Unscoped -> []
    | S.WellScoped -> xs

let ss_terms_all = function
  | SubstScope (_, xs) -> xs

let ss_names = function
  | SubstScope (names, _) -> names

let sty_terms = function
  | SubstRen xs -> xs
  | SubstSubst xs -> xs
  | SubstEq (xs, _) -> xs
  | SubstPred xs -> xs
  | SubstAllfvH (xs, _) -> xs
