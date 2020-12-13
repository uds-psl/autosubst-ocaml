
module CG = Coqgen
module H = Hsig

type substTy = SubstScope of CG.constr_exprs
            | SubstRen of CG.constr_exprs
            | SubstSubst of CG.constr_exprs
            | SubstEq of CG.constr_exprs * (H.tId -> H.binder -> CG.constr_expr -> CG.constr_expr REM.t)
            | SubstConst of CG.constr_exprs

let sty_terms = function
  | SubstScope xs -> xs
  | SubstRen xs -> xs
  | SubstSubst xs -> xs
  | SubstEq (xs,_) -> xs
  | SubstConst xs -> xs

