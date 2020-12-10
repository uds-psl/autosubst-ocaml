
module CG = Coqgen
module H = Hsig

type substTy = SubstScope of CG.constr_exprs
            | SubstRen of CG.constr_exprs
            | SubstSubst of CG.constr_exprs
            | SubstEq of CG.constr_exprs * (H.tId -> H.binder -> CG.constr_expr -> CG.constr_expr REM.t)
            | SubstConst of CG.constr_exprs

(* TODO this bool seems to be whether the fixpoint should actually be a definition. It is set by checking if the sort of the principal argument is recursive. When it's false I should also just generate a Defintion in my translation function. Then I would also have to assert that the fixpointBody list is a singleton *)
(* type fixpoint = Fixpoint of bool * fixpointBody list [@@deriving show] *)

let sty_terms = function
  | SubstScope xs -> xs
  | SubstRen xs -> xs
  | SubstSubst xs -> xs
  | SubstEq (xs,_) -> xs
  | SubstConst xs -> xs

type scopeType = WellScoped | Unscoped
