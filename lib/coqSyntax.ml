open Base

module CG = Coqgen
module H = Hsig

(* TODO the original Haskell code actually only used PatCtor and PatQualId, but PatQualId is just PatCtor with an empty list. so I removed that too. Also PatCtor originally accepted a term as first argument which does not compose well when I want to print it in the end. But the terms was actually always an application (Constr var1 var2 etc) so it should be easy to put them as strings into the second argument *)

type substTy = SubstScope of CG.constr_exprs
            | SubstRen of CG.constr_exprs
            | SubstSubst of CG.constr_exprs
            | SubstEq of CG.constr_exprs * (H.tId -> H.binder -> CG.constr_expr -> CG.constr_expr REM.t)
            | SubstConst of CG.constr_exprs

(* TODO this bool seems to be whether the fixpoint should actually be a definition. It is set by checking if the sort of the principal argument is recursive. When it's false I should also just generate a Defintion in my translation function. Then I would also have to assert that the fixpointBody list is a singleton *)
(* type fixpoint = Fixpoint of bool * fixpointBody list [@@deriving show] *)

let sty_terms = function
  (* | SubstScope xs -> List.map ~f:(fun x -> TermVar x) xs (\* TODO kathrin: this is a hack.
   * The tovar was used I think to filter out the substScope in unscoped code *\) *)
  | SubstScope xs -> xs
  | SubstRen xs -> xs
  | SubstSubst xs -> xs
  | SubstEq (xs,_) -> xs
  | SubstConst xs -> xs

