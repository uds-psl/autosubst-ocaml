open Base
open Coqgen

module H = Hsig

(* TODO the original Haskell code actually only used PatCtor and PatQualId, but PatQualId is just PatCtor with an empty list. so I removed that too. Also PatCtor originally accepted a term as first argument which does not compose well when I want to print it in the end. But the terms was actually always an application (Constr var1 var2 etc) so it should be easy to put them as strings into the second argument *)

type substTy = SubstScope of constr_exprs
            | SubstRen of constr_exprs
            | SubstSubst of constr_exprs
            | SubstEq of constr_exprs * (H.tId -> H.binder -> constr_expr -> constr_expr SigM.t)
            | SubstConst of constr_exprs

(* TODO this bool seems to be whether the fixpoint should actually be a definition. It is set by checking if the sort of the principal argument is recursive. When it's false I should also just generate a Defintion in my translation function. Then I would also have to assert that the fixpointBody list is a singleton *)
(* type fixpoint = Fixpoint of bool * fixpointBody list [@@deriving show] *)

let sty_terms = function
  (* | SubstScope xs -> List.map ~f:(fun x -> TermVar x) xs (\* TODO kathrin: this is a hack. *\) *)
  | SubstScope xs -> xs
  (* Also TODO it seems constructors are special functions b/c I can not eta reduce this. Apparently this was a simplification made for ocaml and someone asked about this 20 years ago  https://caml-list.inria.narkive.com/WUIPH06Z/why-can-t-i-use-constructors-as-functions *)
  | SubstRen xs -> xs
  | SubstSubst xs -> xs
  | SubstEq (xs,_) -> xs
  | SubstConst xs -> xs

