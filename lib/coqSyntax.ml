open Base
(* TODO module H = Hsig *)
open Hsig

type identifier = string [@@deriving show]
type identifiers = identifier list [@@deriving show]

type sort = Prop
          | Set
          | Type [@@deriving show]
(* Rename Some and None because they are already taken and it leads to some strange parsing errors when I leave it in
 * I think when I tried it, the Some was trying to take everything until the `type command` as an argument which does not make any sense *)
(* TODO add scons_p? right now this is often used as a string but does not need to *)
type const = Some_ | None_
          | Refl | Sym | Trans
          | Nat | Suc | Plus
          | Fin
          | Id | Comp
          | Upren | Shift  | Cons | VarZero
          | Ap
          | Fext [@@deriving show]
(* TODO the original Haskell code actually only used PatCtor and PatQualId, but PatQualId is just PatCtor with an empty list. so I removed that too. Also PatCtor originally accepted a term as first argument which does not compose well when I want to print it in the end. But the terms was actually always an application (Constr var1 var2 etc) so it should be easy to put them as strings into the second argument *)
(* type pattern = PatCtor of identifier * identifiers [@@deriving show] *)
            (* | PatCtorEx of string * pattern list
             * | PatAtCtor of term * identifiers
             * | PatAtCtorEx of string * pattern list *)
            (* | PatQualId of term *)
            (* | PatUnderscore *)

type command = Arguments of string * terms [@@deriving show]
and cBinder = BinderName of string
            | BinderNameType of string list * term
            | BinderImplicitName of string
            | BinderImplicitNameType of string list * term
            | BinderScopeNameType of string list * term
            | BinderImplicitScopeNameType of string list * term
and cBinders = cBinder list
(* TODO the term option of mathItem is ignoren in Autosubst2 when the coq code is printer. Check if also ignored in rest of code *)
and matchItem = MatchItem of term * term option
and equation = Equation of identifier * identifiers * term
and substTy = SubstScope of terms
            | SubstRen of terms
            | SubstSubst of terms
            | SubstEq of terms * (tId -> binder -> term -> term SigM.t)
            | SubstConst of terms
and terms = term list
and term =  TermImp of term
         | TermApp of term * terms
         | TermConst of const
         | TermNum of int
         | TermId of string
         | TermSort of sort
         | TermFunction of term * term
         | TermAbs of cBinders * term
         | TermForall of cBinders * term
         | TermAnd of terms
         | TermEq of term * term
         | TermUnderscore
           (* TODO the term option is also ignored here. Check if ignored in code generation too *)
         | TermMatch of matchItem * term option * equation list
         | TupleTy of terms
         | Tuple of terms
         | TermSubst of substTy
         | TermVar of term
         | TermArg of term * string * term
[@@deriving show]

type definition = Definition of string * cBinders * term option * term [@@deriving show]

type fixpointBody = FixpointBody of string * cBinders * term * term [@@deriving show]
(* TODO this bool seems to be whether the fixpoint should actually be a definition. It is set by checking if the sort of the principal argument is recursive. When it's false I should also just generate a Defintion in my translation function. Then I would also have to assert that the fixpointBody list is a singleton *)
type fixpoint = Fixpoint of bool * fixpointBody list [@@deriving show]

type inductiveCtor = InductiveCtor of string * term option [@@deriving show]
type inductiveBody = InductiveBody of string * cBinders * term * inductiveCtor list [@@deriving show]
type inductive = Inductive of inductiveBody list [@@deriving show]

type proof = ProofExact of term
           | ProofString of string [@@deriving show]
type lemma = Lemma of string * cBinders * term * proof [@@deriving show]

type tactic = TacticRewrite of string option * string list * string list * string list
            | TacticSeq of tactic list
            | TacticId of string
            | TacticUnfold of string list * string option
            | TacticFold of string list * string option
            | TacticRepeat of tactic
[@@deriving show]

type sentence = SentenceDefinition of definition
              | SentenceClass of string * cBinders * (string * term) list
              | SentenceInductive of inductive
              | SentenceFixpoint of fixpoint
              | SentenceLemma of lemma
              | SentenceTactic of identifier * tactic
              | SentenceVariable of identifier * term
              | SentenceCommand of command
              | SentenceNotation of string * term * string * string
              | SentenceInstance of cBinders * string * term * term
              | SentenceId of string
              | SentenceTacticNotation of string list * tactic
              | SentenceSection of string * sentence list
[@@deriving show, variants]

type variable = Variable of identifier * term

type tmScope = terms

let idApp s t = TermApp (TermId s, t)

let getType = function
  | BinderNameType (_, t) -> [t]
  | BinderImplicitNameType (_, t) -> [t]
  | BinderScopeNameType (_, t) -> [t]
  | BinderImplicitScopeNameType (_, t) -> [t]
  | _ -> []

let getTypes = List.concat_map ~f:getType

let sty_terms = function
  | SubstScope xs -> List.map ~f:(fun x -> TermVar x) xs (* TODO kathrin: this is a hack. *)
  (* Also TODO it seems constructors are special functions b/c I can not eta reduce this. Apparently this was a simplification made for ocaml and someone asked about this 20 years ago  https://caml-list.inria.narkive.com/WUIPH06Z/why-can-t-i-use-constructors-as-functions *)
  | SubstRen xs -> xs
  | SubstSubst xs -> xs
  | SubstEq (xs,_) -> xs
  | SubstConst xs -> xs

let none_ = TermConst None_
let some_ = TermConst Some_
let eqSym_ s = TermApp (TermConst Sym, [s])
let eqTrans_ s t = TermApp (TermConst Trans, [s; t])
let nat = TermConst Nat

let up_ren_ : tId -> term -> binder -> term = fun y xi -> function
  (* DONE something is broken because when I write y = x ocaml wants to use the equality on int, even though it knows both are tId's. Maybe I need to use an interface for the Hsig module
   * It was because base shadows the polymorphic equal so you need to explicitly open the module *)
  | Single x -> if String.(y = x) then TermApp (TermConst Upren, [xi]) else xi
      (* TODO what's up with the string "upRen_p" here? *)
  | BinderList (m, x) -> if (equal_string y x) then idApp "upRen_p" [TermId m; xi] else xi

let succ_ n z = function
  | Single x -> if String.(z = x) then TermApp (TermConst Suc, [n]) else n
  | BinderList (m, x) -> if String.(z = x) then TermApp (TermConst Plus, [TermId m; n]) else n

let fin_ n = TermApp (TermConst Fin, [n])

let (>>>) s t = TermApp (TermConst Comp, [t; s])

let eq_refl_ = TermConst Refl
let shift_ = TermConst Shift
let id_ = TermConst Shift
let cons_ = TermConst Cons
let varZero_ = TermConst VarZero

let repRew s = List.fold_left ~f:(fun s (t, t_eq) -> TermApp (TermConst Trans, [s; TermApp (TermConst Ap, [t_eq; t])])) ~init:(TermConst Refl) s

let ap_ s = TermApp (TermConst Ap, s)

let fext_ = TermConst Fext

(* TODO variables for constructor name strings? *)
let matchFin_ s f b = TermMatch (MatchItem (s, None), None,
    [ Equation ("Some", ["fin_n"], (f (TermId "fin_n"))); Equation ("None", [], b) ])

let sortType x n = TermApp ((TermId x), [TermSubst n])

let getTerms' = function
  | BinderName s -> [TermId s]
  | BinderNameType (xs,_) -> List.map ~f:(fun x -> TermId x) xs
  | _ -> []

let getTerms = List.concat_map ~f:getTerms'

let (==>) s t = List.fold_right s ~f:(fun s t -> TermFunction (s, t)) ~init:t

