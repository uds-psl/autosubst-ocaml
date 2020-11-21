open Base
open GenM
(* TODO module H = Hsig *)
open Hsig

type identifier = string
type identifiers = identifier list

type command = Arguments of string * terms
and cBinder = BinderName of string
            | BinderNameType of string list * term
            | BinderImplicitName of string
            | BinderImplicitNameType of string list * term
            | BinderScopeNameType of string list * term
            | BinderImplicitScopeNameType of string list * term
and cBinders = cBinder list
and matchItem = MatchItem of term * term option
and equation = Equation of pattern * term
and pattern = PatCtor of term * identifiers
            | PatCtorEx of string * pattern list
            | PatAtCtor of term * identifiers
            | PatAtCtorEx of string * pattern list
            | PatQualId of term
            | PatUnderscore
and substTy = SubstScope of terms
            | SubstRen of terms
            | SubstSubst of terms
            | SubstEq of terms * (tId -> binder -> term -> term GenM.t)
            | SubstConst of terms
and sort = Prop
          | Set
          | Type
and const = Some | None
          | Refl | Sym | Trans
          | Nat | Suc
          | Fin
          | Id | Comp
          | Upren | Shift  | Cons | VarZero
          | Ap
          | Fext
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
         | TermLet of term * term * term (* TODO kathrin: get a pattern?? *)
         | TermUnderscore
         | TermMatch of matchItem * term option * equation list
         | TupleTy of terms
         | Tuple of terms
         | Todo of string
         | TermSubst of substTy
         | TermVar of term
         | TermArg of term * string * term


type t = term


type definition = Definition of string * cBinders * term option * term


type fixpointBody = FixpointBody of string * cBinders * term * term
type fixpoint = Fixpoint of bool * fixpointBody list

type inductiveCtor = InductiveCtor of string * term option
type inductiveBody = InductiveBody of string * cBinders * term * inductiveCtor list
type inductive = Inductive of inductiveBody list

type proof = ProofExact of term
           | ProofString of string
type lemma = Lemma of string * cBinders * term * proof

type tactic = TacticRewrite of string option * string list * string list * string list
            | TacticSeq of tactic list
            | TacticId of string
            | TacticUnfold of string list * string option
            | TacticFold of string list * string option
            | TacticRepeat of tactic

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

let none_ = TermConst None
let some_ = TermConst Some
let eqSym_ s = TermApp (TermConst Sym, [s])
let eqTrans_ s t = TermApp (TermConst Trans, [s; t])
let nat = TermConst Nat

let up_ren_ : tId -> term -> binder -> term = fun y xi -> function
  (* TODO something is broken because when I write y = x ocaml wants to use the equality on int, even though it knows both are tId's. Maybe I need to use an interface for the Hsig module *)
  | Single x -> if (equal_string y x) then TermApp (TermConst Upren, [xi]) else xi
      (* TODO what's up with the string "upRen_p" here? *)
  | BinderList (m, x) -> if (equal_string y x) then idApp "upRen_p" [TermId m; xi] else xi

let succ_ n z = function
  | Single x -> if (equal_string z x) then TermApp (TermConst Suc, [n]) else n
  | BinderList (m, x) -> if (equal_string z x) then idApp (m ^ "+") [n] else n

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

let matchFin_ s f b = TermMatch (MatchItem (s, None), None,
    [ Equation (PatCtor (some_, ["fin_n"]), (f (TermId "fin_n"))); Equation (PatQualId none_, b) ])

let sortType x n = TermApp ((TermId x), [TermSubst n])

let getTerms' = function
  | BinderName s -> [TermId s]
  | BinderNameType (xs,_) -> List.map ~f:(fun x -> TermId x) xs
  | _ -> []

let getTerms = List.concat_map ~f:getTerms'

let (==>) s t = List.fold_right s ~f:(fun s t -> TermFunction (s, t)) ~init:t
