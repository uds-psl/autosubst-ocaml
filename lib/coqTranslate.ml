open Base
open CoqSyntax
open Coqgen
module C = Constrexpr
module V = Vernacexpr

(* let translate_const = function
 *   | Some_ -> "Some"
 *   | None_ -> "None"
 *   | Refl -> "eq_refl"
 *   | Sym -> "eq_sym"
 *   | Trans -> "eq_trans"
 *   | Nat -> "nat"
 *   | Suc -> "S"
 *   | Plus -> "plus"
 *   | Fin -> "fin"
 *   | Id -> "id"
 *   | Comp -> "funcomp"
 *   | Upren -> "up_ren"
 *   | Cons -> "scons"
 *   | VarZero -> "var_zero"
 *   | Ap -> "ap"
 *   | Shift -> "shift"
 *   | Fext -> "FunctionalExtensionality.functional_extensionality" *)

(* I added this code to check how many SubstTy terms make it to here. Except for Const there was everything *)
(* let cSScope = ref 0
 * let cSRen = ref 0
 * let cSSubst = ref 0
 * let cSEq = ref 0
 * let cSConst = ref 0 *)

(* let countSubstTy = function
 *   | SubstScope _ -> cSScope := !cSScope + 1
 *   | SubstRen _ -> cSRen := !cSRen + 1
 *   | SubstSubst _ -> cSSubst := !cSSubst + 1
 *   | SubstEq _ -> cSEq := !cSEq + 1
 *   | SubstConst _ -> cSConst := !cSConst + 1
 *
 * let pcount () =
 *   Printf.sprintf ("Scope: %d | Ren: %d | Subst: %d | Eq: %d | Const: %d") !cSScope !cSRen !cSSubst !cSEq !cSConst *)

(* let rec translate_term : term -> C.constr_expr = function
 *   | TermApp (t, ts) -> app_ (translate_term t) (List.map ~f:translate_term ts)
 *   | TermAppExpl (n, ts) -> appExpl_ n (List.map ~f:translate_term ts)
 *   | TermConst c -> ref_ (translate_const c)
 *   | TermId id -> ref_ id
 *   | TermSort sort -> ref_ (translate_sort sort)
 *   | TermFunction (t1, t2) -> arr_ [translate_term t1] (translate_term t2)
 *   | TermAbs (binders, body) -> lambda_ (List.map ~f:translate_binder binders) (translate_term body)
 *   | TermForall (binders, rtype) -> forall_ (List.map ~f:translate_binder binders) (translate_term rtype)
 *   | TermEq (t1, t2) -> eq_ (translate_term t1) (translate_term t2)
 *   | TermUnderscore -> ref_ "_"
 *   | TermMatch (MatchItem (mexpr,_),_,equations) ->
 *     match_ (translate_term mexpr) (List.map equations ~f:(fun (Equation (constr_name, constr_args, bexpr)) -> branch_ constr_name constr_args (translate_term bexpr) ) )
 *   | TermVar v -> translate_term v
 * and translate_binder = function
 *   (\* for the ones without type annotation I guess I should put in an underscore *\)
 *     | BinderName name -> binder1_ name
 *     | BinderNameType (names, typ) -> binder_ ~btype:(translate_term typ) names
 *     | BinderImplicitName name -> binder1_ ~implicit:true name
 *     | BinderImplicitNameType (names, typ) -> binder_ ~implicit:true ~btype:(translate_term typ) names
 *     | BinderScopeNameType (names, typ) -> binder_ ~btype:(translate_term typ) names
 *     | BinderImplicitScopeNameType (names, typ) -> binder_ ~implicit:true ~btype:(translate_term typ) names
 *
 * let translate_constructor (InductiveCtor (name, typ)) =
 *   match typ with
 *   | Some typ ->
 *     constructor_ name (translate_term typ)
 *   | None -> failwith "need to construct return type of constructor!"
 *
 * let translate_proof = function
 *   | ProofExact tm -> translate_term tm
 *   | ProofString tactic -> ref_ tactic
 *
 * let translate_sentence : sentence -> V.vernac_expr list = function
 *   | SentenceDefinition (Definition (name, binders, rtype, body)) ->
 *     let binders = List.map ~f:translate_binder binders in
 *     let rtype = Option.map ~f:translate_term rtype in
 *     let body = translate_term body in
 *     [definition_ name binders ?rtype body]
 *   | SentenceInductive (Inductive inductiveBodies) ->
 *     let translate_inductive (InductiveBody (name, binders, rtype, ctors)) =
 *         let binders = List.map ~f:translate_binder binders in
 *         let ctors = List.map ~f:translate_constructor ctors in
 *         let rtype = translate_term rtype in
 *         inductiveBody_ name binders ~rtype ctors in
 *     let inductiveBodies = List.map ~f:translate_inductive inductiveBodies in
 *     [inductive_ inductiveBodies]
 *   | SentenceFixpoint (Fixpoint (_, fixpointBodies)) ->
 *     (\* TODO I decided to ignore the fixpoint bool atm and always return a fixpoint. Not sure when thsi would even happen *\)
 *     let translate_fixpoint (FixpointBody (name, binders, rtype, body)) =
 *       let binders = List.map ~f:translate_binder binders in
 *       let rtype = translate_term rtype in
 *       let body = translate_term body in
 *       fixpointBody_ name binders rtype body in
 *     let fixpointBodies = List.map ~f:translate_fixpoint fixpointBodies in
 *     [fixpoint_ fixpointBodies]
 *   | SentenceLemma (Lemma (name, binders, rtype, proof)) ->
 *     let binders = List.map ~f:translate_binder binders in
 *     let rtype = translate_term rtype in
 *     let proof = translate_proof proof in
 *     lemma_ name binders rtype proof *)
