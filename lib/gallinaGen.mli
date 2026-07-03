(** This module implements smart constructors for all the different kind of AST nodes
 ** and vernacular expressions we need.
 ** And it has an interface for printing these expressions. *)

type identifier = string
type identifiers = identifier list

type constr_expr = Constrexpr.constr_expr
type constr_exprs = constr_expr list
type binder_expr = Constrexpr.local_binder_expr
type branch_expr = Constrexpr.branch_expr

val name_ : identifier -> Names.Name.t
val qualid_ : identifier -> Libnames.qualid
val ref_ : identifier -> constr_expr
val name_id_ : identifier -> Names.Id.t
val lident_ : identifier -> Names.lident
val ident_decl_ : identifier -> Constrexpr.ident_decl
val name_decl_ : identifier -> Constrexpr.name_decl

val underscore_ : constr_expr
val prop_ : constr_expr
val type_ : constr_expr

val app_ : constr_expr -> constr_exprs -> constr_expr
val app_ref : ?expl:bool -> string -> constr_exprs -> constr_expr
val app1_ : constr_expr -> constr_expr -> constr_expr
val appExpl_ : identifier -> constr_exprs -> constr_expr
val forall_ : binder_expr list -> constr_expr -> constr_expr
val arr_ : constr_exprs -> constr_expr -> constr_expr
val arr1_ : constr_expr -> constr_expr -> constr_expr
val lambda_ : binder_expr list -> constr_expr -> constr_expr
val eq_ : constr_expr -> constr_expr -> constr_expr

val match_ : constr_expr -> ?rtype:constr_expr -> branch_expr list -> constr_expr
val branch_ : identifier -> identifiers -> constr_expr -> branch_expr

val binder_ : ?implicit: bool -> ?btype:constr_expr -> identifiers -> binder_expr
val binder1_ : ?implicit:bool -> ?btype:constr_expr -> identifier -> binder_expr

type constructor_expr = Vernacexpr.constructor_expr
type inductive_body = Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list
val constructor_ : identifier -> constr_expr -> Vernacexpr.constructor_expr
val inductiveBody_ : identifier -> binder_expr list -> ?rtype:constr_expr -> constructor_expr list -> inductive_body

val definition_expr_ : identifier -> binder_expr list -> ?rtype:constr_expr -> constr_expr -> Vernacexpr.definition_expr
val theorem_expr_ : identifier -> binder_expr list -> constr_expr -> Vernacexpr.definition_expr

type fixpoint_expr = Vernacexpr.fixpoint_expr
val fixpointBody_ : identifier -> binder_expr list -> constr_expr -> constr_expr -> identifier -> fixpoint_expr

val pr_constr_expr : constr_expr -> Pp.t
val pr_exact_expr : constr_expr -> Pp.t
val parse_constr_expr : string -> constr_expr

(** Setup some state in the Coq library like a feedback printer and notations *)
val setup_coq : unit -> unit
