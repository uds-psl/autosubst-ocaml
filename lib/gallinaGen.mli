(** This module implements smart constructors for all the different kind of AST nodes
 ** and vernacular expressions we need.
 ** And it has an interface for printing these expressions. *)

type identifier = string
type identifiers = identifier list

type constr_expr = Constrexpr.constr_expr
type constr_exprs = constr_expr list
type binder_expr = Constrexpr.local_binder_expr
type branch_expr = Constrexpr.branch_expr

val qualid_ : identifier -> Libnames.qualid
val ref_ : identifier -> constr_expr
val name_id_ : identifier -> Names.Id.t

val underscore_ : constr_expr
val prop_ : constr_expr
val type_ : constr_expr

val app_ : constr_expr -> constr_exprs -> constr_expr
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

type constructor_expr = bool * (Names.lident * constr_expr)
type inductive_body = Vernacexpr.inductive_expr * Vernacexpr.decl_notation list
val constructor_ : identifier -> constr_expr -> constructor_expr
val inductiveBody_ : identifier -> binder_expr list -> ?rtype:constr_expr -> constructor_expr list -> inductive_body

type fixpoint_expr = Vernacexpr.fixpoint_expr
val fixpointBody_ : identifier -> binder_expr list -> constr_expr -> constr_expr -> identifier -> fixpoint_expr

type vernac_expr = Vernacexpr.vernac_expr
type vernac_unit
type autosubst_exprs = { as_exprs: vernac_unit list; as_fext_exprs: vernac_unit list }

val expr_to_unit : vernac_expr -> vernac_unit

val inductive_ : inductive_body list -> vernac_unit
val fixpoint_ : is_rec:bool -> fixpoint_expr list -> vernac_unit
val definition_ : identifier -> binder_expr list -> ?rtype:constr_expr -> constr_expr -> vernac_unit
val lemma_ : ?opaque:bool -> identifier -> binder_expr list -> constr_expr -> constr_expr -> vernac_unit

val vernacend : Pp.t
val newline : Pp.t
val parse_constr_expr : string -> constr_expr
val pr_vernac_expr : vernac_expr -> Pp.t
val pr_vernac_unit : vernac_unit -> Pp.t list

(** Setup some state in the Coq library like a feedback printer and notations *)
val setup_coq : unit -> unit