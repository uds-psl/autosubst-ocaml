open GallinaGen
open TacGen

type vernac_expr = Vernacexpr.vernac_expr

type vernac_unit = Vernac of vernac_expr list
                 | TacticLtac of string * tactic_expr
                 | TacticNotation of string list * tactic_expr

type autosubst_exprs = { as_units: vernac_unit list; as_fext_units: vernac_unit list }

val pr_vernac_expr : vernac_expr -> Pp.t
val pr_vernac_unit : vernac_unit -> Pp.t
val pr_vernac_units : vernac_unit list -> Pp.t

val inductive_ : inductive_body list -> vernac_unit
val fixpoint_ : is_rec:bool -> fixpoint_expr list -> vernac_unit
val definition_ : identifier -> binder_expr list -> ?rtype:constr_expr -> constr_expr -> vernac_unit
val lemma_ : ?opaque:bool -> identifier -> binder_expr list -> constr_expr -> constr_expr -> vernac_unit

val class_ : string -> binder_expr list -> constructor_expr list -> vernac_unit
val instance_ : string -> constr_expr -> constr_expr -> vernac_unit
val ex_instances_ : string list -> vernac_unit
val ex_instance_ : string -> vernac_unit

val notation_ : string -> Vernacexpr.syntax_modifier list -> ?scope:Vernacexpr.scope_name -> constr_expr -> vernac_unit

(** create command to set implicit arguments
 ** e.g. Arguments foo {bar} {baz}. *)
val impl_arguments_ : string -> string list -> vernac_unit
  
module GenTestsClass : sig
  val my_instance : Pp.t
  val my_ex_instances : Pp.t
end


module GenTestsTac : sig
  val myasimpl' : Pp.t
  val myasimpl : Pp.t
  val myasimpl_hyp : Pp.t
  val myauto_case : Pp.t
  val myrenamify : Pp.t
  val myrewritestar : Pp.t
end

module GenTestsNotation : sig
  val mynotation : Pp.t
  val mynotation2 : Pp.t
end
