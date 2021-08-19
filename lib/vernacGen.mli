open GallinaGen
open AutomationGen

type vernac_expr = Vernacexpr.vernac_expr

type vernac_unit = Vernac of vernac_expr list
                 | TacticLtac of string * TacGen.t
                 | TacticNotation of string list * TacGen.t

type autosubst_modules = { ren_subst_units: vernac_unit list
                         ; allfv_units : vernac_unit list
                         ; fext_units: vernac_unit list
                         ; interface_units : vernac_unit list }

val append_modules : autosubst_modules -> autosubst_modules -> autosubst_modules
val initial_modules : autosubst_modules


val pr_vernac_expr : vernac_expr -> Pp.t
val pr_vernac_unit : vernac_unit -> Pp.t
val pr_vernac_units : vernac_unit list -> Pp.t

val inductive_ : inductive_body list -> vernac_unit
val fixpoint_ : is_rec:bool -> fixpoint_expr list -> vernac_unit
val definition_ : identifier -> binder_expr list -> ?rtype:constr_expr -> constr_expr -> vernac_unit
val lemma_ : ?opaque:bool -> identifier -> binder_expr list -> constr_expr -> constr_expr -> vernac_unit

val class_ : string -> binder_expr list -> constructor_expr list -> vernac_unit
val instance_ : string -> binder_expr list -> constr_expr -> constr_expr -> vernac_unit
val instance'_ : string -> binder_expr list -> constr_expr -> ?interactive:bool -> constr_expr -> vernac_unit
val ex_instances_ : string list -> vernac_unit
val ex_instance_ : string -> vernac_unit

val notation_ : string -> Vernacexpr.syntax_modifier list -> ?scope:Vernacexpr.scope_name -> constr_expr -> vernac_unit

val module_ : string -> ?imports:(string list) -> vernac_unit list -> vernac_unit list
val import_ : string -> vernac_unit
val export_ : string -> vernac_unit

(** hints for setoid rewriting to treat certain functions as opaque *)
val setoid_opaque_hint : string -> vernac_unit

(** create command to set implicit arguments
 ** e.g.
 **  Arguments foo : clear implicits.
 **  Arguments foo {bar} {baz}. *)
val clear_arguments_ : string -> vernac_unit
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
