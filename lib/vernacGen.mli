open GallinaGen
open AutomationGen

type vernac_unit = Vernac of Vernacexpr.vernac_control list
                 | TacticLtac of string * TacGen.t
                 | TacticNotation of string list * TacGen.t


val pr_vernac_control : Vernacexpr.vernac_control -> Pp.t
val pr_vernac_unit : vernac_unit -> Pp.t
val pr_vernac_units : vernac_unit list -> Pp.t

(** AutosubstModules.t organizes the generated code into different modules. *)
module AutosubstModules : sig
  type module_tag = Core | Fext | Allfv | Extra
  (** Tags to separate code into modules.
      Each new code generation feature should receive its own tag. *)

  type t
  (** The type of a collection of modules *)

  val string_of_tag : module_tag -> string
  (** [string_of_tag tag] return the name of the module. *)

  val add_units : module_tag -> vernac_unit list -> t
  (** [add_units tag units] creates a singular module collection with module [tag] containing [units]. *)

  val from_list : (module_tag * vernac_unit list) list -> t
  (** [from_list l] turns a list into a collection of modules. Currently an identity function. *)

  val remove_tags : module_tag list -> t -> t
  (** [filter_tags tags m] returns a module collection without any tag in in [tags]. *)

  val pr_modules : Pp.t -> t -> Pp.t
  (** [pr_modules preamble m] uses Coq's pretty-printer to generate code out of the given modules.

      The [preamble] is used to set global [Require Import] statements at the beginning of the
      generated code. Only non-empty modules are printed.
      This also adds an "interface" module where all non-empty modules are exported. *)


  (** Monoid operations to aggregate AutosubstModules. *)

  val empty : t
  (** The empty modules. *)
  val append : t -> t -> t
  (** [append m0 m1] appends code in the modules of [m1] to the modules of [m0]. *)
  val concat : t list -> t
  (** [concat ms] extends [append] over lists. *)
end


val inductive_ : inductive_body list -> vernac_unit
val fixpoint_ : is_rec:bool -> fixpoint_expr list -> vernac_unit
val definition_ : identifier -> binder_expr list -> ?rtype:constr_expr -> constr_expr -> vernac_unit
val lemma_ : ?opaque:bool -> identifier -> binder_expr list -> constr_expr -> constr_expr -> vernac_unit

val class_ : string -> binder_expr list -> constructor_expr list -> vernac_unit
val instance_ : string -> binder_expr list -> constr_expr -> ?interactive:bool -> constr_expr -> vernac_unit

val notation_ : string -> Vernacexpr.syntax_modifier list -> ?scope:Vernacexpr.scope_name -> constr_expr -> vernac_unit

val module_ : string -> vernac_unit list -> vernac_unit list
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
