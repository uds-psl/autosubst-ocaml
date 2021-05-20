open Vernacexpr
open GallinaGen

type g_assoc = Gramlib.Gramext.g_assoc

val fscope : scope_name
val subst_scope : scope_name

val notation_ : string -> ?level:int -> ?assoc:g_assoc -> ?fmt:string -> ?modifiers:(syntax_modifier list) -> ?scope:scope_name -> constr_expr -> vernac_expr

module GenTests : sig
  val mynotation : Pp.t
  val mynotation2 : Pp.t
end
