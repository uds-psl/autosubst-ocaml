open Coqgen

val instance_ : string -> string -> constr_expr -> vernac_unit
val ex_instances_ : string list -> vernac_expr

module GenTests : sig
  val my_instance : Pp.t
  val my_ex_instances : Pp.t
end
