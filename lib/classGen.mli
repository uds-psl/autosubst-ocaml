open GallinaGen

type instance_type = Ren of int | Subst of int | Var

val instance_name : string -> instance_type -> string
val class_name : instance_type -> string
val function_name : string -> instance_type -> string
