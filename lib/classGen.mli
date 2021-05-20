open GallinaGen

(* a.d. TODO probably needs sort as an argument because of Up *)
type instance_type = CG_Ren of int
                   | CG_Subst of int
                   | CG_Var
                   | CG_Up

val instance_name : string -> instance_type -> string
val class_name : string -> instance_type -> string
val function_name : string -> instance_type -> string
