(** This module implements the generation of automation, 
    i.e. typeclasses, typeclass instances, notations and tactics. *)


val generate : unit -> VernacGen.AutosubstModules.t RSEM.t
(** [generate ()] generates all of the automation and returns the code in a module collection. *)