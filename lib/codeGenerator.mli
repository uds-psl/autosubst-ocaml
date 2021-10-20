(** This module implements all the code generation functions for
    inductive types, instantiation operations and rewriting lemmas. *)


val generate : Language.tId list -> (Language.binder * Language.tId) list -> VernacGen.AutosubstModules.t RSEM.t
(** [generate component up_list] generates for a given component and list of liftings, the inductive types, instantiation operations and rewriting lemmas.
    The code is returned in a module collection. *)