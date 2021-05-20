(** This module implements all the functions that generate inductive types,
 ** definitions, fixpoints and lemmas. *)
module L = Language

(** For a given component and list of liftings, generate all the vernacular expressions
 ** for the inductive types, definitions and fixpoints.
 ** It returns a tuple of vernacular expression lists since all the definitions using functional
 ** extensionality are separated into a different module.
 ** *)
val gen_code : L.tId list -> (L.binder * L.tId) list -> GallinaGen.autosubst_exprs REM.t
