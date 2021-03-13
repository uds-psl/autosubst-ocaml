(** This module implements all the functions that generate inductive types,
 ** definitions, fixpoints and lemmas. *)
module H = Hsig

(** For a given component and list of liftings, generate all the vernacular expressions
 ** for the inductive types, definitions and fixpoints.
 ** It returns a tuple of vernacular expression lists since all the definitions using functional
 ** extensionality are separated into a different module.
 ** *)
val genCodeT : H.tId list -> (H.binder * H.tId) list -> Coqgen.autosubst_exprs REM.t
