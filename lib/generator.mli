(** This module implements all the functions that generate inductive types,
 ** definitions, fixpoints and lemmas. *)
module H = Hsig

(** For a given component and list of liftings, generate all the vernacular expressions
 ** for the inductive types, definitions, fixpoints and lemmas. *)
val genCodeT : H.tId list -> (H.binder * H.tId) list -> Coqgen.vernac_expr list REM.t
