module H = Hsig

val genCodeT : H.tId list -> (H.binder * H.tId) list -> Coqgen.vernac_expr list SigM.t
