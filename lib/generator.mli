open CoqSyntax
module H = Hsig

val genCodeT : H.tId list -> H.tId list -> (H.binder * H.tId) list -> sentence list SigM.t
