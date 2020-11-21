open Core
open GenM
module H = Hsig

val genCodeT : H.tId list -> H.tId list -> (H.binder * H.tId) list -> string list GenM.t
