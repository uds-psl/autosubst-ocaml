(** This module implements the generation of the allfv operation and lemmas.
    
    It is baed on https://github.com/mrhaandi/coq-library-undecidability/blob/SysF_omega/theories/SemiUnification/autosubst/allfv_more.v
    We were not able to generate all of the lemmas from the above source.

    What we generate is:
    - allfv operation
    - allfvTriv : allfv holds for a predicate that is always true
    - allfvImpl : p x -> q x -> allfv p s -> allfv q s
    - allfvRenL : allfv (fun x => p (xi x)) s -> allfv p (ren xi s)
    - allfvRenR : allfv p (ren xi s) -> allfv (fun x => p (xi x)) s

    More could be generated in the future.
*)


val generate : Language.tId list -> (Language.binder * Language.tId) list -> VernacGen.AutosubstModules.t RSEM.t
(** [generate component up_list] generates for the given component an allfv operation and lemmas about the operation.
    The code is returned in a module collection. *)