(** This module implements mini DSL to generate scope/renaming/substitution variables.
 ** Most code generation functions in Generator use this to intro their variables. *)
open GallinaGen

type scopeVar = [ `K | `L | `M | `N ]
type scopeVars = [ `KS | `LS | `MS | `NS ]
type renVar = [ `XI of scopeVar * scopeVar | `ZETA of scopeVar * scopeVar | `RHO of scopeVar * scopeVar ]
type renVars = [ `XIS of scopeVars * scopeVars | `ZETAS of scopeVars * scopeVars | `RHOS of scopeVars * scopeVars ]
type substVar = [ `SIGMA of scopeVar * scopeVars  | `TAU of scopeVar * scopeVars  | `THETA of scopeVar * scopeVars ]
type substVars = [ `SIGMAS of scopeVars * scopeVars  | `TAUS of scopeVars * scopeVars  | `THETAS of scopeVars * scopeVars ]

type vars = [ scopeVar | scopeVars | renVar | renVars | substVar | substVars ]

val genVariables : string -> vars list -> (constr_expr list * CoqSyntax.substTy list * binder_expr list) RWEM.t
