(** This module implements utility functions for generating Coq AST used in Generator *)
open GallinaGen
open CoqSyntax
open Language

val type_ : constr_expr
val nat_ : constr_expr
val none_ : constr_expr
val some_ : constr_expr
val suc_ : constr_expr
val plus_ : constr_expr
val shift_ : constr_expr
val cons_ : constr_expr
val var_zero_ : constr_expr
val underscore_ : constr_expr
val id_ : constr_expr

val eq_refl_ : constr_expr
val eqSym_ : constr_expr -> constr_expr
val eqTrans_ : constr_expr -> constr_expr -> constr_expr
val ap_ : constr_expr -> constr_expr -> constr_expr
val app_id_ : constr_expr -> constr_expr
val fin_ : constr_expr -> constr_expr
val fext_ : constr_expr -> constr_expr

val mk_refs : identifier list -> constr_exprs

val succ_ : constr_expr -> identifier -> binder -> constr_expr

val (>>>) : constr_expr -> constr_expr -> constr_expr
val (<<>>) : substTy -> substTy -> constr_expr list

val repRew : (constr_expr * constr_expr) list -> constr_expr
val matchFin_ : constr_expr -> (constr_expr -> constr_expr) -> constr_expr -> constr_expr

val app_sort : identifier -> substScope -> constr_expr
val app_constr : identifier -> substScope -> constr_expr list -> constr_expr
val app_var_constr : identifier -> substScope -> constr_expr
val app_fix : ?expl:bool -> identifier -> ?sscopes:substScope list -> ?scopes:substTy list -> constr_expr list -> constr_expr
val mk_underscore_pattern : substScope -> identifier list

val (==>) : constr_expr list -> constr_expr -> constr_expr

val abs_ref : identifier -> constr_expr -> constr_expr

val scons_p_congr_ : constr_expr -> constr_expr -> constr_expr
val scons_p_comp' : constr_expr -> constr_expr
val scons_p_tail' : constr_expr -> constr_expr
val scons_p_head' : constr_expr -> constr_expr

val explicit_ : binder_expr list -> binder_expr list

val definitionBody : identifier -> L.binder -> (constr_expr * constr_expr)
  -> (identifier -> identifier -> constr_expr * constr_expr) -> constr_expr
