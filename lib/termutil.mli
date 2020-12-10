open Coqgen
module CS = CoqSyntax
module H = Hsig

val type_ : constr_expr
val nat_ : constr_expr
val none_ : constr_expr
val some_ : constr_expr
val suc_ : constr_expr
val plus_ : constr_expr
val shift_ : constr_expr
val cons_ : constr_expr
val var_zero_ : constr_expr
val fext_ : constr_expr
val underscore_ : constr_expr
val id_ : constr_expr

val refApp : string -> constr_exprs -> constr_expr
val eq_refl_ : constr_expr
val eqSym_ : constr_expr -> constr_expr
val eqTrans_ : constr_expr -> constr_expr -> constr_expr
val ap_ : constr_expr -> constr_expr -> constr_expr
val idApp_ : constr_expr -> constr_expr
val fin_ : constr_expr -> constr_expr

val mkRefs : identifier list -> constr_exprs

val succ_ : constr_expr -> identifier -> H.binder -> constr_expr

val (>>>) : constr_expr -> constr_expr -> constr_expr
val (<<>>) : CS.substTy -> CS.substTy -> constr_expr list

val repRew : (constr_expr * constr_expr) list -> constr_expr
val matchFin_ : constr_expr -> (constr_expr -> constr_expr) -> constr_expr -> constr_expr

(** TODO here I should filter out the substty when doing unscoped code *)
val sortType : identifier -> CS.substTy -> constr_expr
val (==>) : constr_expr list -> constr_expr -> constr_expr

val refAbs : identifier -> constr_expr -> constr_expr

val scons_p_congr_ : constr_expr -> constr_expr -> constr_expr
val scons_p_comp' : constr_expr -> constr_expr
val scons_p_tail' : constr_expr -> constr_expr
val scons_p_head' : constr_expr -> constr_expr

val explicit_ : binder_expr list -> binder_expr list

val definitionBody : identifier -> H.binder -> (constr_expr * constr_expr)
  -> (identifier -> identifier -> constr_expr * constr_expr) -> constr_expr
