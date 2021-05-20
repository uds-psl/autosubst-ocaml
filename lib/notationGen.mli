open Vernacexpr
open GallinaGen

type g_assoc = Gramlib.Gramext.g_assoc
type notation_type = NG_VarConstr of string * string
                   | NG_VarInst of string * string
                   | NG_Var
                   | NG_Up of string
                   | NG_SubstApply of string * string
                   | NG_Subst of string
                   | NG_RenApply of string * string
                   | NG_Ren of string

val fscope : scope_name
val subst_scope : scope_name

val level_ : int -> syntax_modifier
val assoc_ : g_assoc -> syntax_modifier
val format_ : string -> syntax_modifier
val only_print_ : syntax_modifier


val notation_string : notation_type -> string
val notation_modifiers : notation_type -> syntax_modifier list
val notation_scope : notation_type -> scope_name
