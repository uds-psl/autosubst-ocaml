open Util
open Vernacexpr
open GallinaGen

type instance_type = CG_Ren of int | CG_Subst of int | CG_Var
                   | CG_Up

let instance_name sort = function
  | CG_Ren _ -> sep "Ren" sort
  | CG_Subst _ -> sep "Subst" sort
  | CG_Var -> sep "VarInstance" sort
  | CG_Up -> sepd [ "Up"; sort; sort ]

let class_name sort = function
  | CG_Ren n -> "Ren"^(string_of_int n)
  | CG_Subst n -> "Subst"^(string_of_int n)
  | CG_Var -> "Var"
  | CG_Up -> sep "Up" sort

(* a.d. TODO, maybe directly put constr_expr in the info instead of generating the function name here  *)
let function_name sort = function
  | CG_Ren _ -> sep "ren" sort
  | CG_Subst _ -> sep "subst" sort
  | CG_Var -> CoqNames.var_ sort
  | CG_Up -> sepd ["up"; sort; sort]
