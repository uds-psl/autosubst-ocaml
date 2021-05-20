open Util
open Vernacexpr
open GallinaGen

type instance_type = Ren of int | Subst of int | Var

let instance_name sort = function
  | Ren _ -> sep "Ren" sort
  | Subst _ -> sep "Subst" sort
  | Var -> sep "VarInstance" sort

let class_name = function
  | Ren n -> "Ren"^(string_of_int n)
  | Subst n -> "Subst"^(string_of_int n)
  | Var -> "Var"

let function_name sort = function
  | Ren _ -> sep "ren" sort
  | Subst _ -> sep "subst" sort
  | Var -> CoqNames.var_ sort


