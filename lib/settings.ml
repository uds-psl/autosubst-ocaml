(** This module contains some global variables for which I did not want to add a
 ** state monad to the monad transformer stack *)

(** format string for printing variable constructors *)
let var__ = ref "var_%s"

(** What kind of code we generate. Set after parsing program arguments in Program
 ** TODO can we have mutable references in ocaml that we can only set once? *)
module L = Language

let scope_type = ref L.Unscoped

let is_wellscoped () =
  match !scope_type with
  | L.Unscoped -> false
  | L.WellScoped -> true
