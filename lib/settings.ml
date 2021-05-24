(** This module contains some global variables for which I did not want to add a
 ** state monad to the monad transformer stack *)

(** format string for printing variable constructors *)
let var__ = ref "var_%s"

(** What kind of code we generate. Set after parsing program arguments in Program
 ** TODO can we have mutable references in ocaml that we can only set once? *)
type scope = WellScoped | Unscoped

let equal_scopeType x y = match (x, y) with
| WellScoped, WellScoped -> true
| Unscoped, Unscoped -> true
| _, _ -> false

let scope_type = ref Unscoped

let is_wellscoped () =
  match !scope_type with
  | Unscoped -> false
  | WellScoped -> true

(* before version 8.10 there was no explicit scope declaration so we use a different static file *)
type coq_version = LT810 | GE810

type args = {
  infile : string;
  outfile : string;
  scope : scope;
  axioms_separate : bool;
  generate_static_files : bool;
  version : coq_version;
}
