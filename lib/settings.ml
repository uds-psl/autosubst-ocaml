(** This module contains some global variables for which I did not want to add a
 ** state monad to the monad transformer stack *)

module AL = AssocList

(** Assoc list for printing variable constructors
 ** If a sort has no associated varable constructor name, a default name will be used. *)
let var_name_assoc = ref (AL.empty : (Language.tId, string) AL.t)

(** What kind of code we generate. Set after parsing program arguments in Program
 ** DONE can we have mutable references in ocaml that we can only set once?
 ** Yes, something like this is contained in the Core library https://discuss.ocaml.org/t/value-guaranteed-to-be-set-after-initialization/623/6
 ** We could reimplement it but seems not worth it. *)
type scope = Wellscoped | Unscoped

let equal_scopeType x y = match (x, y) with
  | Wellscoped, Wellscoped -> true
  | Unscoped, Unscoped -> true
  | _, _ -> false

let scope_type = ref Unscoped

let is_wellscoped () =
  match !scope_type with
  | Unscoped -> false
  | Wellscoped -> true

(* before version 8.10 there was no explicit scope declaration so we use a different static file *)
type coq_version = LT810 | GE810

type args = {
  infile : string;
  outfile : string;
  scope : scope;
  gen_allfv : bool;
  gen_fext : bool;
  gen_static_files : bool;
  force_overwrite : bool;
  version : coq_version;
}
