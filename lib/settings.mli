(** This module contains flags for code generation 
    and some global variables that I did not want to add to the Reader/State monad. *)


val var_name_assoc : (Language.tId, string) AssocList.t ref
(** Assoc list for printing variable constructors
    If a sort has no associated varable constructor name, a default name will be used. *)

type scope = Wellscoped | Unscoped
(** Type of syntax that we generate. *)

val equal_scopeType : scope -> scope -> bool
val is_wellscoped : unit -> bool
(** Check if the [scope_type] reference is wellscoped. *)

val scope_type : scope ref
(** Globally readable flag. Set after parsing program arguments in [Program] *)

val use_prelude : bool ref
(** Globally readable flag. Set after parsing program arguments in [Program] *)

type coq_version = LT813 | GE813
(** For which Coq version we generate code. 
    Before version 8.12 there was "export" attribute so we don't generate it. *)

type args = {
  infile : string;
  outfile : string;
  scope : scope;
  gen_allfv : bool;
  gen_fext : bool;
  gen_static_files : bool;
  force_overwrite : bool;
  version : coq_version;
  prelude : string;
}
(** Command line arguments. *)

type flags = { fl_allfv : bool 
             ; fl_fext : bool
             ; fl_version : coq_version }
(** Flags that can be read during code generation. *)
