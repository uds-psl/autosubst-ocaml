open GallinaGen

module TacGen : sig
  type t
  type locus_clause_expr

  val default_locus_clause : locus_clause_expr
  val star_locus_clause : locus_clause_expr

  val idtac_ : t
  val setoid_rewrite_ : ?to_left:bool -> string -> t
  val rewrite_ : ?repeat_star:bool -> ?with_evars:bool -> ?to_left:bool -> ?locus_clause:locus_clause_expr -> string -> t
  val repeat_ : t -> t
  val first_ : t list -> t
  val progress_ : t -> t
  val try_ : t -> t
  val calltac_ : string -> t
  val calltacArgs_ : string -> string list -> t
  val calltacTac_ : string -> t -> t
  val then1_ : t -> t -> t
  val then_ : t list -> t
  val cbn_ : ?locus_clause:locus_clause_expr -> string list -> t
  val intros_ : string list -> t
  val unfold_ : ?locus_clause:locus_clause_expr -> string list -> t
  (* val notation_ : Constrexpr.constr_expr -> t *)

  val pr_tactic_ltac : string -> t -> Pp.t
  val pr_tactic_notation : string list -> t -> Pp.t
end

module ClassGen : sig
  type t = Ren of int
         | Subst of int
         | Var
         | Up of string

  val instance_name : string -> t -> string
  val class_name : string -> t -> string
  val function_name : string -> t -> string
  val class_args : t -> constr_expr list
  val class_field : string -> t -> string
  val instance_unfolds : string -> t -> string list
end

module NotationGen : sig
  open Vernacexpr

  type g_assoc = Gramlib.Gramext.g_assoc
  type t = VarConstr
         | VarInst
         | Var
         | Up
         | UpInst of string
         | SubstApply of string list
         | Subst of string list
         | RenApply of string list
         | Ren of string list

  val fscope : scope_name
  val subst_scope : scope_name

  val level_ : int -> syntax_modifier
  val assoc_ : g_assoc -> syntax_modifier
  val format_ : string -> syntax_modifier
  val only_print_ : syntax_modifier


  val notation_string : string -> t -> string
  val notation_modifiers : string -> t -> syntax_modifier list
  val notation_scope : t -> scope_name
  val notation_body : string -> t -> constr_expr
end

type t = {
  asimpl_rewrite_no_fext : string list;
  asimpl_rewrite_fext : string list;
  asimpl_rewrite_base : string list;
  asimpl_cbn_functions : string list;
  asimpl_unfold_functions : string list;
  substify_lemmas_fext : string list;
  substify_lemmas : string list;
  auto_unfold_functions : string list;
  arguments : (string * string list) list;
  classes : (ClassGen.t * string) list;
  proper_instances : (string * string * string) list;
  instances : (ClassGen.t * string * string list) list;
  notations : (NotationGen.t * string) list;
}

val initial : t

val asimpl_rewrite_no_fext : t -> string list
val asimpl_rewrite_fext : t -> string list
val asimpl_rewrite_base : t -> string list
val asimpl_cbn_functions : t -> string list
val asimpl_unfold_functions : t -> string list
val substify_lemmas_fext : t -> string list
val substify_lemmas : t -> string list
val auto_unfold_functions : t -> string list
val arguments : t -> (string * string list) list
val classes : t -> (ClassGen.t * string) list
val proper_instances : t -> (string * string * string) list
val instances : t -> (ClassGen.t * string * string list) list
val notations : t -> (NotationGen.t * string) list
