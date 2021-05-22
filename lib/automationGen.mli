open GallinaGen

module TacGen : sig
  type t
  type locus_clause_expr

  val default_locus_clause : locus_clause_expr
  val star_locus_clause : locus_clause_expr

  val idtac_ : t
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
  val cbn_ : string list -> t
  val intros_ : string list -> t
  val unfold_ : ?locus_clause:locus_clause_expr -> string list -> t
  (* val notation_ : Constrexpr.constr_expr -> t *)

  val pr_tactic_ltac : string -> t -> Pp.t
  val pr_tactic_notation : string list -> t -> Pp.t
end

module NotationGen : sig
  open Vernacexpr

  type g_assoc = Gramlib.Gramext.g_assoc
  type t = NG_VarConstr of string * string
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


  val notation_string : t -> string
  val notation_modifiers : t -> syntax_modifier list
  val notation_scope : t -> scope_name
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

type t = {
  asimpl_rewrite_lemmas : string list;
  asimpl_cbn_functions : string list;
  asimpl_unfold_functions : string list;
  substify_lemmas : string list;
  auto_unfold_functions : string list;
  arguments : (string * string list) list;
  classes : (ClassGen.t * string) list;
  (* instance info probably also needs parameter information *)
  instances : (ClassGen.t * string) list;
  notations : (NotationGen.t * constr_expr) list;
}

val initial : t

val asimpl_rewrite_lemmas : t -> string list
val asimpl_cbn_functions : t -> string list
val asimpl_unfold_functions : t -> string list
val substify_lemmas : t -> string list
val auto_unfold_functions : t -> string list
val arguments : t -> (string * string list) list
val classes : t -> (ClassGen.t * string) list
val instances : t -> (ClassGen.t * string) list
val notations : t -> (NotationGen.t * constr_expr) list
