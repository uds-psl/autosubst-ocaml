type tactic_expr
type locus_clause_expr

val default_locus_clause : locus_clause_expr
val star_locus_clause : locus_clause_expr

val idtac_ : tactic_expr
val rewrite_ : ?repeat_star:bool -> ?with_evars:bool -> ?to_left:bool -> ?locus_clause:locus_clause_expr -> string -> tactic_expr
val repeat_ : tactic_expr -> tactic_expr
val first_ : tactic_expr list -> tactic_expr
val progress_ : tactic_expr -> tactic_expr
val try_ : tactic_expr -> tactic_expr
val calltac_ : string -> tactic_expr
val calltacArgs_ : string -> string list -> tactic_expr
val calltacTac_ : string -> tactic_expr -> tactic_expr
val then1_ : tactic_expr -> tactic_expr -> tactic_expr
val then_ : tactic_expr list -> tactic_expr
val cbn_ : string list -> tactic_expr
val intros_ : string list -> tactic_expr
val unfold_ : ?locus_clause:locus_clause_expr -> string list -> tactic_expr
val notation_ : Constrexpr.constr_expr -> tactic_expr

val pr_tactic_ltac : string -> tactic_expr -> Pp.t
val pr_tactic_notation : string list -> tactic_expr -> Pp.t

type tactic_info = {
  asimpl_rewrite_lemmas : string list;
  asimpl_cbn_functions : string list;
  asimpl_unfold_functions : string list;
  substify_lemmas : string list;
  auto_unfold_functions : string list;
  (* instance info probably also needs parameter information *)
  instance_infos : (ClassGen.instance_type * string * GallinaGen.constr_expr list) list;
}

