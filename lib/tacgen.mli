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

val pr_tactic : string -> tactic_expr -> Pp.t
val pr_tactic_notation : string list -> tactic_expr -> Pp.t

type tactic = TacticLtac of string * tactic_expr
            | TacticNotation of string list * tactic_expr

val pr_tactic : tactic -> Pp.t

type autosubst_tactics = { as_tactics : tactic list; as_fext_tactics: tactic list }

module GenTests : sig
  val myasimpl' : Pp.t
  val myasimpl : Pp.t
  val myasimpl_hyp : Pp.t
  val myauto_case : Pp.t
  val myrenamify : Pp.t
  val myrewritestar : Pp.t
end
