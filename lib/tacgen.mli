open Ltac_plugin.Tacexpr

type tactic = raw_tactic_expr

val rewrite_ : ?repeat_star:bool -> ?with_evars:bool -> ?to_left:bool -> ?locus_clause:(Names.lident Locus.clause_expr) -> string -> tactic
val repeat_ : tactic -> tactic
val first_ : tactic list -> tactic
val progress_ : tactic -> tactic
val calltac_ : string -> tactic
val calltacArgs_ : string -> string list -> tactic
val calltacTac_ : string -> tactic -> tactic
val then_ : tactic -> tactic -> tactic
val cbn_ : string list -> tactic
val unfold_ : string list -> tactic
val notation_ : Constrexpr.constr_expr -> tactic

val pr_tactic : string -> tactic -> Pp.t
val pr_tactic_notation : string list -> tactic -> Pp.t

module GenTests : sig
  val myasimpl' : Pp.t
  val myasimpl : Pp.t
  val myasimpl_hyp : Pp.t
  val myauto_case : Pp.t
  val myrenamify : Pp.t
  val myrewritestar : Pp.t
end
