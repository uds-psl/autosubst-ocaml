From Chapter7 Require Export expressions.

(* * General Definitions: Star/transitivity of star. *)

Inductive sn {X} (R : X -> X -> Prop) (x : X) : Prop :=
  | SNI :  (forall y, R x y -> sn R y) -> sn R x.

Inductive star {X} (R : X -> X -> Prop) : X -> X -> Prop :=
| srefl e : star R e e
| strans {e1 e2 e3} : R e1 e2 -> star R e2 e3 -> star R e1 e3.

Hint Constructors sn star.

Lemma star_trans {X} (R : X -> X -> Prop) e1 e2 e3 :
  star R e1 e2 -> star R e2 e3 -> star R e1 e3.
Proof.
  induction 1. auto. induction 1; eauto using strans.
Qed.
