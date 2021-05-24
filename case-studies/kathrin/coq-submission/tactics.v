Require Import header_extensible.

(** ** Tactics for modular syntax  *)

Ltac automate_inj :=
repeat (match goal with
  | [H : ?s = ?s |- _ ] => clear H
  | [H : _ = _ |- _] => apply retract_inj in H; inversion H; subst
  end).

Hint Rewrite @retract_tight @retract_works: retract_forward.
Hint Rewrite @retract_tight @retract_works : retract_rev.

Class Imp X Y := imp:  X -> Y.
Class ImpRev X Y := imprev:  X -> Y.

Ltac msimpl := try reflexivity; repeat progress (first [ progress (autorewrite with retract_forward)  | cbn]).

Ltac msimpl_in H := try apply retract_tight in H;
                   try apply imprev in H;
                   repeat progress (first [  progress (autorewrite with retract_rev in H) | cbn in H]).

Ltac minversion H := msimpl_in H; try apply imprev in H; inversion H; repeat automate_inj; subst.
Ltac induction_ H := msimpl_in H; try apply imprev in H; induction H; repeat automate_inj; subst.

Ltac mconstructor := msimpl; try apply imprev; eapply imp; econstructor.

Ltac mapply H := msimpl; try apply imprev; try (msimpl_in H);try (apply imprev in H);  eapply H.

Ltac mapply_in H1 H2 := msimpl_in H1; try (msimpl_in H2); eapply H2 in H1.
