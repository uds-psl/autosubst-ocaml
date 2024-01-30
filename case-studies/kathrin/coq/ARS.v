(** * Appendix A -- Abstract Reduction Systems. *)

(** ** Tactics *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Equality.

Declare Scope prop_scope.
Delimit Scope prop_scope with PROP.
Open Scope prop_scope.

Ltac inv H := inversion H; subst; clear H.

(** Code by Adam Chlipala. *)
Ltac not_in_context P :=
  match goal with
    |[_ : P |- _] => fail 1
    | _ => idtac
  end.

(** Code by Adam Chlipala. Extend context by proposition of  given proof. Fail if proposition is already in context. *)
Ltac extend H :=
let A := type of H in not_in_context A; generalize H; intro.

Definition Rel  (T : Type) := T -> T -> Prop.

(** Union of two relations *)
Inductive Or {X} (R R': X -> X -> Prop) : X -> X -> Prop :=
| Inl x y : R x y -> Or R R' x y
| Inr x y : R' x y -> Or R R' x y.

#[global] Hint Constructors Or : core.


(** ** Reflexive, Transitive closure *)

Section Definitions.

Variables (T : Type) (e : Rel T).
Implicit Types (R S : T -> T -> Prop).

Inductive star (x : T) : T -> Prop :=
| starR : star x x
| starSE y z : e x y -> star y z -> star x z.

Hint Constructors star : core.
#[local] Hint Resolve starR : core.


Lemma star1 x y : e x y -> star x y.
Proof. intros. eapply starSE; eauto. Qed.

Lemma star_trans y x z : star x y -> star y z -> star x z.
Proof.
  intros H H'. revert x H.
  induction H' as [|x y z H1 H2 IH]; intros; eauto. eapply IH. induction H; eauto.
Qed.

End Definitions.
#[global] Hint Constructors star : core.

Arguments star_trans {T e} y {x z} A B.

Lemma star_img T1 T2 (f : T1 -> T2) (e1 : Rel T1) e2 :
  (forall x y, e1 x y -> star e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof.
  intros ? x y H. induction H; eauto.
  eapply star_trans with (y  := f y); eauto.
Qed.

Lemma star_hom T1 T2 (f : T1 -> T2) (e1 : Rel T1) (e2 : Rel T2) :
  (forall x y, e1 x y -> e2 (f x) (f y)) ->
  (forall x y, star e1 x y -> star e2 (f x) (f y)).
Proof.
  intros. induction H0; eauto.
Qed.

Arguments star_hom {T1 T2} f e1 {e2} A x y B.

Inductive plus {X} (R : X -> X -> Prop) : X -> X -> Prop :=
 | plusR s t u : R s t -> star R t u -> plus R s u.

#[global] Hint Constructors plus star : core.

Lemma star_plus {X} (R: X -> X -> Prop) s t :
  star R s t -> star (plus R) s t.
Proof.
  induction 1; eauto.
Qed.


(** ** Strong Normalisation *)

Inductive sn T (e: Rel T)  : T -> Prop :=
| SNI x: (forall y, e x y -> sn e y) -> sn e x.

#[global] Hint Immediate SNI : core.

Definition morphism {T1 T2} (R1 : Rel T1) (R2 : Rel T2) (h : T1 -> T2) :=
  forall x y, R1 x y -> R2 (h x) (h y).

#[global] Hint Unfold morphism : core.

(** Morphism lemma, due to Steven Schäfer. *)
Fact sn_morphism {T1 T2} (R1 : Rel T1) (R2 : Rel T2) (h : T1 -> T2) x :
  morphism R1 R2 h -> sn R2 (h x) -> sn R1 x.
Proof.
  intros H H1.
  remember (h x) as a eqn:H2. revert x H2.
  induction H1 as [a _ IH]. intros x ->.
  constructor. intros y H1 % H.
  apply (IH _ H1). reflexivity.
Qed.

Lemma sn_orL X (R R' : X -> X -> Prop) s:
  sn (Or R R') s -> sn R s.
Proof.
  intros H. induction H.
  constructor; intros; eauto.
Qed.

Lemma sn_orR X (R R' : X -> X -> Prop) s:
  sn (Or R R') s -> sn R' s.
Proof.
  intros H. induction H.
  constructor; intros; eauto.
Qed.


(** Forward Propagation. *)
Fact sn_forward_star X (R : X -> X -> Prop)  s t : sn R s -> star R s t -> sn R t.
Proof.
  intros H. revert t. induction H.
  intros. inv H1.
  - now constructor.
  - eapply H0; eauto.
Qed.

(** Strong normalisation of a relation <-> strong normalisation of its transitive closure. *)
Lemma sn_plus {X} (R : X -> X -> Prop) x:
  sn R x <-> sn (plus R) x.
Proof.
  split.
  - induction 1.
    constructor. intros. destruct H1.
    specialize (H0 _ H1).
    apply sn_forward_star with (s := t); eauto using star_plus.
  - apply sn_morphism with (h := @id X).
    unfold morphism. econstructor; eauto.
Qed.

(** ** Local confluence, confluence, and Newman's Lemma.

Proofs by Gert Smolka, Semantics. *)

Definition locally_confluent {X} (R: X -> X -> Prop) :=
  forall s t, R s t -> forall t', R s t' -> exists u, star R t u /\ star R t' u.

Definition confluent {X} (R: X -> X -> Prop) :=
  forall s t, star R s t -> forall t', star R s t' -> exists u, star R t u /\ star R t' u.

Definition terminating {X} (R : X -> X -> Prop) :=
  forall x, sn R x.

#[global] Hint Unfold terminating : core.

Fact newman {X} (R : X -> X -> Prop) :
  terminating R -> locally_confluent R -> confluent R.
Proof.
  intros H1 H2 x.
  generalize (H1 x).
  induction 1 as [x _ IH].
  intros y1 H3 y2 H4.
  destruct H3 as [|y1 y1' H5 H6].
  { exists y2; eauto. }
  destruct H4 as [|y2 y2' H7 H8].
  { exists y1'. eauto. }
  assert (exists u,  (star R) y1 u /\ star R y2 u) as (u&H9&H10).
  { eapply H2; eauto. }
  assert (exists v, (star R) u v /\ star R y2' v) as (v&H11&H12).
  { eapply (IH y2); eauto. }
  assert (exists w, (star R) y1' w /\ star R v w) as (w&H13&H14).
  { eapply (IH y1); eauto using star_trans. }
  exists w. eauto using star_trans.
Qed.