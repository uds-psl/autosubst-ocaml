(** ** Reduction and Values *)

Require Export ARS Coq.Program.Equality.
From Chapter9 Require Export stlc.
Set Implicit Arguments.
Unset Strict Implicit.

Ltac inv H := dependent destruction H.
Hint Constructors star.

(** *** Single-step reduction *)
Inductive step {n} : tm n -> tm n -> Prop :=
| step_beta A b t : step (app (lam A b) t) (b[t..])
| step_abs A b1 b2 : @step (S n) b1 b2 -> step (lam A b1) (lam A b2)
| step_appL s1 s2 t : step s1 s2 -> step (app s1 t) (app s2 t)
| step_appR s t1 t2 : step t1 t2 -> step (app s t1) (app s t2).

Hint Constructors step.

Lemma step_beta' n A b (t t': tm n):
  t' = b[t..] -> step (app (lam A b) t) t'.
Proof. intros ->. now constructor. Qed.

(** *** Multi-step reduction *)

Lemma mstep_lam n A (s t : tm (S n)) :
  star step s t -> star step (lam A s) (lam A t).
Proof. induction 1; eauto. Qed.

Lemma mstep_app n (s1 s2 : tm n) (t1 t2 : tm n) :
  star step s1 s2 -> star step t1 t2 -> star step (app s1 t1) (app s2 t2).
Proof with eauto.
  intros ms. induction 1. induction ms... auto...
Qed.

(** *** Substitutivity *)

Lemma step_inst {m n} (f : fin m -> tm n) (s t : tm m) :
  step s t -> step (subst_tm f s) (subst_tm f t).
Proof.
   intros st. revert n f.  induction st as  [m b s t |m A b1 b2 _ ih|m s1 s2 t _ ih|m s t1 t2 _ ih]; intros n f; cbn.
  - apply step_beta'. now asimpl.
  - apply step_abs. eapply ih.
  - apply step_appL, ih.
  - apply step_appR, ih.
Qed.

Lemma mstep_inst m n (f : fin m -> tm n) (s t : tm m) :
  star step s t -> star step (s[f]) (t[f]).
Proof. induction 1; eauto using step_inst. Qed.

Lemma mstep_subst m n (f g : fin m -> tm n) (s t : tm m) :
  star step s t -> (forall i, star step (f i) (g i)) ->
  star step (s[f]) (t[g]).
Proof with eauto.
  intros st fg.
  apply star_trans with (y := t[f]); [eauto using mstep_inst|].
  clear s st. revert n f g fg.
  induction t; eauto using mstep_app; intros; simpl.
  - cbn. apply mstep_lam. apply IHt. intros [i|]; [|constructor].
    + asimpl.  cbn. unfold funcomp. substify. now apply mstep_inst.
Qed.

Lemma mstep_beta n (s1 s2 : tm (S n)) (t1 t2 : tm n) :
  star step s1 s2 -> star step t1 t2 ->
  star step (s1 [t1..]) (s2 [t2..]).
Proof.
  intros st1 st2. apply mstep_subst; [assumption|].
  now intros [|].
Qed.

Lemma step_naturality m n (M: tm m) (rho: fin m -> fin n) M' :
  step (M ⟨rho⟩) M' -> exists M'', step M M'' /\ M' = (M'' ⟨rho⟩).
Proof.
  intros H.
  dependent induction H.
  - destruct M; try inversion x. subst.
    destruct M1; try inversion H0. subst.
    exists (M1[M2..]). split. eauto.
    asimpl. reflexivity.
  - destruct M; inversion x. subst.
    edestruct (IHstep _ M) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - destruct M; inversion x. subst.
    edestruct (IHstep _ M1) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - destruct M; inversion x. subst.
    edestruct (IHstep _ M2) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
Qed.

Definition value {m} (e : tm m) : Prop :=
  match e with
  | lam  _ _ => True
  | _ => False
  end.

Lemma value_anti {m n} (xi : fin m -> fin n) (s : tm m) :
  value (s⟨xi⟩) -> value s.
Proof.
  destruct s; eauto.
Qed.
