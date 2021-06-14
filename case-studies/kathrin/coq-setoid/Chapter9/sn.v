Require Import core fintype.
Import ScopedNotations.
From Chapter9 Require Export wn.

(** ** Schäfer's Expression Relation *)

Inductive E_strong' {m} (L_A : tm m -> Prop) (s : tm m) :  Prop :=
 | E_strong_In  : (value s -> L_A s) -> (forall s', step s s' -> E_strong' L_A s') -> E_strong' L_A s.

(** Logical relation for lambda expressions *)
Fixpoint L_strong {m} (A : ty): tm m -> Prop :=
  match A with
  | Base => fun _ => True
  | Fun A1 A2 => fun e => match e with
                      |  (lam B s) => forall k (xi: fin m -> fin k) v, E_strong' (L_strong A1) v -> E_strong' (L_strong A2) (subst_tm (v .: (xi >> var_tm)) s)
                      | _ => False
                      end
  end.


Definition E_strong {m} (A : ty) : tm m -> Prop :=
  E_strong' (L_strong A).

Lemma E_strong_sn {m} (s : tm m) A:
  E_strong A s -> sn step s.
Proof.
  induction 1. constructor. intros s' HH. eauto.
Qed.

Lemma E_strong_step {m} (s: tm m) L_A :
  E_strong' L_A s -> forall s', step s s' -> E_strong' L_A s'.
Proof.
 induction 1; eauto.
Qed.

Lemma E_strong_base {m} (s: tm m) A :
  value s -> E_strong A s -> L_strong A s.
Proof.
  intros C []; eauto.
Qed.

Lemma E_strong_var {m} A (x: fin m) :
  E_strong A (var_tm x).
Proof.
  constructor; eauto.
  - cbn. contradiction.
  - intros. inversion H.
Qed.

Definition G_strong {k m} (Gamma : ctx k) : (fin k -> tm m)  -> Prop :=
  fun σ => forall (x : fin k), E_strong (Gamma x) (σ x) .

Definition has_ty_sem_strong {m} (Gamma : ctx m) (s: tm m) (A: ty) : Prop :=
  forall k (sigma: fin m -> tm k), G_strong Gamma sigma -> E_strong A (subst_tm sigma s).

Lemma L_close_ren_lam m n (xi: fin m -> fin n) s A :
  L_strong A s -> L_strong A (ren_tm xi s).
Proof.
  induction A; eauto.
  destruct s; try contradiction.
  subst. intros. cbn in *. intros. asimpl. eauto.
Qed.

Lemma close_ren  :
  (forall m n (xi: fin m -> fin n) s A, E_strong A s -> E_strong A (ren_tm xi s)).
Proof.
  intros. induction H.
  constructor; eauto. intros.
  assert (value s) by (now destruct s).
  specialize (H H3). now apply L_close_ren_lam.
  intros. apply step_naturality in H2. destruct H2 as (?&?&?); subst.
  apply H1; eauto.
Qed.

Lemma value_anti_renaming_lam m n s (xi: fin m -> fin n) :
  value (ren_tm xi s) -> value s.
Proof.
  destruct s;  eauto.
Qed.

Require Import Setoid Morphisms.

Instance G_strong_morphism {k m} (Gamma : ctx k) :
  Proper (pointwise_relation _ eq ==> Basics.impl) (@G_strong k m Gamma).
Proof.
Admitted.

Lemma sn_fundamental m Gamma (s: tm m) A :
  has_type Gamma s A -> has_ty_sem_strong Gamma s A.
Proof.
  intros C. induction C as [x | n Gamma A B s H IH | n Gamma A B s t H IH H' IH'].
  - unfold has_ty_sem_strong. intros. cbn. apply H.
  - intros k sigma ctx. cbn.
    assert (sn step (subst_tm (up_tm_tm sigma) s)).
    { eapply E_strong_sn. unfold has_ty_sem_strong in IH. apply IH.
      intros [|]; intros.
      - cbn. unfold funcomp. apply close_ren. eauto.
      - cbn. apply E_strong_var. }
    remember (subst_tm (up_tm_tm sigma) s) as s'.
    unfold has_ty_sem_strong in IH.
    assert (forall m (tau : fin (S k) -> tm m), G_strong (A .: Gamma) (up_tm_tm sigma >> subst_tm tau) -> E_strong B (subst_tm tau s')).
    { intros. rewrite Heqs'. revert H1. asimpl. eauto.
      (* TODO adrian here we would want to rewrite with scons_comp' in H' but it does not work since G_strong was not declared as a morphism *)
      (* intros H'. apply IH. asimpl in H'. *)
      (* eauto. *)  }
    clear Heqs'.
    induction H0. constructor.
    + intros V m . intros. apply H1.
      intros [|]; intros; cbn; eauto.
      * unfold funcomp. asimpl.
        (* adrian: I had to add the following line so that renamify works *)
        change (fun x0 : fin k => @var_tm m (xi x0)) with (funcomp var_tm xi).
        renamify. eauto.
        eapply close_ren. eauto.
    + intros. inv H3.
      apply H2; eauto.
      intros. specialize (H1 _ _ H4). eapply E_strong_step; eauto.
      eauto using step_inst.

  - intros k sigma D.
    specialize (IH _ _ D). specialize (IH' _ _ D).
    cbn.
    remember (subst_tm sigma s) as s'. remember (subst_tm sigma t) as t'.
    apply E_strong_sn in IH as IH1'. apply E_strong_sn in IH' as IH2'.
    clear s t Heqs' Heqt' H H'.
    revert t' IH' IH2'. induction IH1' as [s].
    intros t' IH2 IH2'. induction IH2' as [t].
    constructor.
    + contradiction.
    + intros ? HH. inv HH; eauto using E_strong_step.
      * apply E_strong_base in IH.
       -- cbn in IH.
          specialize (IH _ id t). eapply IH.
        assumption.
       -- reflexivity.
     * apply H0; eauto. eapply E_strong_step; eauto.
     * apply H2; eauto. eapply E_strong_step; eauto.
Qed.

Lemma sn (Gamma : fin 0 -> ty) (s: tm 0) A:
  has_type Gamma s A -> sn step s.
Proof.
  intros H%sn_fundamental.
  unfold has_ty_sem_strong in H.
  replace s with (s[ids]) by (now asimpl).
  eapply E_strong_sn. eapply H. intros [].
Qed.
