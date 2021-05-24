(** * Appendix B: Strong Normalisation à la Girard *)

Require Import core core_axioms fintype fintype_axioms.
Import ScopedNotations.
From Chapter9 Require Export preservation sn_raamsdonk.
Open Scope fscope.

(** ** Strong Normalisation *)
Notation sn := (sn (@step _)).
Module SN.

(** *** SN Closure under Weakening *)
Lemma weak k (M: tm k) k' (xi : fin k -> fin k'):
  sn M -> sn (M ⟨xi⟩).
Proof.
  intros H. revert k' xi. induction H as [s H IH]; intros.
  apply SNI. intros s' A.
  destruct (step_naturality A) as (x''&B1&B2); subst.
  now apply IH.
Qed.

End SN.


(** ** The Reducibility Candidates/Logical Predicate*)
Definition cand n := tm n -> Prop.

Fixpoint L {k} (Gamma: ctx k) (T: ty) : cand k :=
  match T with
  |Base => fun M => Gamma |- M : T /\ sn M
  |Fun T1 T2 => fun M => Gamma |- M : Fun T1 T2 /\
                     (forall k' (N: tm k') (Delta: ctx k') xi, ltc Gamma Delta xi -> L Delta T1 N -> L Delta T2 (app (M⟨xi⟩) N))
  end.


Module L.

Lemma ren k k' (Gamma: ctx k) (Delta: ctx k') xi M T (Gamma_Delta : ltc Gamma Delta xi):
  L Gamma T M -> L Delta T (M ⟨xi⟩).
Proof.
  revert k k' Gamma Delta xi M Gamma_Delta.
  induction T; intros; split; eauto; asimpl.
  - apply typing_ren with (Gamma := Gamma); eauto. simpl in H. apply H.
  - apply SN.weak, H.
  - apply typing_ren with (Gamma := Gamma); eauto. apply H.
  - intros. asimpl. eapply H; eauto.
    + intros i. unfold funcomp. rewrite H0. eauto.
Qed.

Lemma L_typing {k} (Gamma: ctx k) (T: ty) M :
  L Gamma T M -> Gamma |- M : T.
Proof. intros H. destruct T; simpl in *; intuition. Qed.

Lemma preservation {k} (Gamma : ctx k) M M' T :
  step M M' -> L Gamma T M -> L Gamma T M'.
Proof.
  revert k Gamma M M'. induction T as [|T IHT S IHS]; intros k Gamma M M' M_M' [H1 H2].
  - split.
    + eauto using preservation.
    + inv H2. now apply H.
  - split; [|].
    + eauto using preservation.
    + intros k' N Delta xi H H0. apply IHS with (M := app (M⟨xi⟩) N).
      * econstructor. substify. now apply step_inst.
      * apply H2; eauto.
Qed.

Lemma preservation_mstep {k} (Gamma : ctx k) M M' T :
  star step M M' -> L Gamma T M -> L Gamma T M'.
Proof. induction 1; eauto using preservation. Qed.

Definition neutral {k} (M: tm k) :=
  match M with
  |lam _ _ => False
  |_ => True
  end.

(** Girard's theorem. *)
Lemma Girard k (Gamma: ctx k) (M : tm k) T :
  (L Gamma T M -> sn M) /\ (Gamma |- M : T -> neutral M -> (forall N, step M N -> L Gamma T N) -> L Gamma T M).
Proof.
  revert k M Gamma. induction T as [|T IHT S IHS]; intros k M Gamma; simpl in *.
  - intuition. constructor. intros N H'. firstorder.
  - split.
    + intros [H1 H2].
      assert ( L (T .: Gamma) S (app (M ⟨↑⟩) (@var_tm (1 + k) None))) as A.
      { apply H2; eauto. intros i; eauto. apply IHT; eauto. constructor. constructor.  intros N H. inv H. }
      revert A. substify. intros A.
      now apply IHS, sn_appL, sn_subst_tm in A.
    + intros H0 H1 H2. split; eauto.
      intros.
      assert (SN_N : sn N) by firstorder.
      induction SN_N as [N sn_N IHN].
      apply IHS; intros; eauto.
      * eapply ty_app.
        -- eapply typing_ren; try eassumption.
        -- auto using L_typing.
      * reflexivity.
      * inv H4.
        -- destruct M; cbn in *; try congruence. contradiction.
        -- destruct (step_naturality H4) as [M'' [H' ->]]. now apply H2.
        -- apply IHN; eauto. eapply preservation; eassumption.
Qed.

Lemma sn k (Gamma: ctx k) (M : tm k) T:
  L Gamma T M -> sn M.
Proof.
  intros H. eapply Girard. eassumption.
Qed.

Lemma var k (Gamma: ctx k) x :
  L Gamma (Gamma x) (ids x).
Proof. apply Girard; intros; eauto. constructor. constructor.  inv H. Qed.

End L.

(** ** Closure under beta expansion and the fundamental theorem *)

Lemma beta_closure k Gamma (N: tm k) T (N_ty : Gamma |- N : T) :
  sn N -> forall S M, (T .: Gamma) |- M : S ->  L Gamma S (M[N..]) -> L Gamma S (app (lam T M) N).
Proof.
  induction 1 as [N H IH_N]. intros S M M_ty H'.
  assert (sn_M := sn_subst_tm _ _ (L.sn _ _ _ _ H')). induction sn_M as [M sn_M IH_M].
  apply L.Girard; eauto.
  - repeat econstructor; eauto.
  - constructor.
  - intros M' H1. inv H1; eauto.
    + inv H1. apply IH_M; eauto using preservation, step_inst, L.preservation, step_naturality.
    + apply IH_N; eauto using preservation, L.preservation_mstep, mstep_beta.
Qed.

Theorem fundamental_theorem k (Gamma: ctx k) M T :
  Gamma |- M : T -> forall k' (Gamma': ctx k') sigma,  (forall x,  L Gamma' (Gamma x) (sigma x)) -> L Gamma' T (M[sigma]).
Proof.
  induction 1 as [| k Gamma T S M H IH | k Gamma T S M N A IHA B IHB]; intros k' Gamma' sigma adm; asimpl.
  - apply adm.
  - cbn. intros.
    assert ( M_ty :  (T .: Gamma') |- (M[ids var_zero .: sigma >> ⟨↑⟩]) : S).
    { assert ( A: forall x, Gamma' |- sigma x : Gamma x) by auto using L.L_typing.
      apply typing_inst with (Gamma := T .: Gamma); eauto.
      intros [i|]; [|constructor]. asimpl. apply typing_ren with (Gamma := Gamma'); eauto. intros x; eauto.  }
    split.
    + now apply ty_abs.
    + intros k'0 N Delta xi A B.
      apply beta_closure; eauto using L.L_typing, L.sn.
      * apply typing_ren with (Gamma := T .: Gamma'); [intros [i|]; simpl; congruence | assumption] .
      * asimpl. apply IH.
        intros [i|]; eauto. cbn. unfold funcomp.
        (* adrian: had to insert the following line *)
        change (fun x : fin k' => @var_tm k'0 (xi x)) with (funcomp var_tm xi).
        renamify. apply L.ren with (Gamma := Gamma'); eauto.
  - destruct (IHA _ _ _ adm) as [IHA1 IHA2]. specialize (IHB _ _ _ adm).
    assert (HH : ltc Gamma' Gamma' id) by now intros.
    specialize (IHA2 _ _ _ id HH IHB). now asimpl in IHA2.
Qed.

Corollary strong_normalisation k (Gamma: ctx k) M T :
  Gamma |- M : T -> sn M.
Proof.
  intros A. apply L.sn with (Gamma := Gamma) (T := T).
  enough (H: L Gamma T  (M[ids])) by now (revert H; asimpl).
  apply fundamental_theorem with (Gamma := Gamma); auto using L.var.
Qed.
