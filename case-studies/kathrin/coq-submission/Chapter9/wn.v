(** ** Weak Head Normalisation *)

From Chapter9 Require Export preservation.
Require Export fintype. 
 


Definition E_ {m} (L: tm m -> Prop)  (s : tm m) : Prop :=
  exists v, star step s v /\ L v.

Fixpoint L {m} (A : ty): tm m -> Prop :=
  match A with
  | Base => fun s => exists v, star step s v /\ value v
  | Fun A1 A2 => fun e => match e with
                      | (lam B s) => forall k (xi: fin m -> fin k) v, L A1 v -> E_ (L A2) (subst_tm (scons v (xi >> var_tm)) s)
                      | _ => False
                      end
  end.

Lemma L_ren {m n} s A (xi: fin m -> fin n) :
  L A s -> L A (ren_tm xi s).
Proof.
  revert m n s xi. induction A; eauto; intros m n s xi.
  - intros (?&?&?).
    exists (x⟨xi⟩). split.
    + substify. eauto using mstep_inst.
    + destruct x; eauto.
  - intros.
    destruct s; try contradiction.
    intros k zeta v H''. cbn in H. specialize (H _ (xi >> zeta) _ H'').
    destruct H as (?&?&?).
    exists x. split; eauto. asimpl. eauto.
Qed.

Definition G {m k} (Gamma : ctx m) : (fin m -> tm k)  -> Prop :=
  fun σ => forall (x : fin m), L (Gamma x) (σ x) .

Definition has_ty_sem {m} (Gamma : ctx m) (s: tm m) (A: ty) : Prop :=
  forall k (sigma: fin m -> tm k), G Gamma sigma -> E_ (L A) (subst_tm sigma s).

Lemma val_inclusion {m} A (e: tm m) :
  L A e -> E_ (L A) e.
Proof. intros. unfold E_. exists e. split; eauto. Qed.

Lemma wn_fundamental_lam {m} Gamma (s: tm m) A:
  has_type Gamma s A -> has_ty_sem Gamma s A.
Proof.
  intros C. unfold has_ty_sem, E_. induction C; subst; intros.
  - eauto.
  - apply val_inclusion. asimpl.
    intros m. intros.
    assert (G (S1 .: Gamma) (v .: (sigma >> ren_tm xi))).     { unfold G. intros [|]; cbn; eauto.
      - cbn in *. specialize (H f). now apply L_ren. }
    asimpl.
    specialize (IHC _ _ H1).
    destruct (IHC) as (v'&?&?).
    exists v'; split; eauto.
    revert H2. rewrite rinstInst_tm. eauto using mstep_inst.
  - destruct (IHC1 _ _  H) as (v1&?&?).
    destruct (IHC2  _ _ H) as (v2&?&?).
    destruct v1; try contradiction.
    cbn in H1.
    destruct (H1 _ id _ H3) as (v&?&?).
    exists v; split; eauto. asimpl.
    enough (star step (stlc.app  (lam t v1) v2) v).
    + eapply star_trans.
      eapply mstep_app; eauto. assumption.
    + eapply star_trans.
      * eright. econstructor; eauto. constructor.
      * now asimpl in *.
Qed.
