(** ** Weak Head Normalisation *)

Require Import core core_axioms fintype fintype_axioms.
Import ScopedNotations.
From Chapter9 Require Export preservation.

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
    exists x. split; eauto.
    asimpl. eauto.
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
    (* TODO here we don't apply ext_tm because the goal is not an equality. How do we solve this?
     1. waybe write another tactic that does something like
     assert (H: s[sigma] = ?x) by now asimpl.
     rewrite H
     which would take the instantiation as an argument (or somehow infer it maybe with `match Goal with _ |- context[ subst_tm ... ])

    2. don't use simple apply in asimpl' but rather rewrite so that the normal asimpl tactic works here. But then we have the problem that ext_tm is much too general since we can rewrite every substitution with it. Maybe setoid rewriting can do it. We should somehow say that we can only rewrite with ext_tm if the substitution contains something that would be rewritten by renComp' (i.e. the one with funext)
    To do that we could form a predicate on subsitutions P : (nat -> tm) -> Prop
    with constructors for the atomic cases for renComp', renRen', etc. (so <xi> >> [sigma] / [sigma] >> [sigma], etc.)
    and other congruence constructors.
    Then declare a Proper instance to rewrite with ext_tm if the substitution fulfills the predicate.
    This might work but to build the proof of the predicate we probably need typeclasses which will probably lead to pain.

     *)
    (* assert (M[(@var_tm (S k) var_zero) .: sigma >> (ren_tm shift)][v .: xi >> (@var_tm m)] = M[_]) by (now asimpl). *)
    asimpl.
    (* rewrite renComp'_tm. *)
    specialize (IHC _ _ H1).
    destruct (IHC) as (v'&?&?).
    exists v'; split; eauto.
    revert H2.
    unfold funcomp. 
    setoid_rewrite rinstInst_tm'. eauto using mstep_inst.
  - destruct (IHC1 _ _  H) as (v1&?&?).
    destruct (IHC2  _ _ H) as (v2&?&?).
    destruct v1; try contradiction.
    cbn in H1.
    destruct (H1 _ id _ H3) as (v&?&?).
    exists v; split; eauto. asimpl.
    enough (star step (app  (lam t v1) v2) v).
    + eapply star_trans.
      eapply mstep_app; eauto. assumption.
    + eapply star_trans.
      * eright. econstructor; eauto. constructor.
      * now asimpl in H4.
Qed.
