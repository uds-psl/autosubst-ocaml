(** ** Raamsdonk's Characterisation *)

Require Import core fintype.
Import ScopedNotations.
From Chapter9 Require Export reduction.

Lemma sn_mstep {n} (s t : tm n):
  star step s t -> sn step s -> sn step t.
Proof.
  eauto using sn_forward_star.
Qed.

Inductive SN : forall {n}, tm n -> Prop :=
| SNeu n (M: tm n): SNe M -> SN M
| SAbs n A (M: tm (S n)) : SN M -> SN (lam A M)
| SRed n (M M': tm n): SNRed M M' -> SN M' -> SN M
with SNe : forall {n}, tm n -> Prop :=
| SVar n (x: fin n) : SNe (ids x)
| SApp n (R: tm n) M : SNe R -> SN M -> SNe (app R M)
with SNRed : forall {n}, tm n -> tm n -> Prop :=
| SBeta n A (M : tm (S n)) N M': SN N -> M' = M[N..] -> SNRed (app (lam A M) N) M'
| SAppl n (R R': tm n) M : SNRed R R' -> SNRed (app R M) (app R' M).

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2  := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.


Lemma sn_appL {n} (s : tm n) (t : tm n) :
  sn step (app s t) -> sn step s.
Proof. apply (@sn_morphism _ _ _ _ (fun s => app s t)); eauto using @step. Qed.

Lemma sn_subst_tm {m n} (f : fin m -> tm n) (s : tm m) :
  sn step (subst_tm f s) -> sn step s.
Proof. apply sn_morphism. eauto using step_inst. Qed.

Lemma closed_lam {n}  (s : tm (S n)) A:
  sn step s -> sn step (lam A s).
Proof.
  induction 1 as [M H IH]. constructor. intros M' C. inv C. auto.
Qed.

Lemma closed_appR n (M: tm n) (N: tm n)  :
  sn step (app M N) -> sn step N.
Proof. eapply sn_morphism. eauto. Qed.

Set Implicit Arguments.
Unset Strict Implicit.

(** Weak Head Reduction *)
Inductive redsn : forall n,  tm n -> tm n -> Prop :=
 | redsn_beta n A (M: tm (S n)) (N: tm n) : sn step N -> redsn (app (lam A M) N) (subst_tm (N.:ids) M)
 | redsn_app n (R R' : tm n) (M : tm n) : redsn R R' -> redsn (app R M) (app R' M).

Lemma fundamental_backwards n (M: tm (S n)) (N: tm n) A:
   sn step N -> sn step (subst_tm (N.: ids) M) -> sn step (app (lam A M) N).
Proof.
  intros sn_N sn_M'.
  assert (H: sn step M) by (now apply sn_subst_tm in sn_M').
  revert M H sn_M'. induction sn_N as [N sn_N IH_N].
  induction 1 as [M sn_M IH_M]. intros H. constructor. intros M' C. inv C.
  - constructor. intros M' H'. inv H. now apply H.
  - inv C. rename b2 into M'. eapply IH_M. assumption.
    eauto using sn_mstep, mstep_beta.
  - eapply IH_N; eauto.
    + eauto using sn_mstep, mstep_beta.
Qed.

(** Neutral terms *)
Fixpoint neutral n (M: tm n) :=
  match M with
  | var_tm  x => True
  | app  s t => neutral s
  | _ => False
  end.

Lemma neutral_preservation n (M N: tm n):
  neutral  M -> step M N ->  neutral N.
Proof. intros H. induction 1; simpl in *; intuition. Qed.

Lemma sn_confluence n (M: tm n):
  forall M' M'', redsn M M' -> step M M'' -> M' = M'' \/ exists M''', redsn M'' M''' /\ star step M' M'''.
Proof.
  induction M as [x | T M IHM | M1 IHM1 M2 IHM2]; intros M' M'' D E; inv D; inv E.
  - now left.
  - inv E. right. eexists. split.
    + now constructor.
    + apply mstep_inst. eauto.
  - right. eexists. split. econstructor. inv H; eauto. apply mstep_beta; eauto.
  - inv D.
  - destruct (IHM _ _ D E) as [IH|(M''&IH1&IH2)].
    + subst. now left.
    + right. eexists. split.
      * econstructor. eassumption.
      * eapply mstep_app. assumption. constructor.
  - right. eexists. split.
    + constructor. eassumption.
    + eapply mstep_app. constructor. eauto.
Qed.

Lemma redsn_backwards n (M M': tm n):
 redsn M M' -> sn step M' -> sn step M.
Proof.
 induction 1 as [|n M M' N H IH].
 - intros D. eapply fundamental_backwards; eauto.
 - intros D. specialize (IH (sn_appL _ _ D)).
   assert (sn_N: sn step N) by (now apply closed_appR in D).
   revert M IH M' D H. induction sn_N as [N sn_N IH_N]. induction 1 as [M sn_M IH_M].
   constructor. intros M_N C. inv C.
   + inv H.
   + destruct (sn_confluence H C) as [E|(M'''&C1&C2)].
     * now subst.
     * eapply IH_M with (M' := M'''); eauto.
       eapply sn_mstep; [|eassumption]. eapply mstep_app; eauto.
   + eapply IH_N; eauto.
     * inv D. apply H. now constructor.
Qed.

Lemma sn_app_neutral n (N : tm n) :
   sn step N -> forall (M: tm n), neutral M -> sn step M -> sn step (app M N).
Proof.
  induction 1 as [N sn_N IH_N].
  induction 2 as [M sn_M IH_M].
  constructor. intros M' C. inv C.
  - contradiction.
  - eauto using neutral_preservation.
  - eauto using sn.
Qed.

Lemma SN_sn :
  (forall n (M: tm n), SN M -> sn step M)
/\ (forall n (M: tm n), SNe M -> sn step M /\ neutral M)
/\ (forall n (M: tm n) M', SNRed M M' -> redsn M M') .
Proof.
  apply SN_multind; intros.
  - intuition.
  - now apply closed_lam.
  - eauto using redsn_backwards.
  - split; [|now constructor].
    + constructor. intros M H. inv H.
  - split; [|intuition].
    + now apply sn_app_neutral.
  - subst. now constructor.
  - now constructor.
Qed.


Ltac invTm :=
match goal with
|[_ : var_tm _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : lam _ _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[_ : app _ _ = ren_tm ?R ?M' |- _] => inv M'; simpl in *; try congruence
|[H: lam _ _ = lam _ _ |- _] => inv H
|[H: app _ _ = app _ _|- _] => inv H
|[H: ids _ = ids _|- _] => inv H
end.

Hint Constructors SN SNe SNRed.

Lemma anti_rename:
  (forall n (M: tm n), SN M -> forall n' M' (R: fin n' -> fin n), M = ren_tm R M' -> SN M')
 /\ (forall n (M: tm n), SNe M -> forall n' M' (R: fin n' -> fin n), M = ren_tm R M' -> SNe M')
 /\ (forall n (M N: tm n), SNRed M N -> forall n' (R: fin n' -> fin n) M', M = ren_tm R M' -> exists N', N = ren_tm R N' /\ SNRed M' N').
Proof.
  apply SN_multind; intros; repeat invTm; (* asimpl in *; *) subst; eauto.
  (* a.d. asimpl * does not exist anymore. was not needed here anyways *)
  - destruct (H0 _ _ _ (eq_refl _)) as (M''&->&?).
    eapply SRed; eauto.
  - asimpl in H.
    destruct M'; simpl in *; try congruence.
    inv H; now constructor.
  - exists (M'0_1 [M'0_2..]).
    split. now asimpl. constructor; eauto.
  - destruct (H0 _ _ _ (eq_refl (ren_tm R0 M'1))) as (N'&->&A2).
    exists (app N' M'2). split; [reflexivity| now constructor].
Qed.

Lemma rename :
  (forall n (M: tm n), SN M -> forall n' (R: fin n -> fin n'), SN (ren_tm R M))
  /\   (forall n (M: tm n),  SNe M -> forall n' (R: fin n -> fin n'), SNe (ren_tm R M))
  /\ (forall n (M N: tm n), SNRed M N -> forall n' (R: fin n -> fin n'), SNRed (ren_tm R M) (ren_tm R N)).
Proof.
  (* a.d. moved asimpl before intros to remove the `in *` *)
  apply SN_multind; asimpl; intros; eauto.
  - constructor.
  - intros. subst. constructor. auto. now asimpl.
Qed.

Lemma ext_SN n (M: tm n) (p: fin n) :
  SN (app M (var_tm p)) -> SN M.
Proof.
  intros H. remember (app M (var_tm p)) as Mp. revert M p HeqMp.
  induction H; intros; subst.
  - inv H. now constructor.
  - inv HeqMp.
  - inv H.
    + apply SAbs. eapply anti_rename. exact H0.
      instantiate (1 := p..). substify.
      now asimpl.
    + eapply SRed. exact H. eapply IHSN. reflexivity.
Qed.


(** ** Logical Relation *)
Fixpoint Red {n} (A : ty) : tm n -> Prop :=
  match A with
  | Base => fun s => SN s
  | Fun A B => fun s =>
      forall n' (S : fin n -> fin n') (t : tm n'), Red A t -> Red B (app (ren_tm S s) t)
  end.

Definition RedS {n n'} (S: fin n -> tm n') (Gamma: fin n -> ty) :=
  forall i, Red (Gamma i) (S i).

Lemma rename_red m n (f : fin m -> fin n) (s : tm m) A :
  Red A s -> Red A (ren_tm f s).
Proof.
  revert s. destruct A as [| A B]; intros s; cbn.
  - intros H. now apply rename.
  - intros H n' g t lt. asimpl. now apply H.
Qed.

Lemma cr A:
  (forall n (M: tm n), Red A M -> SN M) /\ (forall n (M: tm n), SNe M -> Red A M) /\ (forall n (M M': tm n), SNRed M M' -> Red A M' -> Red A M).
Proof.
  induction A as [|A IHA B IHB].
  - repeat split; intros.
    + assumption.
    + now apply SNeu.
    + now apply SRed with (M' := M').
  - repeat split; intros.
    + eapply anti_rename with (R := shift) (M := ren_tm shift M); [|reflexivity].
      eapply ext_SN, IHB. cbn in H. apply H, IHA. apply SVar with (x:= var_zero).
    + intros g' R N H'. apply IHB.
      apply SApp. now apply rename. now intuition.
    + intros g' R N rn. apply IHB with (M' := app (ren_tm R M') N).
     * constructor. now apply rename.
     * apply H0, rn.
Qed.

Lemma red_var n (p: fin n) A:
  Red A (var_tm p).
Proof. apply cr, SVar. Qed.

From Chapter9 Require Export preservation.

Lemma main_lemma n (M: tm n)  A Gamma:
  Gamma |- M : A ->  forall n' (S: fin n -> tm n'), RedS S Gamma  -> Red A (subst_tm S M).
Proof.
  induction 1; intros.
  - cbn. apply H.
    - intros m R N rn.
    eapply cr.
    + cbn. econstructor.
      * eapply cr; eauto.
      * reflexivity.
    + asimpl. eapply IHhas_type. intros [|]; eauto.
      * cbn. unfold funcomp.
        (* a.d. had to insert the following line *) 
        change (fun x : fin n' => @var_tm m (R x)) with (funcomp var_tm R).
       renamify. 
        apply rename_red. eauto.
  - cbn.  specialize (IHhas_type2 _ _ H1).
    specialize (IHhas_type1  _ _ H1 n' id _ IHhas_type2).
    asimpl in IHhas_type1. eauto.
Qed.

Lemma id_red g Gamma: @RedS g g ids Gamma.
Proof. intros i. now apply red_var. Qed.

Lemma norm n (M: tm n) (A: ty) Gamma: Gamma |- M : A -> SN M.
Proof.
  intros C.
  assert (H := main_lemma C (@id_red n Gamma)).
  asimpl in H. now apply cr in H.
Qed.
