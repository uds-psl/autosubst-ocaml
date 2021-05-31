(** ** Decidability of Beta Equivalence *)

(** Proof that algorithmic equivalence and definitional equivalence are equivalent,
following
A case study on logical relations using contextual Types (Andrew Cave, Brigitte Pientka, 2015)
and
Logical Relations and a case study in equivalence checking (Karl Crary, 2005)
**)

Require Export List Omega.
  Require Import core core_axioms unscoped unscoped_axioms.
  Import UnscopedNotations.
From Chapter3 Require Export utlc_pure.

Ltac inv H := inversion H; subst.

Inductive ty := Base | arr : ty -> ty -> ty.

(** *** Reduction, multireduction, and their properties *)

Inductive whr : tm -> tm -> Prop :=
| beta M N M' : M' = M[N..] -> whr (app (lam M) N) M'
| whrapp M M' N : whr M M' -> whr (app M N) (app M' N).

Inductive mwhr : tm -> tm -> Prop :=
 | mwhrR s : mwhr s s
 | mwhrS s t u : whr s t -> mwhr t u -> mwhr s u.

Hint Constructors whr mwhr.

Lemma mwhr_appL s s' t :
  mwhr s s' -> mwhr (app s t) (app s' t).
Proof. induction 1; eauto using whr. Qed.

Lemma mwhr_trans s t u :
  mwhr s t -> mwhr t u ->  mwhr s u.
Proof. induction 1; eauto. Qed.

 Hint Immediate mwhr_trans.

Lemma whr_ren xi M N :
  whr M  N -> whr (M⟨xi⟩) (N⟨xi⟩).
Proof.
  intros H. revert xi.
  induction H; intros; subst; asimpl; eauto.
  econstructor. now asimpl.
Qed.

Lemma mwhr_ren xi M N :
  mwhr M  N -> mwhr (M⟨xi⟩) (N⟨xi⟩).
Proof. induction 1; eauto using whr_ren. Qed.

Lemma confluence {M N1 N2} : mwhr M N1 -> mwhr M N2 -> exists P, mwhr N1 P /\ mwhr N2 P.
Proof.
  induction 1; eauto. destruct 1; eauto.
  enough (t = t0).
  - subst. eauto.
  - clear - H H1. revert t0 H1.
    induction H; intros; inv H1; eauto. inv H4. inv H.
    f_equal. eauto.
Qed.


(** As we are unscoped, a context is a list of types and we need to define
a function get that gets the nth element of the context. *)

Definition ctx := list ty.

Definition get (Gamma : ctx) (n : nat) : ty :=
  nth n Gamma Base.
Notation "Gamma `_ i" := (get Gamma i) (at level 70).

(** A context Delta is a reordering of  Gamma via the renaming xi, if
1.) If x is a valid position in Gamma, then xi x is a valid position in Delta.
2.) For every valid position x in Gamma, the element at position x in Gamma equals the element at position xi x in Delta.
*)
Definition cont_ext Gamma xi Delta :=
  forall x , x < length Gamma -> xi x < length Delta /\  get Gamma x = get Delta (xi x).

Lemma cont_ext_shift Gamma T :
  cont_ext Gamma ↑ (T :: Gamma).
Proof. split. simpl. unfold shift. omega. now asimpl. Qed.

Lemma cont_ext_cons Gamma xi Delta A :
  cont_ext Gamma xi Delta -> cont_ext (A :: Gamma) (up_ren xi) (A :: Delta).
Proof.
  intros H. intros [|i] HH; split; eauto; simpl in *; try omega.
  - asimpl. specialize (H i). omega.
  - cbn. apply H. omega.
Qed.

(** *** Algorithmic Equivalence *)

Inductive algeq : ctx -> tm -> tm -> ty -> Prop :=
| alg_base Gamma M N P Q:  mwhr M P -> mwhr N Q -> algeqNeu Gamma P Q Base -> algeq Gamma M N Base
| alg_arr Gamma M N T S: algeq (T :: Gamma) (app (M⟨↑⟩) 0__tm) (app (N⟨↑⟩) 0__tm) S
                     -> algeq Gamma M N (arr T S)
with algeqNeu : ctx -> tm -> tm -> ty ->  Prop :=
| alg_var Gamma x : x < length Gamma -> forall s, s = (Gamma `_ x) ->  algeqNeu Gamma (var_tm x) (var_tm x) s
| alg_app Gamma M1 M2 T S N1 N2: algeqNeu Gamma M1 M2 (arr T S) -> algeq Gamma N1 N2 T -> algeqNeu Gamma (app M1 N1) (app M2 N2) S.

Scheme algeq_ind_2 := Induction for algeq Sort Prop
  with algeqNeu_ind_2  := Induction for algeqNeu Sort Prop.

Combined Scheme algeq_mut_ind from algeq_ind_2, algeqNeu_ind_2.

 Lemma algEq_monotone :
  (forall Gamma M1 M2 A, algeq Gamma M1 M2 A -> forall Delta xi, cont_ext Gamma xi Delta -> algeq Delta (M1⟨xi⟩) (M2⟨xi⟩) A)
/\ (  (forall Gamma M1 M2 A, algeqNeu Gamma M1 M2 A -> forall Delta xi, cont_ext Gamma xi Delta -> algeqNeu Delta (M1⟨xi⟩) (M2 ⟨xi⟩) A)).
Proof.
  apply algeq_mut_ind; intros; subst; asimpl in *; try (now (econstructor; eauto)).
  - econstructor; [| |eauto]. all: eauto using mwhr_ren.
  - constructor.
    specialize (H _ _ (cont_ext_cons _ _ _ T H0)).
    asimpl in *. auto.
  - destruct (H x l) as (?&->). now constructor.
Qed.

Lemma algeq_backward_closure Gamma s t A s' t':
  algeq Gamma s t A -> mwhr s' s -> mwhr t' t -> algeq Gamma s' t' A.
Proof.
  intros H. revert s' t'. induction H; intros.
  - econstructor; [| |apply H1]; eauto.
  - econstructor. eapply IHalgeq; eauto using mwhr_appL, mwhr_ren.
Qed.

Lemma algeq_sym :
  (forall Gamma s t A, algeq Gamma s t A -> algeq Gamma t s A) /\ (forall Gamma s t A, algeqNeu Gamma s t A -> algeqNeu Gamma t s A).
Proof. apply algeq_mut_ind; intros; econstructor; eauto. Qed.

(** The following statements will be necessary to prove transitivity. *)

Lemma neutral_whr {M N Gamma P T}:
  whr M N -> algeqNeu Gamma M P T -> M = N.
Proof.
  intros H H'. revert N H.
  induction H'; intros; eauto; inv H0; eauto.
  inv H1. inv H'. specialize (IHH' _ H4). now subst.
Qed.

Lemma neutral_mwhr {M N Gamma P T}:
  mwhr M N -> algeqNeu Gamma M P T -> M = N.
Proof.
  induction 1; eauto. intros HH.
  specialize (neutral_whr H HH) as ->. eauto.
Qed.

Lemma type_unique Gamma M1 M2 M3 S T:
  algeqNeu Gamma M1 M2 S -> algeqNeu Gamma M2 M3 T -> S = T.
Proof.
  intros H. revert T M3. induction H; subst; eauto.
  - intros. now inv H0.
  - intros. inv H1. specialize (IHalgeqNeu _ _ H5). congruence.
Qed.

Lemma algeq_trans :
  (forall Gamma s t A, algeq Gamma s t A -> forall u,  algeq Gamma t u A -> algeq Gamma s u A) /\
  (forall Gamma s t A, algeqNeu Gamma s t A -> forall u, algeqNeu Gamma t u A -> algeqNeu Gamma s u A).
Proof.
  apply algeq_mut_ind; intros; try now (econstructor; eauto).
  - inv H0. destruct (confluence m0 H1) as (?&?&?).
    specialize (neutral_mwhr H5 H3) as ->.
    apply algeq_sym in a. specialize (neutral_mwhr H4 a) as ->.
    eapply algeq_backward_closure. econstructor; try (apply H; eauto).
    all: eauto.
  - inv H0. econstructor. now eapply H.
  - subst. inv H. eauto.
  - inv H1.
    enough (T  = T0) by (subst; econstructor; eauto).
    enough (arr T0 S = arr T S) by congruence.
    symmetry. eapply type_unique; eauto.
Qed.


(** *** Logical Equivalence *)

Fixpoint logeq (Gamma : ctx) (s s' : tm) (A: ty) : Prop :=
  match A with
  | Base => algeq Gamma s s' Base
  | arr T1 T2 =>  forall t t' Delta xi, cont_ext Gamma xi Delta
               -> logeq Delta t t' T1 -> logeq Delta (app (s⟨xi⟩) t) (app (s'⟨xi⟩) t') T2
  end.

Lemma logEq_monotone (Gamma : ctx) M1 M2 A :
  logeq Gamma M1 M2 A -> forall Delta xi, cont_ext Gamma xi Delta ->
                           forall M1' M2', M1' = (M1⟨xi⟩) -> M2' =  (M2⟨xi⟩) -> logeq Delta M1' M2' A.
Proof.
  revert Gamma M1 M2. induction A; intros; subst.
  - eapply algEq_monotone; eauto.
  - asimpl in IHA2. cbn. intros. cbn in H. asimpl. eapply H; eauto.
    + intros x A.
      destruct (H0 x A) as (?&->).
      destruct (H1 _ H3) as (?&->).
      eauto.
Qed.

Lemma logeq_backward_closure Gamma s t A s' t':
  logeq Gamma s t A -> mwhr s' s -> mwhr t' t -> logeq Gamma s' t' A.
Proof.
  revert Gamma s t s' t'. induction A; simpl in *; intros; eauto using algeq_backward_closure.
  - eapply IHA2. all: eauto using mwhr_appL, mwhr_ren.
Qed.

Lemma logeq_sym Gamma A s t:
  logeq Gamma s t A -> logeq Gamma t s A.
Proof.
  revert Gamma s t. induction A; simpl in *; intros; eauto.
  - now apply algeq_sym.
Qed.

Lemma logeq_trans Gamma A s t u :
  logeq Gamma s t A -> logeq Gamma t u A -> logeq Gamma s u A.
Proof.
  revert Gamma s t u. induction A; intros; eauto; simpl in *; eauto using algeq_trans.
  - eapply algeq_trans; eauto.
  - intros. eapply IHA2.
    + eapply H; eauto.
    + eapply H0; eauto. eapply IHA1. eapply logeq_sym. eassumption. eassumption.
Qed.

(** *** Main Lemma. *)

Lemma main T :
  (forall Gamma s t, logeq Gamma s t T -> algeq Gamma s t T) /\ (forall Gamma p q, algeqNeu Gamma p q T -> logeq Gamma p q T).
Proof.
  induction T as [|T IHT S IHS]; split; simpl in *; intros; eauto.
  - econstructor; eauto.
  - econstructor. eapply IHS, H; eauto using cont_ext_shift.
    + eapply IHT. constructor. simpl. omega. now asimpl.
  - eapply IHS. econstructor; eauto.
    + eapply algEq_monotone; eauto.
    +  eapply IHT. eauto.
Qed.


(** *** Declarative Equivalence *)

Inductive decleq  : forall (Gamma: ctx) A,  tm -> tm -> Prop :=
| DecBeta Gamma A B M N M' N': decleq (A :: Gamma) B M M' -> decleq Gamma A N N' -> decleq Gamma B (app (lam M) N) (M'[N'..])
| DecLam Gamma A B M N: decleq (A :: Gamma) B M N  -> decleq Gamma (arr A B) (lam M) (lam N)
| DecExt Gamma A B M N : decleq (A :: Gamma) B (app (M⟨↑⟩) 0__tm) (app (N⟨↑⟩) 0__tm)  -> decleq Gamma (arr A B) M N
| DecVar Gamma x: x < length Gamma -> decleq Gamma (get Gamma x) (var_tm x) (var_tm x)
| DecApp Gamma A B M M' N N'  : decleq Gamma (arr A B) M M'  -> decleq Gamma A N N'  -> decleq Gamma B (app M N) (app M' N')
| DecSym Gamma A M N : decleq Gamma A M N -> decleq Gamma A N M
| DecTrans Gamma A M N O : decleq Gamma A M N -> decleq Gamma A N O -> decleq Gamma A M O.

(** All elements in the context will have to be pairwise logically equivalent. *)
Definition logeq_rel (Gamma: ctx) gamma delta Gamma' : Prop :=
  forall x, x < length Gamma ->  logeq Gamma' (gamma x) (delta x) (get Gamma x).

Lemma logeq_id Gamma:  logeq_rel Gamma ids ids Gamma.
Proof. unfold logeq_rel. intros. eapply main. constructor; eauto. Qed.
Lemma cont_ext_id Gamma : cont_ext Gamma id Gamma.
Proof. intros x H. split; auto. Qed.

(** The fundamental theorem. *)
Theorem fundamental Gamma A s t:
  decleq Gamma A s t -> forall Gamma' gamma delta, logeq_rel Gamma gamma delta Gamma' -> logeq Gamma' (s[gamma]) (t[delta]) A.
Proof.
  induction 1; intros.
  - asimpl. eapply logeq_backward_closure; [| |constructor].
    2: {eright. constructor. now asimpl. constructor. }
    eapply IHdecleq1.
    intros [|] HH; cbn; eauto.
    + eapply H1. simpl in *. omega.
  - cbn. intros. eapply logeq_backward_closure.
    2,3 : eright; now constructor.
    asimpl. eapply IHdecleq.
    intros [|x]; unfold get; simpl in *; intros; eauto.
    eapply logEq_monotone; eauto.
    all: try (substify; now reflexivity).
    eapply H0. omega.
  - simpl. intros. asimpl in *. asimpl in IHdecleq.
    (* adrian: had to change scons notation below to not use t, gamma *)
    Open Scope fscope.
    specialize (IHdecleq Delta (t .: gamma >> ⟨xi⟩) (t' .: delta >> ⟨xi⟩)).
    asimpl in *.
    eapply IHdecleq.
    intros [|i] HH; asimpl; eauto.
    cbn. eapply logEq_monotone; eauto. eapply H0. simpl in *. omega.
  - simpl. now eapply H0.
  - specialize (IHdecleq1 _ _ _ H1). asimpl in *.
    specialize (IHdecleq2 _ _ _ H1). cbn in *.
    specialize (IHdecleq1 _ _ _ _ (cont_ext_id Gamma') IHdecleq2).
    asimpl in *. now apply IHdecleq1.
  - apply logeq_sym. eapply IHdecleq.
    intros i HH. now eapply logeq_sym, H0.
  - eapply logeq_trans; eauto.
    eapply IHdecleq2. intros i HH.
    eapply logeq_trans.
    + now eapply logeq_sym, H1.
    + now eapply H1.
Qed.

Lemma completeness Gamma A s t:
  decleq Gamma A s t -> algeq Gamma s t A.
Proof.
  intros H. eapply fundamental with (Gamma' := Gamma) (gamma := ids) (delta := ids) in H; eauto using logeq_id.
  - apply main. now asimpl in H.
Qed.
