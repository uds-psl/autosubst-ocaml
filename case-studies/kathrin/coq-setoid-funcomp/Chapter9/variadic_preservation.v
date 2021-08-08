(** ** Variadic Preservation *)

Require Export ARS Program.Equality.
Require Import core fintype.
Import ScopedNotations.
From Chapter6 Require Export variadic_fin.
Set Implicit Arguments.
Unset Strict Implicit.

Ltac inv H := dependent destruction H.
Hint Constructors star.

(** *** Single-step reduction *)
Inductive step {n} : tm n -> tm n -> Prop :=
| step_beta p b (t: fin p -> tm n) : step (app _ (lam p b) t) (b[scons_p p t ids])
| step_abs  p b1 b2 : @step (p + n) b1 b2 -> step (lam p b1) (lam p b2)
| step_appL p s1 s2 t : step s1 s2 -> step (app p s1 t) (app _ s2 t).

Hint Constructors step.

Lemma step_beta' n p b (t: fin p -> tm n) t':
  t' = b[scons_p p t ids] -> step (app _ (lam p b) t) t'.
Proof. intros ->. now constructor. Qed.

(** *** Substitutivity *)

(* TODO I also need this morphism to rewrite in a subsitution inside another substitution *)
Require Import Setoid Morphisms.
Instance subst_tm_morphism2  {m_tm : nat} {n_tm : nat}:
 (Proper (pointwise_relation _ eq ==> pointwise_relation _ eq)
    (@subst_tm m_tm n_tm)).
Proof.
  intros f g H s. now setoid_rewrite H.
  Qed.

Require Import core_axioms.
Lemma step_inst {m n} (f : fin m -> tm n) (s t : tm m) :
  step s t -> step (subst_tm f s) (subst_tm f t).
Proof.
  intros st. revert n f.  induction st; intros; cbn.
  Hint Opaque scons_p : rewrite.
  - apply step_beta'. asimpl.
    unfold funcomp. setoid_rewrite scons_p_head'.
    (* TODO a.d. why is cod_map not unfolded + why does the rewrite with scons_p_head' fail. It should happen in fsimpl *)
    asimpl. unfold cod_map. asimpl.
    reflexivity.
  - apply step_abs. eapply IHst.
  - apply step_appL, IHst.
Qed.

Lemma mstep_inst m n (f : fin m -> tm n) (s t : tm m) :
  star step s t -> star step (s[f]) (t[f]).
Proof. induction 1; eauto using step_inst. Qed.

(** *** Variadic typing *)

Inductive ty  : Type :=
  | Base : ty
  | arr p : (fin p -> ty)  -> ty  -> ty .

Definition ctx n := fin n -> ty.

Inductive has_type {n} (Gamma : ctx n) : tm n -> ty -> Prop :=
| ty_var (x : fin n) :
    has_type Gamma (var_tm x) (Gamma x)
| ty_abs p (S1 : fin p -> ty) ( S2 : ty) (M : tm (p + n)) :
    @has_type (p + n) (scons_p p S1 Gamma) M S2 ->
    has_type Gamma (lam p M) (arr S1 S2)
| ty_app p (T : fin p -> ty) ( S : ty) (M  : tm n) N :
    has_type Gamma M (arr T S) ->
    (forall x, has_type Gamma (N x) (T x)) ->
    has_type Gamma (app p M N) S.
Notation "Gamma |- M : T" := (has_type Gamma M T) (at level 20, M at level 99).

Lemma ty_var' n  (x : fin n) A Gamma:
  A = Gamma x ->  has_type Gamma (var_tm x) A.
Proof. intros. subst. constructor. Qed.

Definition ltc {k k'} (Gamma: ctx k) (Delta: ctx k') rho := forall x, Delta (rho x) = Gamma x.

Lemma typing_ren n k (Gamma: ctx n) (Delta: ctx k) (rho: fin n -> fin k) (M: tm n) T :
  ltc Gamma Delta rho  -> Gamma |- M : T ->  Delta |- (M⟨rho⟩) : T.
Proof.
  intros C H. revert k Delta rho C. induction H; intros; asimpl; eauto using has_type.
  - unfold ltc in C. rewrite <- C. constructor.
  - constructor. apply IHhas_type. intros x.
    destruct (destruct_fin x) as [(?&->)|(?&->)]; eauto; asimpl; unfold upRen_p; asimpl. cbn. eauto.
    + now asimpl.
  - econstructor; eauto.
Qed.

Lemma typing_inst n k (Gamma: ctx n) (Delta: ctx k) (sigma: fin n -> tm k) (M: tm n) T :
  (forall x, Delta |- sigma x : Gamma x) -> Gamma |- M : T ->  Delta |- (M[sigma]) : T.
Proof.
Proof.
  intros C H. revert k Delta sigma C. induction H; intros; asimpl; eauto using has_type.
  - unfold ltc in C. apply C.
  - constructor. apply IHhas_type. intros x.
    destruct (destruct_fin x) as [(?&->)|(?&->)]; asimpl.
    + apply ty_var'. now asimpl.
    + eapply typing_ren; eauto. intros x. now asimpl.
 - econstructor; eauto.
Qed.

(** *** Preservation *)

Lemma step_typing k (Gamma: ctx k) M T :
  Gamma |- M : T -> forall M', step M M' -> Gamma |- M' : T.
Proof.
  induction 1; intros; cbn.
  - inv H.
  - inv H0. econstructor. now apply IHhas_type.
  - inv H2.
    + inv H. eapply typing_inst; try eassumption.
      intros x. destruct (destruct_fin x) as [(?&->)|(?&->)]; asimpl; eauto.
      * apply ty_var'; eauto.
    + eapply ty_app; eauto.
Qed.
