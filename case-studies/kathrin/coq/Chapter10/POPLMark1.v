(** * Chapter 10 - Type Safety for F-Sub *)

(** ** Part 1 : System F *)

Require Export Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import core fintype.
Import ScopedNotations.
From Chapter10 Require Export sysf.
Require Import Coq.Program.Tactics.

Ltac inv H := inversion H; try clear H; try subst.

Ltac autorevert x :=
  try (match goal with
    | [y : ?Y |- ?claim] =>
      try (match x with y => idtac end; fail 1);
        match goal with [z : _ |- _] =>
          match claim with context[z] =>
            first
              [ match Y with context[z] => revert y; autorevert x end
              | match y with z => revert y; autorevert x end]
          end
        end
       end).

Definition ctx n := fin n -> ty n.

Reserved Notation "'SUB' Delta |- A <: B"
         (at level 68, A at level 99, no associativity).

(** *** Properties of Subtyping *)
Open Scope fscope.

Inductive sub {n} (Delta : ctx n) : ty n -> ty n -> Prop :=
| SA_top A :
    SUB Delta |- A <: top
| SA_Refl x :
    SUB Delta |- var_ty x <: var_ty x
| SA_Trans x  B :
     SUB Delta |- (Delta x) <: B ->  SUB Delta |- var_ty x <: B
| SA_arrow A1 A2 B1 B2 :
    SUB Delta |- B1 <: A1 -> SUB Delta |- A2 <: B2 ->
    SUB Delta |- arr A1 A2 <: arr B1 B2
| SA_all (A1: ty n) (A2: ty (S n)) B1 B2 :
    SUB Delta |- B1 <: A1 -> @sub (S n) ((B1 .: Delta) >> ⟨↑⟩) A2 B2 ->
    SUB Delta |- all A1 A2 <: all B1 B2
where "'SUB' Delta |- A <: B" := (sub Delta A B).

Hint Constructors sub.

Require Import Setoid Morphisms.

(* a.d. we prove this morphism for asimpl *)
Instance sub_morphism {n}:
  Proper (pointwise_relation _ eq ==> eq ==> eq ==> Basics.impl) (@sub n).
Proof.
  intros Gamma Gamma' HGamma T T' -> t t' ->.
  intros H. induction H in Gamma', HGamma |- *.
  - constructor.
  - constructor.
  - constructor. rewrite <- HGamma. apply IHsub. apply HGamma.
  - constructor.
    apply IHsub1, HGamma.
    apply IHsub2, HGamma.
  - constructor.
    apply IHsub1, HGamma.
    apply IHsub2.
    intros [|]. cbn. rewrite HGamma. reflexivity.
    cbn. reflexivity.
Qed.

Lemma sub_refl n (Delta: ctx n) A : SUB Delta |- A <: A.
Proof. revert Delta. induction A; intuition; constructor; eauto. Qed.

Lemma sub_weak m n (Delta1: ctx m) (Delta2: ctx n) A1 A2 A1' A2' (xi: fin m -> fin n) :
  SUB Delta1 |- A1 <: A2 ->
 (forall x, (Delta1 x)⟨xi⟩ = Delta2 (xi x)) ->
  A1' = A1⟨xi⟩ -> A2' = A2⟨xi⟩ ->
  SUB Delta2 |- A1' <: A2' .
Proof.
  intros H. autorevert H. induction H; intros; subst; asimpl; econstructor; eauto.
  - eapply IHsub2; try reflexivity.
    auto_case.
    unfold funcomp.
    rewrite <- H1. now asimpl.
    (* DONE auto_case should call asimpl on this goal. and asimpl directly solves this. so why is it still here?
     pointwise version solves it again *)
Qed.

Lemma sub_weak1 n (Delta : ctx n) A A' B B' C :
  SUB Delta |- A <: B ->  A' = A⟨↑⟩ ->  B' = B⟨↑⟩ -> SUB ((C .: Delta) >> ⟨↑⟩) |- A' <: B'.
Proof. intros. eapply sub_weak;  eauto. intros x. now asimpl. Qed.

Definition transitivity_at {n} (B: ty n) := forall m Gamma (A : ty m) C  (xi: fin n -> fin m),
  SUB Gamma |- A <: B⟨xi⟩ -> SUB Gamma |- B⟨ xi⟩ <: C ->  SUB Gamma |- A <: C.

 Lemma transitivity_proj n (Gamma: ctx n) A B C :
  transitivity_at B ->
  SUB Gamma |- A <: B -> SUB Gamma |- B <: C -> SUB Gamma |- A <: C.
Proof. intros H. specialize (H n Gamma A C id). now asimpl in H. Qed.
Hint Resolve transitivity_proj.

Lemma transitivity_ren m n B (xi: fin m -> fin n) : transitivity_at B -> transitivity_at B⟨xi⟩.
Proof. unfold transitivity_at. intros. apply H with (xi:=funcomp xi0 xi); asimpl in H0; asimpl in H1; eauto.
Qed.

Lemma sub_narrow n (Delta Delta': ctx n) A C :
  (forall x, SUB Delta' |- Delta' x <: Delta x) ->
  (forall x, Delta x = Delta' x \/ transitivity_at (Delta x)) ->
  SUB Delta |- A <: C -> SUB Delta' |- A <: C.
Proof with asimpl;eauto.
  intros H H' HH. autorevert HH. induction HH; intros; eauto.
  - destruct (H' x); eauto. rewrite H0 in *. eauto.
  - constructor; eauto.
    eapply IHHH2.
    + auto_case; try apply sub_refl.
      eapply sub_weak; try reflexivity. eapply H. now asimpl.
    + auto_case. destruct (H' f);  eauto using transitivity_ren.
      rewrite H0. now left.
Qed.

Corollary sub_trans' n (B : ty n): transitivity_at B.
Proof with asimpl;eauto.
  unfold transitivity_at.
  autorevert B. induction B; intros...
  - depind H...
  - depind H... depind H0...
  - depind H... depind H1...
  - depind H... depind H1...
    econstructor... clear IHsub0 IHsub3 IHsub1 IHsub2.
    eapply IHB2 with (xi:=upRen_ty_ty xi).
    + asimpl. eapply sub_narrow; try eapply H0.
      * auto_case. apply sub_refl.
        eapply sub_weak with (xi := ↑); try reflexivity; eauto.
      * intros [x|]; try cbn; eauto. right. apply transitivity_ren. apply transitivity_ren. eauto.
    + asimpl in H1_0. auto.
Qed.

Corollary sub_trans n (Delta  : ctx n) A B C:
  SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C.
Proof. eauto using sub_trans'. Qed.

Lemma sub_substitution m m' (sigma : fin m -> ty m') Delta (Delta': ctx m') A B:
   (forall x ,  SUB Delta' |- sigma x <: (Delta x)[sigma] ) ->
   SUB Delta |- A <: B -> SUB Delta' |- subst_ty sigma A <: subst_ty sigma B.
Proof.
    intros eq H. autorevert H. induction H; try now (econstructor; eauto).
  - intros. asimpl. eapply sub_refl.
  - intros. asimpl. eauto. cbn in *. eauto using sub_trans.
  - intros. asimpl. econstructor; eauto.
    asimpl. eapply IHsub2.
    auto_case; asimpl; cbn; eauto using sub_refl.
    eapply sub_weak; try reflexivity. eapply eq.
    all: now asimpl.
Qed.

(** *** Type Safety *)

Inductive value {m n}: tm m n -> Prop :=
| Value_abs A s : value(abs A s)
| Value_tabs A s : value(tabs A s).

Reserved Notation "'TY' Delta ; Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "'TY'  Delta ; Gamma  |-  A  :  B").

Definition dctx m n := fin m -> ty n.

Inductive has_ty {m n} (Delta : ctx m) (Gamma : dctx  n m) : tm m n -> ty m -> Prop :=
| T_Var  x :
    TY Delta;Gamma |- var_tm x : (Gamma x)
 | T_abs (A: ty m) B (s: tm m (S n)):
    @has_ty m (S n) Delta (A .: Gamma) s B   ->
    TY Delta;Gamma |- abs A s : arr A B
| T_app A B s t:
    TY Delta;Gamma |- s : arr A B   ->   TY Delta;Gamma |- t : A   ->
    TY Delta;Gamma |- app s t : B
| T_tabs A B s :
    @has_ty (S m) n ((A .: Delta) >> ⟨↑⟩) (Gamma >> ⟨↑⟩) s B ->
    TY Delta;Gamma |- tabs A s : all A B
| T_Tapp A B A' s B' :
    TY Delta;Gamma |- s : all A B ->
    SUB Delta |- A' <: A -> B' = subst_ty (A'..) B ->
    TY Delta;Gamma |- tapp s A' : B'
 | T_Sub A B s :
    TY Delta;Gamma |- s : A   ->   SUB Delta |- A <: B   ->
    TY Delta;Gamma |- s : B
where "'TY' Delta ; Gamma |- s : A" := (has_ty Delta Gamma s A).

Hint Constructors has_ty.

(* a.d. we prove this morphism for asimpl *)
Instance has_ty_morphism {m n} :
  Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq ==> eq ==> Basics.impl) (@has_ty m n).
Proof.
  intros Delta Delta' HDelta Gamma Gamma' HGamma T T' -> t t' -> H.
  induction H in Delta', Gamma', HDelta, HGamma |- *.
  - rewrite HGamma. constructor.
  - constructor.
    apply IHhas_ty. assumption.
    intros [|]; cbn. apply HGamma. reflexivity.
  - econstructor. apply IHhas_ty1; assumption.
    apply IHhas_ty2; assumption.
  - constructor. apply IHhas_ty.
    intros [|]; cbn. rewrite HDelta. 1, 2: reflexivity.
    intros x. unfold funcomp. rewrite HGamma. reflexivity.
  - econstructor. apply IHhas_ty; assumption.
    setoid_rewrite <- HDelta. assumption.
    assumption.
  - econstructor. 2: setoid_rewrite <- HDelta; apply H0.
    apply IHhas_ty; assumption.
Qed.

Reserved Notation "'EV' s => t"
  (at level 68, s at level 80, no associativity, format "'EV'   s  =>  t").
Inductive eval {m n} : tm m n -> tm m n -> Prop :=
| E_appabs A s t : EV app (abs A s) t => s[ids; t..]
| E_Tapptabs A s B : EV tapp (tabs A s) B => s[B..; ids]
| E_appFun s s' t :
     EV s => s' ->
     EV app s t => app s' t
| E_appArg s s' v:
     EV s => s' -> value v ->
     EV app v s => app v s'
| E_TyFun s s' A :
     EV s => s' ->
     EV tapp s A => tapp s' A
where "'EV' s => t" := (eval s t).

(* a.d. we prove this morphism for asimpl *)
Instance eval_morphism {m n}:
  Proper (eq ==> eq ==> Basics.impl) (@eval m n).
Proof.
  intros s s' -> t t' ->. unfold Basics.impl. trivial.
Qed.

(** **** Progress *)

Definition empty {X} : fin 0 -> X :=
  fun x => match x with end.

Lemma can_form_arr {s: tm 0 0} {A B}:
  TY empty;empty |- s : arr A B -> value s -> exists C t, s = abs C t.
Proof.
  intros H.
  depind H; intros; eauto.
  all: try now (try destruct x0; try inversion H1).
  inversion H0; subst; eauto. inversion x.
Qed.

Lemma can_form_all {s A B}:
  TY empty;empty |- s : all A B -> value s -> exists C t, s = tabs C t.
Proof.
  intros H.
  depind H; intros; eauto.
  all: try now (try destruct x0; try inversion H1).
  inv H0; subst; eauto. inversion x.
Qed.

Theorem ev_progress s A:
  TY empty;empty |- s : A -> value s \/ exists t,  EV s => t.
Proof.
  intros. depind H; eauto; try (left; constructor).
  - inversion x.
  - right. edestruct IHhas_ty1 as [? | [? ?]]; try reflexivity.
    + edestruct (can_form_arr H H1) as [? [? ?]]; subst.
      eexists. econstructor.
    + eexists. econstructor. eauto.
  - right. edestruct IHhas_ty as [? | [? ?]]; try reflexivity.
    + edestruct (can_form_all H H1) as [? [? ?]]; subst. eexists. econstructor.
    + eexists. econstructor. eauto.
Qed.

(** **** Preservation *)

Lemma context_renaming_lemma m m' n n' (Delta: ctx m') (Gamma: dctx n' m')                                                   (s: tm m n) A (sigma : fin m -> fin m') (tau: fin n -> fin n') Delta' (Gamma' : dctx n m):
  (forall x, (Delta' x)⟨sigma⟩ = Delta (sigma x)) ->
  (forall (x: fin n) , (Gamma' x)⟨sigma⟩ =  (Gamma (tau x))) ->
  TY Delta'; Gamma' |- s : A -> TY Delta; Gamma |- s⟨sigma;tau⟩ : A⟨sigma⟩.
Proof.
  intros H H' ty. autorevert ty.
  induction ty; asimpl; intros; (* asimpl in *;  *)subst; try now (econstructor; eauto).
  - rewrite H0. constructor.
  - constructor. apply IHty; eauto. auto_case.
  - econstructor. apply IHty; eauto.
    + auto_case; try now asimpl.
      unfold funcomp.
      rewrite <- H. now asimpl.
    + intros. asimpl.
      unfold funcomp.
      rewrite <- H'. now asimpl.
  - eapply T_Tapp with (A0 := A⟨sigma⟩) (B0:=ren_ty (upRen_ty_ty sigma) B).
    asimpl in IHty.
    eapply IHty; eauto.
    eapply sub_weak; eauto.
    now asimpl.
  - econstructor. eauto.
    eapply sub_weak; eauto.
Qed.

Lemma context_morphism_lemma m m' n n' (Delta: ctx m) (Delta': ctx m') (Gamma: dctx n m) (s: tm m n) A (sigma : fin m -> ty m') (tau: fin n -> tm m' n') (Gamma' : dctx n' m'):
  (forall x, SUB Delta' |- sigma x <: (Delta x)[sigma]) ->
  (forall (x: fin n) ,  TY Delta'; Gamma' |- tau x : subst_ty sigma (Gamma x)) ->
  TY Delta; Gamma |- s : A -> TY Delta'; Gamma' |- s[sigma;tau] : A[sigma].
Proof.
  intros eq1 eq2 ty. autorevert ty.
  induction ty; intros; subst; asimpl; try now (econstructor; eauto).
  - eapply eq2.
  - constructor. eapply IHty; eauto.
    auto_case; asimpl.
    +  assert (subst_ty sigma (Gamma f)  = ((Gamma f)[sigma]⟨id⟩)) as -> by (now asimpl) .
       eapply context_renaming_lemma; eauto; now asimpl.
    + econstructor.
  - constructor. eapply IHty; eauto.
    + auto_case.
      * asimpl.
        specialize (eq1 f).
        eapply sub_weak1 with (C := A[sigma]) in eq1; eauto.  asimpl in eq1. eapply eq1.
      * asimpl. econstructor. apply sub_refl.
    + intros x. asimpl.
      assert ((Gamma x) [sigma >> ⟨↑⟩] = (Gamma x)[sigma]⟨↑⟩) by (now asimpl).
      auto_unfold in *. rewrite H.
      eapply context_renaming_lemma; eauto.
      * intros. now asimpl.
      * intros. now asimpl.
  - eapply T_Tapp with (A0 := subst_ty sigma A) (B0:=B[up_ty_ty sigma]).
    asimpl in IHty. eapply IHty; eauto.
    eapply sub_substitution; eauto.
    now asimpl.
 - econstructor.
    + eapply IHty; eauto.
    + eapply sub_substitution; eauto.
Qed.

 Lemma ty_inv_abs m n Delta Gamma A A' B C (s: tm m (S n)):
  TY Delta;Gamma |- abs A s : C   ->   SUB Delta |- C <: arr A' B   ->
  (SUB Delta |- A' <: A /\
    exists B', TY Delta; A .: Gamma |- s : B' /\ SUB Delta |- B' <: B).
Proof.
  intros H. depind H; intros.
  - inv H0. split; eauto.
  - eauto using sub_trans.
Qed.

Lemma ty_subst m n (Gamma: dctx m n) (Delta: ctx n) Delta' s A:
    (forall x, SUB Delta' |- Delta' x <: Delta x) ->
  TY Delta; Gamma |- s : A -> TY Delta'; Gamma |- s : A.
Proof.
  intros eq H. autorevert H. induction H; eauto; intros.
  - econstructor; eauto. asimpl. eapply IHhas_ty. auto_case; eauto using sub_refl.
    eapply sub_weak; try reflexivity. apply eq. intros x. now asimpl.
  - econstructor; eauto.
    replace A with (A[ids]) by (now asimpl). replace A' with (A'[ids]) by (now asimpl).
    eapply sub_substitution; eauto. intros x.
    asimpl. econstructor. eauto.
  - econstructor; eauto. eapply sub_substitution with (sigma := ids) (Delta':=Delta') in H0; eauto.
    + asimpl in H0. apply H0.
    + intros x. econstructor. asimpl. eapply eq.
Qed.

Lemma ty_inv_tabs {m n} {Delta Gamma A A' B C} (s : tm (S m) n):
  TY Delta;Gamma |- tabs A s : C   ->   SUB Delta |- C <: all A' B   ->
  (SUB Delta |- A' <: A /\ exists B',
   TY (A'.:Delta) >> ren_ty ↑; Gamma >> ren_ty ↑ |- s : B' /\ SUB (A' .: Delta) >> ren_ty ↑ |- B' <: B).
Proof.
  intros H. depind H; intros.
  - inv H0. split; eauto.
    eexists. split; eauto.
    eapply ty_subst; eauto. auto_case.
    apply sub_refl. eapply sub_weak; try reflexivity; eauto.
  - eauto using sub_trans.
Qed.

Theorem preservation m n Delta Gamma (s: tm m n) t A :
  TY Delta;Gamma |- s : A -> EV s => t ->
  TY Delta;Gamma |- t : A.
Proof.
  intros H_ty H_ev. autorevert H_ev.
  induction H_ev; intros; eauto using ty.
  all: try (now (depind H_ty; eauto)).
  - depind H_ty; [|eauto].
    + depind H_ty1; subst.
      * replace B with (B[ids]) by (now asimpl).
        eapply context_morphism_lemma; eauto.
        -- intros. asimpl. repeat constructor. apply sub_refl.
        -- intros [|]; intros; cbn; asimpl; eauto.
      * pose proof (ty_inv_abs _ _ _ _ _ _ _ _ _ H_ty1 H) as (?&?&?&?).
        eapply T_Sub; eauto.
        replace x with (x[var_ty]) by (now asimpl).
        eapply context_morphism_lemma; eauto.
        -- intros. asimpl. repeat constructor. apply sub_refl.
        -- intros [|]; intros; cbn; asimpl; eauto.
  - depind H_ty; eauto.
    + depind H_ty.
      * asimpl in H_ty.
        eapply context_morphism_lemma; try eapply H_ty; eauto.
        -- auto_case.
           ++ asimpl. constructor. apply sub_refl.
        -- intros x. asimpl. constructor.
      * pose proof (ty_inv_tabs _ H_ty H) as (?&?&?&?).
        eapply T_Sub; eauto. 
        eapply context_morphism_lemma; eauto.
        -- auto_case; asimpl; eauto. asimpl. constructor. apply sub_refl.
        -- intros z. unfold funcomp. asimpl. constructor.
        -- eapply sub_substitution; eauto.
           auto_case; asimpl.
           constructor. apply sub_refl.
Qed.

Print Assumptions preservation.