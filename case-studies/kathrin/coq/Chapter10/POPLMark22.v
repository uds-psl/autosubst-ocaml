Require Export Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import core core_axioms fintype fintype_axioms.
Import ScopedNotations.
From Chapter10 Require Export sysf_pat.
Require Import Coq.Program.Tactics.

Open Scope fscope.

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
Definition dctx m n := fin m -> ty n.
Definition empty {X} : fin 0 -> X :=  fun x => match x with end.

Inductive unique {X} : list (nat * X) -> Prop :=
| unil : unique nil
| ucons l x xs : unique xs -> (forall x, ~ In (l, x) xs) ->  unique (cons (l,x) xs).

Hint Constructors unique.

Lemma unique_map {X Y: Type} {f : X -> Y} (xs : list (nat * X)) :
  unique xs -> unique (map (prod_map (fun x => x) f) xs).
Proof.
  intros.
  induction H; cbn; eauto.
  constructor; eauto.
  intros z A. rewrite in_map_iff in A. destruct A as ((?&?)&?&?).
  inv H1. eapply H0; eauto.
Qed.

Lemma unique_spec {X} (xs : list (nat * X)) :
  unique xs -> (forall l x y, In (l, x) xs -> In (l, y) xs -> x = y).
Proof.
  induction 1; intros; cbn in *.
  - contradiction.
  - destruct H1 as [|]; destruct H2 as [|]; try inversion H1; try inversion H2; subst; eauto; firstorder.
Qed.

Lemma in_map {X Y: Type} {f : X -> Y} (xs : list (nat * X)) l x:
  In (l, x) xs -> In (l, f x) (map (prod_map (fun x => x) f) xs).
Proof.
  unfold prod_map.
  induction xs;  cbn; eauto.
  - destruct a; eauto. intros [|]; eauto. inversion H; eauto.
Qed.

Definition label_equiv {X Y} (xs : list (nat * X)) (ys : list (nat * Y)) :=
   (forall i, (exists s, In (i, s) xs) <-> (exists A, In (i, A) ys)).

Lemma label_equiv_map {X X' Y Y': Type} {f : X -> X'} {g : Y -> Y'} (xs : list (nat * X)) (ys : list (nat * Y)) :
  label_equiv xs ys -> label_equiv (map (prod_map (fun x => x) f) xs) (map (prod_map (fun x => x) g) ys).
Proof.
  intros H. intros l.
  unfold prod_map. split; intros (?&?).
  - rewrite in_map_iff in H0. destruct H0 as ((?&?)&?&?). inv H0.
  unfold label_equiv in H. specialize (H l). assert (exists x0, In (l, x0) xs) by eauto.
  apply H in H0. destruct H0 as (?&?). exists (g x). rewrite in_map_iff. exists (l, x). eauto.
- rewrite in_map_iff in H0. destruct H0 as ((?&?)&?&?). inv H0.
  unfold label_equiv in H. specialize (H l). assert (exists x0, In (l, x0) ys) by eauto.
  apply H in H0. destruct H0 as (?&?). exists (f x). rewrite in_map_iff. exists (l, x). eauto.
Qed.

Hint Resolve unique_map label_equiv_map.

Definition update {X} (ts : list (nat * X)) l x : list (nat * X) :=
  map (fun p => if (Nat.eqb (fst p) l) then (l, x) else p) ts.

Lemma unique_update {X} (xs :list (nat * X)) l x :
  unique xs -> unique (update xs l x).
Proof.
  unfold update. intros H.
  induction xs; eauto. inv H. specialize (IHxs H2). cbn.
  destruct (Nat.eqb l0 l) eqn: H; cbn; eauto.
  - constructor; eauto. intros. apply PeanoNat.Nat.eqb_eq in H. subst. intros HH. apply in_map_iff in HH. destruct HH as (?&?&?). destruct x2. cbn in *.  destruct (Nat.eqb n l) eqn: HHH; eauto.
    apply PeanoNat.Nat.eqb_eq in HHH. subst. inv H. eapply H3. eauto. inv H. eapply H3. eauto.
  - constructor; eauto. intros z HH. apply in_map_iff in HH. destruct HH as ((?&?)&?&?). cbn in *.
    destruct (Nat.eqb n l) eqn:HHH; inversion H0; eauto. subst. apply PeanoNat.Nat.eqb_eq in HHH. subst. eapply H3. eauto. subst. eapply H3; eauto.
Qed.

Lemma natequiv_update {X Y} (xs :list (nat * X)) l x (ys: list (nat * Y)):
  label_equiv xs ys -> label_equiv (update xs l x) ys.
Proof.
  enough (label_equiv xs (update xs l x)).
  - intros A i. unfold label_equiv in H, A. now rewrite <- A, H.
  - clear ys. unfold label_equiv. induction xs; cbn; eauto.
    + intros _. split; eauto.
    + destruct a. intros i. cbn. split.
      * intros (?&?). destruct H; eauto.
        -- inv H. destruct (Nat.eqb i l) eqn:HH; eauto. apply PeanoNat.Nat.eqb_eq in HH. subst. eauto. -- assert (exists s, In (i, s) xs) by eauto. apply IHxs in H0. destruct H0 as (?&?). eauto.
      * intros (?&?). destruct H.
        -- destruct (Nat.eqb n l) eqn:HH; eauto. apply PeanoNat.Nat.eqb_eq in HH. subst. inv H. eauto.
        -- assert (exists A, In (i, A) (update xs l x)) by eauto. apply IHxs in H0.
           destruct H0. eauto.
Qed.

Lemma update_char {X} (xs : list (nat * X)) l x i s:
  In (i, s) (update xs l x) -> In (i, s) xs \/ (l = i /\ s = x).
Proof.
  induction xs; eauto. destruct a. cbn.
  destruct (Nat.eqb n l); intros [|]; try inversion H; eauto.
  all: destruct (IHxs H); eauto.
Qed.

Lemma list_dec {X} (P Q : X -> Prop) xs (IH : forall x, In x xs -> P x \/ Q x) :
  (forall x, In x xs -> P x) \/ (exists x, In x xs /\ Q x).
Proof.
  induction xs; cbn; eauto.
  - left. cbn. intros _ [].
  - cbn in IH. assert (forall x, In x xs -> P x \/ Q x) by firstorder.
    destruct (IHxs H) as [|(x&?&?)].
    + assert (P a \/ Q a) as[|] by eauto; cbn; eauto. left. intros z [->|]; cbn; eauto.
    + right. cbn. eauto.
Qed.

Hint Resolve unique_update natequiv_update.

(** POPLMark 1B. *)
Reserved Notation "'SUB' Delta |- A <: B" (at level 68, A at level 99, no associativity).

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
    SUB Delta |- B1 <: A1 -> @sub (S n) ((B1 .:  Delta) >> ⟨↑⟩) A2 B2 ->
    SUB Delta |- all A1 A2 <: all B1 B2
| SA_rec (xs ys : list (nat * ty n)) : (forall l T', In (l, T') ys -> exists T, In (l, T) xs /\ SUB Delta |- T <: T') ->
                       unique xs -> unique ys -> SUB Delta |- recty xs <: recty ys
where "'SUB' Delta |- A <: B" := (sub Delta A B).

Hint Constructors sub.


Require Import Setoid Morphisms.
Instance sub_morphism {n}:
  Proper (pointwise_relation _ eq ==> eq ==> eq ==> Basics.impl) (@sub n).
Proof.
    (* TODO I think here I actually need a stronger induction lemma though I'm not sure how to do it with two lists. Marcel's Bachelor thesis can probably help *)
Admitted.

Lemma sub_rec :  forall P : forall n : nat, ctx n -> ty n -> ty n -> Prop,
       (forall (n : nat) (Delta : ctx n) (A : ty n), P n Delta A top) ->
       (forall (n : nat) (Delta : ctx n) (x : fin n), P n Delta (var_ty x) (var_ty x)) ->
       (forall (n : nat) (Delta : ctx n) (x : fin n) (B : ty n),
        SUB Delta |- Delta x <: B -> P n Delta (Delta x) B -> P n Delta (var_ty x) B) ->
       (forall (n : nat) (Delta : ctx n) (A1 A2 B1 B2 : ty n),
        SUB Delta |- B1 <: A1 ->
        P n Delta B1 A1 ->
        SUB Delta |- A2 <: B2 -> P n Delta A2 B2 -> P n Delta (arr A1 A2) (arr B1 B2)) ->
       (forall (n : nat) (Delta : ctx n) (A1 : ty n) (A2 : ty (S n)) (B1 : ty n) (B2 : ty (S n)),
        SUB Delta |- B1 <: A1 ->
        P n Delta B1 A1 ->
        SUB (B1 .: Delta) >> ⟨↑⟩ |- A2 <: B2 ->
        P (S n) ((B1 .: Delta) >> ⟨↑⟩) A2 B2 -> P n Delta (all A1 A2) (all B1 B2)) ->
       (forall (n : nat) (Delta : ctx n) (xs ys : list (nat * ty n)),
        (forall (i : nat) (T' : ty n),
         In (i, T') ys -> exists  (T : ty n), In (i, T) xs /\ SUB Delta |- T <: T' /\ P _ Delta T T') ->
        unique xs -> unique ys -> P n Delta (recty xs) (recty ys)) ->
       forall (n : nat) (Delta : ctx n) (t t0 : ty n), SUB Delta |- t <: t0 -> P n Delta t t0.
Proof. intros P. fix IH 11.
  intros. induction H5; try now (clear IH; eauto).
  eapply H4. intros. destruct (H5 _ _ H8) as (T&?&?).
  exists T. repeat split; eauto. all: eauto.
Qed.

Lemma ty_rec
     : forall P : forall nty : nat, ty nty -> Prop,
       (forall (nty : nat) (f : fin nty), P nty (var_ty f)) ->
       (forall nty : nat, P nty top) ->
       (forall (nty : nat) (t : ty nty), P nty t -> forall t0 : ty nty, P nty t0 -> P nty (arr t t0)) ->
       (forall (nty : nat) (t : ty nty),
        P nty t -> forall t0 : ty (S nty), P (S nty) t0 -> P nty (all t t0)) ->
       (forall (nty : nat) (l : list (nat * ty nty)), (forall i t, In (i,t) l -> P _ t) -> P nty (recty l)) ->
       forall (nty : nat) (t : ty nty), P nty t.
Proof.
  intros P. fix IH 7. intros.
  induction t; try now (clear IH; eauto).
  eapply H3. intros. induction l.
  - contradiction.
  - destruct H4 as [|].
    + destruct a. specialize (IH H H0 H1 H2 H3 _ t0). intros. inv H4. apply IH.
    + now apply IHl.
Qed.


Section Pattern.

(** We assume that the subtyping relation is reflexive.
A proof requires a well-formedness condition.*)
Variable sub_refl : forall  n (Delta : ctx n) A, SUB Delta |- A <: A.

Lemma sub_weak m n (Delta1: ctx m) (Delta2: ctx n) A1 A2 A1' A2' (xi: fin m -> fin n) :
  SUB Delta1 |- A1 <: A2 ->
 (forall x, (Delta1 x)⟨xi⟩ = Delta2 (xi x)) ->
  A1' = A1⟨xi⟩ -> A2' = A2⟨xi⟩ ->
  SUB Delta2 |- A1' <: A2' .
Proof.
  intros H. autorevert H. induction H using @sub_rec; intros; subst; asimpl; cbn; econstructor; eauto.
  - eapply IHsub2; try reflexivity.
    auto_case; eauto. rewrite <- H1. now asimpl.
  - intros l T' HH. rewrite in_map_iff in HH. destruct HH as ([]&HH&?).
    inv HH. destruct (H _ _ H3) as (?&?&?&?).
    exists (x⟨xi⟩). split; eauto. apply in_map; eauto.
 Qed.

Lemma sub_weak1 n (Delta : ctx n) A A' B B' C :
  SUB Delta |- A <: B ->  A' = A⟨↑⟩ ->  B' = B⟨↑⟩ -> SUB ((C .: Delta) >> ⟨↑⟩) |- A' <: B'.
Proof. intros. eapply sub_weak;  eauto. intros x. now asimpl. Qed.

Definition transitivity_at {n} (B: ty n) := forall m Gamma (A : ty m) C  (xi: fin n -> fin m),
  SUB Gamma |- A <: B⟨xi⟩ -> SUB Gamma |- B⟨ xi⟩ <: C ->  SUB Gamma |- A <: C.

Lemma transitivity_proj n (Gamma: ctx n) A B C :
  transitivity_at B ->
  SUB Gamma |- A <: B -> SUB Gamma |- B <: C -> SUB Gamma |- A <: C.
Proof. intros H. specialize (H n Gamma A C id).  now asimpl in H. Qed.

Hint Resolve transitivity_proj.

Lemma transitivity_ren m n B (xi: fin m -> fin n) : transitivity_at B -> transitivity_at B⟨xi⟩.
Proof. unfold transitivity_at. intros. eapply H; asimpl in H0; asimpl in H1; eauto. Qed.

Lemma sub_narrow n (Delta Delta': ctx n) A C :
  (forall x, SUB Delta' |- Delta' x <: Delta x) ->
  (forall x, Delta x = Delta' x \/ transitivity_at (Delta x)) ->
  SUB Delta |- A <: C -> SUB Delta' |- A <: C.
Proof with asimpl;eauto.
  intros H H' HH. autorevert HH. induction HH using sub_rec; intros; eauto.
  - destruct (H' x); eauto. rewrite H0 in *. eauto.
  - constructor; eauto.
    eapply IHHH2.
    + auto_case; try apply sub_refl.
      eapply sub_weak; try reflexivity.
      2: intros x; reflexivity. apply H.
    + auto_case. destruct (H' f);  eauto using transitivity_ren.
      rewrite H0. now left.
  - econstructor; eauto. intros l T' HH.
    destruct (H _ _ HH) as (T&?&?&?). exists  T.
    split; eauto.
Qed.

Corollary sub_trans' n (B : ty n): transitivity_at B.
Proof with asimpl;eauto.
  unfold transitivity_at.
  autorevert B. induction B using ty_rec; intros...
  - depind H...
  - depind H... depind H0...
  - depind H... depind H1...
  - depind H... depind H1...
    econstructor... clear IHsub0 IHsub3 IHsub1 IHsub2.
    eapply IHB2; eauto.
    + asimpl. eapply sub_narrow; try eapply H0.
      * auto_case.
        eapply sub_weak with (xi := ↑); try reflexivity; eauto.
        (* adrian: as of 7b3472c the goal is already solved by eauto
         TODO find out why *)
        now asimpl.
      * intros [x|]; try cbn; eauto. right. apply transitivity_ren. apply transitivity_ren. eauto.
    + asimpl in H1_0. auto.
  - depind H0... depind H3...
    econstructor; eauto. intros.
    destruct (H5 _ _ H6) as (T&?&?). rewrite in_map_iff in H7.
    destruct H7 as ((?&?)&?&?). inv H7.
    edestruct (H2 l0 (t⟨xi⟩)) as (T&?&?).
    + apply in_map_iff. exists (l0, t). eauto.
    + eauto.
Qed.

Corollary sub_trans n (Delta  : ctx n) A B C:
  SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C.
Proof. eauto using sub_trans'. Qed.

Lemma sub_substitution m m' (sigma : fin m -> ty m') Delta (Delta': ctx m') A B:
   (forall x ,  SUB Delta' |- sigma x <: (Delta x)[sigma] ) ->
   SUB Delta |- A <: B -> SUB Delta' |- subst_ty sigma A <: subst_ty sigma B.
Proof.
    intros eq H. autorevert H. induction H using sub_rec; try now (econstructor; eauto).
  - intros. asimpl. eapply sub_refl.
  - intros. asimpl. eauto. cbn in *. eauto using sub_trans.
  - intros. asimpl. econstructor; eauto.
    asimpl. eapply IHsub2.
    auto_case; asimpl; cbn; eauto using sub_refl.
    eapply sub_weak; try reflexivity. eapply eq.
    all: try now asimpl.
    (* asimpl in H0. *)
  - intros. asimpl. econstructor; eauto. intros. rewrite in_map_iff in H2. destruct H2 as ((?&?)&?&?).
    inv H2. destruct (H _ _ H3) as (T&?&?&?).
    exists (T[sigma]). split; eauto. apply in_map. eauto.
Qed.

(** POPLMark Challenge 2b *)


Variable pat_ty : forall {m} (p: nat), pat m -> ty m ->  (fin p -> (ty m)) -> Prop.
Variable pat_eval : forall {m n} p, pat m -> tm m n -> (fin p -> (tm m n)) -> Prop.
Variable pat_ty_subst: forall {m n} (sigma: fin m -> ty n) p pt A Gamma, pat_ty m p pt A Gamma -> pat_ty n p (pt[sigma]) (A[sigma]) (Gamma >>  subst_ty sigma).


Instance pat_ty_morphism {m p} :
  Proper (eq ==> eq ==> pointwise_relation _ eq ==> Basics.impl) (@pat_ty m p).
Proof.
Admitted.


Inductive value {m n}: tm m n -> Prop :=
| Value_abs A s : value(abs A s)
| Value_tabs A s : value(tabs A s)
| Value_rec xs : (forall i s, In (i, s) xs -> value s) -> value (rectm xs).

Reserved Notation "'TY' Delta ; Gamma |- A : B"
  (at level 68, A at level 99, no associativity,
   format "'TY'  Delta ; Gamma  |-  A  :  B").

Inductive has_ty {m n} (Delta : ctx m) (Gamma : dctx  n m) : tm m n -> ty m -> Prop :=
| T_Var  x :
    TY Delta;Gamma |- var_tm x : Gamma x
  | T_abs (A: ty m) B (s: tm m (S n)):
    @has_ty m (S n) Delta (A .: Gamma) s B   ->
    TY Delta;Gamma |- abs A s : arr A B
| T_app A B s t: TY Delta;Gamma |- s : arr A B  -> TY Delta;Gamma |- t : A -> TY Delta;Gamma |- app s t : B
| T_tabs A B s : @has_ty (S m) n ((A .: Delta) >> ⟨↑⟩) (Gamma >> ⟨↑⟩) s B -> TY Delta;Gamma |- tabs A s : all A B
| T_Tapp A B A' s B' : TY Delta;Gamma |- s : all A B -> SUB Delta |- A' <: A -> B' = B[A'..] ->  TY Delta;Gamma |- tapp s A' : B'
| T_Rcd xs As : unique xs -> unique As -> label_equiv xs As
                -> (forall i A s, In (i, s) xs -> In (i, A) As -> TY Delta; Gamma |- s : A) -> TY Delta;Gamma |- rectm xs : recty As
| T_Proj xs j A As: TY Delta; Gamma |- xs : recty As -> In (j, A) As -> TY Delta; Gamma |- proj xs j : A
| letpat_ty p (pt: pat m) (s : tm m n) (t: tm m (p + n)) A (B : ty m) (Gamma': fin p -> ty m): has_ty Delta Gamma s A -> pat_ty _ p pt A Gamma' -> @has_ty m (p + n) Delta (scons_p p Gamma' Gamma) t B ->  has_ty Delta Gamma (letpat  p pt s t) B
| T_Sub A B s :
    TY Delta;Gamma |- s : A  -> SUB Delta |- A <: B   ->
    TY Delta;Gamma |- s : B
where "'TY' Delta ; Gamma |- s : A" := (has_ty Delta Gamma s A).

Instance has_ty_morphism {m n} :
  Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq ==> eq ==> Basics.impl) (@has_ty m n).
Proof.
Admitted.

Lemma T_Var' {m n} (Delta : ctx m) (Gamma : dctx n m) x :
  forall A, A = Gamma x -> TY Delta;Gamma |- var_tm x : A.
Proof. intros A ->. now econstructor. Qed.

Reserved Notation "'EV' s => t"
  (at level 68, s at level 80, no associativity, format "'EV'  s  =>  t").

Inductive eval {m n} : tm m n -> tm m n -> Prop :=
| E_appabs A s t : EV app (abs A s) t => s[ids; t..]
| E_Tapptabs A s B : EV tapp (tabs A s) B => s[B..; ids]
| E_RecProj  xs j s : In (j, s) xs -> EV (proj (rectm  xs) j) => s
| letpat_eval p (pt : pat m) (s : tm m n) (t : tm m (p + n)) (sigma: fin p -> tm m n) :  pat_eval _ _ p pt s sigma -> eval (letpat  p pt s t) (subst_tm (@var_ty m) (scons_p _ sigma (@var_tm _ _)) t)
| E_appFun s s' t :
     EV s => s' ->
     EV app s t => app s' t
| E_appArg s s' v:
     EV s => s' -> value v ->
     EV app v s => app v s'
| E_TyFun s s' A :
     EV s => s' ->
     EV tapp s A => tapp s' A
| E_Proj s s' j : EV s => s' -> EV (proj s j) => (proj s' j)
| E_Rec l ts t t' : EV t => t' -> In (l,t) ts -> EV (rectm ts) => rectm (update ts l t')                  | E_LetL p pt s s' t : EV s => s' -> EV (letpat p pt s t) => (letpat p pt s'  t)
where "'EV' s => t" := (eval s t).

Instance eval_morphism {m n}:
  Proper (eq ==> eq ==> Basics.impl) (@eval m n).
Proof.
Admitted.

(** Assumptions of progress and typing on patterns. *)
Variable pat_progress : forall p pt s A Gamma, TY empty; empty |- s : A -> pat_ty _ p pt A Gamma -> exists sigma, pat_eval _ _ p pt s sigma.


(** Progress *)

Lemma can_form_arr {s: tm 0 0} {A B}:
  TY empty;empty |- s : arr A B -> value s -> exists C t, s = abs C t.
Proof.
  intros H.
  depind H; intros; eauto.
  all: try now (try destruct x0;  try inversion H1).
 + inversion H0; subst; eauto. inversion x.
Qed.

Lemma can_form_all {s A B}:
  TY empty;empty |- s : all A B -> value s -> exists C t, s = tabs C t.
Proof.
  intros H.
  depind H; intros; eauto.
  all: try now (try destruct x0; try inversion H1).
  + inv H0; subst.  inversion x.  eauto.
Qed.

Lemma can_form_rectm {s A}:
  TY empty;empty |- s : recty A -> value s -> exists xs, s = rectm xs /\ forall l A', In (l, A') A -> exists s', In (l, s') xs.
Proof.
  intros H.
  depind H; intros; eauto.
   all: try now (try destruct x0; try inversion H1).
  + eexists. split; eauto.
    intros. apply H1; eauto.
  +  inv H0; subst; eauto.
     * inversion x.
     * edestruct IHhas_ty as (?&?&?); eauto.
       subst. exists x; split; eauto. intros.
       edestruct (H3 _ _ H0).
       eapply H2. apply H5.
Qed.

Theorem ev_progress s A:
  TY empty;empty |- s : A -> value s \/ exists t,  EV s => t.
Proof.
  intros. depind H; eauto; try now (left; constructor).
   - inversion x.
   - right. edestruct IHhas_ty1 as [? | [? ?]]; try reflexivity; eauto.
    + edestruct (can_form_arr H H1) as [? [? ?]]; subst.
      eexists. econstructor.
    + eexists. econstructor. eauto.
  - right. edestruct IHhas_ty as [? | [? ?]]; try reflexivity; eauto.
    + edestruct (can_form_all H H1) as [? [? ?]]; subst. eexists. econstructor.
    + eexists. econstructor. eauto.
  - assert ((forall p, In p xs -> value (snd p)) \/ (exists p, In p xs /\ exists s', EV (snd p) => s')) as [|].
    { apply list_dec. intros (?&?) ?. cbn.
      assert (exists A, In (n, A) As) as (A&?). apply H1; eauto.
      eauto. }
    + left. constructor. intros. specialize (H4 (i, s)). eauto.
    + destruct H4 as ((l&s)&?&(s'&?)).
      right. exists (rectm (update xs l s')). econstructor; eauto.

  - right. edestruct IHhas_ty as [? | [? ?]]; eauto.
    + edestruct (can_form_rectm H H1) as [? [? ?]]; try reflexivity. subst.
      rename x into xs.
      enough (exists x, In (j, x) xs) as (?&?).
      * eexists. constructor. eauto.
      * inversion H; eauto.
    + eexists. constructor. eassumption.
  - edestruct (IHhas_ty1 pat_ty_subst pat_progress s0 A0) as [|[? ?]]; eauto.
    + right. edestruct (pat_progress _ _ _ _ _ H H0). eexists. econstructor. eauto.
    + right. eexists. apply E_LetL; eauto.
Qed.


(** Preservation *)

(* TODO always use setoid_rewrite in substify in renamify *)
Ltac substify := auto_unfold; try repeat setoid_rewrite rinstInst'_tm;
                  try repeat setoid_rewrite rinstInst'_pat;
                  try repeat setoid_rewrite rinstInst'_ty.

Ltac fsimpl_fext :=
  repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *); idtac "fsimpl0"
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *); idtac "fsimpl1"
         | [|- context [id ?s]] => change (id s) with s; idtac "fsimpl2"
         (* | [|- context[comp ?f ?g]] => change (comp f g) with (g >> f) (* AsimplCompIdL *) *)
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *); idtac "fsimpl3"

         | [|- zero_p >> scons_p ?f ?g] => rewrite scons_p_head; idtac "fsimpl4"

         | [|- context[(?s.:?sigma) var_zero]] => change ((s.:sigma) var_zero) with s; idtac "fsimpl5"
         | [|- context[(?s.:?sigma) (shift ?m)]] => change ((s.:sigma) (shift m)) with (sigma m); idtac "fsimpl6"

         | [|- context[idren >> ?f]] => change (idren >> f) with f; idtac "fsimpl7"
         | [|- context[?f >> idren]] => change (f >> idren) with f; idtac "fsimpl8"
         | [|- context[?f >> (?x .: ?g)]] => change (f >> (x .: g)) with g; idtac "fsimpl9"
         | [|- context[?x2 .: shift >> ?f]] => change x2 with (f var_zero); rewrite (@scons_eta _ _ f); idtac "fsimpl10"
         | [|- context[?f var_zero .: ?g]] => change g with (shift >> f); rewrite scons_eta; idtac "fsimpl11"

         |[|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s); idtac "fsimpl12"
         |[|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s); idtac "fsimpl13"

         | _ => first [progress (rewrite scons_comp) |  progress (rewrite scons_eta_id) | progress (autorewrite with FunctorInstances)]; idtac "fsimpl14"
         end.

Ltac asimpl_fext' := repeat (first
                      [ progress rewrite substSubst_tm; idtac "substSubst_tm"
                      | progress rewrite renSubst_tm; idtac "renSubst_tm"
                      | progress rewrite substRen_tm; idtac "substRen_tm"
                      | progress rewrite renRen_tm; idtac "renRen_tm"
                      | progress rewrite substSubst_pat; idtac "substSubst_pat"
                      | progress rewrite renSubst_pat; idtac "renSubst_pat"
                      | progress rewrite substRen_pat; idtac "substRen_pat"
                      | progress rewrite renRen_pat; idtac "renRen_pat"
                      | progress rewrite substSubst_ty; idtac "substSubst_ty"
                      | progress rewrite renSubst_ty; idtac "renSubst_ty"
                      | progress rewrite substRen_ty; idtac "substRen_ty"
                      | progress rewrite renRen_ty; idtac "renRen_ty"
                      | progress rewrite substSubst'_tm; idtac "substSubst'_tm"
                      | progress rewrite renSubst'_tm; idtac "renSubst'_tm"
                      | progress rewrite substRen'_tm; idtac "substRen'_tm"
                      | progress rewrite renRen'_tm; idtac "renRen'_tm"
                      | progress rewrite varLRen_tm; idtac "varLRen_tm"
                      | progress rewrite varL_tm; idtac "varL_tm"
                      | progress rewrite rinstId_tm; idtac "rinstId_tm"
                      | progress rewrite instId_tm; idtac "instId_tm"
                      | progress rewrite substSubst'_pat; idtac "substSubst'_pat"
                      | progress rewrite renSubst'_pat; idtac "renSubst'_pat"
                      | progress rewrite substRen'_pat; idtac "substRen'_pat"
                      | progress rewrite renRen'_pat; idtac "renRen'_pat"
                      | progress rewrite rinstId_pat; idtac "rinstId_pat"
                      | progress rewrite instId_pat; idtac "instId_pat"
                      | progress rewrite substSubst'_ty; idtac "substSubst'_ty"
                      | progress rewrite renSubst'_ty; idtac "renSubst'_ty"
                      | progress rewrite substRen'_ty; idtac "substRen'_ty"
                      | progress rewrite renRen'_ty; idtac "renRen'_ty"
                      | progress rewrite varLRen_ty; idtac "varLRen_ty"
                      | progress rewrite varL_ty; idtac "varL_ty"
                      | progress rewrite rinstId_ty; idtac "rinstId_ty"
                      | progress rewrite instId_ty; idtac "instId_ty"
                      | progress
                         unfold up_list_tm_tm, up_list_tm_ty, up_list_ty_tm,
                          up_tm_tm, up_tm_ty, up_ty_tm, upRen_list_tm_tm,
                          upRen_list_tm_ty, upRen_list_ty_tm, upRen_tm_tm,
                          upRen_tm_ty, upRen_ty_tm, up_list_ty_ty, up_ty_ty,
                          upRen_list_ty_ty, upRen_ty_ty, up_ren; idtac "unfold"
                      | progress
                         cbn[subst_tm ren_tm subst_pat ren_pat subst_ty
                            ren_ty]; idtac "cbn"
                      | fsimpl_fext; idtac "fsimpl" ]).

Ltac asimpl_fext := repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                       Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                       Ren_pat, Ren1, ren1, Subst_pat, Subst1, subst1,
                       VarInstance_tm, Var, ids, Ren_tm, Ren2, ren2,
                       Up_ty_tm, Up_tm, up_tm, Up_tm_ty, Up_ty, up_ty,
                       Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst2, subst2 
                       in *; asimpl_fext'; repeat try unfold_funcomp.

Instance scons_p_morphism {X:Type} (m n:nat) :
  Proper (pointwise_relation (fin m) eq ==> pointwise_relation (fin n) eq ==> @eq (fin (m + n)) ==> @eq X) (@scons_p X m n).
Proof.
  intros sigma sigma' Hsigma tau tau' Htau x x' <-.
  induction m as [|m] in n, sigma, tau, sigma', tau', Hsigma, Htau, x |- *.
  - cbn. apply Htau.
  - cbn. destruct x as [|x].
    + cbn. apply IHm.
      intros y.
      apply (Hsigma (Some y)).
      apply Htau.
    + cbn. apply (Hsigma var_zero).
Qed.

(* Ltac fsimpl := *)
(*   repeat match goal with *)
(*          | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *) *)
(*          | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *) *)
(*          | [|- context [id ?s]] => change (id s) with s *)
(*          | [|- context[(?f >> ?g) >> ?h]] => change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *) *)
(*          (* | [|- zero_p >> scons_p ?f ?g] => rewrite scons_p_head *) *)
(*          | [|- context[(?s .: ?sigma) var_zero]] => change ((s.:sigma) var_zero) with s *)
(*          | [|- context[(?s .: ?sigma) (shift ?m)]] => change ((s.:sigma) (shift m)) with (sigma m) *)
(*          | [|- context[idren >> ?f]] => change (idren >> f) with f *)
(*          | [|- context[?f >> idren]] => change (f >> idren) with f *)
(*          | [|- context[?f >> (?x .: ?g)]] => change (f >> (x .: g)) with g (* f should evaluate to shift *) *)
(*          | [|- context[?x2 .: (fun x => ?f (shift x))]] => change (scons x2 (fun x => f (shift x))) with (fun x => (scons (f var_zero) (fun x => f (shift x))) x); setoid_rewrite (@scons_eta' _ _ f); eta_reduce *)
(*          | [|- context[?f var_zero .: ?g]] => change (scons (f var_zero) g) with (fun x => (scons (f var_zero) (fun x => f (shift x))) x); setoid_rewrite scons_eta'; eta_reduce *)
(*          (* we completely unfold funcomp *) *)
(*          (* |[|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s) *) *)
(*          (* |[|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s) *) *)
(*          | [|- context[fun x => ?tau (scons ?s ?sigma x)]] => setoid_rewrite scons_comp'; eta_reduce *)
(*          | [|- context[fun x => ?tau (scons_p ?p ?f ?g x)]] => setoid_rewrite scons_p_comp'; eta_reduce *)
(*          | [|- context[scons (@var_zero ?n) shift]] => change (scons (@var_zero n) shift) with (fun x => (scons (@var_zero n) shift) x); setoid_rewrite scons_eta_id'; eta_reduce *)
(*          (* | _ => progress autorewrite with FunctorInstances2 *) *)
(*          end. *)

(* Hint Rewrite @scons_p_comp' @scons_p_head' @scons_p_tail' : FunctorInstances2. *)

Lemma scons_p_head2' {X} {m n} (f : fin m -> X) (g : fin n -> X):
  pointwise_relation _ eq (zero_p m >> (scons_p m f g)) f.
Proof.
  intros z.
  unfold funcomp.
 induction m.
  - inversion z.
  - destruct z.
    + simpl. simpl. now rewrite IHm.
    + reflexivity.
Qed.

Lemma scons_p_tail2' X  m n (f : fin m -> X) (g : fin n -> X) :
  pointwise_relation _ eq (shift_p m >> scons_p m f g) g.
Proof. intros z; unfold funcomp. induction m; cbn; eauto. Qed.

Lemma scons_p_comp2' X Y m n (f : fin m -> X) (g : fin n -> X) (h : X -> Y):
  pointwise_relation _ eq ((scons_p m f g) >> h) (scons_p m (f >> h) (g >> h)).
Proof.
  intros x.
  unfold funcomp.
  destruct (destruct_fin x) as [[x' ->]|[x' ->]].
  - (* TODO this might be one of the problems Yannick encountered.
     * *)
    now setoid_rewrite scons_p_head'.
  - now setoid_rewrite scons_p_tail'.
Qed.

Instance funcomp_morphism {X Y Z} :
  Proper (@pointwise_relation Y Z eq ==> @pointwise_relation X Y eq ==> @pointwise_relation X Z eq) funcomp.
Proof.
  cbv - [funcomp].
  intros g0 g1 Hg f0 f1 Hf x.
  unfold funcomp. rewrite Hf, Hg.
  reflexivity.
Qed.

(* Lemma forall_pointwise {X} {Y: X} (f g: X -> Y) : (forall x, f x = g x) -> pointwise_relation _ eq f g. *)
(* Proof. *)
(*   intros * H x. apply H. *)
(* Qed. *)

Lemma crl0:
  forall (m n p : nat) (pt : pat m) (s : tm m n) (t : tm m (p + n)) (A B : ty m) (m' n' : nat)
    (Delta: ctx m) (Gamma: dctx n m)
    (Delta0 : ctx m') (Gamma0 : dctx n' m') (xi : fin m -> fin m') (zeta : fin n -> fin n')
    (Gamma': fin p -> ty m) (H: pat_ty m p pt A Gamma')
    (ty1: TY Delta;Gamma |- s : A) (ty2: TY Delta;scons_p p Gamma' Gamma |- t : B)
  (IHty1 : forall (m' n' : nat) (Delta0 : ctx m') (Gamma0 : dctx n' m') (xi : fin m -> fin m')
            (zeta : fin n -> fin n'),
          (forall x : fin m, (Delta x) ⟨xi⟩ = Delta0 (xi x)) ->
          (forall x : fin n, (Gamma x) ⟨xi⟩ = Gamma0 (zeta x)) -> TY Delta0;Gamma0 |- s ⟨xi;zeta⟩ : A ⟨xi⟩)
  (IHty2 : forall (m' n' : nat) (Delta0 : ctx m') (Gamma0 : dctx n' m') (xi : fin m -> fin m')
            (zeta : fin (p + n) -> fin n'),
          (forall x : fin m, (Delta x) ⟨xi⟩ = Delta0 (xi x)) ->
          (forall x : fin (p + n), (scons_p p Gamma' Gamma x) ⟨xi⟩ = Gamma0 (zeta x)) ->
          TY Delta0;Gamma0 |- t ⟨xi;zeta⟩ : B ⟨xi⟩)
  (H0: forall x : fin m, (Delta x) ⟨xi⟩ = Delta0 (xi x)) (H': forall x : fin n, (Gamma x) ⟨xi⟩ = Gamma0 (zeta x)),
  
 TY Delta0;Gamma0 |- letpat p pt ⟨xi⟩ s ⟨xi;zeta⟩ t ⟨xi;upRen_p p zeta⟩ : B ⟨xi⟩.
Proof.
  intros m n p pt s t A B m' n' Delta Gamma Delta0 Gamma0 xi zeta Gamma' H ty1 ty2 IHty1 IHty2 H0 H'.
  cbn. asimpl. apply letpat_ty  with (A0 := A⟨xi⟩) (Gamma'0 := Gamma' >> ⟨xi⟩); eauto.
  + unfold funcomp.
    (* TODO the unfold funcomp should not be necessary anymore when I use Yannicks appraoch *)
    substify.
    eauto.
  + asimpl.
    Hint Opaque scons_p : rewrite.
    Hint Opaque subst_ty : rewrite.
    eapply IHty2; eauto; asimpl.
    *
      (** * works *)
      (* DONE try to make the goal into pointwise_relation *)
      (* enough (H2: pointwise_relation _ eq ((scons_p p Gamma' Gamma ) >> (ren_ty xi)) ((upRen_p p zeta ) >> (scons_p p (Gamma' >> ren_ty xi) Gamma0 ))) by apply H2. *)
      (* (* intros z. *) *)
      (* (* adrian: had to add the following line to make it compile.*) *)
      (* unfold dctx in Gamma, Gamma0. unfold upRen_p. *)
      (* (* TODO setoid-asimpl does not work with scons_p yet *) *)
      (* (* DONE use normal rewrite for asimpl_fext *)
      (*  * works the same as it should (because it only used rewrite to begin with) *) *)
      (* (* match goal with *) *)
      (* (*    |[|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s); idtac "fsimpl12" *) *)
      (* (*    |[|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s); idtac "fsimpl13" *) *)
      (* (* end. *) *)
      (* (* match goal with *) *)
      (* (*    |[|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s); idtac "fsimpl12" *) *)
      (* (*    |[|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s); idtac "fsimpl13" *) *)
      (* (* end. *) *)
      (* (* autorewrite with FunctorInstances. *) *)

      (* setoid_rewrite scons_p_comp2'. *)
      (* setoid_rewrite scons_p_head2'. *)
      (* match goal with *)
      (*    | [|- context[(?f >> ?g) >> ?h]] => *)
      (*      change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *); idtac "fsimpl3" *)
      (* end. *)
      (* setoid_rewrite scons_p_tail2'. *)

      (* (* TODO can we do it without unfolding funcomp? *) *)
      (* unfold funcomp. *)
      (* setoid_rewrite H'. *)

      intros z.
      unfold dctx in Gamma, Gamma0. unfold upRen_p.
      unfold funcomp.
      (* TODO this rewrites too eagerly and also uses the eq that is applied to the scons_p
       * If I don't unfold funcomp this would not be a problem
       * But I'm wondering why this happens here but not in the other file with just scons?*)
      Fail setoid_rewrite scons_p_comp'.
      (* autorewrite with FunctorInstances2. *)
      rewrite (scons_p_comp' _ _ (ren_ty xi)).
      rewrite (scons_p_comp' _ _ (scons_p p (fun x : fin p => ren_ty xi (Gamma' x)) Gamma0)).
      unfold funcomp.
      setoid_rewrite scons_p_head'.
      (* match goal with *)
      (*    | [|- context[(?f >> ?g) >> ?h]] => *)
      (*      change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *); idtac "fsimpl3" *)
      (* end. *)
      setoid_rewrite scons_p_tail'.
      (* autorewrite with FunctorInstances. *)
      (* fsimpl_fext. *)
      (* asimpl_fext. *)
  (* scons_p p (Gamma' >> ⟨xi⟩) (Gamma >> ⟨xi⟩) z = scons_p p (Gamma' >> ⟨xi⟩) (zeta >> Gamma0) z *)
      (* asimpl. *)
      (* unfold funcomp. *)
      (* setoid_rewrite scons_p_comp'. *)
      unfold funcomp.
      (* DONE why does it not use the morphism?
       * because my scons_p morphism had (pointwise_relation) in the conclusion (because scons_p returns a function)
       * but here we want to solve an equality so we need eq in the conclusion.
       * therefore we need to inline the extensional equality in the morphism's signature by taking another eq argument and returning an eq of the results *)
      setoid_rewrite H'.
      reflexivity.
Qed.

Lemma context_renaming_lemma m m' n n' (Delta: ctx m') (Gamma: dctx n' m')                                                   (s: tm m n) A (xi : fin m -> fin m') (zeta: fin n -> fin n') Delta' (Gamma' : dctx n m):
  (forall x, (Delta' x)⟨xi⟩ = Delta (xi x)) ->
  (forall (x: fin n) , (Gamma' x)⟨xi⟩ =  (Gamma (zeta x))) ->
  TY Delta'; Gamma' |- s : A -> TY Delta; Gamma |- s⟨xi;zeta⟩ : A⟨xi⟩.
Proof.
  intros H H' ty. autorevert ty.
  depind ty; asimpl; intros; subst; try now (econstructor; eauto).
  - rewrite H0. constructor.
  - constructor. eapply IHty; eauto.
    auto_case; asimpl.
  - cbn. econstructor. apply IHty; eauto.
    + auto_case; try now asimpl. rewrite <- H. now asimpl.
    + intros. asimpl. rewrite <- H'. now asimpl.
  - cbn. eapply T_Tapp with (A0 := A⟨xi⟩) .
    asimpl in IHty. eapply IHty; eauto.
    eapply sub_weak; eauto. now asimpl.
  - econstructor; eauto.
    + intros.
      eapply in_map_iff in H5. destruct H5 as ([]&?&?). inv H5.
      eapply in_map_iff in H6. destruct H6 as ([j A']&?&?). inv H5.
      eapply H3; eassumption.
  - cbn. econstructor; eauto. now apply in_map.
  - apply (crl0 m n p pt s t A B m' n' Delta Gamma Delta0 Gamma0 xi zeta Gamma' H ty1 ty2 IHty1 IHty2 H0 H').
  - econstructor. eauto. eapply sub_weak; eauto.
Qed.

Lemma context_renaming_lemma' m m' n n' (Delta: ctx m') (Gamma: dctx n' m')                                                   (s: tm m n) A (xi : fin m -> fin m') (zeta: fin n -> fin n') Delta' (Gamma' : dctx n m):
  (forall x, (Delta' x)⟨xi⟩ = Delta (xi x)) ->
  (forall (x: fin n) , (Gamma' x)⟨xi⟩ =  (Gamma (zeta x))) ->
  TY Delta'; Gamma' |- s : A -> forall s' A', s' = s⟨xi;zeta⟩ -> A' = A⟨xi⟩ -> TY Delta; Gamma |- s' : A'.
Proof. intros. subst. now eapply context_renaming_lemma. Qed.

Lemma context_morphism_lemma m m' n n' (Delta: ctx m) (Delta': ctx m') (Gamma: dctx n m) (s: tm m n) A (sigma : fin m -> ty m') (tau: fin n -> tm m' n') (Gamma' : dctx n' m'):
  (forall x, SUB Delta' |- sigma x <: (Delta x)[sigma]) ->
  (forall (x: fin n) ,  TY Delta'; Gamma' |- tau x : subst_ty sigma (Gamma x)) ->
  TY Delta; Gamma |- s : A -> TY Delta'; Gamma' |- s[sigma;tau] : A[sigma].
Proof.
   intros eq1 eq2 ty. autorevert ty.
   depind ty; intros; subst; asimpl; try now (econstructor; eauto).
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
    + intros x. asimpl.
      assert ((Gamma x) [sigma >> ⟨↑⟩] = (Gamma x)[sigma]⟨↑⟩) by (now asimpl).
      auto_unfold in *. rewrite H.
      eapply context_renaming_lemma; try eapply eq2.
      * intros. now asimpl.
      * intros. now asimpl.
  - eapply T_Tapp with (A0 := subst_ty sigma A) .
    asimpl in IHty. eapply IHty; eauto.
    eapply sub_substitution; eauto.
    now asimpl.
  - econstructor; eauto.
    + intros.
      eapply in_map_iff in H5. destruct H5 as ([]&?&?). inv H5.
      eapply in_map_iff in H4. destruct H4 as ([j A']&?&?). inv H4.
      eapply H3; eauto.
  - econstructor; eauto. now apply in_map.
  - econstructor; eauto.
     { eapply IHty2.
      * eauto.
      * intros x.
        destruct (destruct_fin x) as [[x' ->] |[x' ->]]; asimpl; eauto.
        -- eapply T_Var'. now asimpl.
        -- eapply context_renaming_lemma'; try eapply eq2; try now asimpl.
           intros z.
           now asimpl.
           (* TODO setoid-asimpl does not work with scons_p yet *)
           intros x. now asimpl_fext.
     } 
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
   - edestruct (IHhas_ty pat_ty_subst pat_progress  _ _ _ _ (eq_refl _) (sub_trans _ _ _ _ _ H0 H1)) as (?&?&?&?).
     split.
     + assumption.
     + eauto.
Qed.

Lemma ty_inv_rec {m n} {Delta Gamma A As'} xs  :
  TY Delta;Gamma |- rectm xs: A  ->  SUB Delta |- A <: recty As' ->
   (  (forall (i : nat) (s : tm m n) B',
          In (i, s) xs -> In (i, B') As' ->  exists (B : ty m),  TY Delta;Gamma |- s : B /\ SUB Delta |- B <: B')).
Proof.
  intros H. depind H; intros.
  - inv H4. eauto.
    assert (exists A, In (i, A) As) as [A ?].
    + apply H1. eauto.
    + specialize (H2 _ _ _ H5 H4).
      destruct (H9 _ _ H6) as (?&?&?).
      assert (x = A) as -> by eauto using unique_spec.
      eauto.
  - eauto using sub_trans.
Qed.

Lemma ty_subst m n (Gamma: dctx m n) (Delta: ctx n) Delta' s A:
    (forall x, SUB Delta' |- Delta' x <: Delta x) ->
  TY Delta; Gamma |- s : A -> TY Delta'; Gamma |- s : A.
Proof.
  intros eq H. autorevert H. depind H; eauto; intros; try now (econstructor; eauto).
  - econstructor; eauto. asimpl. eapply IHhas_ty. auto_case; eauto using sub_refl.
    eapply sub_weak; try reflexivity. apply eq. intros x. now asimpl.
  - econstructor; eauto.
    replace A with (A[ids]) by (now asimpl). replace A' with (A'[ids]) by (now asimpl).
    eapply sub_substitution; eauto. intros x.
    asimpl. econstructor. eauto.
 - econstructor; eauto. eapply sub_substitution with (sigma := ids) in H0; eauto.
    asimpl in H0. eapply H0. intros x. econstructor. asimpl. eapply eq.
Qed.

Lemma ty_inv_tabs {m n} {Delta Gamma A A' B C} (s : tm (S m) n):
  TY Delta;Gamma |- tabs A s : C -> SUB Delta |- C <: all A' B   ->
  (SUB Delta |- A' <: A /\ exists B',
   TY (A'.:Delta) >> ren_ty ↑; Gamma >> ren_ty ↑ |- s : B' /\ SUB (A' .: Delta) >> ren_ty ↑ |- B' <: B).
Proof.
  intros H. depind H; intros.
  - inv H0. split; eauto.
    eexists. split; eauto.
    eapply ty_subst; try eapply H.
    auto_case. eapply sub_weak; try reflexivity; eauto.
  - eauto using sub_trans.
Qed.

Variable pat_ty_eval : forall m n p pt s A (Gamma: fin n -> ty m) Gamma' Delta sigma, pat_ty m p pt A Gamma' -> TY Delta; Gamma |- s : A -> pat_eval m n p pt s sigma -> forall (x: fin p), TY Delta; Gamma |- sigma x : Gamma' x.


Theorem preservation m n Delta Gamma (s: tm m n) t A :
  TY Delta;Gamma |- s : A -> EV s => t ->
  TY Delta;Gamma |- t : A.
Proof.
  intros H_ty H_ev. autorevert H_ev.
  induction H_ev; intros; eauto using ty.
  all: try now (depind H_ty; [econstructor; eauto|eapply T_Sub; eauto]).
  - depind H_ty; [|eauto].
    + inv H_ty1; subst.
      * replace B with (B[ids]) by (now asimpl).
        eapply context_morphism_lemma; eauto.
        -- intros. asimpl. repeat constructor. now apply sub_refl.
        -- intros [|]; intros; cbn; asimpl;  eauto. econstructor; eauto.
      * pose proof (ty_inv_abs _ _ _ _ _ _ _ _ _ H H0) as (?&?&?&?).
        eapply T_Sub; eauto.
        replace x with (x[var_ty]) by (now asimpl).
        eapply context_morphism_lemma; eauto.
        -- intros. asimpl. repeat constructor. apply sub_refl.
        -- intros [|]; intros; cbn; asimpl; eauto; econstructor; eauto.
     + asimpl. econstructor; eauto.
  - depind H_ty; eauto.
    + depind H_ty.
      * asimpl in H_ty.
        eapply context_morphism_lemma; try eapply H_ty; eauto.
        -- auto_case; asimpl; eauto using sub_refl.
        -- intros x. asimpl. constructor.
      * pose proof (ty_inv_tabs _ H_ty H) as (?&?&?&?).
        eapply T_Sub.  asimpl.
        (* asimpl in * *)
        eapply context_morphism_lemma; eauto.
        -- auto_case; asimpl; eauto.
        -- intros z. asimpl. constructor.
        -- eapply sub_substitution; eauto.
           auto_case; asimpl.
    + econstructor; eauto.
  -  depind H_ty; eauto.
    + depind H_ty.
      * eapply H2; eauto.
      * pose proof (ty_inv_rec _ H_ty H  _ _ _ H1 H0) as(?&?&?).
        subst. eapply T_Sub; eauto.
    + econstructor; eauto.
  - depind H_ty.
    + replace B with (B[ids]) by now asimpl.
      eapply context_morphism_lemma; try now apply H_ty2.
      * intros. asimpl. constructor. now apply sub_refl.
      * intros. destruct (destruct_fin x) as [[]|[]]; subst.
        (* TODO why did I have to do `exact Gamma'` here twice? *)
        -- asimpl. eapply pat_ty_eval; eauto. exact Gamma'.
        -- asimpl. constructor. exact Gamma'.
    + eapply T_Sub; eauto.
  - depind H_ty; [|eapply T_Sub; eauto].
    econstructor; eauto.
    + intros.
      apply update_char in H5 as [|(->&->)]; eauto.
Qed.

End Pattern.
