(** * Decidable [In] Predicate *)

Set Implicit Arguments.

Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.

(** In the current work, we need a decidable version of [In] predicate.
   - The standard [In] in the Coq library is not suitable for the current work.
   - It is necessary in defining language syntax.
     (Cf. the definition of [pterm] in [language_syntax.v])
   - We need an decidable, but equivalent variant. *)

Definition decidable (A:Type)
  := forall a b :A, {a = b} + { a <> b}.

Definition dec (P :Prop)
  := { P } + {~P}.

Fixpoint IN A (decA:decidable A)(a:A)(l:list A) {struct l} : Prop :=
  match l with
    | nil    => False
    | b :: m => 
      if decA a b then True else IN decA a m
  end.

(** Abbreviations for [IN] in case of natural numbers.
   We remark that any denumerably decidable set can be use
   instead of [nat].
   Here we use natural numbers for any kind of names for simplicity. *)

Notation name := nat.
Notation eqdec := eq_nat_dec.


Lemma decIn : forall (x:nat) (l:list nat),
  {In x l} + {~ In x l}.
Proof.
  induction l as [| a l' [IH|IH]].
  - now right.
  - left. right. assumption.
  - destruct (eqdec a x) as [->|H].
    + left. left. reflexivity.
    + right. intros [H'|H'].
      apply H, H'.
      apply IH, H'.
Defined.


Notation "k == i" := (eqdec k i) (at level 70).

Notation IN_name := (@IN name eqdec).

Notation " x # l " := (~ IN_name  x l) (at level 70).

Notation rm_name := (remove eqdec).

(** Tactics for destructing the decidable equality between naturals numbers. *)

Ltac case_var :=
  let ldestr k i := destruct (k == i); [try subst k | idtac] in
  match goal with
  | |- context [?k == ?i]      => ldestr k i
  | H: context [?k == ?i] |- _ => ldestr k i
  end.

Ltac case_dec decA :=
  match goal with
    | |- context [decA ?a ?b]       => destruct (decA a b)
    | _ : context [decA ?a ?b] |- _ => destruct (decA a b)
  end.

(** Decidability of being-in-a-list *)

Lemma decIN : forall A decA (x:A) (l:list A),
  {IN decA x l} + {~ IN decA x l}.
Proof.
  induction l as [| a]; simpl;
    [ right
      | case_dec decA
    ]; auto.
Defined.

Notation "x <-? l" := (decIN eqdec x l) (at level 70).

Ltac case_IN :=
  match goal with
    | |- context [?x <-? ?l]       => destruct (x <-? l)
    | H : context [?x <-? ?l] |- _ => destruct (x <-? l)
  end.

(** Uniqueness of proofs of being-in-a-list *)

Lemma IN_proof_uniq : forall A decA (a:A)(l:list A)(p q:IN decA a l),
  p = q.
Proof.
  induction l; simpl; intros p q;
    [ elim p
      | case_dec decA;
        [ case p; case q; reflexivity
          | apply IHl
        ]
    ].
Qed.

Hint Resolve decIN IN_proof_uniq : datatypes.

(** Equivalence of [IN] and [In] *)

Lemma IN_In : forall A decA (l:list A)(a:A),
  IN decA a l <-> In a l.
Proof. 
  induction l; simpl;
    [ tauto
      | split; intros; case_dec decA; firstorder; congruence].
Qed.

(** Repalcing [IN] with [In] in order to use the library about [In]. *)

Ltac rew_IN :=
  match goal with
    | |- context [IN _ _ _]       => rewrite IN_In
    | H : context [IN _ _ _] |- _ => rewrite IN_In in H
  end.

Ltac rew_In decA :=
  match goal with
    | |- context [In _ _]       => rewrite <- (IN_In decA)
    | H : context [In _ _] |- _ => rewrite <- (IN_In decA) in H
  end.

(** Useful lemmas about [IN] *)

Lemma IN_eq : forall A decA (a:A) (l:list A),
  IN decA a (a :: l). 
Proof.
  intros; rewrite IN_In; auto with datatypes. 
Qed.

Lemma IN_cons : forall A decA (l : list A)(a b:A), 
  IN decA b l ->
  IN decA b (a::l).
Proof.
  intros; repeat rew_IN; auto using in_cons.
Qed.  

Lemma neq_IN_cons : forall A decA (l : list A) (a b:A), 
  a <> b ->
  IN decA b (a::l) ->
  IN decA b l.
Proof.
  intros until 1; simpl; case_dec decA; congruence.
Qed.

Hint Resolve IN_In IN_eq IN_cons neq_IN_cons : datatypes.

Lemma IN_rm_1 : forall A decA (a b : A) (l: list A),
  IN decA a (remove decA b l) ->
  IN decA a l.
Proof.
  induction l as [| c l IHl]; simpl; intros; auto.
  repeat case_dec decA; auto.
  apply IHl; apply neq_IN_cons with c; auto.
Qed.

Lemma IN_rm_2 : forall A decA (a b:A) (l:list A), 
  a <> b ->
  IN decA a l ->
  IN decA a (remove decA b l).
Proof.
  induction l as [|c]; simpl; intros; auto.
  repeat case_dec decA;
    [ congruence
      | auto
      | subst; apply IN_eq
      | repeat rew_IN; auto using in_cons ].
Qed.

Lemma IN_rm_neq : forall A decA (a b : A) (l: list A),
  IN decA a (remove decA b l) ->
  a <> b.
Proof.
  induction l as [| c l IHl]; simpl; intros; auto.
  intro; subst.
  case_dec decA; firstorder.
  elim IHl; eauto using neq_IN_cons.
Qed.

Hint Resolve IN_rm_1 IN_rm_2 IN_rm_neq : datatypes.

Lemma IN_or_app : forall A decA (a:A) (l m :list A),
  IN decA a l \/ IN decA a m ->
  IN decA a (l ++ m).
Proof.
  intros; repeat rew_IN; auto with datatypes.
Qed.
    
Lemma IN_app_or : forall A decA (a:A) (l m :list A),
  IN decA a (l ++ m) ->
  IN decA a l \/ IN decA a m.
Proof.
  intros; repeat rew_IN; auto with datatypes.
Qed.
      
Arguments IN_app_or [A decA a l m].

Lemma IN_appL : forall A decA (a:A)(l m: list A),
  IN decA a l ->
  IN decA a (l ++ m).
Proof.
  intros; apply IN_or_app; left; assumption.
Qed.

Lemma IN_appR : forall A decA (a:A)(l m: list A),
  IN decA a m ->
  IN decA a (l ++ m).
Proof.
  intros; apply IN_or_app; right; assumption.
Qed.

Hint Resolve IN_or_app IN_app_or IN_appL IN_appR : datatypes.

Lemma notIN_rm_1 : forall A decA (a : A) (l: list A),
  ~ IN decA a (remove decA a l).
Proof.
  induction l; simpl; intros; intuition.
  case_dec decA; auto.
  simpl in H; case_dec decA; auto.
Qed.

Lemma notIN_rm_2 : forall A decA (a b:A) (l:list A), 
  ~ IN decA a (remove decA b l) ->
  a <> b ->
  ~ IN decA a l.
Proof.
  intros * Hnin Hneq Hin.
  apply Hnin. apply IN_rm_2; assumption.
Qed.

Hint Resolve notIN_rm_1 notIN_rm_2 : datatypes.

Lemma notIN_app_1 : forall A decA (a:A) (l m :list A),
  ~ IN decA a (l ++ m) ->
  ~ IN decA a l /\ ~ IN decA a m.
Proof.
  firstorder with datatypes.
Qed.

Lemma notIN_app_2 : forall A decA (a:A) (l m :list A),
  ~ IN decA a l ->
  ~ IN decA a m ->
  ~ IN decA a (l ++ m).
Proof.
  intuition; elim (IN_app_or H1); assumption.
Qed.

Lemma notIN_app_3 : forall A decA (a:A)(l m: list A),
  ~ IN decA a (l ++ m) -> ~ IN decA a l.
Proof.
  intros; elim (notIN_app_1 _ _ _ _ H); tauto.
Qed.

Lemma notIN_app_4 : forall A decA (a:A)(l m: list A),
  ~ IN decA a (l ++ m) -> ~ IN decA a m. 
Proof.
  intros; elim (notIN_app_1 _ _ _ _ H); tauto.
Qed.

Lemma notIN_cons_1 : forall A decA (a b:A)(l:list A),
  ~ IN decA a (b :: l) ->
  a <> b.
Proof.
  red; intros ? ? ? ? ? H ?; subst.
  elim H; apply IN_eq.
Qed.

Lemma notIN_cons_2 : forall A decA (a b:A)(l:list A),
  ~ IN decA a (b :: l) ->
  ~ IN decA a l.
Proof.
  red; intros ? ? ? ? ? H ?.
  elim H; repeat rew_IN; auto with datatypes.
Qed.

Hint Resolve notIN_app_1 notIN_app_2 notIN_app_3 notIN_app_4 : datatypes.
Hint Resolve IN_cons notIN_cons_1 notIN_cons_2 : datatypes.

Lemma notIN_cons_3 : forall A decA (a b:A) (l:list A),
  a <> b ->
  ~ IN decA b l ->
  ~ IN decA b (a :: l).
Proof.
  firstorder; simpl; case_dec decA; auto.
Qed.

Lemma notIN_singleton_1 : forall A decA (a b:A),
  a <> b ->
  ~ IN decA b (a :: nil).
Proof.
  firstorder; simpl; case_dec decA; auto.
Qed.

Lemma notIN_empty_1 : forall A decA (a:A),
  ~ IN decA a nil.
Proof.
  firstorder.
Qed.

Lemma rm_cons : forall A decA a b (l:list A),
  a <> b ->
  b :: remove decA a l = remove decA a (b :: l).
Proof.
  intros; simpl; destruct (decA a b);
    [ elim H
      | ];
    auto.
Qed.
