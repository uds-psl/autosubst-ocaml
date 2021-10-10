Require Import List Arith.
Import ListNotations.
Require Import core.


Notation eqdec := eq_nat_dec.

(* Fixpoint InN (n: nat) (l: list nat) : Type := *)
(*   match l with *)
(*   | [] => False *)
(*   | m :: l => (m = n) + InN n l *)
(*   (* | m :: l => (m = n) + (m <> n) * InN n l *) *)
(*   end. *)

Inductive le' : nat -> nat -> Prop :=
  | le0 : forall m, le' 0 m
  | le__S : forall n m, le' n m -> le' (S n) (S m).

Definition le_full_ind : forall (p : forall x y, le' x y -> Prop),
    (forall y, p 0 y (le0 y)) ->
    (forall x y (d: le' x y), p x y d -> p (S x) (S y) (le__S x y d)) ->
    forall x y (d: le' x y), p x y d
  := fun p f0 f1 => fix F _ _ d {struct d} :=
       match d with
       | le0 y => f0 y
       | le__S x y d' => f1 x y d' (F x y d')
       end.

Lemma le'_sound : forall n m, n <= m -> le' n m.
Proof.
  induction n as [|n'].
  - intros m _. constructor.
  - intros m H.
    destruct m as [|m'].
    + inversion H.
    + constructor. apply IHn'. apply Peano.le_S_n, H.
Qed.

Lemma le'_complete : forall n m, le' n m -> n <= m.
Proof.
  induction 1.
  - apply Peano.le_0_n.
  - apply Peano.le_n_S, IHle'.
Qed.


Definition cast {X} {x y: X} {p: X -> Type}
  : x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

Fact eq_le0 : forall y (d: le' 0 y), le0 y = d.
Proof.
  enough (forall x y (d: le' x y), match x as x0 return (x = x0 -> Prop) with
                                  0 => fun H => le0 y = @cast _ _ _ (fun x => le' x y) H d
                                | _ => fun _ => True
                                end eq_refl).
  - intros y d. specialize (H 0 y d). simpl in H. assumption.
  - intros x y d. destruct d.
    simpl. reflexivity. exact I.
Qed.

Fact eq_le__S : forall x y (d: le' (S x) (S y)), exists d', le__S x y d' = d.
  enough (forall x y (d: le' x y), match x as x0, y as y0 return (x = x0 -> y = y0 -> Prop) with
                                  S x', S y' => fun H H' => exists d', le__S x' y' d' = @cast _ _ _ (fun x => le' x (S y')) H (@cast _ _ _ (fun y => le' x y) H' d)
                                | _, _ => fun _ _ => True
                                end eq_refl eq_refl).
  - intros x y d. specialize (H (S x) (S y) d). simpl in H. assumption.
  - intros x y d. destruct d. exact I. exists d. simpl. reflexivity.
Qed.

Lemma le'_uniq : forall x y (d d': le' x y), d = d'.
Proof.
  refine (fun x y d => le_full_ind (fun x y d => forall d', d = d') _ _ x y d).
  - apply eq_le0.
  - intros x0 y0 d0 IH d'. destruct (eq_le__S x0 y0 d') as [d'' <-].
    f_equal. apply IH.
Qed.

Inductive lessu : nat -> nat -> Prop :=
  l1 : forall y, lessu 0 (S y)
| l2 : forall x y, lessu x y -> lessu (S x) (S y).

Definition lessu_full_ind : forall (p : forall x y, lessu x y -> Prop),
    (forall y, p 0 (S y) (l1 y)) ->
    (forall x y (d: lessu x y), p x y d -> p (S x) (S y) (l2 x y d)) ->
    forall x y (d: lessu x y), p x y d
  := fun p f0 f1 => fix F _ _ d {struct d} :=
       match d with
       | l1 y => f0 y
       | l2 x y d' => f1 x y d' (F x y d')
       end.

Fact lem__less1 : forall y (d: lessu 0 (S y)), l1 y = d.
Proof.
  enough (forall x y (d: lessu x y), match x as x0, y as y0 return (x = x0 -> y = y0 -> Prop) with
                                  0, S y' => fun H H' => l1 y' = @cast _ _ _ (fun x => lessu x (S y')) H (@cast _ _ _ (fun y => lessu x y) H' d)
                                | _, _ => fun _ _ => True
                                end eq_refl eq_refl).
  - intros y d. specialize (H 0 (S y) d). simpl in H. assumption.
  - intros x y d. destruct d.
    simpl. reflexivity. exact I.
Qed.

Fact lem__less2 : forall x y (d: lessu (S x) (S y)), exists d', l2 x y d' = d.
  enough (forall x y (d: lessu x y), match x as x0, y as y0 return (x = x0 -> y = y0 -> Prop) with
                                  S x', S y' => fun H H' => exists d', l2 x' y' d' = @cast _ _ _ (fun x => lessu x (S y')) H (@cast _ _ _ (fun y => lessu x y) H' d)
                                | _, _ => fun _ _ => True
                                end eq_refl eq_refl).
  - intros x y d. specialize (H (S x) (S y) d). simpl in H. assumption.
  - intros x y d. destruct d. exact I. exists d. simpl. reflexivity.
Qed.

Lemma lessu_uniq : forall x y (d d': lessu x y), d = d'.
Proof.
  refine (fun x y d => lessu_full_ind (fun x y d => forall d', d = d') _ _ x y d).
  - apply lem__less1.
  - intros x0 y0 d0 IH d'. destruct (lem__less2 x0 y0 d') as [d'' <-].
    f_equal. apply IH.
Qed.

Lemma UIP_nat : forall (n: nat) (e: n = n), e = eq_refl.
Proof.
  apply Eqdep_dec.UIP_refl_nat.
Qed.

Require Import Lia.

Lemma lessu_sound : forall n m, n < m -> lessu n m.
Proof.
  intros n m.
  induction m as [|m'] in n |- *.
  - lia.
  - intros H.
    destruct n as [|n'].
    + constructor.
    + constructor. apply IHm'. lia.
Qed.

Lemma lessu_complete : forall n m, lessu n m -> n < m.
Proof.
  induction 1.
  - lia.
  - lia.
Qed.
                                  
Lemma lessu_irrefl : forall n, ~ lessu n n.
  intros n H%lessu_complete. lia.
Qed.

Inductive InN (n: nat) : list nat -> Type :=
  | InNCarry : forall l m (H: InN n l), (lessu m n) -> InN n (m :: l)
  | InNCons : forall l, InN n (n :: l).

Lemma InN_Cons : forall n l (d : InN n (n::l)), InNCons n l = d.
  enough (H: forall n l (d: InN n l), match l as l0 return (l = l0 -> Type) with
                              | [] => fun _ => True
                              | m :: l' => fun H => forall (H': m = n), InNCons n l' = @cast _ _ _ (fun l => InN n l) (@cast _ _ _ (fun m => l = m :: l') H' H) d
                              end eq_refl).
  - intros *.
    specialize (H n (n::l) d). simpl in H.
    specialize (H eq_refl). simpl in H. assumption.
  - intros *. destruct d.
    + intros ->.
      destruct (lessu_irrefl _ l0).
    + intros H'.
      rewrite (UIP_nat _ H').
      simpl. reflexivity.
Qed.

Print Assumptions InN_Cons.

  (* enough (forall x y (d: lessu x y), match x as x0, y as y0 return (x = x0 -> y = y0 -> Prop) with *)
  (*                                 S x', S y' => fun H H' => exists d', l2 x' y' d' = @cast _ _ _ (fun x => lessu x (S y')) H (@cast _ _ _ (fun y => lessu x y) H' d) *)
  (*                               | _, _ => fun _ _ => True *)
  (*                               end eq_refl eq_refl). *)

Lemma InN_Carry : forall n l m (e: lessu m n) (d: InN n (m::l)), exists d', InNCarry n l m d' e = d.
  enough (H: forall n l m (e: lessu m n) (d: InN n l),
           match l as l0 return (l = l0 -> Type) with
           | [] => fun _ => True
           | m0 :: l' => fun H => forall (H': m = m0), exists d', InNCarry n l' m0 d' (@cast _ _ _ (fun m' => lessu m' n) H' e) = @cast _ _ _ (fun l => InN n l) H d
           end eq_refl).
  - intros *.
    specialize (H n (m::l) m e d).
    simpl in H. specialize (H eq_refl) as [d' <-].
    exists d'. reflexivity.
  - intros n l m e d.
    destruct d.
    + intros H'. exists d.
      destruct H'.
      simpl.
      rewrite (lessu_uniq _ _ e l0).
      reflexivity.
    + intros ->.
      exfalso.
      apply (lessu_irrefl _ e).
Qed.

Lemma InN_uniq : forall (x:nat) (l: list nat) (p q: InN x l),
  p = q.
Proof.
  refine (fun x l p => InN_rect x (fun l p => forall q, p = q) _ _ l p).
  - intros l0 m0 d0 IH Hle q.
    destruct (InN_Carry x l0 m0 Hle q) as [d'' <-].
    f_equal. apply IH.
  - apply InN_Cons.
Qed.
    
Print Assumptions InN_uniq.

(* Lemma InNle : forall n m l, InN n (m :: l) -> m <= n. *)
(* Proof. *)
(*   intros *. *)
(*   refine (InN_rect n (fun l0 d => match l0 with *)
(*                                | [] => False *)
(*                                | m' :: _ => m' <= n *)
(*                                end) _ _ (m :: l)). *)
(*   + intros _ ? _ _ H. *)
(*     apply Nat.lt_le_incl, H. *)
(*   + intros _. constructor. *)
(* Qed. *)

(* Lemma InNlt : forall n m l, m < n -> InN n (m :: l) -> InN n l. *)
(* Proof. *)
(*   intros * Hlt d. *)
(*   refine (InN_rect n (fun l0 d => match l0 with *)
(*                                | [] => False *)
(*                                | m' :: l0 => m' < n -> InN n l0 *)
(*                                end) _ _ (m :: l) d Hlt). *)
(*   + intros ? ? H _ _ _. assumption. *)
(*   + intros ? H. *)
(*     exfalso. apply (Nat.lt_irrefl _ H). *)
(* Qed. *)

(* Lemma lt_eq_lt_dec : forall n m, { n < m } + { n = m } + { m < n }. *)
(* Proof. *)
(*   intros n m. *)
(*   destruct (le_lt_dec n m) as [H|H]. *)
(*   - left. *)
(*     destruct (le_lt_eq_dec n m H) as [H'|H']. *)
(*     + now left. *)
(*     + now right. *)
(*   - now right. *)
(* Qed. *)

(* Lemma decInN : forall (x:nat) (l:list nat), *)
(*   InN x l + (InN x l -> False). *)
(* Proof. *)
(*   induction l as [| a l' [IH|IH]]. *)
(*   - now right. *)
(*   - destruct (lt_eq_lt_dec a x) as [[H| ->]|H]. *)
(*     + left. apply InNCarry; assumption. *)
(*     + left. apply InNCons. *)
(*     + right. intros H'. *)
(*       specialize (InNle _ _ _ H'). *)
(*       apply lt_not_le, H. *)
(*   - destruct (lt_eq_lt_dec a x) as [[H| ->]|H]. *)
(*     + right. *)
(*       intros H'. *)
(*       apply IH. *)
(*       apply (InNlt _ a _ H H'). *)
(*     + left. apply InNCons. *)
(*     + right. *)
(*       intros H'. *)
(*       specialize (InNle _ _ _ H'). *)
(*       apply lt_not_le, H. *)
(* Qed. *)


Module renSubst.


Notation upT vs := (0 :: List.map S vs).

Inductive tm (vs : list nat) : Type :=
  | var_tm : forall (v:nat) (H: InN v vs), tm vs
  | app : tm vs -> tm vs -> tm vs
  | lam : tm (upT vs) -> tm vs.
Arguments var_tm {vs} {v}.
Arguments app {vs}.
Arguments lam {vs}.

Lemma congr_app {vs : list nat} {s0 : tm vs} {s1 : tm vs} {t0 : tm vs}
  {t1 : tm vs} (H0 : s0 = t0) (H1 : s1 = t1) :
  app s0 s1 = app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
         (ap (fun x => app t0 x) H1)).
Qed.

Lemma congr_lam {vs : list nat} {v: nat} {s0 : tm (upT vs)} {t0 : tm (upT vs)}
  (H0 : s0 = t0) : lam s0 = lam t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam x) H0)).
Qed.

Inductive Lifted : nat -> Type := lift : forall x, Lifted x.
Fixpoint finList (vs: list nat) : Type :=
  match vs with
  | [] => False
  | v :: vs => Lifted v + (finList vs)
  end.

Check (inl (lift 3) : finList [3; 4]).

(* problem with this approach is that the var constructor does not work directly as a substitution *)
Inductive finList2 : list nat -> Type :=
    liftFinList : forall (v:nat) (vs: list nat) (H: InN v vs), finList2 vs.
Definition var_tm_finList2 : forall (vs: list nat), finList2 vs -> tm vs :=
  fun vs l =>
  match l with
  | liftFinList v vs H => @var_tm vs v H
  end.

Compute (In 3 [3;4]).
Check (liftFinList 3 [3; 4] (i eq_refl) : finList2 [3; 4]).

Open Scope type.
Notation "X <=> Y" := ((X -> Y) * (Y -> X))
                                         (at level 70, no associativity).

(* Lemma in_map_if_nat :  *)
(*   forall (f : nat -> nat) (l : list nat) (y : nat), *)
(*   InN y (List.map f l) -> { x : nat & (f x = y) * InN x l }. *)
(* Proof. *)
(*   induction l as [|a l']; intros *. *)
(*   - split. *)
(*     intros []. *)
(*     intros (? & _ & []). *)
(*   - split. *)
(*     + intros [H|H]. *)
(*       exists a. split. assumption. now left. *)
(*       destruct (IHl' y) as [IH _]. *)
(*       specialize (IH H) as (x & Hx0 & Hx1). *)
(*       exists x. split. assumption. now right. *)
(*     + intros (x & Hx0 & [-> | Hx1]). *)
(*       now left. *)
(*       right. apply IHl'. exists x. *)
(*       now split. *)
(* Defined. *)
                                         
Lemma in_map_if_nat : 
  forall (f : nat -> nat) (l : list nat) (y : nat),
  InN y (List.map f l) -> { x : nat & (f x = y) * InN x l }.
Proof.
  induction l as [|a l']; intros *.
  - intros [].
  - intros [H|H].
    exists a. split. assumption. now left.
    specialize (IHl' y H) as (x & Hx0 & Hx1).
    exists x. split. assumption. now right.
Defined.

Lemma in_map_nat :
  forall (f : nat -> nat) (l : list nat) (x : nat),
  InN x l -> InN (f x) (List.map f l).
Proof.
  induction l as [|a l']; intros *.
  - intros [].
  - intros [->|H].
    now left.
    right. apply IHl', H.
Defined.
      
Definition scons {X : Type} {vs : list nat} (x : X) (f : finList2 vs -> X) (m : finList2 (upT vs)) : X.
Proof.
  remember (upT vs) as vs'.
  destruct m. rewrite Heqvs' in *.
  cbn in H. destruct H as [H|H].
  - (* m is 0 so we return the given x *)
    exact x.
  - assert ({ v' & (S v' = v) * InN v' vs}) as (v' & Hv0 & Hv1)
        by (apply (in_map_if_nat S vs v), H). 
    apply (f (liftFinList v' vs Hv1)).
Defined.

Compute (@scons nat [2] 1 (fun _ => 6)
        (liftFinList 3 (upT [2]) (inr (inl eq_refl)))).
Compute (@scons nat [2]  1 (fun _ => 6)
        (liftFinList 0 (upT [2]) (inl eq_refl))).
Definition var_zero {vs: list nat} : finList2 (upT vs) := liftFinList 0 (upT vs) (inl eq_refl).

Definition shift {vs: list nat} : finList2 vs -> finList2 (upT vs).
Proof.
  intros H. destruct H.
  apply (in_map_nat S _ _) in H.
  exact (liftFinList (S v) (upT vs) (inr H)).
Defined.

Definition up_ren_traced {vs0 vs1 : list nat} (xi: finList2 vs0 -> finList2 vs1) : finList2 (upT vs0) -> finList2 (upT vs1) :=
  scons var_zero (funcomp shift xi).

Fixpoint ren_tm {vs0 vs1: list nat} (xi_tm : finList2 vs0 -> finList2 vs1) (s: tm vs0) {struct s} : tm vs1.
Proof.
  destruct s.
  - specialize (xi_tm (liftFinList v vs0 H)).
    destruct xi_tm as [v' vs1 H'].
    exact (var_tm H').
  - apply (app (ren_tm vs0 vs1 xi_tm s1) (ren_tm vs0 vs1 xi_tm s2)).
  - apply lam. eapply ren_tm. 2: exact s. apply up_ren_traced. exact xi_tm.
Defined.

Print Assumptions ren_tm.

Lemma up_tm_tm {m : list nat} {n_tm : list nat} (sigma : finList2 m -> tm n_tm) :
  finList2 (upT m) -> tm (upT n_tm).
Proof.
exact (scons (@var_tm (upT n_tm) 0 (inl eq_refl)) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm {m_tm : list nat} {n_tm : list nat} (sigma_tm : finList2 m_tm -> tm n_tm)
(s : tm m_tm) {struct s} : tm n_tm.
  destruct s as [v H | s0 s1 | s0].
  - apply sigma_tm. econstructor. exact H.
  - apply app; eapply subst_tm; eassumption.
  - apply lam. eapply subst_tm. 2: exact s0. apply up_tm_tm, sigma_tm.
Defined.

Print Assumptions subst_tm.

(* lambda x y . x w (lambda z . w z y) *)
(* lambda . lambda . 1 2 (lambda . 3 0 1) *)
Definition testtm : tm [0].
Proof.
  refine (lam (lam (app (app (* x w *) _ _)
                        (lam (app (app (* w z *) _ _) (* y *) _))))).
  - (* x *)
    cbv.
    (* apparently here Coq's unification is too weak *)
    exact (@var_tm [0;1;2] 1 (inr (inl (eq_refl 1)))).
  - (* outer w *)
    exact (@var_tm [0;1;2] 2 (inr (inr (inl (eq_refl 2))))).
  - (* inner w *)
    exact (@var_tm [0;1;2;3] 3 (inr (inr (inr (inl (eq_refl 3)))))).
  - (* z *)
    exact (@var_tm [0;1;2;3] 0 (inl (eq_refl 0))).
  - (* y *)
    exact (@var_tm [0;1;2;3] 2 (inr (inr (inl (eq_refl 2))))).
Defined.

Print testtm.
Compute (ren_tm shift testtm).
(* Compute (subst_tm var_tm). *)

Arguments liftFinList v {vs} H.

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

(* Lemma in_map_if_nat2 : forall (f: nat -> nat) (l: list nat) (x: nat), *)
(*   in_map_nat *)
Lemma upId_tm {vs : list nat} (sigma : finList2 vs -> tm vs)
  (Eq : forall v (H: InN v vs), sigma (liftFinList v H) = var_tm H) :
  forall v H, up_tm_tm sigma (liftFinList v H) = @var_tm (upT vs) v H.
Proof.
  unfold up_tm_tm.
  intros v H.
  (* H: v is either 0 or some number in vs + 1 *)
  destruct H as [H|H].
  - (* v = 0 *)
    cbv.
    destruct H.
    reflexivity.
  - (* v is some number in vs + 1 *)
    simpl.
    destruct (in_map_if_nat S vs v H) as (v' & Hv'0 & Hv'1) eqn:E .
    (* assert ({ v' & (S v' = v) * InN v' vs}) as (v'' & Hv''0 & Hv''1). *)
    (* apply in_map_if_nat; assumption. *)
    subst v.
    specialize (Eq v' Hv'1).
    unfold funcomp.
    rewrite Eq.
    cbn [ren_tm].
    cbn [shift].
    assert (E0: in_map_nat S vs v' Hv'1 = H) by admit.
    rewrite E0.
    reflexivity.
    rewrite E.
    pose proof (H2) as H3.
    destruct H2 as .
    revert H.
    rewrite <- Hv'0.
    intros H.
    cbn [scons].
    cbn [eq_rect].
    

Fixpoint idSubst_tm {m_tm : nat} (sigma_tm : fin m_tm -> tm m_tm)
(Eq_tm : forall x, sigma_tm x = var_tm m_tm x) (s : tm m_tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  end.


      
(* Lemma upRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n) : *)
(*   fin (S m) -> fin (S n). *)
(* Proof. *)
(* exact (up_ren xi). *)
(* Defined. *)

(* Fixpoint ren_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) *)
(* (s : tm m_tm) {struct s} : tm n_tm := *)
(*   match s with *)
(*   | var_tm _ s0 => var_tm n_tm (xi_tm s0) *)
(*   | app _ s0 s1 => app n_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1) *)
(*   | lam _ s0 => lam n_tm (ren_tm (upRen_tm_tm xi_tm) s0) *)
(*   end. *)

Lemma up_tm_tm {m : nat} {n_tm : nat} (sigma : fin m -> tm n_tm) :
  fin (S m) -> tm (S n_tm).
Proof.
exact (scons (var_tm (S n_tm) var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Lemma up_list_tm_tm (p : nat) {m : nat} {n_tm : nat}
  (sigma : fin m -> tm n_tm) : fin (plus p m) -> tm (plus p n_tm).
Proof.
exact (scons_p p (funcomp (var_tm (plus p n_tm)) (zero_p p))
         (funcomp (ren_tm (shift_p p)) sigma)).
Defined.

Fixpoint subst_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
(s : tm m_tm) {struct s} : tm n_tm :=
  match s with
  | var_tm _ s0 => sigma_tm s0
  | app _ s0 s1 => app n_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | lam _ s0 => lam n_tm (subst_tm (up_tm_tm sigma_tm) s0)
  end.

Lemma upId_tm_tm {m_tm : nat} (sigma : fin m_tm -> tm m_tm)
  (Eq : forall x, sigma x = var_tm m_tm x) :
  forall x, up_tm_tm sigma x = var_tm (S m_tm) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_tm_tm {p : nat} {m_tm : nat} (sigma : fin m_tm -> tm m_tm)
  (Eq : forall x, sigma x = var_tm m_tm x) :
  forall x, up_list_tm_tm p sigma x = var_tm (plus p m_tm) x.
Proof.
exact (fun n =>
       scons_p_eta (var_tm (plus p m_tm))
         (fun n => ap (ren_tm (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_tm {m_tm : nat} (sigma_tm : fin m_tm -> tm m_tm)
(Eq_tm : forall x, sigma_tm x = var_tm m_tm x) (s : tm m_tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  end.

Lemma upExtRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_tm_tm {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_tm p xi x = upRen_list_tm_tm p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
(zeta_tm : fin m_tm -> fin n_tm) (Eq_tm : forall x, xi_tm x = zeta_tm x)
(s : tm m_tm) {struct s} : ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm _ s0 => ap (var_tm n_tm) (Eq_tm s0)
  | app _ s0 s1 =>
      congr_app (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  end.

Lemma upExt_tm_tm {m : nat} {n_tm : nat} (sigma : fin m -> tm n_tm)
  (tau : fin m -> tm n_tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_tm_tm {p : nat} {m : nat} {n_tm : nat}
  (sigma : fin m -> tm n_tm) (tau : fin m -> tm n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_tm p sigma x = up_list_tm_tm p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_tm (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
(tau_tm : fin m_tm -> tm n_tm) (Eq_tm : forall x, sigma_tm x = tau_tm x)
(s : tm m_tm) {struct s} : subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  end.

Lemma up_ren_ren_tm_tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_tm_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_tm p zeta) (upRen_list_tm_tm p xi) x =
  upRen_list_tm_tm p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
(rho_tm : fin m_tm -> fin l_tm)
(Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x) (s : tm m_tm) {struct
 s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm _ s0 => ap (var_tm l_tm) (Eq_tm s0)
  | app _ s0 s1 =>
      congr_app (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  end.

Lemma up_ren_subst_tm_tm {k : nat} {l : nat} {m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_tm) (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_tm_tm {p : nat} {k : nat} {l : nat} {m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_tm) (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_tm_tm p tau) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_tm (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm m_tm) {struct
 s} : subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_ren_tm_tm {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_tm_tm {p : nat} {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_list_tm_tm p zeta_tm)) (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_tm (plus p m_tm)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_tm (shift_p p) (upRen_list_tm_tm p zeta_tm)
                  (funcomp (shift_p p) zeta_tm)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_tm zeta_tm (shift_p p)
                        (funcomp (shift_p p) zeta_tm) (fun x => eq_refl)
                        (sigma n))) (ap (ren_tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x)
(s : tm m_tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_subst_tm_tm {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (tau_tm : fin l_tm -> tm m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma fin_n))) (ap (ren_tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_tm_tm {p : nat} {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (tau_tm : fin l_tm -> tm m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_tm_tm p tau_tm)) (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_tm (plus p l_tm)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_tm (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_tm (shift_p p) (up_list_tm_tm p tau_tm)
                  (funcomp (up_list_tm_tm p tau_tm) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_tm tau_tm (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm m_tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma rinstInst_up_tm_tm {m : nat} {n_tm : nat} (xi : fin m -> fin n_tm)
  (sigma : fin m -> tm n_tm)
  (Eq : forall x, funcomp (var_tm n_tm) xi x = sigma x) :
  forall x, funcomp (var_tm (S n_tm)) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_tm_tm {p : nat} {m : nat} {n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_tm)
  (Eq : forall x, funcomp (var_tm n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (plus p n_tm)) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_tm (plus p n_tm)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_tm (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_tm {m_tm : nat} {n_tm : nat}
(xi_tm : fin m_tm -> fin n_tm) (sigma_tm : fin m_tm -> tm n_tm)
(Eq_tm : forall x, funcomp (var_tm n_tm) xi_tm x = sigma_tm x) (s : tm m_tm)
{struct s} : ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  end.

Lemma renRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) (s : tm m_tm)
  : subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
  (s : tm m_tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
  (s : tm m_tm) : ren_tm xi_tm s = subst_tm (funcomp (var_tm n_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise {m_tm : nat} {n_tm : nat}
  (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq (ren_tm xi_tm)
    (subst_tm (funcomp (var_tm n_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm {m_tm : nat} (s : tm m_tm) : subst_tm (var_tm m_tm) s = s.
Proof.
exact (idSubst_tm (var_tm m_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise {m_tm : nat} :
  pointwise_relation _ eq (subst_tm (var_tm m_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm m_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm {m_tm : nat} (s : tm m_tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise {m_tm : nat} :
  pointwise_relation _ eq (@ren_tm m_tm m_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
  (x : fin m_tm) : subst_tm sigma_tm (var_tm m_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise {m_tm : nat} {n_tm : nat}
  (sigma_tm : fin m_tm -> tm n_tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm m_tm))
    sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
  (x : fin m_tm) : ren_tm xi_tm (var_tm m_tm x) = var_tm n_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise {m_tm : nat} {n_tm : nat}
  (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm m_tm))
    (funcomp (var_tm n_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

Instance Subst_tm  {m_tm n_tm : nat}: (Subst1 _ _ _) := (@subst_tm m_tm n_tm).

Instance Up_tm_tm  {m n_tm : nat}: (Up_tm _ _) := (@up_tm_tm m n_tm).

Instance Ren_tm  {m_tm n_tm : nat}: (Ren1 _ _ _) := (@ren_tm m_tm n_tm).

Instance VarInstance_tm  {n_tm : nat}: (Var _ _) := (@var_tm n_tm).

Notation "[ sigma_tm ]" := (subst_tm sigma_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__tm" := up_tm (only printing) : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing) : subst_scope.

Notation "⟨ xi_tm ⟩" := (ren_tm xi_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing) : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
  ( at level 5, format "x __tm", only printing) : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm") :
  subst_scope.

Instance subst_tm_morphism  {m_tm : nat} {n_tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm m_tm n_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

Instance ren_tm_morphism  {m_tm : nat} {n_tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_tm m_tm n_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress
                    unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm,
                     upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm.

End renSubst.

Module fext.

Import
renSubst.

Lemma rinstInst_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) :
  ren_tm xi_tm = subst_tm (funcomp (var_tm n_tm) xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_tm xi_tm _ (fun n => eq_refl) x)).
Qed.

Lemma instId_tm {m_tm : nat} : subst_tm (var_tm m_tm) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_tm (var_tm m_tm) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_tm {m_tm : nat} : @ren_tm m_tm m_tm id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _)) instId_tm).
Qed.

Lemma varL_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm) :
  funcomp (subst_tm sigma_tm) (var_tm m_tm) = sigma_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) :
  funcomp (ren_tm xi_tm) (var_tm m_tm) = funcomp (var_tm n_tm) xi_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (ren_tm xi_tm) = ren_tm (funcomp zeta_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_tm xi_tm zeta_tm n)).
Qed.

Lemma substRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_tm sigma_tm zeta_tm n)).
Qed.

Lemma renSubst'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  funcomp (subst_tm tau_tm) (ren_tm xi_tm) = subst_tm (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_tm xi_tm tau_tm n)).
Qed.

Lemma substSubst'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  funcomp (subst_tm tau_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_tm sigma_tm tau_tm n)).
Qed.

Ltac asimpl_fext' := repeat (first
                      [ progress setoid_rewrite substSubst_tm_pointwise
                      | progress setoid_rewrite substSubst_tm
                      | progress setoid_rewrite renSubst_tm_pointwise
                      | progress setoid_rewrite renSubst_tm
                      | progress setoid_rewrite substRen_tm_pointwise
                      | progress setoid_rewrite substRen_tm
                      | progress setoid_rewrite renRen'_tm_pointwise
                      | progress setoid_rewrite renRen_tm
                      | progress setoid_rewrite substSubst'_tm
                      | progress setoid_rewrite renSubst'_tm
                      | progress setoid_rewrite substRen'_tm
                      | progress setoid_rewrite renRen'_tm
                      | progress setoid_rewrite varLRen_tm
                      | progress setoid_rewrite varL_tm
                      | progress setoid_rewrite rinstId_tm
                      | progress setoid_rewrite instId_tm
                      | progress
                         unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm,
                          upRen_tm_tm, up_ren
                      | progress cbn[subst_tm ren_tm]
                      | fsimpl_fext ]).

Ltac asimpl_fext := check_no_evars; repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                       Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 
                       in *; asimpl_fext'; repeat try unfold_funcomp.

Tactic Notation "asimpl_fext" "in" hyp(J) := revert J; asimpl_fext; intros J.

Ltac substify_fext := auto_unfold; try repeat erewrite ?rinstInst_tm.

Ltac renamify_fext := auto_unfold; try repeat erewrite <- ?rinstInst_tm.

End fext.

Module interface.

Export renSubst.

Export
fext.

Arguments var_tm {n_tm}.

Arguments lam {n_tm}.

Arguments app {n_tm}.

Hint Opaque subst_tm: rewrite.

Hint Opaque ren_tm: rewrite.

End interface.

Export interface.

