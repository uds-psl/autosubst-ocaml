Require Import List Arith.
Import ListNotations.
Require Import core.


Notation eqdec := eq_nat_dec.

Require Import Lia.

Module renSubst.

Notation upT vs := (0 :: vs).

(** Definition of finite type based on lists.
    It's very similar to the normal fin type of wellscoped syntax. 
    Maybe even too much. I'm havin doubts that this is an appropriate
    formalization of traced syntax. *)
Inductive wrapNat (n:nat) : Type := wrapC : wrapNat n.

Fixpoint fin (l: list nat) : Type :=
  match l with
  | [] => False
  | n :: l => (wrapNat n) + (fin l)
  end.

(* compute the natural number that a value of type fin l denotes. *)
Fixpoint denote {l: list nat} (x: fin l) {struct l} : nat.
Proof.
  destruct l as [|n l'].
  - destruct x.
  - refine (match x with
            | inl (wrapC _) => n
            | inr x' => S (denote l' x')
            end).
Defined.

(* compute a "flattened" list, i.e. with the simplification which only tracks differences between the elements. *)
Fixpoint flatten (l: list nat) (acc: nat) : list nat :=
  match l with
  | [] => []
  | x :: l =>
    let x' := x - acc in
    x' :: flatten l (S x)
  end.

(* some values of the finite type *)
Definition fl (l: list nat) : list nat := flatten l 0.
Definition f0 : fin [0] := inl (wrapC 0).
Definition f1 : fin (fl [0;2;3]) := inl (wrapC 0). (* denotes 0 *)
Definition f2 : fin (fl [0;2;3]) := inr (inl (wrapC 1)). (* denotes 2 *)
Definition f3 : fin (fl [0;2;3]) := inr (inr (inl (wrapC 0))). (* denotes 3 *)

Compute (denote f0).
Compute (denote f1).
Compute (denote f2).
Compute (denote f3).

(* language definition *)
Inductive tm (vs : list nat) : Type :=
  | var_tm : fin vs -> tm vs
  | app : tm vs -> tm vs -> tm vs
  | lam : tm (upT vs) -> tm vs.

(* congruence lemmas are unchanged except list scope variable *)
Lemma congr_app {vs : list nat} {s0 : tm vs} {s1 : tm vs} {t0 : tm vs}
  {t1 : tm vs} (H0 : s0 = t0) (H1 : s1 = t1) :
  app _ s0 s1 = app _ t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app _ x s1) H0))
         (ap (fun x => app _ t0 x) H1)).
Qed.

Lemma congr_lam {vs : list nat} {s0 : tm (upT vs)} {t0 : tm (upT vs)}
  (H0 : s0 = t0) : lam _ s0 = lam _ t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam _ x) H0)).
Qed.


Open Scope type.

(* scons is the biggest problem when we map S over the list.
 * because we have to take the m, which is mapped, and pass it to f, which does not want the map.
 * With my simplification it works fine. *)
Definition scons {X : Type} {vs : list nat} (x : X) (f : fin vs -> X) (m : fin (upT vs)) : X.
Proof.
  destruct m as [n|m'].
  - exact x.
  - exact (f m').
Defined.

Compute (@scons nat (fl [1;2]) 1 (fun _ => 6) f1).
Compute (@scons nat (fl [1;2]) 1 (fun _ => 6) f2).
Compute (@scons nat (fl [1;2]) 1 (fun _ => 6) f3).

(* we can define "lossy" primitives.  *)
Definition var_zero {vs: list nat} : fin (upT vs) := inl (wrapC 0).
Definition shift {vs: list nat} : fin vs -> fin (upT vs) := inr.

(* with traced syntax we can know that var_zero is in fin [0] and shift does not contain a 0
 * but these non-lossy versions are not easy to use. *)
Definition var_zero' : fin [0] := inl (wrapC 0).
Definition shift' {vs: list nat} : fin vs -> fin (List.map S vs).
Proof.
  intros m. induction vs as [|v vs].
  - destruct m.
  - destruct m as [n|m'].
    + left. constructor.
    + right. exact (IHvs m').
Defined.  
 
Definition up_ren {m n} (xi : fin m -> fin n) : fin (upT m) -> fin (upT n) :=
  scons var_zero (funcomp shift xi).

Definition upRen_tm_tm {vs0 vs1 : list nat} (xi: fin vs0 -> fin vs1) : fin (upT vs0) -> fin (upT vs1) := up_ren xi.

Fixpoint ren_tm {vs0 vs1: list nat} (xi_tm : fin vs0 -> fin vs1) (s: tm vs0) {struct s} : tm vs1.
Proof.
  refine (match s with
          | var_tm _ x => _
          | app _ s0 s1 => _
          | lam _ s0 => _
          end).
  - exact (var_tm _ (xi_tm x)).
  - exact (app _ (ren_tm _ _ xi_tm s0) (ren_tm _ _ xi_tm s1)).
  - exact (lam _ (ren_tm _ _ (upRen_tm_tm xi_tm) s0)).
Defined.

Print Assumptions ren_tm.

Lemma up_tm_tm {vs0 : list nat} {vs1 : list nat} (sigma : fin vs0 -> tm vs1) :
  fin (upT vs0) -> tm (upT vs1).
Proof.
  exact (scons (@var_tm (upT vs1) var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm {vs0 : list nat} {vs1 : list nat} (sigma_tm : fin vs0 -> tm vs1) (s : tm vs0) {struct s}
  : tm vs1.
Proof.
  refine (match s with
          | var_tm _ x => _
          | app _ s0 s1 => _
          | lam _ s0 => _
          end).
  - exact (sigma_tm x).
  - exact (app _ (subst_tm _ _ sigma_tm s0) (subst_tm _ _ sigma_tm s1)).
  - exact (lam _ (subst_tm _ _ (up_tm_tm sigma_tm) s0)).
Defined.

Print Assumptions subst_tm.

(* lambda x y . x w (lambda z . w z y) *)
(* lambda . lambda . 1 2 (lambda . 3 0 1) *)
Definition testtm : tm [1].
Proof.
  refine (lam _ (lam _ (app _ (app _ (* x w *) _ _)
                        (lam _ (app _ (app _ (* w z *) _ _) (* y *) _))))).
  - (* x *)
    cbv.
    (* apparently here Coq's unification is too weak *)
    refine (@var_tm (fl [0;1;3]) var_zero).
  - (* outer w *)
    refine (@var_tm (fl [0;1;3]) (shift var_zero)).
  - (* inner w *)
    refine (@var_tm (fl [0;1;2;4]) (shift (shift var_zero))).
  - (* z *)
    exact (@var_tm (fl [0;1;2;4]) var_zero).
  - (* y *)
    refine (@var_tm (fl [0;1;2;4]) (shift (shift var_zero))).
Defined.

Print Assumptions testtm.
Print testtm.

(* and here we see that the formalization is bad. we should have enough information that a shift increases the only free variable.
   so the type should be tm [2], but we are essentially throwing that info away. *)
Fail Check (ren_tm shift testtm : tm [2]).
Check (ren_tm shift testtm : tm [0;1]).
(* we can compute with these definitions *)
Compute (ren_tm shift testtm).
Compute (subst_tm (var_tm _) testtm).

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition cast {X} {x y: X} {p: X -> Type}
  : x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

Lemma upId_tm_tm {vs : list nat} (sigma : fin vs -> tm vs)
  (Eq : forall x, sigma x = var_tm _ x) :
  forall x, up_tm_tm sigma x = @var_tm (upT vs) x.
Proof.
  refine (fun x =>
          match x with
          | inr x' => ap (ren_tm shift) (Eq x')
          | inl (wrapC _) => eq_refl
          end).
Qed.

Fixpoint idSubst_tm {vs : list nat} (sigma_tm : fin vs -> tm vs)
(Eq_tm : forall x, sigma_tm x = var_tm _ x) (s : tm vs) {struct s} :
subst_tm sigma_tm s = s :=
  match s as s0 return subst_tm sigma_tm s0 = s0
  with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 => congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | lam _ s0 => congr_lam (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm sigma_tm Eq_tm) s0)
  end.


Lemma upExtRen_tm_tm {m : list nat} {n : list nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n =>
       match n with
       | inr x' => ap shift (Eq x')
       | inl n => match n with wrapC _ => eq_refl end
       end).
Qed.


Fixpoint extRen_tm {m_tm : list nat} {n_tm : list nat} (xi_tm : fin m_tm -> fin n_tm)
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

  
Lemma upExt_tm_tm {m : list nat} {n_tm : list nat} (sigma : fin m -> tm n_tm)
  (tau : fin m -> tm n_tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | inr fin_n => ap (ren_tm shift) (Eq fin_n)
       | inl n => match n with wrapC _ => eq_refl end
       end).
Qed.

Fixpoint ext_tm {m_tm : list nat} {n_tm : list nat} (sigma_tm : fin m_tm -> tm n_tm)
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

Lemma up_ren_ren (k l m : list nat) (xi: fin k -> fin l) (zeta : fin l -> fin m) (rho: fin k -> fin m) (E: forall x, (funcomp zeta xi) x = rho x) :
  forall x, up_ren zeta (up_ren xi x) = up_ren rho x.
Proof.
  intros [n|x'].
  - reflexivity.
  - cbn. unfold funcomp. now rewrite <- E.
Qed.

Arguments up_ren_ren {k l m} xi zeta rho E.

Lemma up_ren_ren_tm_tm {k : list nat} {l : list nat} {m : list nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
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

Lemma up_ren_subst_tm_tm {k : list nat} {l : list nat} {m_tm : list nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_tm) (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | inr fin_n => ap (ren_tm shift) (Eq fin_n)
       | inl n => match n with wrapC _ => eq_refl end
       end).
Qed.

Fixpoint compRenSubst_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
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

Lemma up_subst_ren_tm_tm {k : list nat} {l_tm : list nat} {m_tm : list nat}
  (sigma : fin k -> tm l_tm) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | inr fin_n =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_tm shift) (Eq fin_n)))
       | inl n => eq_refl
       end).
Qed.


Fixpoint compSubstRen_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
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

Lemma up_subst_subst_tm_tm {k : list nat} {l_tm : list nat} {m_tm : list nat}
  (sigma : fin k -> tm l_tm) (tau_tm : fin l_tm -> tm m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | inr fin_n =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma fin_n))) (ap (ren_tm shift) (Eq fin_n)))
       | inl n => eq_refl
       end).
Qed.


Fixpoint compSubstSubst_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
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

Lemma rinstInst_up_tm_tm {m : list nat} {n_tm : list nat} (xi : fin m -> fin n_tm)
  (sigma : fin m -> tm n_tm)
  (Eq : forall x, funcomp (var_tm n_tm) xi x = sigma x) :
  forall x, funcomp (var_tm (upT n_tm)) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | inr fin_n => ap (ren_tm shift) (Eq fin_n)
       | inl n => eq_refl
       end).
Qed.


Fixpoint rinst_inst_tm {m_tm : list nat} {n_tm : list nat}
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

Lemma renRen_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Require Import Setoid Morphisms.

Lemma renRen'_tm_pointwise {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) (s : tm m_tm)
  : subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
  (s : tm m_tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm {m_tm : list nat} {n_tm : list nat} (xi_tm : fin m_tm -> fin n_tm)
  (s : tm m_tm) : ren_tm xi_tm s = subst_tm (funcomp (var_tm n_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise {m_tm : list nat} {n_tm : list nat}
  (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq (ren_tm xi_tm)
    (subst_tm (funcomp (var_tm n_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm {m_tm : list nat} (s : tm m_tm) : subst_tm (var_tm m_tm) s = s.
Proof.
exact (idSubst_tm (var_tm m_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise {m_tm : list nat} :
  pointwise_relation _ eq (subst_tm (var_tm m_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm m_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm {m_tm : list nat} (s : tm m_tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise {m_tm : list nat} :
  pointwise_relation _ eq (@ren_tm m_tm m_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm {m_tm : list nat} {n_tm : list nat} (sigma_tm : fin m_tm -> tm n_tm)
  (x : fin m_tm) : subst_tm sigma_tm (var_tm m_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise {m_tm : list nat} {n_tm : list nat}
  (sigma_tm : fin m_tm -> tm n_tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm m_tm))
    sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm {m_tm : list nat} {n_tm : list nat} (xi_tm : fin m_tm -> fin n_tm)
  (x : fin m_tm) : ren_tm xi_tm (var_tm m_tm x) = var_tm n_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise {m_tm : list nat} {n_tm : list nat}
  (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm m_tm))
    (funcomp (var_tm n_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

(* Class Up_tm X Y := *)
(*     up_tm : X -> Y. *)

(* Instance Subst_tm  {m_tm n_tm : nat}: (Subst1 _ _ _) := (@subst_tm m_tm n_tm). *)

(* Instance Up_tm_tm  {m n_tm : nat}: (Up_tm _ _) := (@up_tm_tm m n_tm). *)

(* Instance Ren_tm  {m_tm n_tm : nat}: (Ren1 _ _ _) := (@ren_tm m_tm n_tm). *)

(* Instance VarInstance_tm  {n_tm : nat}: (Var _ _) := (@var_tm n_tm). *)

(* Notation "[ sigma_tm ]" := (subst_tm sigma_tm) *)
(*   ( at level 1, left associativity, only printing) : fscope. *)

(* Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s) *)
(*   ( at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "↑__tm" := up_tm (only printing) : subst_scope. *)

(* Notation "↑__tm" := up_tm_tm (only printing) : subst_scope. *)

(* Notation "⟨ xi_tm ⟩" := (ren_tm xi_tm) *)
(*   ( at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s) *)
(*   ( at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "'var'" := var_tm ( at level 1, only printing) : subst_scope. *)

(* Notation "x '__tm'" := (@ids _ _ VarInstance_tm x) *)
(*   ( at level 5, format "x __tm", only printing) : subst_scope. *)

(* Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm") : *)
(*   subst_scope. *)

Instance subst_tm_morphism  {m_tm : list nat} {n_tm : list nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm m_tm n_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

Instance ren_tm_morphism  {m_tm : list nat} {n_tm : list nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_tm m_tm n_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

(* Ltac auto_unfold := repeat *)
(*                      unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1, *)
(*                       Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1. *)

(* Tactic Notation "auto_unfold" "in" "*" := repeat *)
(*                                            unfold VarInstance_tm, Var, ids, *)
(*                                             Ren_tm, Ren1, ren1, Up_tm_tm, *)
(*                                             Up_tm, up_tm, Subst_tm, Subst1, *)
(*                                             subst1 in *. *)

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
                    unfold up_tm_tm, 
                     upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                   ]).



End renSubst.

Module fext.

Import
renSubst.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma rinstInst_tm {m_tm : list nat} {n_tm : list nat} (xi_tm : fin m_tm -> fin n_tm) :
  ren_tm xi_tm = subst_tm (funcomp (var_tm n_tm) xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_tm xi_tm _ (fun n => eq_refl) x)).
Qed.

Lemma instId_tm {m_tm : list nat} : subst_tm (var_tm m_tm) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_tm (var_tm m_tm) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_tm {m_tm : list nat} : @ren_tm m_tm m_tm id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _)) instId_tm).
Qed.

Lemma varL_tm {m_tm : list nat} {n_tm : list nat} (sigma_tm : fin m_tm -> tm n_tm) :
  funcomp (subst_tm sigma_tm) (var_tm m_tm) = sigma_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_tm {m_tm : list nat} {n_tm : list nat} (xi_tm : fin m_tm -> fin n_tm) :
  funcomp (ren_tm xi_tm) (var_tm m_tm) = funcomp (var_tm n_tm) xi_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (ren_tm xi_tm) = ren_tm (funcomp zeta_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_tm xi_tm zeta_tm n)).
Qed.

Lemma substRen'_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_tm sigma_tm zeta_tm n)).
Qed.

Lemma renSubst'_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  funcomp (subst_tm tau_tm) (ren_tm xi_tm) = subst_tm (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_tm xi_tm tau_tm n)).
Qed.

Lemma substSubst'_tm {k_tm : list nat} {l_tm : list nat} {m_tm : list nat}
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
                         unfold up_tm_tm, 
                          upRen_tm_tm, up_ren
                      | progress cbn[subst_tm ren_tm] ]).


End fext.

Module interface.

Export renSubst.

Export
fext.

Arguments var_tm {vs}.

Arguments lam {vs}.

Arguments app {vs}.

Hint Opaque subst_tm: rewrite.

Hint Opaque ren_tm: rewrite.

End interface.

Export interface.

