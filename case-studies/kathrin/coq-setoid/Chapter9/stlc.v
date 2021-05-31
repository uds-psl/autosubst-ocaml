Require Import core core_axioms fintype fintype_axioms.
Inductive ty : Type :=
  | Base : ty
  | Fun : ty -> ty -> ty.

Lemma congr_Base : Base = Base.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Fun {s0 : ty} {s1 : ty} {t0 : ty} {t1 : ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : Fun s0 s1 = Fun t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Fun x s1) H0))
         (ap (fun x => Fun t0 x) H1)).
Qed.

Inductive tm (n_tm : nat) : Type :=
  | var_tm : fin n_tm -> tm n_tm
  | app : tm n_tm -> tm n_tm -> tm n_tm
  | lam : ty -> tm (S n_tm) -> tm n_tm.

Lemma congr_app {m_tm : nat} {s0 : tm m_tm} {s1 : tm m_tm} {t0 : tm m_tm}
  {t1 : tm m_tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_tm s0 s1 = app m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_tm x s1) H0))
         (ap (fun x => app m_tm t0 x) H1)).
Qed.

Lemma congr_lam {m_tm : nat} {s0 : ty} {s1 : tm (S m_tm)} {t0 : ty}
  {t1 : tm (S m_tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  lam m_tm s0 s1 = lam m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lam m_tm x s1) H0))
         (ap (fun x => lam m_tm t0 x) H1)).
Qed.

Lemma upRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_tm_tm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
(s : tm m_tm) {struct s} : tm n_tm :=
  match s with
  | var_tm _ s0 => var_tm n_tm (xi_tm s0)
  | app _ s0 s1 => app n_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | lam _ s0 s1 => lam n_tm ((fun x => x) s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  end.

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
  | lam _ s0 s1 =>
      lam n_tm ((fun x => x) s0) (subst_tm (up_tm_tm sigma_tm) s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
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
  | lam _ s0 s1 =>
      congr_lam ((fun x => eq_refl x) s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  end.

Lemma renRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma compRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renComp_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) (s : tm m_tm)
  : subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma compComp_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
  (s : tm m_tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

Definition Subst_tm {m_tm n_tm : nat} : Subst1 _ _ _ := @subst_tm m_tm n_tm.

Existing Instance Subst_tm.

Definition Up_tm_tm {m n_tm : nat} : Up_tm _ _ := @up_tm_tm m n_tm.

Existing Instance Up_tm_tm.

Definition Ren_tm {m_tm n_tm : nat} : Ren1 _ _ _ := @ren_tm m_tm n_tm.

Existing Instance Ren_tm.

Definition VarInstance_tm {n_tm : nat} : Var _ _ := @var_tm n_tm.

Existing Instance VarInstance_tm.

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


Lemma rinstInst_tm' {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) :
  forall s:tm m_tm, ren_tm xi_tm s = subst_tm (funcomp (var_tm n_tm) xi_tm) s.
Proof.
  apply rinst_inst_tm. intros x. reflexivity.
Qed.

(* Lemma rinstInst_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) : *)
(*   ren_tm xi_tm = subst_tm (funcomp (var_tm n_tm) xi_tm). *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun x => rinst_inst_tm xi_tm _ (fun n => eq_refl) x)). *)
(* Qed. *)

Lemma instId_tm' {n_tm:nat} : forall (s: tm n_tm), subst_tm (var_tm n_tm) s = s.
Proof.
  exact (fun x => idSubst_tm (var_tm _) (fun n => eq_refl) x).
Qed.

Lemma rinstId_tm' {n_tm:nat}: forall (s: tm n_tm), ren_tm id s = s.
Proof.
  intros s.
  erewrite rinst_inst_tm. apply instId_tm'.
  intros x. reflexivity.
Qed.
(* Lemma instId_tm {m_tm : nat} : subst_tm (var_tm m_tm) = id. *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun x => idSubst_tm (var_tm m_tm) (fun n => eq_refl) (id x))). *)
(* Qed. *)

(* Lemma rinstId_tm {m_tm : nat} : @ren_tm m_tm m_tm id = id. *)
(* Proof. *)
(* exact (eq_trans (rinstInst_tm (id _)) instId_tm). *)
(* Qed. *)

Lemma varL_tm' {m_tm n_tm:nat} (sigma_tm : fin m_tm -> tm n_tm) (s: tm m_tm) :
  subst_tm (fun x => subst_tm sigma_tm (var_tm _ x)) s = subst_tm sigma_tm s.
Proof.
  apply ext_tm. intros x. reflexivity.
Qed.

(* Lemma varL_tm'' {m_tm n_tm:nat} (sigma_tm : fin m_tm -> tm n_tm) (x: fin m_tm) : *)
(*   (funcomp (subst_tm sigma_tm) (var_tm _)) x = subst_tm sigma_tm (var_tm _ x). *)
(* Proof. *)
(*   unfold funcomp. reflexivity. *)
(* Qed. *)

(* Lemma varL_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm) : *)
(*   funcomp (subst_tm sigma_tm) (var_tm m_tm) = sigma_tm. *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun x => eq_refl)). *)
(* Qed. *)

Lemma varLRen_tm' {m_tm n_tm: nat} (xi_tm : fin m_tm -> fin n_tm) (s : tm m_tm) :
  subst_tm (fun x => ren_tm xi_tm (var_tm _ x)) s = subst_tm (fun x => var_tm _ (xi_tm x)) s.
Proof.
  apply ext_tm. intros x. reflexivity.
Qed.

(* Lemma varLRen_tm'' {m_tm n_tm: nat} (xi_tm : fin m_tm -> fin n_tm) (x: fin m_tm) : *)
(*   (funcomp (ren_tm xi_tm) (var_tm _)) x = (funcomp (var_tm _) xi_tm) x. *)
(* Proof. *)
(*   unfold funcomp. cbn [ ren_tm ]. reflexivity. *)
(* Qed. *)

(* Lemma varLRen_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) : *)
(*   funcomp (ren_tm xi_tm) (var_tm m_tm) = funcomp (var_tm n_tm) xi_tm. *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun x => eq_refl)). *)
(* Qed. *)

(* Lemma renRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat} *)
(*   (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) : *)
(*   funcomp (ren_tm zeta_tm) (ren_tm xi_tm) = ren_tm (funcomp zeta_tm xi_tm). *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun n => renRen_tm xi_tm zeta_tm n)). *)
(* Qed. *)

(* Lemma compRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat} *)
(*   (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) : *)
(*   funcomp (ren_tm zeta_tm) (subst_tm sigma_tm) = *)
(*   subst_tm (funcomp (ren_tm zeta_tm) sigma_tm). *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun n => compRen_tm sigma_tm zeta_tm n)). *)
(* Qed. *)

(* Lemma renComp'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat} *)
(*   (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) : *)
(*   funcomp (subst_tm tau_tm) (ren_tm xi_tm) = subst_tm (funcomp tau_tm xi_tm). *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun n => renComp_tm xi_tm tau_tm n)). *)
(* Qed. *)

(* Lemma compComp'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat} *)
(*   (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm) : *)
(*   funcomp (subst_tm tau_tm) (subst_tm sigma_tm) = *)
(*   subst_tm (funcomp (subst_tm tau_tm) sigma_tm). *)
(* Proof. *)
(* exact (FunctionalExtensionality.functional_extensionality _ _ *)
(*          (fun n => compComp_tm sigma_tm tau_tm n)). *)
(* Qed. *)

Arguments lam {n_tm}.

Arguments app {n_tm}.

Arguments var_tm {n_tm}.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1 in *.


Require Import Setoid Morphisms.
Require Import Relation_Definitions.

Instance subst_morphism {m_tm n_tm:nat}:
  Proper (pointwise_relation _ eq ==> eq ==> eq) (@subst_tm m_tm n_tm).
Proof.
  cbv - [subst_tm].
  intros sigma tau H s t ->. apply ext_tm.
  apply H.
Qed.

Instance scons_morphism {m_tm n_tm:nat} (t: tm m_tm) :
  Proper (pointwise_relation _ eq ==> pointwise_relation _ eq) (fun f  => (@scons _ n_tm t f)).
Proof.
  cbv - [scons].
  intros sigma tau H.
  intros x.
  destruct x.
  cbn.  apply H.
  reflexivity.
Qed.

(* Instance eta_morphism {X Y} : *)
(*   Proper (pointwise_relation _ eq ==> pointwise_relation _ eq) (fun g : X -> Y => fun x => g x). *)
(* Proof. *)
(*   intros g g' Hg x. apply Hg. *)
(* Qed. *)

Instance funcomp_morphism2 {X Y Z} (f: X -> Y) :
  Proper (pointwise_relation _ eq ==> pointwise_relation _ eq) (fun g : Y -> Z => funcomp g f).
Proof.
  cbv - [funcomp].
  intros g h H. setoid_rewrite H.
  intros ?; reflexivity.
Qed.

(* Lemma scons_comp' {m_tm n_tm k_tm:nat} {s: tm n_tm} (sigma: fin m_tm -> tm n_tm) (tau: tm n_tm -> tm k_tm) : forall n : fin (S m_tm), (funcomp tau (scons s sigma)) n = (scons (tau s) (funcomp tau sigma)) n. *)
(* Proof. *)
(*   intros [n|]. reflexivity. simpl. reflexivity. *)
(* Qed. *)

Ltac eta_expand_subst :=
     repeat match goal with  
     | [|- context[subst_tm ?f]] =>
       lazymatch f with
       | (fun x => ?b x) => fail
       | _ => change (subst_tm f) with (subst_tm (fun x => f x))
       end
     end.

Ltac eta_reduce :=
     repeat match goal with
            | [|- context[(fun x => ?b x)]] => change (fun x => b x) with b
            end.

Ltac setoidasimpl' := repeat (first
                        [
                        (* progress rewrite ?compComp'_tm *)
                 progress setoid_rewrite compComp_tm; idtac "compComp"
                 (* | progress rewrite ?renComp'_tm *)
                 | progress setoid_rewrite renComp_tm; idtac "renComp"
                 (* | progress rewrite ?compRen'_tm *)
                 | progress setoid_rewrite compRen_tm; idtac "compRen"
                 (* | progress rewrite ?renRen'_tm *)
                 | progress setoid_rewrite renRen_tm; idtac "renRen"
                 (* | progress setoid_rewrite scons_comp'; idtac "scons_comp" *)
                 | progress eta_expand_subst; setoid_rewrite scons_comp'; eta_reduce; idtac "scons_comp"
                 (* | progress rewrite ?varLRen_tm *)
                 (* | progress setoid_rewrite varLRen_tm'; idtac "varLRen" *)
                 (* | progress rewrite ?varL_tm *)
                 (* | progress setoid_rewrite varL_tm'; idtac "varL" *)
                 (* | progress rewrite ?rinstId_tm *)
                 | progress setoid_rewrite rinstId_tm'; idtac "rinstId"
                 (* | progress rewrite ?instId_tm *)
                 | progress setoid_rewrite instId_tm'; idtac "instId"
                 | progress
                    unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm,
                     upRen_tm_tm, up_ren; idtac "unfold"
                 | progress cbn[subst_tm ren_tm]; idtac "cbn"
                 | progress fsimpl; idtac "fsimpl"
                 | repeat unfold funcomp; idtac "funcomp"
                       ]).

(* Ltac asimpl' := repeat (first *)
(*                         [ *)
(*                         progress rewrite ?compComp'_tm; idtac "compComp'" *)
(*                  | progress rewrite ?compComp_tm; idtac "compComp" *)
(*                  | progress rewrite ?renComp'_tm; idtac "renComp'" *)
(*                  | progress rewrite ?renComp_tm; idtac "renComp" *)
(*                  | progress rewrite ?compRen'_tm; idtac "compRen'" *)
(*                  | progress rewrite ?compRen_tm; idtac "compRen" *)
(*                  | progress rewrite ?renRen'_tm; idtac "renRen'" *)
(*                  | progress rewrite ?renRen_tm; idtac "renRen" *)
(*                  | progress rewrite ?varLRen_tm; idtac "varLRen" *)
(*                  | progress rewrite ?varL_tm; idtac "varL" *)
(*                  | progress rewrite ?rinstId_tm; idtac "rinstId" *)
(*                  | progress rewrite ?instId_tm; idtac "instId" *)
(*                  | progress *)
(*                     unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, *)
(*                      upRen_tm_tm, up_ren; idtac "unfold" *)
(*                  | progress cbn[subst_tm ren_tm]; idtac "cbn" *)
(*                  | fsimpl; idtac "fsimpl" *)
(*                        ]). *)

Ltac asimpl := repeat try unfold_funcomp;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                setoidasimpl'; repeat try unfold_funcomp.

(* Ltac oldasimpl := repeat try unfold_funcomp; *)
(*                 repeat *)
(*                  unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1, *)
(*                   Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *; *)
(*                 asimpl'; repeat try unfold_funcomp. *)

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).


Ltac substify := auto_unfold; try repeat erewrite ?rinstInst_tm'.

Ltac renamify := auto_unfold; try repeat erewrite <- ?rinstInst_tm'.

