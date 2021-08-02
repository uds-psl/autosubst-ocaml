Require Import core unscoped.

Inductive ty : Type :=
  | var_ty : nat -> ty
  | arr : ty -> ty -> ty
  | all : ty -> ty.

Lemma congr_arr {s0 : ty} {s1 : ty} {t0 : ty} {t1 : ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : arr s0 s1 = arr t0 t1.

Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => arr x s1) H0))
                (ap (fun x => arr t0 x) H1)).

Qed.

Lemma congr_all {s0 : ty} {t0 : ty} (H0 : s0 = t0) : all s0 = all t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => all x) H0)).

Qed.

Lemma upRen_ty_ty (xi : nat -> nat) : nat -> nat.

Proof.
exact (up_ren xi).

Defined.

Fixpoint ren_ty (xi_ty : nat -> nat) (s : ty) {struct s} : ty :=
  match s with
  | var_ty s0 => var_ty (xi_ty s0)
  | arr s0 s1 => arr (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | all s0 => all (ren_ty (upRen_ty_ty xi_ty) s0)
  end.

Lemma up_ty_ty (sigma : nat -> ty) : nat -> ty.

Proof.
exact (scons (var_ty var_zero) (funcomp (ren_ty shift) sigma)).

Defined.

Fixpoint subst_ty (sigma_ty : nat -> ty) (s : ty) {struct s} : ty :=
  match s with
  | var_ty s0 => sigma_ty s0
  | arr s0 s1 => arr (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | all s0 => all (subst_ty (up_ty_ty sigma_ty) s0)
  end.

Lemma upId_ty_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x) :
  forall x, up_ty_ty sigma x = var_ty x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_ty shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint idSubst_ty (sigma_ty : nat -> ty)
(Eq_ty : forall x, sigma_ty x = var_ty x) (s : ty) {struct s} :
subst_ty sigma_ty s = s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | arr s0 s1 =>
      congr_arr (idSubst_ty sigma_ty Eq_ty s0) (idSubst_ty sigma_ty Eq_ty s1)
  | all s0 =>
      congr_all (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ Eq_ty) s0)
  end.

Lemma upExtRen_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_ty xi x = upRen_ty_ty zeta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap shift (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint extRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x) (s : ty) {struct s} :
ren_ty xi_ty s = ren_ty zeta_ty s :=
  match s with
  | var_ty s0 => ap var_ty (Eq_ty s0)
  | arr s0 s1 =>
      congr_arr (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | all s0 =>
      congr_all
        (extRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upExtRen_ty_ty _ _ Eq_ty) s0)
  end.

Lemma upExt_ty_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_ty sigma x = up_ty_ty tau x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_ty shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint ext_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty)
(Eq_ty : forall x, sigma_ty x = tau_ty x) (s : ty) {struct s} :
subst_ty sigma_ty s = subst_ty tau_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | arr s0 s1 =>
      congr_arr (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | all s0 =>
      congr_all
        (ext_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty) (upExt_ty_ty _ _ Eq_ty)
           s0)
  end.

Lemma up_ren_ren_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Fixpoint compRenRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat)
(rho_ty : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(s : ty) {struct s} : ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty rho_ty s :=
  match s with
  | var_ty s0 => ap var_ty (Eq_ty s0)
  | arr s0 s1 =>
      congr_arr (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | all s0 =>
      congr_all
        (compRenRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upRen_ty_ty rho_ty) (up_ren_ren _ _ _ Eq_ty) s0)
  end.

Lemma up_ren_subst_ty_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_ty shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint compRenSubst_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x) (s : ty) {struct s} :
subst_ty tau_ty (ren_ty xi_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | arr s0 s1 =>
      congr_arr (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | all s0 =>
      congr_all
        (compRenSubst_ty (upRen_ty_ty xi_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_ren_subst_ty_ty _ _ _ Eq_ty) s0)
  end.

Lemma up_subst_ren_ty_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_ty_ty zeta_ty)) (up_ty_ty sigma) x =
  up_ty_ty theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenRen_ty shift (upRen_ty_ty zeta_ty)
                       (funcomp shift zeta_ty) (fun x => eq_refl) (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compRenRen_ty zeta_ty shift
                             (funcomp shift zeta_ty) (fun x => eq_refl)
                             (sigma n'))) (ap (ren_ty shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstRen_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x) 
(s : ty) {struct s} :
ren_ty zeta_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | arr s0 s1 =>
      congr_arr (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | all s0 =>
      congr_all
        (compSubstRen_ty (up_ty_ty sigma_ty) (upRen_ty_ty zeta_ty)
           (up_ty_ty theta_ty) (up_subst_ren_ty_ty _ _ _ Eq_ty) s0)
  end.

Lemma up_subst_subst_ty_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_ty_ty tau_ty)) (up_ty_ty sigma) x = up_ty_ty theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenSubst_ty shift (up_ty_ty tau_ty)
                       (funcomp (up_ty_ty tau_ty) shift) (fun x => eq_refl)
                       (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_ty tau_ty shift
                             (funcomp (ren_ty shift) tau_ty)
                             (fun x => eq_refl) (sigma n')))
                       (ap (ren_ty shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstSubst_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(s : ty) {struct s} :
subst_ty tau_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | arr s0 s1 =>
      congr_arr (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | all s0 =>
      congr_all
        (compSubstSubst_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_subst_subst_ty_ty _ _ _ Eq_ty) s0)
  end.

Lemma rinstInst_up_ty_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp var_ty xi x = sigma x) :
  forall x, funcomp var_ty (upRen_ty_ty xi) x = up_ty_ty sigma x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_ty shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint rinst_inst_ty (xi_ty : nat -> nat) (sigma_ty : nat -> ty)
(Eq_ty : forall x, funcomp var_ty xi_ty x = sigma_ty x) (s : ty) {struct s} :
ren_ty xi_ty s = subst_ty sigma_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | arr s0 s1 =>
      congr_arr (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | all s0 =>
      congr_all
        (rinst_inst_ty (upRen_ty_ty xi_ty) (up_ty_ty sigma_ty)
           (rinstInst_up_ty_ty _ _ Eq_ty) s0)
  end.

Lemma renRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty (funcomp zeta_ty xi_ty) s.

Proof.
exact (compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).

Qed.

Lemma compRen_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s.

Proof.
exact (compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).

Qed.

Lemma renComp_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (ren_ty xi_ty s) = subst_ty (funcomp tau_ty xi_ty) s.

Proof.
exact (compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).

Qed.

Lemma compComp_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s.

Proof.
exact (compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).

Qed.

Inductive tm : Type :=
  | var_tm : nat -> tm
  | app : tm -> tm -> tm
  | tapp : tm -> ty -> tm
  | lam : ty -> tm -> tm
  | tlam : tm -> tm.

Lemma congr_app {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : app s0 s1 = app t0 t1.

Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
                (ap (fun x => app t0 x) H1)).

Qed.

Lemma congr_tapp {s0 : tm} {s1 : ty} {t0 : tm} {t1 : ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : tapp s0 s1 = tapp t0 t1.

Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tapp x s1) H0))
                (ap (fun x => tapp t0 x) H1)).

Qed.

Lemma congr_lam {s0 : ty} {s1 : tm} {t0 : ty} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : lam s0 s1 = lam t0 t1.

Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lam x s1) H0))
                (ap (fun x => lam t0 x) H1)).

Qed.

Lemma congr_tlam {s0 : tm} {t0 : tm} (H0 : s0 = t0) : tlam s0 = tlam t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => tlam x) H0)).

Qed.

Lemma upRen_ty_tm (xi : nat -> nat) : nat -> nat.

Proof.
exact (xi).

Defined.

Lemma upRen_tm_ty (xi : nat -> nat) : nat -> nat.

Proof.
exact (xi).

Defined.

Lemma upRen_tm_tm (xi : nat -> nat) : nat -> nat.

Proof.
exact (up_ren xi).

Defined.

Fixpoint ren_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat) (s : tm) {struct s}
   : tm :=
  match s with
  | var_tm s0 => var_tm (xi_tm s0)
  | app s0 s1 => app (ren_tm xi_ty xi_tm s0) (ren_tm xi_ty xi_tm s1)
  | tapp s0 s1 => tapp (ren_tm xi_ty xi_tm s0) (ren_ty xi_ty s1)
  | lam s0 s1 =>
      lam (ren_ty xi_ty s0)
        (ren_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm) s1)
  | tlam s0 => tlam (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm) s0)
  end.

Lemma up_ty_tm (sigma : nat -> tm) : nat -> tm.

Proof.
exact (funcomp (ren_tm shift id) sigma).

Defined.

Lemma up_tm_ty (sigma : nat -> ty) : nat -> ty.

Proof.
exact (funcomp (ren_ty id) sigma).

Defined.

Lemma up_tm_tm (sigma : nat -> tm) : nat -> tm.

Proof.
exact (scons (var_tm var_zero) (funcomp (ren_tm id shift) sigma)).

Defined.

Fixpoint subst_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm) (s : tm)
{struct s} : tm :=
  match s with
  | var_tm s0 => sigma_tm s0
  | app s0 s1 =>
      app (subst_tm sigma_ty sigma_tm s0) (subst_tm sigma_ty sigma_tm s1)
  | tapp s0 s1 => tapp (subst_tm sigma_ty sigma_tm s0) (subst_ty sigma_ty s1)
  | lam s0 s1 =>
      lam (subst_ty sigma_ty s0)
        (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) s1)
  | tlam s0 => tlam (subst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) s0)
  end.

Lemma upId_ty_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_ty_tm sigma x = var_tm x.

Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).

Qed.

Lemma upId_tm_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x) :
  forall x, up_tm_ty sigma x = var_ty x.

Proof.
exact (fun n => ap (ren_ty id) (Eq n)).

Qed.

Lemma upId_tm_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = var_tm x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_tm id shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint idSubst_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
(Eq_ty : forall x, sigma_ty x = var_ty x)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : tm) {struct s} :
subst_tm sigma_ty sigma_tm s = s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
  | tapp s0 s1 =>
      congr_tapp (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (upId_tm_ty _ Eq_ty) (upId_tm_tm _ Eq_tm) s1)
  | tlam s0 =>
      congr_tlam
        (idSubst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (upId_ty_ty _ Eq_ty) (upId_ty_tm _ Eq_tm) s0)
  end.

Lemma upExtRen_ty_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_tm xi x = upRen_ty_tm zeta x.

Proof.
exact (fun n => Eq n).

Qed.

Lemma upExtRen_tm_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_ty xi x = upRen_tm_ty zeta x.

Proof.
exact (fun n => Eq n).

Qed.

Lemma upExtRen_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap shift (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint extRen_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
(zeta_ty : nat -> nat) (zeta_tm : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm) {struct s} :
ren_tm xi_ty xi_tm s = ren_tm zeta_ty zeta_tm s :=
  match s with
  | var_tm s0 => ap var_tm (Eq_tm s0)
  | app s0 s1 =>
      congr_app (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
        (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s1)
  | tapp s0 s1 =>
      congr_tapp (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_ty _ _ Eq_ty) (upExtRen_tm_tm _ _ Eq_tm) s1)
  | tlam s0 =>
      congr_tlam
        (extRen_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm)
           (upExtRen_ty_ty _ _ Eq_ty) (upExtRen_ty_tm _ _ Eq_tm) s0)
  end.

Lemma upExt_ty_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_tm sigma x = up_ty_tm tau x.

Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).

Qed.

Lemma upExt_tm_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_ty sigma x = up_tm_ty tau x.

Proof.
exact (fun n => ap (ren_ty id) (Eq n)).

Qed.

Lemma upExt_tm_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_tm id shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint ext_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
(tau_ty : nat -> ty) (tau_tm : nat -> tm)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm) {struct s} :
subst_tm sigma_ty sigma_tm s = subst_tm tau_ty tau_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
        (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s1)
  | tapp s0 s1 =>
      congr_tapp (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) (up_tm_ty tau_ty)
           (up_tm_tm tau_tm) (upExt_tm_ty _ _ Eq_ty) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | tlam s0 =>
      congr_tlam
        (ext_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) (up_ty_ty tau_ty)
           (up_ty_tm tau_tm) (upExt_ty_ty _ _ Eq_ty) (upExt_ty_tm _ _ Eq_tm)
           s0)
  end.

Lemma up_ren_ren_ty_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_tm zeta) (upRen_ty_tm xi) x = upRen_ty_tm rho x.

Proof.
exact (Eq).

Qed.

Lemma up_ren_ren_tm_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_ty zeta) (upRen_tm_ty xi) x = upRen_tm_ty rho x.

Proof.
exact (Eq).

Qed.

Lemma up_ren_ren_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Fixpoint compRenRen_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
(zeta_ty : nat -> nat) (zeta_tm : nat -> nat) (rho_ty : nat -> nat)
(rho_tm : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x) (s : tm) {struct s} :
ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s) = ren_tm rho_ty rho_tm s :=
  match s with
  | var_tm s0 => ap var_tm (Eq_tm s0)
  | app s0 s1 =>
      congr_app
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s0)
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s1)
  | tapp s0 s1 =>
      congr_tapp
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s0) (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm) (upRen_tm_ty rho_ty)
           (upRen_tm_tm rho_tm) Eq_ty (up_ren_ren _ _ _ Eq_tm) s1)
  | tlam s0 =>
      congr_tlam
        (compRenRen_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm) (upRen_ty_ty rho_ty)
           (upRen_ty_tm rho_tm) (up_ren_ren _ _ _ Eq_ty) Eq_tm s0)
  end.

Lemma up_ren_subst_ty_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_tm tau) (upRen_ty_tm xi) x = up_ty_tm theta x.

Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).

Qed.

Lemma up_ren_subst_tm_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_ty tau) (upRen_tm_ty xi) x = up_tm_ty theta x.

Proof.
exact (fun n => ap (ren_ty id) (Eq n)).

Qed.

Lemma up_ren_subst_tm_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_tm id shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint compRenSubst_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
(tau_ty : nat -> ty) (tau_tm : nat -> tm) (theta_ty : nat -> ty)
(theta_tm : nat -> tm)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm) {struct s} :
subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s) = subst_tm theta_ty theta_tm s
:=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s0)
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s1)
  | tapp s0 s1 =>
      congr_tapp
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s0) (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (up_tm_ty tau_ty) (up_tm_tm tau_tm) (up_tm_ty theta_ty)
           (up_tm_tm theta_tm) (up_ren_subst_tm_ty _ _ _ Eq_ty)
           (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | tlam s0 =>
      congr_tlam
        (compRenSubst_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (up_ty_ty tau_ty) (up_ty_tm tau_tm) (up_ty_ty theta_ty)
           (up_ty_tm theta_tm) (up_ren_subst_ty_ty _ _ _ Eq_ty)
           (up_ren_subst_ty_tm _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_ren_ty_tm (sigma : nat -> tm) (zeta_ty : nat -> nat)
  (zeta_tm : nat -> nat) (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm))
    (up_ty_tm sigma) x = up_ty_tm theta x.

Proof.
exact (fun n =>
              eq_trans
                (compRenRen_tm shift id (upRen_ty_ty zeta_ty)
                   (upRen_ty_tm zeta_tm) (funcomp shift zeta_ty)
                   (funcomp id zeta_tm) (fun x => eq_refl) (fun x => eq_refl)
                   (sigma n))
                (eq_trans
                   (eq_sym
                      (compRenRen_tm zeta_ty zeta_tm shift id
                         (funcomp shift zeta_ty) (funcomp id zeta_tm)
                         (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
                   (ap (ren_tm shift id) (Eq n)))).

Qed.

Lemma up_subst_ren_tm_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_tm_ty zeta_ty)) (up_tm_ty sigma) x =
  up_tm_ty theta x.

Proof.
exact (fun n =>
              eq_trans
                (compRenRen_ty id (upRen_tm_ty zeta_ty) (funcomp id zeta_ty)
                   (fun x => eq_refl) (sigma n))
                (eq_trans
                   (eq_sym
                      (compRenRen_ty zeta_ty id (funcomp id zeta_ty)
                         (fun x => eq_refl) (sigma n)))
                   (ap (ren_ty id) (Eq n)))).

Qed.

Lemma up_subst_ren_tm_tm (sigma : nat -> tm) (zeta_ty : nat -> nat)
  (zeta_tm : nat -> nat) (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm))
    (up_tm_tm sigma) x = up_tm_tm theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenRen_tm id shift (upRen_tm_ty zeta_ty)
                       (upRen_tm_tm zeta_tm) (funcomp id zeta_ty)
                       (funcomp shift zeta_tm) (fun x => eq_refl)
                       (fun x => eq_refl) (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compRenRen_tm zeta_ty zeta_tm id shift
                             (funcomp id zeta_ty) (funcomp shift zeta_tm)
                             (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                       (ap (ren_tm id shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstRen_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
(zeta_ty : nat -> nat) (zeta_tm : nat -> nat) (theta_ty : nat -> ty)
(theta_tm : nat -> tm)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_tm : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
ren_tm zeta_ty zeta_tm (subst_tm sigma_ty sigma_tm s) =
subst_tm theta_ty theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s1)
  | tapp s0 s1 =>
      congr_tapp
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm) (up_tm_ty theta_ty)
           (up_tm_tm theta_tm) (up_subst_ren_tm_ty _ _ _ Eq_ty)
           (up_subst_ren_tm_tm _ _ _ _ Eq_tm) s1)
  | tlam s0 =>
      congr_tlam
        (compSubstRen_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm) (up_ty_ty theta_ty)
           (up_ty_tm theta_tm) (up_subst_ren_ty_ty _ _ _ Eq_ty)
           (up_subst_ren_ty_tm _ _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_subst_ty_tm (sigma : nat -> tm) (tau_ty : nat -> ty)
  (tau_tm : nat -> tm) (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_ty_ty tau_ty) (up_ty_tm tau_tm)) (up_ty_tm sigma) x =
  up_ty_tm theta x.

Proof.
exact (fun n =>
              eq_trans
                (compRenSubst_tm shift id (up_ty_ty tau_ty) (up_ty_tm tau_tm)
                   (funcomp (up_ty_ty tau_ty) shift)
                   (funcomp (up_ty_tm tau_tm) id) (fun x => eq_refl)
                   (fun x => eq_refl) (sigma n))
                (eq_trans
                   (eq_sym
                      (compSubstRen_tm tau_ty tau_tm shift id
                         (funcomp (ren_ty shift) tau_ty)
                         (funcomp (ren_tm shift id) tau_tm)
                         (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
                   (ap (ren_tm shift id) (Eq n)))).

Qed.

Lemma up_subst_subst_tm_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_tm_ty tau_ty)) (up_tm_ty sigma) x = up_tm_ty theta x.

Proof.
exact (fun n =>
              eq_trans
                (compRenSubst_ty id (up_tm_ty tau_ty)
                   (funcomp (up_tm_ty tau_ty) id) (fun x => eq_refl)
                   (sigma n))
                (eq_trans
                   (eq_sym
                      (compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty)
                         (fun x => eq_refl) (sigma n)))
                   (ap (ren_ty id) (Eq n)))).

Qed.

Lemma up_subst_subst_tm_tm (sigma : nat -> tm) (tau_ty : nat -> ty)
  (tau_tm : nat -> tm) (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_ty tau_ty) (up_tm_tm tau_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenSubst_tm id shift (up_tm_ty tau_ty)
                       (up_tm_tm tau_tm) (funcomp (up_tm_ty tau_ty) id)
                       (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                       (fun x => eq_refl) (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_tm tau_ty tau_tm id shift
                             (funcomp (ren_ty id) tau_ty)
                             (funcomp (ren_tm id shift) tau_tm)
                             (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                       (ap (ren_tm id shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstSubst_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
(tau_ty : nat -> ty) (tau_tm : nat -> tm) (theta_ty : nat -> ty)
(theta_tm : nat -> tm)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_tm : forall x, funcomp (subst_tm tau_ty tau_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm s) =
subst_tm theta_ty theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s1)
  | tapp s0 s1 =>
      congr_tapp
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (up_tm_ty tau_ty) (up_tm_tm tau_tm) (up_tm_ty theta_ty)
           (up_tm_tm theta_tm) (up_subst_subst_tm_ty _ _ _ Eq_ty)
           (up_subst_subst_tm_tm _ _ _ _ Eq_tm) s1)
  | tlam s0 =>
      congr_tlam
        (compSubstSubst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (up_ty_ty tau_ty) (up_ty_tm tau_tm) (up_ty_ty theta_ty)
           (up_ty_tm theta_tm) (up_subst_subst_ty_ty _ _ _ Eq_ty)
           (up_subst_subst_ty_tm _ _ _ _ Eq_tm) s0)
  end.

Lemma rinstInst_up_ty_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp var_tm xi x = sigma x) :
  forall x, funcomp var_tm (upRen_ty_tm xi) x = up_ty_tm sigma x.

Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).

Qed.

Lemma rinstInst_up_tm_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp var_ty xi x = sigma x) :
  forall x, funcomp var_ty (upRen_tm_ty xi) x = up_tm_ty sigma x.

Proof.
exact (fun n => ap (ren_ty id) (Eq n)).

Qed.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp var_tm xi x = sigma x) :
  forall x, funcomp var_tm (upRen_tm_tm xi) x = up_tm_tm sigma x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_tm id shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint rinst_inst_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
(sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
(Eq_ty : forall x, funcomp var_ty xi_ty x = sigma_ty x)
(Eq_tm : forall x, funcomp var_tm xi_tm x = sigma_tm x) (s : tm) {struct s} :
ren_tm xi_ty xi_tm s = subst_tm sigma_ty sigma_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
  | tapp s0 s1 =>
      congr_tapp (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | lam s0 s1 =>
      congr_lam (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_ty _ _ Eq_ty) (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | tlam s0 =>
      congr_tlam
        (rinst_inst_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (rinstInst_up_ty_ty _ _ Eq_ty) (rinstInst_up_ty_tm _ _ Eq_tm) s0)
  end.

Lemma renRen_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm) s.

Proof.
exact (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm _ _
                (fun n => eq_refl) (fun n => eq_refl) s).

Qed.

Lemma compRen_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_tm (subst_tm sigma_ty sigma_tm s) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm) s.

Proof.
exact (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm _ _
                (fun n => eq_refl) (fun n => eq_refl) s).

Qed.

Lemma renComp_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm) s.

Proof.
exact (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm _ _
                (fun n => eq_refl) (fun n => eq_refl) s).

Qed.

Lemma compComp_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm s) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_tm tau_ty tau_tm) sigma_tm) s.

Proof.
exact (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm _ _
                (fun n => eq_refl) (fun n => eq_refl) s).

Qed.
