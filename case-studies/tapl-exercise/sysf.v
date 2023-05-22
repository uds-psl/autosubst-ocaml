Require Import core unscoped.

Require Import core_axioms unscoped_axioms.
Require Import Setoid Morphisms Relation_Definitions.


Module Core.

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
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x) (s : ty) {struct s} :
ren_ty xi_ty s = ren_ty zeta_ty s :=
  match s with
  | var_ty s0 => ap (var_ty) (Eq_ty s0)
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
  | var_ty s0 => ap (var_ty) (Eq_ty s0)
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
                   (compRenRen_ty zeta_ty shift (funcomp shift zeta_ty)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_ty shift) (Eq n')))
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
                      (funcomp (ren_ty shift) tau_ty) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_ty shift) (Eq n')))
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

Lemma renRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty (funcomp zeta_ty xi_ty) s.
Proof.
exact (compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_ty_pointwise (xi_ty : nat -> nat) (zeta_ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty zeta_ty) (ren_ty xi_ty))
    (ren_ty (funcomp zeta_ty xi_ty)).
Proof.
exact (fun s => compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (ren_ty xi_ty s) = subst_ty (funcomp tau_ty xi_ty) s.
Proof.
exact (compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty_pointwise (xi_ty : nat -> nat) (tau_ty : nat -> ty) :
  pointwise_relation _ eq (funcomp (subst_ty tau_ty) (ren_ty xi_ty))
    (subst_ty (funcomp tau_ty xi_ty)).
Proof.
exact (fun s => compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s.
Proof.
exact (compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ty_pointwise (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty zeta_ty) (subst_ty sigma_ty))
    (subst_ty (funcomp (ren_ty zeta_ty) sigma_ty)).
Proof.
exact (fun s => compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s.
Proof.
exact (compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty_pointwise (sigma_ty : nat -> ty) (tau_ty : nat -> ty) :
  pointwise_relation _ eq (funcomp (subst_ty tau_ty) (subst_ty sigma_ty))
    (subst_ty (funcomp (subst_ty tau_ty) sigma_ty)).
Proof.
exact (fun s => compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_ty_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp (var_ty) xi x = sigma x) :
  forall x, funcomp (var_ty) (upRen_ty_ty xi) x = up_ty_ty sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_ty (xi_ty : nat -> nat) (sigma_ty : nat -> ty)
(Eq_ty : forall x, funcomp (var_ty) xi_ty x = sigma_ty x) (s : ty) {struct s}
   : ren_ty xi_ty s = subst_ty sigma_ty s :=
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

Lemma rinstInst'_ty (xi_ty : nat -> nat) (s : ty) :
  ren_ty xi_ty s = subst_ty (funcomp (var_ty) xi_ty) s.
Proof.
exact (rinst_inst_ty xi_ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_ty_pointwise (xi_ty : nat -> nat) :
  pointwise_relation _ eq (ren_ty xi_ty) (subst_ty (funcomp (var_ty) xi_ty)).
Proof.
exact (fun s => rinst_inst_ty xi_ty _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ty (s : ty) : subst_ty (var_ty) s = s.
Proof.
exact (idSubst_ty (var_ty) (fun n => eq_refl) s).
Qed.

Lemma instId'_ty_pointwise : pointwise_relation _ eq (subst_ty (var_ty)) id.
Proof.
exact (fun s => idSubst_ty (var_ty) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_ty (s : ty) : ren_ty id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id s)).
Qed.

Lemma rinstId'_ty_pointwise : pointwise_relation _ eq (@ren_ty id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id s)).
Qed.

Lemma varL'_ty (sigma_ty : nat -> ty) (x : nat) :
  subst_ty sigma_ty (var_ty x) = sigma_ty x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_ty_pointwise (sigma_ty : nat -> ty) :
  pointwise_relation _ eq (funcomp (subst_ty sigma_ty) (var_ty)) sigma_ty.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_ty (xi_ty : nat -> nat) (x : nat) :
  ren_ty xi_ty (var_ty x) = var_ty (xi_ty x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_ty_pointwise (xi_ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty xi_ty) (var_ty))
    (funcomp (var_ty) xi_ty).
Proof.
exact (fun x => eq_refl).
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
exact (fun n => match n with
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
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
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
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
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
         (compRenRen_tm shift id (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm)
            (funcomp shift zeta_ty) (funcomp id zeta_tm) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
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
                  (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n)))).
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
                (funcomp shift zeta_tm) (fun x => eq_refl) (fun x => eq_refl)
                (sigma n'))
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
            (funcomp (up_ty_ty tau_ty) shift) (funcomp (up_ty_tm tau_tm) id)
            (fun x => eq_refl) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_tm tau_ty tau_tm shift id
                  (funcomp (ren_ty shift) tau_ty)
                  (funcomp (ren_tm shift id) tau_tm) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
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
         (compRenSubst_ty id (up_tm_ty tau_ty) (funcomp (up_tm_ty tau_ty) id)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty)
                  (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n)))).
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
             (compRenSubst_tm id shift (up_tm_ty tau_ty) (up_tm_tm tau_tm)
                (funcomp (up_tm_ty tau_ty) id)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_ty tau_tm id shift
                      (funcomp (ren_ty id) tau_ty)
                      (funcomp (ren_tm id shift) tau_tm) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma n')))
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

Lemma renRen_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_tm zeta_ty zeta_tm) (ren_tm xi_ty xi_tm))
    (ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s =>
       compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) :
  pointwise_relation _ eq
    (funcomp (subst_tm tau_ty tau_tm) (ren_tm xi_ty xi_tm))
    (subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm)).
Proof.
exact (fun s =>
       compRenSubst_tm xi_ty xi_tm tau_ty tau_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_tm (subst_tm sigma_ty sigma_tm s) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_tm zeta_ty zeta_tm) (subst_tm sigma_ty sigma_tm))
    (subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
       (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm)).
Proof.
exact (fun s =>
       compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm s) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_tm tau_ty tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) :
  pointwise_relation _ eq
    (funcomp (subst_tm tau_ty tau_tm) (subst_tm sigma_ty sigma_tm))
    (subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
       (funcomp (subst_tm tau_ty tau_tm) sigma_tm)).
Proof.
exact (fun s =>
       compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_ty_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_ty_tm xi) x = up_ty_tm sigma x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma rinstInst_up_tm_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp (var_ty) xi x = sigma x) :
  forall x, funcomp (var_ty) (upRen_tm_ty xi) x = up_tm_ty sigma x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
(sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
(Eq_ty : forall x, funcomp (var_ty) xi_ty x = sigma_ty x)
(Eq_tm : forall x, funcomp (var_tm) xi_tm x = sigma_tm x) (s : tm) {struct s}
   : ren_tm xi_ty xi_tm s = subst_tm sigma_ty sigma_tm s :=
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

Lemma rinstInst'_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat) (s : tm) :
  ren_tm xi_ty xi_tm s =
  subst_tm (funcomp (var_ty) xi_ty) (funcomp (var_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_ty xi_tm _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise (xi_ty : nat -> nat) (xi_tm : nat -> nat) :
  pointwise_relation _ eq (ren_tm xi_ty xi_tm)
    (subst_tm (funcomp (var_ty) xi_ty) (funcomp (var_tm) xi_tm)).
Proof.
exact (fun s =>
       rinst_inst_tm xi_ty xi_tm _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_ty) (var_tm) s = s.
Proof.
exact (idSubst_tm (var_ty) (var_tm) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise :
  pointwise_relation _ eq (subst_tm (var_ty) (var_tm)) id.
Proof.
exact (fun s =>
       idSubst_tm (var_ty) (var_tm) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma rinstId'_tm_pointwise : pointwise_relation _ eq (@ren_tm id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma varL'_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm) (x : nat) :
  subst_tm sigma_ty sigma_tm (var_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise (sigma_ty : nat -> ty) (sigma_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_ty sigma_tm) (var_tm))
    sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat) (x : nat) :
  ren_tm xi_ty xi_tm (var_tm x) = var_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise (xi_ty : nat -> nat) (xi_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm xi_ty xi_tm) (var_tm))
    (funcomp (var_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

Class Up_ty X Y :=
    up_ty : X -> Y.

#[export]Instance Subst_tm : (Subst2 _ _ _ _) := @subst_tm.

#[export]Instance Up_tm_tm : (Up_tm _ _) := @up_tm_tm.

#[export]Instance Up_tm_ty : (Up_ty _ _) := @up_tm_ty.

#[export]Instance Up_ty_tm : (Up_tm _ _) := @up_ty_tm.

#[export]Instance Ren_tm : (Ren2 _ _ _ _) := @ren_tm.

#[export]Instance VarInstance_tm : (Var _ _) := @var_tm.

#[export]Instance Subst_ty : (Subst1 _ _ _) := @subst_ty.

#[export]Instance Up_ty_ty : (Up_ty _ _) := @up_ty_ty.

#[export]Instance Ren_ty : (Ren1 _ _ _) := @ren_ty.

#[export]
Instance VarInstance_ty : (Var _ _) := @var_ty.

Notation "[ sigma_ty ; sigma_tm ]" := (subst_tm sigma_ty sigma_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_ty ; sigma_tm ]" := (subst_tm sigma_ty sigma_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__tm" := up_tm (only printing) : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing) : subst_scope.

Notation "↑__ty" := up_tm_ty (only printing) : subst_scope.

Notation "↑__tm" := up_ty_tm (only printing) : subst_scope.

Notation "⟨ xi_ty ; xi_tm ⟩" := (ren_tm xi_ty xi_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_ty ; xi_tm ⟩" := (ren_tm xi_ty xi_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing) : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
  ( at level 5, format "x __tm", only printing) : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm") :
  subst_scope.

Notation "[ sigma_ty ]" := (subst_ty sigma_ty)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_ty ]" := (subst_ty sigma_ty s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__ty" := up_ty (only printing) : subst_scope.

Notation "↑__ty" := up_ty_ty (only printing) : subst_scope.

Notation "⟨ xi_ty ⟩" := (ren_ty xi_ty)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_ty ⟩" := (ren_ty xi_ty s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := var_ty ( at level 1, only printing) : subst_scope.

Notation "x '__ty'" := (@ids _ _ VarInstance_ty x)
  ( at level 5, format "x __ty", only printing) : subst_scope.

Notation "x '__ty'" := (var_ty x) ( at level 5, format "x __ty") :
  subst_scope.

Instance subst_tm_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@subst_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_ty f_tm s = subst_tm g_ty g_tm t')
         (ext_tm f_ty f_tm g_ty g_tm Eq_ty Eq_tm s) t Eq_st).
Qed.

Instance subst_tm_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_tm g_tm Eq_tm s =>
       ext_tm f_ty f_tm g_ty g_tm Eq_ty Eq_tm s).
Qed.

Instance ren_tm_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@ren_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_ty f_tm s = ren_tm g_ty g_tm t')
         (extRen_tm f_ty f_tm g_ty g_tm Eq_ty Eq_tm s) t Eq_st).
Qed.

Instance ren_tm_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_tm g_tm Eq_tm s =>
       extRen_tm f_ty f_tm g_ty g_tm Eq_ty Eq_tm s).
Qed.

Instance subst_ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s (fun t' => subst_ty f_ty s = subst_ty g_ty t')
         (ext_ty f_ty g_ty Eq_ty s) t Eq_st).
Qed.

Instance subst_ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s => ext_ty f_ty g_ty Eq_ty s).
Qed.

Instance ren_ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s (fun t' => ren_ty f_ty s = ren_ty g_ty t')
         (extRen_ty f_ty g_ty Eq_ty s) t Eq_st).
Qed.

Instance ren_ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s => extRen_ty f_ty g_ty Eq_ty s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                      Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                      VarInstance_tm, Var, ids, Ren_tm, Ren2, ren2, Up_ty_tm,
                      Up_tm, up_tm, Up_tm_ty, Up_ty, up_ty, Up_tm_tm, Up_tm,
                      up_tm, Subst_tm, Subst2, subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_ty, Var, ids,
                                            Ren_ty, Ren1, ren1, Up_ty_ty,
                                            Up_ty, up_ty, Subst_ty, Subst1,
                                            subst1, VarInstance_tm, Var, ids,
                                            Ren_tm, Ren2, ren2, Up_ty_tm,
                                            Up_tm, up_tm, Up_tm_ty, Up_ty,
                                            up_ty, Up_tm_tm, Up_tm, up_tm,
                                            Subst_tm, Subst2, subst2 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite substSubst_ty_pointwise
                 | progress setoid_rewrite substSubst_ty
                 | progress setoid_rewrite substRen_ty_pointwise
                 | progress setoid_rewrite substRen_ty
                 | progress setoid_rewrite renSubst_ty_pointwise
                 | progress setoid_rewrite renSubst_ty
                 | progress setoid_rewrite renRen'_ty_pointwise
                 | progress setoid_rewrite renRen_ty
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress setoid_rewrite varLRen'_ty_pointwise
                 | progress setoid_rewrite varLRen'_ty
                 | progress setoid_rewrite varL'_ty_pointwise
                 | progress setoid_rewrite varL'_ty
                 | progress setoid_rewrite rinstId'_ty_pointwise
                 | progress setoid_rewrite rinstId'_ty
                 | progress setoid_rewrite instId'_ty_pointwise
                 | progress setoid_rewrite instId'_ty
                 | progress
                    unfold up_tm_tm, up_tm_ty, up_ty_tm, upRen_tm_tm,
                     upRen_tm_ty, upRen_ty_tm, up_ty_ty, upRen_ty_ty, up_ren
                 | progress cbn[subst_tm ren_tm subst_ty ren_ty]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                  Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                  VarInstance_tm, Var, ids, Ren_tm, Ren2, ren2, Up_ty_tm,
                  Up_tm, up_tm, Up_tm_ty, Up_ty, up_ty, Up_tm_tm, Up_tm,
                  up_tm, Subst_tm, Subst2, subst2 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm;
                  try setoid_rewrite rinstInst'_ty_pointwise;
                  try setoid_rewrite rinstInst'_ty.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm;
                  try setoid_rewrite_left rinstInst'_ty_pointwise;
                  try setoid_rewrite_left rinstInst'_ty.

End Core.

Module Fext.

Import
Core.

Lemma renRen'_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat) :
  funcomp (ren_ty zeta_ty) (ren_ty xi_ty) = ren_ty (funcomp zeta_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_ty xi_ty zeta_ty n)).
Qed.

Lemma renSubst'_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty) :
  funcomp (subst_ty tau_ty) (ren_ty xi_ty) = subst_ty (funcomp tau_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_ty xi_ty tau_ty n)).
Qed.

Lemma substRen'_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) :
  funcomp (ren_ty zeta_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_ty sigma_ty zeta_ty n)).
Qed.

Lemma substSubst'_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty) :
  funcomp (subst_ty tau_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_ty sigma_ty tau_ty n)).
Qed.

Lemma rinstInst_ty (xi_ty : nat -> nat) :
  ren_ty xi_ty = subst_ty (funcomp (var_ty) xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_ty xi_ty _ (fun n => eq_refl) x)).
Qed.

Lemma instId_ty : subst_ty (var_ty) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_ty (var_ty) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_ty : @ren_ty id = id.
Proof.
exact (eq_trans (rinstInst_ty (id _)) instId_ty).
Qed.

Lemma varL_ty (sigma_ty : nat -> ty) :
  funcomp (subst_ty sigma_ty) (var_ty) = sigma_ty.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_ty (xi_ty : nat -> nat) :
  funcomp (ren_ty xi_ty) (var_ty) = funcomp (var_ty) xi_ty.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) :
  funcomp (ren_tm zeta_ty zeta_tm) (ren_tm xi_ty xi_tm) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_tm xi_ty xi_tm zeta_ty zeta_tm n)).
Qed.

Lemma renSubst'_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) :
  funcomp (subst_tm tau_ty tau_tm) (ren_tm xi_ty xi_tm) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_tm xi_ty xi_tm tau_ty tau_tm n)).
Qed.

Lemma substRen'_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) :
  funcomp (ren_tm zeta_ty zeta_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_tm sigma_ty sigma_tm zeta_ty zeta_tm n)).
Qed.

Lemma substSubst'_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) :
  funcomp (subst_tm tau_ty tau_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_tm tau_ty tau_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_tm sigma_ty sigma_tm tau_ty tau_tm n)).
Qed.

Lemma rinstInst_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat) :
  ren_tm xi_ty xi_tm =
  subst_tm (funcomp (var_ty) xi_ty) (funcomp (var_tm) xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          rinst_inst_tm xi_ty xi_tm _ _ (fun n => eq_refl) (fun n => eq_refl)
            x)).
Qed.

Lemma instId_tm : subst_tm (var_ty) (var_tm) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          idSubst_tm (var_ty) (var_tm) (fun n => eq_refl) (fun n => eq_refl)
            (id x))).
Qed.

Lemma rinstId_tm : @ren_tm id id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _) (id _)) instId_tm).
Qed.

Lemma varL_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm) :
  funcomp (subst_tm sigma_ty sigma_tm) (var_tm) = sigma_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat) :
  funcomp (ren_tm xi_ty xi_tm) (var_tm) = funcomp (var_tm) xi_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Ltac asimpl_fext' := repeat (first
                      [ progress rewrite ?substSubst_tm_pointwise
                      | progress rewrite ?substSubst_tm
                      | progress rewrite ?substRen_tm_pointwise
                      | progress rewrite ?substRen_tm
                      | progress rewrite ?renSubst_tm_pointwise
                      | progress rewrite ?renSubst_tm
                      | progress rewrite ?renRen'_tm_pointwise
                      | progress rewrite ?renRen_tm
                      | progress rewrite ?substSubst_ty_pointwise
                      | progress rewrite ?substSubst_ty
                      | progress rewrite ?substRen_ty_pointwise
                      | progress rewrite ?substRen_ty
                      | progress rewrite ?renSubst_ty_pointwise
                      | progress rewrite ?renSubst_ty
                      | progress rewrite ?renRen'_ty_pointwise
                      | progress rewrite ?renRen_ty
                      | progress rewrite ?varLRen_tm
                      | progress rewrite ?varL_tm
                      | progress rewrite ?rinstId_tm
                      | progress rewrite ?instId_tm
                      | progress rewrite ?substSubst'_tm
                      | progress rewrite ?substRen'_tm
                      | progress rewrite ?renSubst'_tm
                      | progress rewrite ?renRen'_tm
                      | progress rewrite ?varLRen_ty
                      | progress rewrite ?varL_ty
                      | progress rewrite ?rinstId_ty
                      | progress rewrite ?instId_ty
                      | progress rewrite ?substSubst'_ty
                      | progress rewrite ?substRen'_ty
                      | progress rewrite ?renSubst'_ty
                      | progress rewrite ?renRen'_ty
                      | progress
                         unfold up_tm_tm, up_tm_ty, up_ty_tm, upRen_tm_tm,
                          upRen_tm_ty, upRen_ty_tm, up_ty_ty, upRen_ty_ty,
                          up_ren
                      | progress cbn[subst_tm ren_tm subst_ty ren_ty]
                      | fsimpl_fext ]).

Ltac asimpl_fext := check_no_evars; repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                       Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                       VarInstance_tm, Var, ids, Ren_tm, Ren2, ren2,
                       Up_ty_tm, Up_tm, up_tm, Up_tm_ty, Up_ty, up_ty,
                       Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst2, subst2 
                       in *; asimpl_fext'; repeat try unfold_funcomp.

Tactic Notation "asimpl_fext" "in" hyp(J) := revert J; asimpl_fext; intros J.

Tactic Notation "auto_case_fext" := auto_case ltac:(asimpl_fext; cbn; eauto).

Ltac substify_fext := auto_unfold; try repeat erewrite ?rinstInst_tm;
                       try repeat erewrite ?rinstInst_ty.

Ltac renamify_fext := auto_unfold; try repeat erewrite <- ?rinstInst_tm;
                       try repeat erewrite <- ?rinstInst_ty.

End Fext.

Module Extra.

Import Core.

#[export]Hint Opaque subst_tm: rewrite.

#[export]Hint Opaque ren_tm: rewrite.

#[export]Hint Opaque subst_ty: rewrite.

#[export]Hint Opaque ren_ty: rewrite.

End Extra.

Module interface.

Export Core.

Export Fext.

Export Extra.

End interface.

Export interface.

