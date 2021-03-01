Require Import axioms unscoped header_extensible.
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
Definition upRen_ty_ty (xi : nat -> nat) : nat -> nat := up_ren xi.
Fixpoint ren_ty (xi_ty : nat -> nat) (s : ty) : ty :=
  match s with
  | var_ty s0 => var_ty (xi_ty s0)
  | arr s0 s1 => arr (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | all s0 => all (ren_ty (upRen_ty_ty xi_ty) s0)
  end.
Definition up_ty_ty (sigma : nat -> ty) : nat -> ty :=
  scons (var_ty var_zero) (funcomp (ren_ty shift) sigma).
Fixpoint subst_ty (sigma_ty : nat -> ty) (s : ty) : ty :=
  match s with
  | var_ty s0 => sigma_ty s0
  | arr s0 s1 => arr (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | all s0 => all (subst_ty (up_ty_ty sigma_ty) s0)
  end.
Definition upId_ty_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x)
  : forall x, up_ty_ty sigma x = var_ty x :=
  fun n =>
  match n with
  | S n' => ap (ren_ty shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint idSubst_ty (sigma_ty : nat -> ty)
(Eq_ty : forall x, sigma_ty x = var_ty x) (s : ty) : subst_ty sigma_ty s = s
:=
  match s with
  | var_ty s0 => Eq_ty s0
  | arr s0 s1 =>
      congr_arr (idSubst_ty sigma_ty Eq_ty s0) (idSubst_ty sigma_ty Eq_ty s1)
  | all s0 =>
      congr_all (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ Eq_ty) s0)
  end.
Definition upExtRen_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_ty xi x = upRen_ty_ty zeta x :=
  fun n => match n with
           | S n' => ap shift (Eq n')
           | O => eq_refl
           end.
Fixpoint extRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x) (s : ty) :
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
Definition upExt_ty_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_ty sigma x = up_ty_ty tau x :=
  fun n =>
  match n with
  | S n' => ap (ren_ty shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint ext_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty)
(Eq_ty : forall x, sigma_ty x = tau_ty x) (s : ty) :
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
Definition up_ren_ren_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x :=
  up_ren_ren xi zeta rho Eq.
Fixpoint compRenRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat)
(rho_ty : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(s : ty) : ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty rho_ty s :=
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
Definition up_ren_subst_ty_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x :=
  fun n =>
  match n with
  | S n' => ap (ren_ty shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint compRenSubst_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x) (s : ty) :
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
Definition up_subst_ren_ty_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_ty_ty zeta_ty)) (up_ty_ty sigma) x =
  up_ty_ty theta x :=
  fun n =>
  match n with
  | S n' =>
      eq_trans
        (compRenRen_ty shift (upRen_ty_ty zeta_ty) (funcomp shift zeta_ty)
           (fun x => eq_refl) (sigma n'))
        (eq_trans
           (eq_sym
              (compRenRen_ty zeta_ty shift (funcomp shift zeta_ty)
                 (fun x => eq_refl) (sigma n'))) (ap (ren_ty shift) (Eq n')))
  | O => eq_refl
  end.
Fixpoint compSubstRen_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x) 
(s : ty) : ren_ty zeta_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
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
Definition up_subst_subst_ty_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_ty_ty tau_ty)) (up_ty_ty sigma) x = up_ty_ty theta x :=
  fun n =>
  match n with
  | S n' =>
      eq_trans
        (compRenSubst_ty shift (up_ty_ty tau_ty)
           (funcomp (up_ty_ty tau_ty) shift) (fun x => eq_refl) (sigma n'))
        (eq_trans
           (eq_sym
              (compSubstRen_ty tau_ty shift (funcomp (ren_ty shift) tau_ty)
                 (fun x => eq_refl) (sigma n'))) (ap (ren_ty shift) (Eq n')))
  | O => eq_refl
  end.
Fixpoint compSubstSubst_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(s : ty) : subst_ty tau_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
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
Definition rinstInst_up_ty_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp var_ty xi x = sigma x) :
  forall x, funcomp var_ty (upRen_ty_ty xi) x = up_ty_ty sigma x :=
  fun n =>
  match n with
  | S n' => ap (ren_ty shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint rinst_inst_ty (xi_ty : nat -> nat) (sigma_ty : nat -> ty)
(Eq_ty : forall x, funcomp var_ty xi_ty x = sigma_ty x) (s : ty) :
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
Lemma rinstInst_ty (xi_ty : nat -> nat) :
  ren_ty xi_ty = subst_ty (funcomp var_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_ty xi_ty _ (fun n => eq_refl) x)).
Qed.
Lemma instId_ty : subst_ty var_ty = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_ty var_ty (fun n => eq_refl) (id x))).
Qed.
Lemma rinstId_ty : @ren_ty id = id.
Proof.
exact (eq_trans (rinstInst_ty (id _)) instId_ty).
Qed.
Lemma varL_ty (sigma_ty : nat -> ty) :
  funcomp (subst_ty sigma_ty) var_ty = sigma_ty.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma varLRen_ty (xi_ty : nat -> nat) :
  funcomp (ren_ty xi_ty) var_ty = funcomp var_ty xi_ty.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma renRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty (funcomp zeta_ty xi_ty) s.
Proof.
exact (compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma renRen'_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat) :
  funcomp (ren_ty zeta_ty) (ren_ty xi_ty) = ren_ty (funcomp zeta_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_ty xi_ty zeta_ty n)).
Qed.
Lemma compRen_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s.
Proof.
exact (compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma compRen'_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) :
  funcomp (ren_ty zeta_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_ty sigma_ty zeta_ty n)).
Qed.
Lemma renComp_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (ren_ty xi_ty s) = subst_ty (funcomp tau_ty xi_ty) s.
Proof.
exact (compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma renComp'_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty) :
  funcomp (subst_ty tau_ty) (ren_ty xi_ty) = subst_ty (funcomp tau_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_ty xi_ty tau_ty n)).
Qed.
Lemma compComp_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s.
Proof.
exact (compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma compComp'_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty) :
  funcomp (subst_ty tau_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_ty sigma_ty tau_ty n)).
Qed.
Inductive tm : Type :=
  | app : tm -> tm -> tm
  | tapp : tm -> ty -> tm
  | vt : vl -> tm
with vl : Type :=
  | var_vl : nat -> vl
  | lam : ty -> tm -> vl
  | tlam : tm -> vl.
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
Lemma congr_vt {s0 : vl} {t0 : vl} (H0 : s0 = t0) : vt s0 = vt t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => vt x) H0)).
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
Definition upRen_ty_vl (xi : nat -> nat) : nat -> nat := xi.
Definition upRen_vl_ty (xi : nat -> nat) : nat -> nat := xi.
Definition upRen_vl_vl (xi : nat -> nat) : nat -> nat := up_ren xi.
Fixpoint ren_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat) (s : tm) : tm :=
  match s with
  | app s0 s1 => app (ren_tm xi_ty xi_vl s0) (ren_tm xi_ty xi_vl s1)
  | tapp s0 s1 => tapp (ren_tm xi_ty xi_vl s0) (ren_ty xi_ty s1)
  | vt s0 => vt (ren_vl xi_ty xi_vl s0)
  end
with ren_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat) (s : vl) : vl :=
  match s with
  | var_vl s0 => var_vl (xi_vl s0)
  | lam s0 s1 =>
      lam (ren_ty xi_ty s0)
        (ren_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl) s1)
  | tlam s0 => tlam (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl) s0)
  end.
Definition up_ty_vl (sigma : nat -> vl) : nat -> vl :=
  funcomp (ren_vl shift id) sigma.
Definition up_vl_ty (sigma : nat -> ty) : nat -> ty :=
  funcomp (ren_ty id) sigma.
Definition up_vl_vl (sigma : nat -> vl) : nat -> vl :=
  scons (var_vl var_zero) (funcomp (ren_vl id shift) sigma).
Fixpoint subst_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl) (s : tm) : tm
:=
  match s with
  | app s0 s1 =>
      app (subst_tm sigma_ty sigma_vl s0) (subst_tm sigma_ty sigma_vl s1)
  | tapp s0 s1 => tapp (subst_tm sigma_ty sigma_vl s0) (subst_ty sigma_ty s1)
  | vt s0 => vt (subst_vl sigma_ty sigma_vl s0)
  end
with subst_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl) (s : vl) : vl :=
  match s with
  | var_vl s0 => sigma_vl s0
  | lam s0 s1 =>
      lam (subst_ty sigma_ty s0)
        (subst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl) s1)
  | tlam s0 => tlam (subst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl) s0)
  end.
Definition upId_ty_vl (sigma : nat -> vl) (Eq : forall x, sigma x = var_vl x)
  : forall x, up_ty_vl sigma x = var_vl x :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition upId_vl_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x)
  : forall x, up_vl_ty sigma x = var_ty x := fun n => ap (ren_ty id) (Eq n).
Definition upId_vl_vl (sigma : nat -> vl) (Eq : forall x, sigma x = var_vl x)
  : forall x, up_vl_vl sigma x = var_vl x :=
  fun n =>
  match n with
  | S n' => ap (ren_vl id shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint idSubst_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = var_ty x)
(Eq_vl : forall x, sigma_vl x = var_vl x) (s : tm) :
subst_tm sigma_ty sigma_vl s = s :=
  match s with
  | app s0 s1 =>
      congr_app (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s1)
  | tapp s0 s1 =>
      congr_tapp (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | vt s0 => congr_vt (idSubst_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
  end
with idSubst_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = var_ty x)
(Eq_vl : forall x, sigma_vl x = var_vl x) (s : vl) :
subst_vl sigma_ty sigma_vl s = s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | lam s0 s1 =>
      congr_lam (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (upId_vl_ty _ Eq_ty) (upId_vl_vl _ Eq_vl) s1)
  | tlam s0 =>
      congr_tlam
        (idSubst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (upId_ty_ty _ Eq_ty) (upId_ty_vl _ Eq_vl) s0)
  end.
Definition upExtRen_ty_vl (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_vl xi x = upRen_ty_vl zeta x := fun n => Eq n.
Definition upExtRen_vl_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_vl_ty xi x = upRen_vl_ty zeta x := fun n => Eq n.
Definition upExtRen_vl_vl (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_vl_vl xi x = upRen_vl_vl zeta x :=
  fun n => match n with
           | S n' => ap shift (Eq n')
           | O => eq_refl
           end.
Fixpoint extRen_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_vl : forall x, xi_vl x = zeta_vl x) (s : tm) :
ren_tm xi_ty xi_vl s = ren_tm zeta_ty zeta_vl s :=
  match s with
  | app s0 s1 =>
      congr_app (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
        (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s1)
  | tapp s0 s1 =>
      congr_tapp (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | vt s0 => congr_vt (extRen_vl xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
  end
with extRen_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_vl : forall x, xi_vl x = zeta_vl x) (s : vl) :
ren_vl xi_ty xi_vl s = ren_vl zeta_ty zeta_vl s :=
  match s with
  | var_vl s0 => ap var_vl (Eq_vl s0)
  | lam s0 s1 =>
      congr_lam (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl)
           (upExtRen_vl_ty _ _ Eq_ty) (upExtRen_vl_vl _ _ Eq_vl) s1)
  | tlam s0 =>
      congr_tlam
        (extRen_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl)
           (upExtRen_ty_ty _ _ Eq_ty) (upExtRen_ty_vl _ _ Eq_vl) s0)
  end.
Definition upExt_ty_vl (sigma : nat -> vl) (tau : nat -> vl)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_vl sigma x = up_ty_vl tau x :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition upExt_vl_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_vl_ty sigma x = up_vl_ty tau x :=
  fun n => ap (ren_ty id) (Eq n).
Definition upExt_vl_vl (sigma : nat -> vl) (tau : nat -> vl)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_vl_vl sigma x = up_vl_vl tau x :=
  fun n =>
  match n with
  | S n' => ap (ren_vl id shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint ext_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_vl : forall x, sigma_vl x = tau_vl x) (s : tm) :
subst_tm sigma_ty sigma_vl s = subst_tm tau_ty tau_vl s :=
  match s with
  | app s0 s1 =>
      congr_app (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
        (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s1)
  | tapp s0 s1 =>
      congr_tapp (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | vt s0 => congr_vt (ext_vl sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
  end
with ext_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_vl : forall x, sigma_vl x = tau_vl x) (s : vl) :
subst_vl sigma_ty sigma_vl s = subst_vl tau_ty tau_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | lam s0 s1 =>
      congr_lam (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl) (up_vl_ty tau_ty)
           (up_vl_vl tau_vl) (upExt_vl_ty _ _ Eq_ty) (upExt_vl_vl _ _ Eq_vl)
           s1)
  | tlam s0 =>
      congr_tlam
        (ext_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl) (up_ty_ty tau_ty)
           (up_ty_vl tau_vl) (upExt_ty_ty _ _ Eq_ty) (upExt_ty_vl _ _ Eq_vl)
           s0)
  end.
Definition up_ren_ren_ty_vl (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_vl zeta) (upRen_ty_vl xi) x = upRen_ty_vl rho x :=
  Eq.
Definition up_ren_ren_vl_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_vl_ty zeta) (upRen_vl_ty xi) x = upRen_vl_ty rho x :=
  Eq.
Definition up_ren_ren_vl_vl (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_vl_vl zeta) (upRen_vl_vl xi) x = upRen_vl_vl rho x :=
  up_ren_ren xi zeta rho Eq.
Fixpoint compRenRen_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (rho_ty : nat -> nat)
(rho_vl : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_vl : forall x, funcomp zeta_vl xi_vl x = rho_vl x) (s : tm) :
ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s) = ren_tm rho_ty rho_vl s :=
  match s with
  | app s0 s1 =>
      congr_app
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0)
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s1)
  | tapp s0 s1 =>
      congr_tapp
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0) (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | vt s0 =>
      congr_vt
        (compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0)
  end
with compRenRen_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (rho_ty : nat -> nat)
(rho_vl : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_vl : forall x, funcomp zeta_vl xi_vl x = rho_vl x) (s : vl) :
ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s) = ren_vl rho_ty rho_vl s :=
  match s with
  | var_vl s0 => ap var_vl (Eq_vl s0)
  | lam s0 s1 =>
      congr_lam (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl) (upRen_vl_ty rho_ty)
           (upRen_vl_vl rho_vl) Eq_ty (up_ren_ren _ _ _ Eq_vl) s1)
  | tlam s0 =>
      congr_tlam
        (compRenRen_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl) (upRen_ty_ty rho_ty)
           (upRen_ty_vl rho_vl) (up_ren_ren _ _ _ Eq_ty) Eq_vl s0)
  end.
Definition up_ren_subst_ty_vl (xi : nat -> nat) (tau : nat -> vl)
  (theta : nat -> vl) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_vl tau) (upRen_ty_vl xi) x = up_ty_vl theta x :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition up_ren_subst_vl_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_vl_ty tau) (upRen_vl_ty xi) x = up_vl_ty theta x :=
  fun n => ap (ren_ty id) (Eq n).
Definition up_ren_subst_vl_vl (xi : nat -> nat) (tau : nat -> vl)
  (theta : nat -> vl) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_vl_vl tau) (upRen_vl_vl xi) x = up_vl_vl theta x :=
  fun n =>
  match n with
  | S n' => ap (ren_vl id shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint compRenSubst_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_vl : forall x, funcomp tau_vl xi_vl x = theta_vl x) (s : tm) :
subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s) = subst_tm theta_ty theta_vl s
:=
  match s with
  | app s0 s1 =>
      congr_app
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0)
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s1)
  | tapp s0 s1 =>
      congr_tapp
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0) (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | vt s0 =>
      congr_vt
        (compRenSubst_vl xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0)
  end
with compRenSubst_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_vl : forall x, funcomp tau_vl xi_vl x = theta_vl x) (s : vl) :
subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s) = subst_vl theta_ty theta_vl s
:=
  match s with
  | var_vl s0 => Eq_vl s0
  | lam s0 s1 =>
      congr_lam (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (up_vl_ty tau_ty) (up_vl_vl tau_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_ren_subst_vl_ty _ _ _ Eq_ty)
           (up_ren_subst_vl_vl _ _ _ Eq_vl) s1)
  | tlam s0 =>
      congr_tlam
        (compRenSubst_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (up_ty_ty tau_ty) (up_ty_vl tau_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_ren_subst_ty_ty _ _ _ Eq_ty)
           (up_ren_subst_ty_vl _ _ _ Eq_vl) s0)
  end.
Definition up_subst_ren_ty_vl (sigma : nat -> vl) (zeta_ty : nat -> nat)
  (zeta_vl : nat -> nat) (theta : nat -> vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl))
    (up_ty_vl sigma) x = up_ty_vl theta x :=
  fun n =>
  eq_trans
    (compRenRen_vl shift id (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl)
       (funcomp shift zeta_ty) (funcomp id zeta_vl) (fun x => eq_refl)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_vl zeta_ty zeta_vl shift id (funcomp shift zeta_ty)
             (funcomp id zeta_vl) (fun x => eq_refl) (fun x => eq_refl)
             (sigma n))) (ap (ren_vl shift id) (Eq n))).
Definition up_subst_ren_vl_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_vl_ty zeta_ty)) (up_vl_ty sigma) x =
  up_vl_ty theta x :=
  fun n =>
  eq_trans
    (compRenRen_ty id (upRen_vl_ty zeta_ty) (funcomp id zeta_ty)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_ty zeta_ty id (funcomp id zeta_ty) (fun x => eq_refl)
             (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_ren_vl_vl (sigma : nat -> vl) (zeta_ty : nat -> nat)
  (zeta_vl : nat -> nat) (theta : nat -> vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl))
    (up_vl_vl sigma) x = up_vl_vl theta x :=
  fun n =>
  match n with
  | S n' =>
      eq_trans
        (compRenRen_vl id shift (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl)
           (funcomp id zeta_ty) (funcomp shift zeta_vl) (fun x => eq_refl)
           (fun x => eq_refl) (sigma n'))
        (eq_trans
           (eq_sym
              (compRenRen_vl zeta_ty zeta_vl id shift (funcomp id zeta_ty)
                 (funcomp shift zeta_vl) (fun x => eq_refl)
                 (fun x => eq_refl) (sigma n')))
           (ap (ren_vl id shift) (Eq n')))
  | O => eq_refl
  end.
Fixpoint compSubstRen_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x = theta_vl x)
(s : tm) :
ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s) =
subst_tm theta_ty theta_vl s :=
  match s with
  | app s0 s1 =>
      congr_app
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s1)
  | tapp s0 s1 =>
      congr_tapp
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | vt s0 =>
      congr_vt
        (compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
  end
with compSubstRen_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x = theta_vl x)
(s : vl) :
ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s) =
subst_vl theta_ty theta_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | lam s0 s1 =>
      congr_lam (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_subst_ren_vl_ty _ _ _ Eq_ty)
           (up_subst_ren_vl_vl _ _ _ _ Eq_vl) s1)
  | tlam s0 =>
      congr_tlam
        (compSubstRen_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_subst_ren_ty_ty _ _ _ Eq_ty)
           (up_subst_ren_ty_vl _ _ _ _ Eq_vl) s0)
  end.
Definition up_subst_subst_ty_vl (sigma : nat -> vl) (tau_ty : nat -> ty)
  (tau_vl : nat -> vl) (theta : nat -> vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_ty_ty tau_ty) (up_ty_vl tau_vl)) (up_ty_vl sigma) x =
  up_ty_vl theta x :=
  fun n =>
  eq_trans
    (compRenSubst_vl shift id (up_ty_ty tau_ty) (up_ty_vl tau_vl)
       (funcomp (up_ty_ty tau_ty) shift) (funcomp (up_ty_vl tau_vl) id)
       (fun x => eq_refl) (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compSubstRen_vl tau_ty tau_vl shift id
             (funcomp (ren_ty shift) tau_ty)
             (funcomp (ren_vl shift id) tau_vl) (fun x => eq_refl)
             (fun x => eq_refl) (sigma n))) (ap (ren_vl shift id) (Eq n))).
Definition up_subst_subst_vl_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_vl_ty tau_ty)) (up_vl_ty sigma) x = up_vl_ty theta x :=
  fun n =>
  eq_trans
    (compRenSubst_ty id (up_vl_ty tau_ty) (funcomp (up_vl_ty tau_ty) id)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty)
             (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_subst_vl_vl (sigma : nat -> vl) (tau_ty : nat -> ty)
  (tau_vl : nat -> vl) (theta : nat -> vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_vl_ty tau_ty) (up_vl_vl tau_vl)) (up_vl_vl sigma) x =
  up_vl_vl theta x :=
  fun n =>
  match n with
  | S n' =>
      eq_trans
        (compRenSubst_vl id shift (up_vl_ty tau_ty) (up_vl_vl tau_vl)
           (funcomp (up_vl_ty tau_ty) id) (funcomp (up_vl_vl tau_vl) shift)
           (fun x => eq_refl) (fun x => eq_refl) (sigma n'))
        (eq_trans
           (eq_sym
              (compSubstRen_vl tau_ty tau_vl id shift
                 (funcomp (ren_ty id) tau_ty)
                 (funcomp (ren_vl id shift) tau_vl) (fun x => eq_refl)
                 (fun x => eq_refl) (sigma n')))
           (ap (ren_vl id shift) (Eq n')))
  | O => eq_refl
  end.
Fixpoint compSubstSubst_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (subst_vl tau_ty tau_vl) sigma_vl x = theta_vl x)
(s : tm) :
subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s) =
subst_tm theta_ty theta_vl s :=
  match s with
  | app s0 s1 =>
      congr_app
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s1)
  | tapp s0 s1 =>
      congr_tapp
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | vt s0 =>
      congr_vt
        (compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
  end
with compSubstSubst_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (subst_vl tau_ty tau_vl) sigma_vl x = theta_vl x)
(s : vl) :
subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s) =
subst_vl theta_ty theta_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | lam s0 s1 =>
      congr_lam (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (up_vl_ty tau_ty) (up_vl_vl tau_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_subst_subst_vl_ty _ _ _ Eq_ty)
           (up_subst_subst_vl_vl _ _ _ _ Eq_vl) s1)
  | tlam s0 =>
      congr_tlam
        (compSubstSubst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (up_ty_ty tau_ty) (up_ty_vl tau_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_subst_subst_ty_ty _ _ _ Eq_ty)
           (up_subst_subst_ty_vl _ _ _ _ Eq_vl) s0)
  end.
Definition rinstInst_up_ty_vl (xi : nat -> nat) (sigma : nat -> vl)
  (Eq : forall x, funcomp var_vl xi x = sigma x) :
  forall x, funcomp var_vl (upRen_ty_vl xi) x = up_ty_vl sigma x :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition rinstInst_up_vl_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp var_ty xi x = sigma x) :
  forall x, funcomp var_ty (upRen_vl_ty xi) x = up_vl_ty sigma x :=
  fun n => ap (ren_ty id) (Eq n).
Definition rinstInst_up_vl_vl (xi : nat -> nat) (sigma : nat -> vl)
  (Eq : forall x, funcomp var_vl xi x = sigma x) :
  forall x, funcomp var_vl (upRen_vl_vl xi) x = up_vl_vl sigma x :=
  fun n =>
  match n with
  | S n' => ap (ren_vl id shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint rinst_inst_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, funcomp var_ty xi_ty x = sigma_ty x)
(Eq_vl : forall x, funcomp var_vl xi_vl x = sigma_vl x) (s : tm) :
ren_tm xi_ty xi_vl s = subst_tm sigma_ty sigma_vl s :=
  match s with
  | app s0 s1 =>
      congr_app (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s1)
  | tapp s0 s1 =>
      congr_tapp (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | vt s0 =>
      congr_vt (rinst_inst_vl xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
  end
with rinst_inst_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, funcomp var_ty xi_ty x = sigma_ty x)
(Eq_vl : forall x, funcomp var_vl xi_vl x = sigma_vl x) (s : vl) :
ren_vl xi_ty xi_vl s = subst_vl sigma_ty sigma_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | lam s0 s1 =>
      congr_lam (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (rinstInst_up_vl_ty _ _ Eq_ty) (rinstInst_up_vl_vl _ _ Eq_vl) s1)
  | tlam s0 =>
      congr_tlam
        (rinst_inst_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (rinstInst_up_ty_ty _ _ Eq_ty) (rinstInst_up_ty_vl _ _ Eq_vl) s0)
  end.
Lemma rinstInst_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat) :
  ren_tm xi_ty xi_vl = subst_tm (funcomp var_ty xi_ty) (funcomp var_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_tm xi_ty xi_vl _ _ (fun n => eq_refl)
                   (fun n => eq_refl) x)).
Qed.
Lemma rinstInst_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat) :
  ren_vl xi_ty xi_vl = subst_vl (funcomp var_ty xi_ty) (funcomp var_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_vl xi_ty xi_vl _ _ (fun n => eq_refl)
                   (fun n => eq_refl) x)).
Qed.
Lemma instId_tm : subst_tm var_ty var_vl = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_tm var_ty var_vl (fun n => eq_refl)
                   (fun n => eq_refl) (id x))).
Qed.
Lemma instId_vl : subst_vl var_ty var_vl = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_vl var_ty var_vl (fun n => eq_refl)
                   (fun n => eq_refl) (id x))).
Qed.
Lemma rinstId_tm : @ren_tm id id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _) (id _)) instId_tm).
Qed.
Lemma rinstId_vl : @ren_vl id id = id.
Proof.
exact (eq_trans (rinstInst_vl (id _) (id _)) instId_vl).
Qed.
Lemma varL_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl) :
  funcomp (subst_vl sigma_ty sigma_vl) var_vl = sigma_vl.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma varLRen_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat) :
  funcomp (ren_vl xi_ty xi_vl) var_vl = funcomp var_vl xi_vl.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma renRen_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s.
Proof.
exact (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renRen'_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  funcomp (ren_tm zeta_ty zeta_vl) (ren_tm xi_ty xi_vl) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_tm xi_ty xi_vl zeta_ty zeta_vl n)).
Qed.
Lemma renRen_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : vl) :
  ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s) =
  ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s.
Proof.
exact (compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renRen'_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  funcomp (ren_vl zeta_ty zeta_vl) (ren_vl xi_ty xi_vl) =
  ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_vl xi_ty xi_vl zeta_ty zeta_vl n)).
Qed.
Lemma compRen_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s.
Proof.
exact (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compRen'_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  funcomp (ren_tm zeta_ty zeta_vl) (subst_tm sigma_ty sigma_vl) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_tm sigma_ty sigma_vl zeta_ty zeta_vl n)).
Qed.
Lemma compRen_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : vl) :
  ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s) =
  subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s.
Proof.
exact (compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compRen'_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  funcomp (ren_vl zeta_ty zeta_vl) (subst_vl sigma_ty sigma_vl) =
  subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_vl sigma_ty sigma_vl zeta_ty zeta_vl n)).
Qed.
Lemma renComp_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : tm) :
  subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s.
Proof.
exact (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renComp'_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  funcomp (subst_tm tau_ty tau_vl) (ren_tm xi_ty xi_vl) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_tm xi_ty xi_vl tau_ty tau_vl n)).
Qed.
Lemma renComp_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : vl) :
  subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s) =
  subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s.
Proof.
exact (compRenSubst_vl xi_ty xi_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renComp'_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  funcomp (subst_vl tau_ty tau_vl) (ren_vl xi_ty xi_vl) =
  subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_vl xi_ty xi_vl tau_ty tau_vl n)).
Qed.
Lemma compComp_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : tm) :
  subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s.
Proof.
exact (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compComp'_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  funcomp (subst_tm tau_ty tau_vl) (subst_tm sigma_ty sigma_vl) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_tm sigma_ty sigma_vl tau_ty tau_vl n)).
Qed.
Lemma compComp_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : vl) :
  subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s) =
  subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s.
Proof.
exact (compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compComp'_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  funcomp (subst_vl tau_ty tau_vl) (subst_vl sigma_ty sigma_vl) =
  subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_vl sigma_ty sigma_vl tau_ty tau_vl n)).
Qed.
