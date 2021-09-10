Require Import core fintype.

Require Import core_axioms fintype_axioms.
Require Import Setoid Morphisms Relation_Definitions.

Module renSubst.

Inductive ty (n_ty : nat) : Type :=
  | var_ty : fin n_ty -> ty n_ty
  | top : ty n_ty
  | arr : ty n_ty -> ty n_ty -> ty n_ty
  | all : ty n_ty -> ty (S n_ty) -> ty n_ty.

Lemma congr_top {m_ty : nat} : top m_ty = top m_ty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_arr {m_ty : nat} {s0 : ty m_ty} {s1 : ty m_ty} {t0 : ty m_ty}
  {t1 : ty m_ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  arr m_ty s0 s1 = arr m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => arr m_ty x s1) H0))
         (ap (fun x => arr m_ty t0 x) H1)).
Qed.

Lemma congr_all {m_ty : nat} {s0 : ty m_ty} {s1 : ty (S m_ty)} {t0 : ty m_ty}
  {t1 : ty (S m_ty)} (H0 : s0 = t0) (H1 : s1 = t1) :
  all m_ty s0 s1 = all m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => all m_ty x s1) H0))
         (ap (fun x => all m_ty t0 x) H1)).
Qed.

Lemma upRen_ty_ty {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_ty_ty (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
(s : ty m_ty) {struct s} : ty n_ty :=
  match s with
  | var_ty _ s0 => var_ty n_ty (xi_ty s0)
  | top _ => top n_ty
  | arr _ s0 s1 => arr n_ty (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | all _ s0 s1 => all n_ty (ren_ty xi_ty s0) (ren_ty (upRen_ty_ty xi_ty) s1)
  end.

Lemma up_ty_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty) :
  fin (S m) -> ty (S n_ty).
Proof.
exact (scons (var_ty (S n_ty) var_zero) (funcomp (ren_ty shift) sigma)).
Defined.

Lemma up_list_ty_ty (p : nat) {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) : fin (plus p m) -> ty (plus p n_ty).
Proof.
exact (scons_p p (funcomp (var_ty (plus p n_ty)) (zero_p p))
         (funcomp (ren_ty (shift_p p)) sigma)).
Defined.

Fixpoint subst_ty {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty)
(s : ty m_ty) {struct s} : ty n_ty :=
  match s with
  | var_ty _ s0 => sigma_ty s0
  | top _ => top n_ty
  | arr _ s0 s1 => arr n_ty (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | all _ s0 s1 =>
      all n_ty (subst_ty sigma_ty s0) (subst_ty (up_ty_ty sigma_ty) s1)
  end.

Lemma upId_ty_ty {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_ty_ty sigma x = var_ty (S m_ty) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_ty_ty {p : nat} {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_list_ty_ty p sigma x = var_ty (plus p m_ty) x.
Proof.
exact (fun n =>
       scons_p_eta (var_ty (plus p m_ty))
         (fun n => ap (ren_ty (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_ty {m_ty : nat} (sigma_ty : fin m_ty -> ty m_ty)
(Eq_ty : forall x, sigma_ty x = var_ty m_ty x) (s : ty m_ty) {struct s} :
subst_ty sigma_ty s = s :=
  match s with
  | var_ty _ s0 => Eq_ty s0
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (idSubst_ty sigma_ty Eq_ty s0) (idSubst_ty sigma_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ Eq_ty) s1)
  end.

Lemma upExtRen_ty_ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_ty xi x = upRen_ty_ty zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_ty_ty {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_ty_ty p xi x = upRen_list_ty_ty p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
(zeta_ty : fin m_ty -> fin n_ty) (Eq_ty : forall x, xi_ty x = zeta_ty x)
(s : ty m_ty) {struct s} : ren_ty xi_ty s = ren_ty zeta_ty s :=
  match s with
  | var_ty _ s0 => ap (var_ty n_ty) (Eq_ty s0)
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upExtRen_ty_ty _ _ Eq_ty) s1)
  end.

Lemma upExt_ty_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty)
  (tau : fin m -> ty n_ty) (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_ty sigma x = up_ty_ty tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_ty_ty {p : nat} {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) (tau : fin m -> ty n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ty_ty p sigma x = up_list_ty_ty p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_ty (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_ty {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty)
(tau_ty : fin m_ty -> ty n_ty) (Eq_ty : forall x, sigma_ty x = tau_ty x)
(s : ty m_ty) {struct s} : subst_ty sigma_ty s = subst_ty tau_ty s :=
  match s with
  | var_ty _ s0 => Eq_ty s0
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty) (upExt_ty_ty _ _ Eq_ty)
           s1)
  end.

Lemma up_ren_ren_ty_ty {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_ty_ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_ty_ty p zeta) (upRen_list_ty_ty p xi) x =
  upRen_list_ty_ty p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty)
(rho_ty : fin m_ty -> fin l_ty)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x) (s : ty m_ty) {struct
 s} : ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty rho_ty s :=
  match s with
  | var_ty _ s0 => ap (var_ty l_ty) (Eq_ty s0)
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upRen_ty_ty rho_ty) (up_ren_ren _ _ _ Eq_ty) s1)
  end.

Lemma up_ren_subst_ty_ty {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_ty_ty {p : nat} {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_ty_ty p tau) (upRen_list_ty_ty p xi) x =
  up_list_ty_ty p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_ty (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x) (s : ty m_ty) {struct
 s} : subst_ty tau_ty (ren_ty xi_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty _ s0 => Eq_ty s0
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_ty (upRen_ty_ty xi_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_ren_subst_ty_ty _ _ _ Eq_ty) s1)
  end.

Lemma up_subst_ren_ty_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_ty_ty zeta_ty)) (up_ty_ty sigma) x =
  up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_ty shift (upRen_ty_ty zeta_ty)
                (funcomp shift zeta_ty) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_ty zeta_ty shift (funcomp shift zeta_ty)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_ty shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_ty_ty {p : nat} {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_list_ty_ty p zeta_ty)) (up_list_ty_ty p sigma) x =
  up_list_ty_ty p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_ty (plus p m_ty)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_ty (shift_p p) (upRen_list_ty_ty p zeta_ty)
                  (funcomp (shift_p p) zeta_ty)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_ty zeta_ty (shift_p p)
                        (funcomp (shift_p p) zeta_ty) (fun x => eq_refl)
                        (sigma n))) (ap (ren_ty (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(s : ty m_ty) {struct s} :
ren_ty zeta_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty _ s0 => Eq_ty s0
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_ty (up_ty_ty sigma_ty) (upRen_ty_ty zeta_ty)
           (up_ty_ty theta_ty) (up_subst_ren_ty_ty _ _ _ Eq_ty) s1)
  end.

Lemma up_subst_subst_ty_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_ty_ty tau_ty)) (up_ty_ty sigma) x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_ty shift (up_ty_ty tau_ty)
                (funcomp (up_ty_ty tau_ty) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_ty tau_ty shift
                      (funcomp (ren_ty shift) tau_ty) (fun x => eq_refl)
                      (sigma fin_n))) (ap (ren_ty shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_ty_ty {p : nat} {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_list_ty_ty p tau_ty)) (up_list_ty_ty p sigma) x =
  up_list_ty_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_ty (plus p l_ty)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_ty (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_ty (shift_p p) (up_list_ty_ty p tau_ty)
                  (funcomp (up_list_ty_ty p tau_ty) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_ty tau_ty (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_ty (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(s : ty m_ty) {struct s} :
subst_ty tau_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty _ s0 => Eq_ty s0
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_subst_subst_ty_ty _ _ _ Eq_ty) s1)
  end.

Lemma rinstInst_up_ty_ty {m : nat} {n_ty : nat} (xi : fin m -> fin n_ty)
  (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x, funcomp (var_ty (S n_ty)) (upRen_ty_ty xi) x = up_ty_ty sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_ty_ty {p : nat} {m : nat} {n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty (plus p n_ty)) (upRen_list_ty_ty p xi) x =
  up_list_ty_ty p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_ty (plus p n_ty)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_ty (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_ty {m_ty : nat} {n_ty : nat}
(xi_ty : fin m_ty -> fin n_ty) (sigma_ty : fin m_ty -> ty n_ty)
(Eq_ty : forall x, funcomp (var_ty n_ty) xi_ty x = sigma_ty x) (s : ty m_ty)
{struct s} : ren_ty xi_ty s = subst_ty sigma_ty s :=
  match s with
  | var_ty _ s0 => Eq_ty s0
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_ty (upRen_ty_ty xi_ty) (up_ty_ty sigma_ty)
           (rinstInst_up_ty_ty _ _ Eq_ty) s1)
  end.

Lemma renRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty)
  (s : ty m_ty) :
  ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty (funcomp zeta_ty xi_ty) s.
Proof.
exact (compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty)
  (s : ty m_ty) :
  ren_ty zeta_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s.
Proof.
exact (compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty) (s : ty m_ty)
  : subst_ty tau_ty (ren_ty xi_ty s) = subst_ty (funcomp tau_ty xi_ty) s.
Proof.
exact (compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty)
  (s : ty m_ty) :
  subst_ty tau_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s.
Proof.
exact (compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
  (s : ty m_ty) : ren_ty xi_ty s = subst_ty (funcomp (var_ty n_ty) xi_ty) s.
Proof.
exact (rinst_inst_ty xi_ty _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ty {m_ty : nat} (s : ty m_ty) : subst_ty (var_ty m_ty) s = s.
Proof.
exact (idSubst_ty (var_ty m_ty) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_ty {m_ty : nat} (s : ty m_ty) : ren_ty id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id s)).
Qed.

Lemma varL'_ty {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty)
  (x : fin m_ty) : subst_ty sigma_ty (var_ty m_ty x) = sigma_ty x.
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
  (x : fin m_ty) : ren_ty xi_ty (var_ty m_ty x) = var_ty n_ty (xi_ty x).
Proof.
exact (eq_refl).
Qed.

Inductive tm (n_ty n_tm : nat) : Type :=
  | var_tm : fin n_tm -> tm n_ty n_tm
  | app : tm n_ty n_tm -> tm n_ty n_tm -> tm n_ty n_tm
  | tapp : tm n_ty n_tm -> ty n_ty -> tm n_ty n_tm
  | vt : tm n_ty n_tm -> tm n_ty n_tm
  | abs : ty n_ty -> tm n_ty (S n_tm) -> tm n_ty n_tm
  | tabs : ty n_ty -> tm (S n_ty) n_tm -> tm n_ty n_tm.

Lemma congr_app {m_ty m_tm : nat} {s0 : tm m_ty m_tm} {s1 : tm m_ty m_tm}
  {t0 : tm m_ty m_tm} {t1 : tm m_ty m_tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_ty m_tm s0 s1 = app m_ty m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_ty m_tm x s1) H0))
         (ap (fun x => app m_ty m_tm t0 x) H1)).
Qed.

Lemma congr_tapp {m_ty m_tm : nat} {s0 : tm m_ty m_tm} {s1 : ty m_ty}
  {t0 : tm m_ty m_tm} {t1 : ty m_ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  tapp m_ty m_tm s0 s1 = tapp m_ty m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tapp m_ty m_tm x s1) H0))
         (ap (fun x => tapp m_ty m_tm t0 x) H1)).
Qed.

Lemma congr_vt {m_ty m_tm : nat} {s0 : tm m_ty m_tm} {t0 : tm m_ty m_tm}
  (H0 : s0 = t0) : vt m_ty m_tm s0 = vt m_ty m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => vt m_ty m_tm x) H0)).
Qed.

Lemma congr_abs {m_ty m_tm : nat} {s0 : ty m_ty} {s1 : tm m_ty (S m_tm)}
  {t0 : ty m_ty} {t1 : tm m_ty (S m_tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  abs m_ty m_tm s0 s1 = abs m_ty m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => abs m_ty m_tm x s1) H0))
         (ap (fun x => abs m_ty m_tm t0 x) H1)).
Qed.

Lemma congr_tabs {m_ty m_tm : nat} {s0 : ty m_ty} {s1 : tm (S m_ty) m_tm}
  {t0 : ty m_ty} {t1 : tm (S m_ty) m_tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  tabs m_ty m_tm s0 s1 = tabs m_ty m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tabs m_ty m_tm x s1) H0))
         (ap (fun x => tabs m_ty m_tm t0 x) H1)).
Qed.

Lemma upRen_ty_tm {m : nat} {n : nat} (xi : fin m -> fin n) : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_tm_ty {m : nat} {n : nat} (xi : fin m -> fin n) : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_ty_tm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_tm_ty (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_tm_tm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
(s : tm m_ty m_tm) {struct s} : tm n_ty n_tm :=
  match s with
  | var_tm _ _ s0 => var_tm n_ty n_tm (xi_tm s0)
  | app _ _ s0 s1 =>
      app n_ty n_tm (ren_tm xi_ty xi_tm s0) (ren_tm xi_ty xi_tm s1)
  | tapp _ _ s0 s1 =>
      tapp n_ty n_tm (ren_tm xi_ty xi_tm s0) (ren_ty xi_ty s1)
  | vt _ _ s0 => vt n_ty n_tm (ren_tm xi_ty xi_tm s0)
  | abs _ _ s0 s1 =>
      abs n_ty n_tm (ren_ty xi_ty s0)
        (ren_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm) s1)
  | tabs _ _ s0 s1 =>
      tabs n_ty n_tm (ren_ty xi_ty s0)
        (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm) s1)
  end.

Lemma up_ty_tm {m : nat} {n_ty n_tm : nat} (sigma : fin m -> tm n_ty n_tm) :
  fin m -> tm (S n_ty) n_tm.
Proof.
exact (funcomp (ren_tm shift id) sigma).
Defined.

Lemma up_tm_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty) :
  fin m -> ty n_ty.
Proof.
exact (funcomp (ren_ty id) sigma).
Defined.

Lemma up_tm_tm {m : nat} {n_ty n_tm : nat} (sigma : fin m -> tm n_ty n_tm) :
  fin (S m) -> tm n_ty (S n_tm).
Proof.
exact (scons (var_tm n_ty (S n_tm) var_zero)
         (funcomp (ren_tm id shift) sigma)).
Defined.

Lemma up_list_ty_tm (p : nat) {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) : fin m -> tm (plus p n_ty) n_tm.
Proof.
exact (funcomp (ren_tm (shift_p p) id) sigma).
Defined.

Lemma up_list_tm_ty (p : nat) {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) : fin m -> ty n_ty.
Proof.
exact (funcomp (ren_ty id) sigma).
Defined.

Lemma up_list_tm_tm (p : nat) {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) : fin (plus p m) -> tm n_ty (plus p n_tm).
Proof.
exact (scons_p p (funcomp (var_tm n_ty (plus p n_tm)) (zero_p p))
         (funcomp (ren_tm id (shift_p p)) sigma)).
Defined.

Fixpoint subst_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm)
(s : tm m_ty m_tm) {struct s} : tm n_ty n_tm :=
  match s with
  | var_tm _ _ s0 => sigma_tm s0
  | app _ _ s0 s1 =>
      app n_ty n_tm (subst_tm sigma_ty sigma_tm s0)
        (subst_tm sigma_ty sigma_tm s1)
  | tapp _ _ s0 s1 =>
      tapp n_ty n_tm (subst_tm sigma_ty sigma_tm s0) (subst_ty sigma_ty s1)
  | vt _ _ s0 => vt n_ty n_tm (subst_tm sigma_ty sigma_tm s0)
  | abs _ _ s0 s1 =>
      abs n_ty n_tm (subst_ty sigma_ty s0)
        (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) s1)
  | tabs _ _ s0 s1 =>
      tabs n_ty n_tm (subst_ty sigma_ty s0)
        (subst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) s1)
  end.

Lemma upId_ty_tm {m_ty m_tm : nat} (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_ty_tm sigma x = var_tm (S m_ty) m_tm x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma upId_tm_ty {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_tm_ty sigma x = var_ty m_ty x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upId_tm_tm {m_ty m_tm : nat} (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_tm_tm sigma x = var_tm m_ty (S m_tm) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_ty_tm {p : nat} {m_ty m_tm : nat}
  (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_list_ty_tm p sigma x = var_tm (plus p m_ty) m_tm x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma upId_list_tm_ty {p : nat} {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_list_tm_ty p sigma x = var_ty m_ty x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upId_list_tm_tm {p : nat} {m_ty m_tm : nat}
  (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_list_tm_tm p sigma x = var_tm m_ty (plus p m_tm) x.
Proof.
exact (fun n =>
       scons_p_eta (var_tm m_ty (plus p m_tm))
         (fun n => ap (ren_tm id (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_tm {m_ty m_tm : nat} (sigma_ty : fin m_ty -> ty m_ty)
(sigma_tm : fin m_tm -> tm m_ty m_tm)
(Eq_ty : forall x, sigma_ty x = var_ty m_ty x)
(Eq_tm : forall x, sigma_tm x = var_tm m_ty m_tm x) (s : tm m_ty m_tm)
{struct s} : subst_tm sigma_ty sigma_tm s = s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | vt _ _ s0 => congr_vt (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
  | abs _ _ s0 s1 =>
      congr_abs (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (upId_tm_ty _ Eq_ty) (upId_tm_tm _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (upId_ty_ty _ Eq_ty) (upId_ty_tm _ Eq_tm) s1)
  end.

Lemma upExtRen_ty_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_tm xi x = upRen_ty_tm zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_tm_ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_ty xi x = upRen_tm_ty zeta x.
Proof.
exact (fun n => Eq n).
Qed.

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

Lemma upExtRen_list_ty_tm {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_ty_tm p xi x = upRen_list_ty_tm p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_tm_ty {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_ty p xi x = upRen_list_tm_ty p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_tm_tm {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_tm p xi x = upRen_list_tm_tm p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
(zeta_ty : fin m_ty -> fin n_ty) (zeta_tm : fin m_tm -> fin n_tm)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm m_ty m_tm) {struct s} :
ren_tm xi_ty xi_tm s = ren_tm zeta_ty zeta_tm s :=
  match s with
  | var_tm _ _ s0 => ap (var_tm n_ty n_tm) (Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
        (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
  | abs _ _ s0 s1 =>
      congr_abs (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_ty _ _ Eq_ty) (upExtRen_tm_tm _ _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm)
           (upExtRen_ty_ty _ _ Eq_ty) (upExtRen_ty_tm _ _ Eq_tm) s1)
  end.

Lemma upExt_ty_tm {m : nat} {n_ty n_tm : nat} (sigma : fin m -> tm n_ty n_tm)
  (tau : fin m -> tm n_ty n_tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_tm sigma x = up_ty_tm tau x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma upExt_tm_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty)
  (tau : fin m -> ty n_ty) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_ty sigma x = up_tm_ty tau x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upExt_tm_tm {m : nat} {n_ty n_tm : nat} (sigma : fin m -> tm n_ty n_tm)
  (tau : fin m -> tm n_ty n_tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_ty_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) (tau : fin m -> tm n_ty n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ty_tm p sigma x = up_list_ty_tm p tau x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma upExt_list_tm_ty {p : nat} {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) (tau : fin m -> ty n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_ty p sigma x = up_list_tm_ty p tau x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upExt_list_tm_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) (tau : fin m -> tm n_ty n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_tm p sigma x = up_list_tm_tm p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_tm id (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm)
(tau_ty : fin m_ty -> ty n_ty) (tau_tm : fin m_tm -> tm n_ty n_tm)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm m_ty m_tm) {struct s} :
subst_tm sigma_ty sigma_tm s = subst_tm tau_ty tau_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
        (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
  | abs _ _ s0 s1 =>
      congr_abs (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) (up_tm_ty tau_ty)
           (up_tm_tm tau_tm) (upExt_tm_ty _ _ Eq_ty) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) (up_ty_ty tau_ty)
           (up_ty_tm tau_tm) (upExt_ty_ty _ _ Eq_ty) (upExt_ty_tm _ _ Eq_tm)
           s1)
  end.

Lemma up_ren_ren_ty_tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_tm zeta) (upRen_ty_tm xi) x = upRen_ty_tm rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_tm_ty {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_ty zeta) (upRen_tm_ty xi) x = upRen_tm_ty rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_tm_tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_ty_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_ty_tm p zeta) (upRen_list_ty_tm p xi) x =
  upRen_list_ty_tm p rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_list_tm_ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_ty p zeta) (upRen_list_tm_ty p xi) x =
  upRen_list_tm_ty p rho x.
Proof.
exact (Eq).
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

Fixpoint compRenRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
(xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
(zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm)
(rho_ty : fin m_ty -> fin l_ty) (rho_tm : fin m_tm -> fin l_tm)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x) (s : tm m_ty m_tm)
{struct s} :
ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s) = ren_tm rho_ty rho_tm s :=
  match s with
  | var_tm _ _ s0 => ap (var_tm l_ty l_tm) (Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s0)
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s0) (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s0)
  | abs _ _ s0 s1 =>
      congr_abs (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm) (upRen_tm_ty rho_ty)
           (upRen_tm_tm rho_tm) Eq_ty (up_ren_ren _ _ _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm) (upRen_ty_ty rho_ty)
           (upRen_ty_tm rho_tm) (up_ren_ren _ _ _ Eq_ty) Eq_tm s1)
  end.

Lemma up_ren_subst_ty_tm {k : nat} {l : nat} {m_ty m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  : forall x, funcomp (up_ty_tm tau) (upRen_ty_tm xi) x = up_ty_tm theta x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma up_ren_subst_tm_ty {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_ty tau) (upRen_tm_ty xi) x = up_tm_ty theta x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma up_ren_subst_tm_tm {k : nat} {l : nat} {m_ty m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  : forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_ty_tm {p : nat} {k : nat} {l : nat} {m_ty m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_list_ty_tm p tau) (upRen_list_ty_tm p xi) x =
  up_list_ty_tm p theta x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma up_ren_subst_list_tm_ty {p : nat} {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_tm_ty p tau) (upRen_list_tm_ty p xi) x =
  up_list_tm_ty p theta x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma up_ren_subst_list_tm_tm {p : nat} {k : nat} {l : nat} {m_ty m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_list_tm_tm p tau) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_tm id (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_tm {k_ty k_tm : nat} {l_ty l_tm : nat}
{m_ty m_tm : nat} (xi_ty : fin m_ty -> fin k_ty)
(xi_tm : fin m_tm -> fin k_tm) (tau_ty : fin k_ty -> ty l_ty)
(tau_tm : fin k_tm -> tm l_ty l_tm) (theta_ty : fin m_ty -> ty l_ty)
(theta_tm : fin m_tm -> tm l_ty l_tm)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm m_ty m_tm)
{struct s} :
subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s) = subst_tm theta_ty theta_tm s
:=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s0)
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s0) (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s0)
  | abs _ _ s0 s1 =>
      congr_abs (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (up_tm_ty tau_ty) (up_tm_tm tau_tm) (up_tm_ty theta_ty)
           (up_tm_tm theta_tm) (up_ren_subst_tm_ty _ _ _ Eq_ty)
           (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (up_ty_ty tau_ty) (up_ty_tm tau_tm) (up_ty_ty theta_ty)
           (up_ty_tm theta_tm) (up_ren_subst_ty_ty _ _ _ Eq_ty)
           (up_ren_subst_ty_tm _ _ _ Eq_tm) s1)
  end.

Lemma up_subst_ren_ty_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (zeta_ty : fin l_ty -> fin m_ty)
  (zeta_tm : fin l_tm -> fin m_tm) (theta : fin k -> tm m_ty m_tm)
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

Lemma up_subst_ren_tm_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
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

Lemma up_subst_ren_tm_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (zeta_ty : fin l_ty -> fin m_ty)
  (zeta_tm : fin l_tm -> fin m_tm) (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm))
    (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_tm id shift (upRen_tm_ty zeta_ty)
                (upRen_tm_tm zeta_tm) (funcomp id zeta_ty)
                (funcomp shift zeta_tm) (fun x => eq_refl) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_ty zeta_tm id shift
                      (funcomp id zeta_ty) (funcomp shift zeta_tm)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_tm id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_ty_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (zeta_ty : fin l_ty -> fin m_ty) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_list_ty_ty p zeta_ty) (upRen_list_ty_tm p zeta_tm))
    (up_list_ty_tm p sigma) x = up_list_ty_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_tm (shift_p p) id (upRen_list_ty_ty p zeta_ty)
            (upRen_list_ty_tm p zeta_tm) (funcomp (shift_p p) zeta_ty)
            (funcomp id zeta_tm) (fun x => scons_p_tail' _ _ x)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_tm zeta_ty zeta_tm (shift_p p) id
                  (funcomp (shift_p p) zeta_ty) (funcomp id zeta_tm)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_tm (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_tm_ty {p : nat} {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_list_tm_ty p zeta_ty)) (up_list_tm_ty p sigma) x =
  up_list_tm_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ty id (upRen_list_tm_ty p zeta_ty) (funcomp id zeta_ty)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ty zeta_ty id (funcomp id zeta_ty)
                  (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_tm_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (zeta_ty : fin l_ty -> fin m_ty) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_list_tm_ty p zeta_ty) (upRen_list_tm_tm p zeta_tm))
    (up_list_tm_tm p sigma) x = up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_tm m_ty (plus p m_tm)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_tm id (shift_p p) (upRen_list_tm_ty p zeta_ty)
                  (upRen_list_tm_tm p zeta_tm) (funcomp id zeta_ty)
                  (funcomp (shift_p p) zeta_tm) (fun x => eq_refl)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_tm zeta_ty zeta_tm id (shift_p p)
                        (funcomp id zeta_ty) (funcomp (shift_p p) zeta_tm)
                        (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
                  (ap (ren_tm id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat}
{m_ty m_tm : nat} (sigma_ty : fin m_ty -> ty k_ty)
(sigma_tm : fin m_tm -> tm k_ty k_tm) (zeta_ty : fin k_ty -> fin l_ty)
(zeta_tm : fin k_tm -> fin l_tm) (theta_ty : fin m_ty -> ty l_ty)
(theta_tm : fin m_tm -> tm l_ty l_tm)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_tm : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma_tm x = theta_tm x)
(s : tm m_ty m_tm) {struct s} :
ren_tm zeta_ty zeta_tm (subst_tm sigma_ty sigma_tm s) =
subst_tm theta_ty theta_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
  | abs _ _ s0 s1 =>
      congr_abs (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm) (up_tm_ty theta_ty)
           (up_tm_tm theta_tm) (up_subst_ren_tm_ty _ _ _ Eq_ty)
           (up_subst_ren_tm_tm _ _ _ _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm) (up_ty_ty theta_ty)
           (up_ty_tm theta_tm) (up_subst_ren_ty_ty _ _ _ Eq_ty)
           (up_subst_ren_ty_tm _ _ _ _ Eq_tm) s1)
  end.

Lemma up_subst_subst_ty_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (tau_ty : fin l_ty -> ty m_ty)
  (tau_tm : fin l_tm -> tm m_ty m_tm) (theta : fin k -> tm m_ty m_tm)
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

Lemma up_subst_subst_tm_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
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

Lemma up_subst_subst_tm_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (tau_ty : fin l_ty -> ty m_ty)
  (tau_tm : fin l_tm -> tm m_ty m_tm) (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_ty tau_ty) (up_tm_tm tau_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_tm id shift (up_tm_ty tau_ty) (up_tm_tm tau_tm)
                (funcomp (up_tm_ty tau_ty) id)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_ty tau_tm id shift
                      (funcomp (ren_ty id) tau_ty)
                      (funcomp (ren_tm id shift) tau_tm) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_tm id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_ty_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (tau_ty : fin l_ty -> ty m_ty) (tau_tm : fin l_tm -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_ty_ty p tau_ty) (up_list_ty_tm p tau_tm))
    (up_list_ty_tm p sigma) x = up_list_ty_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_tm (shift_p p) id (up_list_ty_ty p tau_ty)
            (up_list_ty_tm p tau_tm)
            (funcomp (up_list_ty_ty p tau_ty) (shift_p p))
            (funcomp (up_list_ty_tm p tau_tm) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_tm tau_ty tau_tm (shift_p p) id _ _
                  (fun x => eq_sym (scons_p_tail' _ _ x))
                  (fun x => eq_sym eq_refl) (sigma n)))
            (ap (ren_tm (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_tm_ty {p : nat} {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_list_tm_ty p tau_ty)) (up_list_tm_ty p sigma) x =
  up_list_tm_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ty id (up_list_tm_ty p tau_ty)
            (funcomp (up_list_tm_ty p tau_ty) id) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_ty id _ (fun x => eq_sym eq_refl)
                  (sigma n))) (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_tm_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (tau_ty : fin l_ty -> ty m_ty) (tau_tm : fin l_tm -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_tm_ty p tau_ty) (up_list_tm_tm p tau_tm))
    (up_list_tm_tm p sigma) x = up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_tm l_ty (plus p l_tm)) (zero_p p)) _ _
            n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_tm id (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_tm id (shift_p p) (up_list_tm_ty p tau_ty)
                  (up_list_tm_tm p tau_tm)
                  (funcomp (up_list_tm_ty p tau_ty) id)
                  (funcomp (up_list_tm_tm p tau_tm) (shift_p p))
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_tm tau_ty tau_tm id (shift_p p) _ _
                        (fun x => eq_sym eq_refl)
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_tm id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_tm {k_ty k_tm : nat} {l_ty l_tm : nat}
{m_ty m_tm : nat} (sigma_ty : fin m_ty -> ty k_ty)
(sigma_tm : fin m_tm -> tm k_ty k_tm) (tau_ty : fin k_ty -> ty l_ty)
(tau_tm : fin k_tm -> tm l_ty l_tm) (theta_ty : fin m_ty -> ty l_ty)
(theta_tm : fin m_tm -> tm l_ty l_tm)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_tm : forall x, funcomp (subst_tm tau_ty tau_tm) sigma_tm x = theta_tm x)
(s : tm m_ty m_tm) {struct s} :
subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm s) =
subst_tm theta_ty theta_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s0)
  | abs _ _ s0 s1 =>
      congr_abs (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (up_tm_ty tau_ty) (up_tm_tm tau_tm) (up_tm_ty theta_ty)
           (up_tm_tm theta_tm) (up_subst_subst_tm_ty _ _ _ Eq_ty)
           (up_subst_subst_tm_tm _ _ _ _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (up_ty_ty tau_ty) (up_ty_tm tau_tm) (up_ty_ty theta_ty)
           (up_ty_tm theta_tm) (up_subst_subst_ty_ty _ _ _ Eq_ty)
           (up_subst_subst_ty_tm _ _ _ _ Eq_tm) s1)
  end.

Lemma rinstInst_up_ty_tm {m : nat} {n_ty n_tm : nat} (xi : fin m -> fin n_tm)
  (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (S n_ty) n_tm) (upRen_ty_tm xi) x = up_ty_tm sigma x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma rinstInst_up_tm_ty {m : nat} {n_ty : nat} (xi : fin m -> fin n_ty)
  (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x, funcomp (var_ty n_ty) (upRen_tm_ty xi) x = up_tm_ty sigma x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma rinstInst_up_tm_tm {m : nat} {n_ty n_tm : nat} (xi : fin m -> fin n_tm)
  (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm n_ty (S n_tm)) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_ty_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (plus p n_ty) n_tm) (upRen_list_ty_tm p xi) x =
  up_list_ty_tm p sigma x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma rinstInst_up_list_tm_ty {p : nat} {m : nat} {n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty n_ty) (upRen_list_tm_ty p xi) x = up_list_tm_ty p sigma x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma rinstInst_up_list_tm_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm n_ty (plus p n_tm)) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_tm n_ty (plus p n_tm)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_tm id (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
(sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm)
(Eq_ty : forall x, funcomp (var_ty n_ty) xi_ty x = sigma_ty x)
(Eq_tm : forall x, funcomp (var_tm n_ty n_tm) xi_tm x = sigma_tm x)
(s : tm m_ty m_tm) {struct s} :
ren_tm xi_ty xi_tm s = subst_tm sigma_ty sigma_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
  | abs _ _ s0 s1 =>
      congr_abs (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm)
           (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_ty _ _ Eq_ty) (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm)
           (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (rinstInst_up_ty_ty _ _ Eq_ty) (rinstInst_up_ty_tm _ _ Eq_tm) s1)
  end.

Lemma renRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_ty m_tm) :
  ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_tm : fin m_tm -> tm k_ty k_tm)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_ty m_tm) :
  ren_tm zeta_ty zeta_tm (subst_tm sigma_ty sigma_tm s) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
  (tau_ty : fin k_ty -> ty l_ty) (tau_tm : fin k_tm -> tm l_ty l_tm)
  (s : tm m_ty m_tm) :
  subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_tm : fin m_tm -> tm k_ty k_tm)
  (tau_ty : fin k_ty -> ty l_ty) (tau_tm : fin k_tm -> tm l_ty l_tm)
  (s : tm m_ty m_tm) :
  subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm s) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_tm tau_ty tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
  (s : tm m_ty m_tm) :
  ren_tm xi_ty xi_tm s =
  subst_tm (funcomp (var_ty n_ty) xi_ty) (funcomp (var_tm n_ty n_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_ty xi_tm _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm {m_ty m_tm : nat} (s : tm m_ty m_tm) :
  subst_tm (var_ty m_ty) (var_tm m_ty m_tm) s = s.
Proof.
exact (idSubst_tm (var_ty m_ty) (var_tm m_ty m_tm) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm {m_ty m_tm : nat} (s : tm m_ty m_tm) : ren_tm id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma varL'_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
  (sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm)
  (x : fin m_tm) :
  subst_tm sigma_ty sigma_tm (var_tm m_ty m_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
  (x : fin m_tm) :
  ren_tm xi_ty xi_tm (var_tm m_ty m_tm x) = var_tm n_ty n_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

Class Up_ty X Y :=
    up_ty : X -> Y.

Instance Subst_tm  {m_ty m_tm n_ty n_tm : nat}: (Subst2 _ _ _ _) :=
 (@subst_tm m_ty m_tm n_ty n_tm).

Instance Up_tm_tm  {m n_ty n_tm : nat}: (Up_tm _ _) :=
 (@up_tm_tm m n_ty n_tm).

Instance Up_tm_ty  {m n_ty : nat}: (Up_ty _ _) := (@up_tm_ty m n_ty).

Instance Up_ty_tm  {m n_ty n_tm : nat}: (Up_tm _ _) :=
 (@up_ty_tm m n_ty n_tm).

Instance Ren_tm  {m_ty m_tm n_ty n_tm : nat}: (Ren2 _ _ _ _) :=
 (@ren_tm m_ty m_tm n_ty n_tm).

Instance VarInstance_tm  {n_ty n_tm : nat}: (Var _ _) := (@var_tm n_ty n_tm).

Instance Subst_ty  {m_ty n_ty : nat}: (Subst1 _ _ _) := (@subst_ty m_ty n_ty).

Instance Up_ty_ty  {m n_ty : nat}: (Up_ty _ _) := (@up_ty_ty m n_ty).

Instance Ren_ty  {m_ty n_ty : nat}: (Ren1 _ _ _) := (@ren_ty m_ty n_ty).

Instance VarInstance_ty  {n_ty : nat}: (Var _ _) := (@var_ty n_ty).

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

Instance subst_tm_morphism  {m_ty m_tm : nat} {n_ty n_tm : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_tm m_ty m_tm n_ty n_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_ty f_tm s = subst_tm g_ty g_tm t')
         (ext_tm f_ty f_tm g_ty g_tm Eq_ty Eq_tm s) t Eq_st).
Qed.

Instance ren_tm_morphism  {m_ty m_tm : nat} {n_ty n_tm : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_tm m_ty m_tm n_ty n_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_ty f_tm s = ren_tm g_ty g_tm t')
         (extRen_tm f_ty f_tm g_ty g_tm Eq_ty Eq_tm s) t Eq_st).
Qed.

Instance subst_ty_morphism  {m_ty : nat} {n_ty : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ty m_ty n_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s (fun t' => subst_ty f_ty s = subst_ty g_ty t')
         (ext_ty f_ty g_ty Eq_ty s) t Eq_st).
Qed.

Instance ren_ty_morphism  {m_ty : nat} {n_ty : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_ty m_ty n_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s (fun t' => ren_ty f_ty s = ren_ty g_ty t')
         (extRen_ty f_ty g_ty Eq_ty s) t Eq_st).
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
                 [ progress setoid_rewrite substSubst_tm
                 | progress rewrite ?substSubst_tm
                 | progress setoid_rewrite renSubst_tm
                 | progress rewrite ?renSubst_tm
                 | progress setoid_rewrite substRen_tm
                 | progress rewrite ?substRen_tm
                 | progress setoid_rewrite renRen_tm
                 | progress rewrite ?renRen_tm
                 | progress setoid_rewrite substSubst_ty
                 | progress rewrite ?substSubst_ty
                 | progress setoid_rewrite renSubst_ty
                 | progress rewrite ?renSubst_ty
                 | progress setoid_rewrite substRen_ty
                 | progress rewrite ?substRen_ty
                 | progress setoid_rewrite renRen_ty
                 | progress rewrite ?renRen_ty
                 | progress setoid_rewrite varLRen'_tm
                 | progress rewrite ?varLRen'_tm
                 | progress setoid_rewrite varL'_tm
                 | progress rewrite ?varL'_tm
                 | progress setoid_rewrite rinstId'_tm
                 | progress rewrite ?rinstId'_tm
                 | progress setoid_rewrite instId'_tm
                 | progress rewrite ?instId'_tm
                 | progress setoid_rewrite varLRen'_ty
                 | progress rewrite ?varLRen'_ty
                 | progress setoid_rewrite varL'_ty
                 | progress rewrite ?varL'_ty
                 | progress setoid_rewrite rinstId'_ty
                 | progress rewrite ?rinstId'_ty
                 | progress setoid_rewrite instId'_ty
                 | progress rewrite ?instId'_ty
                 | progress
                    unfold up_list_tm_tm, up_list_tm_ty, up_list_ty_tm,
                     up_tm_tm, up_tm_ty, up_ty_tm, upRen_list_tm_tm,
                     upRen_list_tm_ty, upRen_list_ty_tm, upRen_tm_tm,
                     upRen_tm_ty, upRen_ty_tm, up_list_ty_ty, up_ty_ty,
                     upRen_list_ty_ty, upRen_ty_ty, up_ren
                 | progress cbn[subst_tm ren_tm subst_ty ren_ty]
                 | progress fsimpl
                 | repeat unfold funcomp ]).

Ltac asimpl := repeat try unfold_funcomp;
                repeat
                 unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                  Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                  VarInstance_tm, Var, ids, Ren_tm, Ren2, ren2, Up_ty_tm,
                  Up_tm, up_tm, Up_tm_ty, Up_ty, up_ty, Up_tm_tm, Up_tm,
                  up_tm, Subst_tm, Subst2, subst2 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try repeat erewrite ?rinstInst'_tm;
                  try repeat erewrite ?rinstInst'_ty.

Ltac renamify := auto_unfold; try repeat erewrite <- ?rinstInst'_tm;
                  try repeat erewrite <- ?rinstInst'_ty.

End renSubst.

Module fext.

Import
renSubst.

Lemma rinstInst_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty) :
  ren_ty xi_ty = subst_ty (funcomp (var_ty n_ty) xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_ty xi_ty _ (fun n => eq_refl) x)).
Qed.

Lemma instId_ty {m_ty : nat} : subst_ty (var_ty m_ty) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_ty (var_ty m_ty) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_ty {m_ty : nat} : @ren_ty m_ty m_ty id = id.
Proof.
exact (eq_trans (rinstInst_ty (id _)) instId_ty).
Qed.

Lemma varL_ty {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty) :
  funcomp (subst_ty sigma_ty) (var_ty m_ty) = sigma_ty.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty) :
  funcomp (ren_ty xi_ty) (var_ty m_ty) = funcomp (var_ty n_ty) xi_ty.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty) :
  funcomp (ren_ty zeta_ty) (ren_ty xi_ty) = ren_ty (funcomp zeta_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_ty xi_ty zeta_ty n)).
Qed.

Lemma substRen'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty) :
  funcomp (ren_ty zeta_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_ty sigma_ty zeta_ty n)).
Qed.

Lemma renSubst'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty) :
  funcomp (subst_ty tau_ty) (ren_ty xi_ty) = subst_ty (funcomp tau_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_ty xi_ty tau_ty n)).
Qed.

Lemma substSubst'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty) :
  funcomp (subst_ty tau_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_ty sigma_ty tau_ty n)).
Qed.

Lemma rinstInst_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm) :
  ren_tm xi_ty xi_tm =
  subst_tm (funcomp (var_ty n_ty) xi_ty) (funcomp (var_tm n_ty n_tm) xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          rinst_inst_tm xi_ty xi_tm _ _ (fun n => eq_refl) (fun n => eq_refl)
            x)).
Qed.

Lemma instId_tm {m_ty m_tm : nat} :
  subst_tm (var_ty m_ty) (var_tm m_ty m_tm) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          idSubst_tm (var_ty m_ty) (var_tm m_ty m_tm) (fun n => eq_refl)
            (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_tm {m_ty m_tm : nat} : @ren_tm m_ty m_tm m_ty m_tm id id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _) (id _)) instId_tm).
Qed.

Lemma varL_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
  (sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm) :
  funcomp (subst_tm sigma_ty sigma_tm) (var_tm m_ty m_tm) = sigma_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm) :
  funcomp (ren_tm xi_ty xi_tm) (var_tm m_ty m_tm) =
  funcomp (var_tm n_ty n_tm) xi_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_ty zeta_tm) (ren_tm xi_ty xi_tm) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_tm xi_ty xi_tm zeta_ty zeta_tm n)).
Qed.

Lemma substRen'_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_tm : fin m_tm -> tm k_ty k_tm)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_ty zeta_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_tm sigma_ty sigma_tm zeta_ty zeta_tm n)).
Qed.

Lemma renSubst'_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
  (tau_ty : fin k_ty -> ty l_ty) (tau_tm : fin k_tm -> tm l_ty l_tm) :
  funcomp (subst_tm tau_ty tau_tm) (ren_tm xi_ty xi_tm) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_tm xi_ty xi_tm tau_ty tau_tm n)).
Qed.

Lemma substSubst'_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_tm : fin m_tm -> tm k_ty k_tm)
  (tau_ty : fin k_ty -> ty l_ty) (tau_tm : fin k_tm -> tm l_ty l_tm) :
  funcomp (subst_tm tau_ty tau_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_tm tau_ty tau_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_tm sigma_ty sigma_tm tau_ty tau_tm n)).
Qed.

Ltac asimpl_fext' := repeat (first
                      [ progress setoid_rewrite substSubst_tm
                      | progress setoid_rewrite renSubst_tm
                      | progress setoid_rewrite substRen_tm
                      | progress setoid_rewrite renRen_tm
                      | progress setoid_rewrite substSubst_ty
                      | progress setoid_rewrite renSubst_ty
                      | progress setoid_rewrite substRen_ty
                      | progress setoid_rewrite renRen_ty
                      | progress setoid_rewrite substSubst'_tm
                      | progress setoid_rewrite renSubst'_tm
                      | progress setoid_rewrite substRen'_tm
                      | progress setoid_rewrite renRen'_tm
                      | progress setoid_rewrite varLRen_tm
                      | progress setoid_rewrite varL_tm
                      | progress setoid_rewrite rinstId_tm
                      | progress setoid_rewrite instId_tm
                      | progress setoid_rewrite substSubst'_ty
                      | progress setoid_rewrite renSubst'_ty
                      | progress setoid_rewrite substRen'_ty
                      | progress setoid_rewrite renRen'_ty
                      | progress setoid_rewrite varLRen_ty
                      | progress setoid_rewrite varL_ty
                      | progress setoid_rewrite rinstId_ty
                      | progress setoid_rewrite instId_ty
                      | progress
                         unfold up_list_tm_tm, up_list_tm_ty, up_list_ty_tm,
                          up_tm_tm, up_tm_ty, up_ty_tm, upRen_list_tm_tm,
                          upRen_list_tm_ty, upRen_list_ty_tm, upRen_tm_tm,
                          upRen_tm_ty, upRen_ty_tm, up_list_ty_ty, up_ty_ty,
                          upRen_list_ty_ty, upRen_ty_ty, up_ren
                      | progress cbn[subst_tm ren_tm subst_ty ren_ty]
                      | fsimpl_fext ]).

Ltac asimpl_fext := repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                       Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                       VarInstance_tm, Var, ids, Ren_tm, Ren2, ren2,
                       Up_ty_tm, Up_tm, up_tm, Up_tm_ty, Up_ty, up_ty,
                       Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst2, subst2 
                       in *; asimpl_fext'; repeat try unfold_funcomp.

Tactic Notation "asimpl_fext" "in" hyp(J) := revert J; asimpl_fext; intros J.

Ltac substify_fext := auto_unfold; try repeat erewrite ?rinstInst_tm;
                       try repeat erewrite ?rinstInst_ty.

Ltac renamify_fext := auto_unfold; try repeat erewrite <- ?rinstInst_tm;
                       try repeat erewrite <- ?rinstInst_ty.

End fext.

Module interface.

Export renSubst.

Export
fext.

Arguments tabs {n_ty n_tm}.

Arguments abs {n_ty n_tm}.

Arguments vt {n_ty n_tm}.

Arguments tapp {n_ty n_tm}.

Arguments app {n_ty n_tm}.

Arguments var_tm {n_ty n_tm}.

Arguments all {n_ty}.

Arguments arr {n_ty}.

Arguments top {n_ty}.

Arguments var_ty {n_ty}.

End interface.

Export interface.

