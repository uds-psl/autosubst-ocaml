Require Import core fintype.

Require Import core_axioms fintype_axioms.
Require Import Setoid Morphisms Relation_Definitions.

Module renSubst.

Inductive ty (n_ty : nat) : Type :=
  | var_ty : fin n_ty -> ty n_ty
  | arr : ty n_ty -> ty n_ty -> ty n_ty
  | all : ty (S n_ty) -> ty n_ty.

Lemma congr_arr {m_ty : nat} {s0 : ty m_ty} {s1 : ty m_ty} {t0 : ty m_ty}
  {t1 : ty m_ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  arr m_ty s0 s1 = arr m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => arr m_ty x s1) H0))
         (ap (fun x => arr m_ty t0 x) H1)).
Qed.

Lemma congr_all {m_ty : nat} {s0 : ty (S m_ty)} {t0 : ty (S m_ty)}
  (H0 : s0 = t0) : all m_ty s0 = all m_ty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => all m_ty x) H0)).
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
  | arr _ s0 s1 => arr n_ty (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | all _ s0 => all n_ty (ren_ty (upRen_ty_ty xi_ty) s0)
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
  | arr _ s0 s1 => arr n_ty (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | all _ s0 => all n_ty (subst_ty (up_ty_ty sigma_ty) s0)
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
  | arr _ s0 s1 =>
      congr_arr (idSubst_ty sigma_ty Eq_ty s0) (idSubst_ty sigma_ty Eq_ty s1)
  | all _ s0 =>
      congr_all (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ Eq_ty) s0)
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
  | arr _ s0 s1 =>
      congr_arr (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (extRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upExtRen_ty_ty _ _ Eq_ty) s0)
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
  | arr _ s0 s1 =>
      congr_arr (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (ext_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty) (upExt_ty_ty _ _ Eq_ty)
           s0)
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
  | arr _ s0 s1 =>
      congr_arr (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compRenRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upRen_ty_ty rho_ty) (up_ren_ren _ _ _ Eq_ty) s0)
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
  | arr _ s0 s1 =>
      congr_arr (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compRenSubst_ty (upRen_ty_ty xi_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_ren_subst_ty_ty _ _ _ Eq_ty) s0)
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
  | arr _ s0 s1 =>
      congr_arr (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compSubstRen_ty (up_ty_ty sigma_ty) (upRen_ty_ty zeta_ty)
           (up_ty_ty theta_ty) (up_subst_ren_ty_ty _ _ _ Eq_ty) s0)
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
  | arr _ s0 s1 =>
      congr_arr (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compSubstSubst_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_subst_subst_ty_ty _ _ _ Eq_ty) s0)
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
  | arr _ s0 s1 =>
      congr_arr (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (rinst_inst_ty (upRen_ty_ty xi_ty) (up_ty_ty sigma_ty)
           (rinstInst_up_ty_ty _ _ Eq_ty) s0)
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

Inductive tm (n_ty n_vl : nat) : Type :=
  | app : tm n_ty n_vl -> tm n_ty n_vl -> tm n_ty n_vl
  | tapp : tm n_ty n_vl -> ty n_ty -> tm n_ty n_vl
  | vt : vl n_ty n_vl -> tm n_ty n_vl
with vl (n_ty n_vl : nat) : Type :=
  | var_vl : fin n_vl -> vl n_ty n_vl
  | lam : ty n_ty -> tm n_ty (S n_vl) -> vl n_ty n_vl
  | tlam : tm (S n_ty) n_vl -> vl n_ty n_vl.

Lemma congr_app {m_ty m_vl : nat} {s0 : tm m_ty m_vl} {s1 : tm m_ty m_vl}
  {t0 : tm m_ty m_vl} {t1 : tm m_ty m_vl} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_ty m_vl s0 s1 = app m_ty m_vl t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_ty m_vl x s1) H0))
         (ap (fun x => app m_ty m_vl t0 x) H1)).
Qed.

Lemma congr_tapp {m_ty m_vl : nat} {s0 : tm m_ty m_vl} {s1 : ty m_ty}
  {t0 : tm m_ty m_vl} {t1 : ty m_ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  tapp m_ty m_vl s0 s1 = tapp m_ty m_vl t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tapp m_ty m_vl x s1) H0))
         (ap (fun x => tapp m_ty m_vl t0 x) H1)).
Qed.

Lemma congr_vt {m_ty m_vl : nat} {s0 : vl m_ty m_vl} {t0 : vl m_ty m_vl}
  (H0 : s0 = t0) : vt m_ty m_vl s0 = vt m_ty m_vl t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => vt m_ty m_vl x) H0)).
Qed.

Lemma congr_lam {m_ty m_vl : nat} {s0 : ty m_ty} {s1 : tm m_ty (S m_vl)}
  {t0 : ty m_ty} {t1 : tm m_ty (S m_vl)} (H0 : s0 = t0) (H1 : s1 = t1) :
  lam m_ty m_vl s0 s1 = lam m_ty m_vl t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lam m_ty m_vl x s1) H0))
         (ap (fun x => lam m_ty m_vl t0 x) H1)).
Qed.

Lemma congr_tlam {m_ty m_vl : nat} {s0 : tm (S m_ty) m_vl}
  {t0 : tm (S m_ty) m_vl} (H0 : s0 = t0) :
  tlam m_ty m_vl s0 = tlam m_ty m_vl t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tlam m_ty m_vl x) H0)).
Qed.

Lemma upRen_ty_vl {m : nat} {n : nat} (xi : fin m -> fin n) : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_vl_ty {m : nat} {n : nat} (xi : fin m -> fin n) : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_vl_vl {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_ty_vl (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_vl_ty (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_vl_vl (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_tm {m_ty m_vl : nat} {n_ty n_vl : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
(s : tm m_ty m_vl) {struct s} : tm n_ty n_vl :=
  match s with
  | app _ _ s0 s1 =>
      app n_ty n_vl (ren_tm xi_ty xi_vl s0) (ren_tm xi_ty xi_vl s1)
  | tapp _ _ s0 s1 =>
      tapp n_ty n_vl (ren_tm xi_ty xi_vl s0) (ren_ty xi_ty s1)
  | vt _ _ s0 => vt n_ty n_vl (ren_vl xi_ty xi_vl s0)
  end
with ren_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
(s : vl m_ty m_vl) {struct s} : vl n_ty n_vl :=
  match s with
  | var_vl _ _ s0 => var_vl n_ty n_vl (xi_vl s0)
  | lam _ _ s0 s1 =>
      lam n_ty n_vl (ren_ty xi_ty s0)
        (ren_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl) s1)
  | tlam _ _ s0 =>
      tlam n_ty n_vl (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl) s0)
  end.

Lemma up_ty_vl {m : nat} {n_ty n_vl : nat} (sigma : fin m -> vl n_ty n_vl) :
  fin m -> vl (S n_ty) n_vl.
Proof.
exact (funcomp (ren_vl shift id) sigma).
Defined.

Lemma up_vl_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty) :
  fin m -> ty n_ty.
Proof.
exact (funcomp (ren_ty id) sigma).
Defined.

Lemma up_vl_vl {m : nat} {n_ty n_vl : nat} (sigma : fin m -> vl n_ty n_vl) :
  fin (S m) -> vl n_ty (S n_vl).
Proof.
exact (scons (var_vl n_ty (S n_vl) var_zero)
         (funcomp (ren_vl id shift) sigma)).
Defined.

Lemma up_list_ty_vl (p : nat) {m : nat} {n_ty n_vl : nat}
  (sigma : fin m -> vl n_ty n_vl) : fin m -> vl (plus p n_ty) n_vl.
Proof.
exact (funcomp (ren_vl (shift_p p) id) sigma).
Defined.

Lemma up_list_vl_ty (p : nat) {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) : fin m -> ty n_ty.
Proof.
exact (funcomp (ren_ty id) sigma).
Defined.

Lemma up_list_vl_vl (p : nat) {m : nat} {n_ty n_vl : nat}
  (sigma : fin m -> vl n_ty n_vl) : fin (plus p m) -> vl n_ty (plus p n_vl).
Proof.
exact (scons_p p (funcomp (var_vl n_ty (plus p n_vl)) (zero_p p))
         (funcomp (ren_vl id (shift_p p)) sigma)).
Defined.

Fixpoint subst_tm {m_ty m_vl : nat} {n_ty n_vl : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl)
(s : tm m_ty m_vl) {struct s} : tm n_ty n_vl :=
  match s with
  | app _ _ s0 s1 =>
      app n_ty n_vl (subst_tm sigma_ty sigma_vl s0)
        (subst_tm sigma_ty sigma_vl s1)
  | tapp _ _ s0 s1 =>
      tapp n_ty n_vl (subst_tm sigma_ty sigma_vl s0) (subst_ty sigma_ty s1)
  | vt _ _ s0 => vt n_ty n_vl (subst_vl sigma_ty sigma_vl s0)
  end
with subst_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl)
(s : vl m_ty m_vl) {struct s} : vl n_ty n_vl :=
  match s with
  | var_vl _ _ s0 => sigma_vl s0
  | lam _ _ s0 s1 =>
      lam n_ty n_vl (subst_ty sigma_ty s0)
        (subst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl) s1)
  | tlam _ _ s0 =>
      tlam n_ty n_vl (subst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl) s0)
  end.

Lemma upId_ty_vl {m_ty m_vl : nat} (sigma : fin m_vl -> vl m_ty m_vl)
  (Eq : forall x, sigma x = var_vl m_ty m_vl x) :
  forall x, up_ty_vl sigma x = var_vl (S m_ty) m_vl x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma upId_vl_ty {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_vl_ty sigma x = var_ty m_ty x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upId_vl_vl {m_ty m_vl : nat} (sigma : fin m_vl -> vl m_ty m_vl)
  (Eq : forall x, sigma x = var_vl m_ty m_vl x) :
  forall x, up_vl_vl sigma x = var_vl m_ty (S m_vl) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_ty_vl {p : nat} {m_ty m_vl : nat}
  (sigma : fin m_vl -> vl m_ty m_vl)
  (Eq : forall x, sigma x = var_vl m_ty m_vl x) :
  forall x, up_list_ty_vl p sigma x = var_vl (plus p m_ty) m_vl x.
Proof.
exact (fun n => ap (ren_vl (shift_p p) id) (Eq n)).
Qed.

Lemma upId_list_vl_ty {p : nat} {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_list_vl_ty p sigma x = var_ty m_ty x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upId_list_vl_vl {p : nat} {m_ty m_vl : nat}
  (sigma : fin m_vl -> vl m_ty m_vl)
  (Eq : forall x, sigma x = var_vl m_ty m_vl x) :
  forall x, up_list_vl_vl p sigma x = var_vl m_ty (plus p m_vl) x.
Proof.
exact (fun n =>
       scons_p_eta (var_vl m_ty (plus p m_vl))
         (fun n => ap (ren_vl id (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_tm {m_ty m_vl : nat} (sigma_ty : fin m_ty -> ty m_ty)
(sigma_vl : fin m_vl -> vl m_ty m_vl)
(Eq_ty : forall x, sigma_ty x = var_ty m_ty x)
(Eq_vl : forall x, sigma_vl x = var_vl m_ty m_vl x) (s : tm m_ty m_vl)
{struct s} : subst_tm sigma_ty sigma_vl s = s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | vt _ _ s0 => congr_vt (idSubst_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
  end
with idSubst_vl {m_ty m_vl : nat} (sigma_ty : fin m_ty -> ty m_ty)
(sigma_vl : fin m_vl -> vl m_ty m_vl)
(Eq_ty : forall x, sigma_ty x = var_ty m_ty x)
(Eq_vl : forall x, sigma_vl x = var_vl m_ty m_vl x) (s : vl m_ty m_vl)
{struct s} : subst_vl sigma_ty sigma_vl s = s :=
  match s with
  | var_vl _ _ s0 => Eq_vl s0
  | lam _ _ s0 s1 =>
      congr_lam (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (upId_vl_ty _ Eq_ty) (upId_vl_vl _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (idSubst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (upId_ty_ty _ Eq_ty) (upId_ty_vl _ Eq_vl) s0)
  end.

Lemma upExtRen_ty_vl {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_vl xi x = upRen_ty_vl zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_vl_ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_vl_ty xi x = upRen_vl_ty zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_vl_vl {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_vl_vl xi x = upRen_vl_vl zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_ty_vl {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_ty_vl p xi x = upRen_list_ty_vl p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_vl_ty {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_vl_ty p xi x = upRen_list_vl_ty p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_vl_vl {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_vl_vl p xi x = upRen_list_vl_vl p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_tm {m_ty m_vl : nat} {n_ty n_vl : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
(zeta_ty : fin m_ty -> fin n_ty) (zeta_vl : fin m_vl -> fin n_vl)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_vl : forall x, xi_vl x = zeta_vl x) (s : tm m_ty m_vl) {struct s} :
ren_tm xi_ty xi_vl s = ren_tm zeta_ty zeta_vl s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
        (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt (extRen_vl xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
  end
with extRen_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
(zeta_ty : fin m_ty -> fin n_ty) (zeta_vl : fin m_vl -> fin n_vl)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_vl : forall x, xi_vl x = zeta_vl x) (s : vl m_ty m_vl) {struct s} :
ren_vl xi_ty xi_vl s = ren_vl zeta_ty zeta_vl s :=
  match s with
  | var_vl _ _ s0 => ap (var_vl n_ty n_vl) (Eq_vl s0)
  | lam _ _ s0 s1 =>
      congr_lam (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl)
           (upExtRen_vl_ty _ _ Eq_ty) (upExtRen_vl_vl _ _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (extRen_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl)
           (upExtRen_ty_ty _ _ Eq_ty) (upExtRen_ty_vl _ _ Eq_vl) s0)
  end.

Lemma upExt_ty_vl {m : nat} {n_ty n_vl : nat} (sigma : fin m -> vl n_ty n_vl)
  (tau : fin m -> vl n_ty n_vl) (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_vl sigma x = up_ty_vl tau x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma upExt_vl_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty)
  (tau : fin m -> ty n_ty) (Eq : forall x, sigma x = tau x) :
  forall x, up_vl_ty sigma x = up_vl_ty tau x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upExt_vl_vl {m : nat} {n_ty n_vl : nat} (sigma : fin m -> vl n_ty n_vl)
  (tau : fin m -> vl n_ty n_vl) (Eq : forall x, sigma x = tau x) :
  forall x, up_vl_vl sigma x = up_vl_vl tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_ty_vl {p : nat} {m : nat} {n_ty n_vl : nat}
  (sigma : fin m -> vl n_ty n_vl) (tau : fin m -> vl n_ty n_vl)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ty_vl p sigma x = up_list_ty_vl p tau x.
Proof.
exact (fun n => ap (ren_vl (shift_p p) id) (Eq n)).
Qed.

Lemma upExt_list_vl_ty {p : nat} {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) (tau : fin m -> ty n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_vl_ty p sigma x = up_list_vl_ty p tau x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upExt_list_vl_vl {p : nat} {m : nat} {n_ty n_vl : nat}
  (sigma : fin m -> vl n_ty n_vl) (tau : fin m -> vl n_ty n_vl)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_vl_vl p sigma x = up_list_vl_vl p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_vl id (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_tm {m_ty m_vl : nat} {n_ty n_vl : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl)
(tau_ty : fin m_ty -> ty n_ty) (tau_vl : fin m_vl -> vl n_ty n_vl)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_vl : forall x, sigma_vl x = tau_vl x) (s : tm m_ty m_vl) {struct s} :
subst_tm sigma_ty sigma_vl s = subst_tm tau_ty tau_vl s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
        (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt (ext_vl sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
  end
with ext_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl)
(tau_ty : fin m_ty -> ty n_ty) (tau_vl : fin m_vl -> vl n_ty n_vl)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_vl : forall x, sigma_vl x = tau_vl x) (s : vl m_ty m_vl) {struct s} :
subst_vl sigma_ty sigma_vl s = subst_vl tau_ty tau_vl s :=
  match s with
  | var_vl _ _ s0 => Eq_vl s0
  | lam _ _ s0 s1 =>
      congr_lam (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl) (up_vl_ty tau_ty)
           (up_vl_vl tau_vl) (upExt_vl_ty _ _ Eq_ty) (upExt_vl_vl _ _ Eq_vl)
           s1)
  | tlam _ _ s0 =>
      congr_tlam
        (ext_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl) (up_ty_ty tau_ty)
           (up_ty_vl tau_vl) (upExt_ty_ty _ _ Eq_ty) (upExt_ty_vl _ _ Eq_vl)
           s0)
  end.

Lemma up_ren_ren_ty_vl {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_vl zeta) (upRen_ty_vl xi) x = upRen_ty_vl rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_vl_ty {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_vl_ty zeta) (upRen_vl_ty xi) x = upRen_vl_ty rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_vl_vl {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_vl_vl zeta) (upRen_vl_vl xi) x = upRen_vl_vl rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_ty_vl {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_ty_vl p zeta) (upRen_list_ty_vl p xi) x =
  upRen_list_ty_vl p rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_list_vl_ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_vl_ty p zeta) (upRen_list_vl_ty p xi) x =
  upRen_list_vl_ty p rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_list_vl_vl {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_vl_vl p zeta) (upRen_list_vl_vl p xi) x =
  upRen_list_vl_vl p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
(xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
(zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl)
(rho_ty : fin m_ty -> fin l_ty) (rho_vl : fin m_vl -> fin l_vl)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_vl : forall x, funcomp zeta_vl xi_vl x = rho_vl x) (s : tm m_ty m_vl)
{struct s} :
ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s) = ren_tm rho_ty rho_vl s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0)
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0) (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0)
  end
with compRenRen_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
(xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
(zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl)
(rho_ty : fin m_ty -> fin l_ty) (rho_vl : fin m_vl -> fin l_vl)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_vl : forall x, funcomp zeta_vl xi_vl x = rho_vl x) (s : vl m_ty m_vl)
{struct s} :
ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s) = ren_vl rho_ty rho_vl s :=
  match s with
  | var_vl _ _ s0 => ap (var_vl l_ty l_vl) (Eq_vl s0)
  | lam _ _ s0 s1 =>
      congr_lam (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl) (upRen_vl_ty rho_ty)
           (upRen_vl_vl rho_vl) Eq_ty (up_ren_ren _ _ _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (compRenRen_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl) (upRen_ty_ty rho_ty)
           (upRen_ty_vl rho_vl) (up_ren_ren _ _ _ Eq_ty) Eq_vl s0)
  end.

Lemma up_ren_subst_ty_vl {k : nat} {l : nat} {m_ty m_vl : nat}
  (xi : fin k -> fin l) (tau : fin l -> vl m_ty m_vl)
  (theta : fin k -> vl m_ty m_vl) (Eq : forall x, funcomp tau xi x = theta x)
  : forall x, funcomp (up_ty_vl tau) (upRen_ty_vl xi) x = up_ty_vl theta x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma up_ren_subst_vl_ty {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_vl_ty tau) (upRen_vl_ty xi) x = up_vl_ty theta x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma up_ren_subst_vl_vl {k : nat} {l : nat} {m_ty m_vl : nat}
  (xi : fin k -> fin l) (tau : fin l -> vl m_ty m_vl)
  (theta : fin k -> vl m_ty m_vl) (Eq : forall x, funcomp tau xi x = theta x)
  : forall x, funcomp (up_vl_vl tau) (upRen_vl_vl xi) x = up_vl_vl theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_ty_vl {p : nat} {k : nat} {l : nat} {m_ty m_vl : nat}
  (xi : fin k -> fin l) (tau : fin l -> vl m_ty m_vl)
  (theta : fin k -> vl m_ty m_vl) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_list_ty_vl p tau) (upRen_list_ty_vl p xi) x =
  up_list_ty_vl p theta x.
Proof.
exact (fun n => ap (ren_vl (shift_p p) id) (Eq n)).
Qed.

Lemma up_ren_subst_list_vl_ty {p : nat} {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_vl_ty p tau) (upRen_list_vl_ty p xi) x =
  up_list_vl_ty p theta x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma up_ren_subst_list_vl_vl {p : nat} {k : nat} {l : nat} {m_ty m_vl : nat}
  (xi : fin k -> fin l) (tau : fin l -> vl m_ty m_vl)
  (theta : fin k -> vl m_ty m_vl) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_list_vl_vl p tau) (upRen_list_vl_vl p xi) x =
  up_list_vl_vl p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_vl id (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_tm {k_ty k_vl : nat} {l_ty l_vl : nat}
{m_ty m_vl : nat} (xi_ty : fin m_ty -> fin k_ty)
(xi_vl : fin m_vl -> fin k_vl) (tau_ty : fin k_ty -> ty l_ty)
(tau_vl : fin k_vl -> vl l_ty l_vl) (theta_ty : fin m_ty -> ty l_ty)
(theta_vl : fin m_vl -> vl l_ty l_vl)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_vl : forall x, funcomp tau_vl xi_vl x = theta_vl x) (s : tm m_ty m_vl)
{struct s} :
subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s) = subst_tm theta_ty theta_vl s
:=
  match s with
  | app _ _ s0 s1 =>
      congr_app
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0)
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0) (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compRenSubst_vl xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0)
  end
with compRenSubst_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
(xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
(tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl)
(theta_ty : fin m_ty -> ty l_ty) (theta_vl : fin m_vl -> vl l_ty l_vl)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_vl : forall x, funcomp tau_vl xi_vl x = theta_vl x) (s : vl m_ty m_vl)
{struct s} :
subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s) = subst_vl theta_ty theta_vl s
:=
  match s with
  | var_vl _ _ s0 => Eq_vl s0
  | lam _ _ s0 s1 =>
      congr_lam (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (up_vl_ty tau_ty) (up_vl_vl tau_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_ren_subst_vl_ty _ _ _ Eq_ty)
           (up_ren_subst_vl_vl _ _ _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (compRenSubst_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (up_ty_ty tau_ty) (up_ty_vl tau_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_ren_subst_ty_ty _ _ _ Eq_ty)
           (up_ren_subst_ty_vl _ _ _ Eq_vl) s0)
  end.

Lemma up_subst_ren_ty_vl {k : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma : fin k -> vl l_ty l_vl) (zeta_ty : fin l_ty -> fin m_ty)
  (zeta_vl : fin l_vl -> fin m_vl) (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl))
    (up_ty_vl sigma) x = up_ty_vl theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_vl shift id (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl)
            (funcomp shift zeta_ty) (funcomp id zeta_vl) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_vl zeta_ty zeta_vl shift id
                  (funcomp shift zeta_ty) (funcomp id zeta_vl)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_vl shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_vl_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_vl_ty zeta_ty)) (up_vl_ty sigma) x =
  up_vl_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ty id (upRen_vl_ty zeta_ty) (funcomp id zeta_ty)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ty zeta_ty id (funcomp id zeta_ty)
                  (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_ren_vl_vl {k : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma : fin k -> vl l_ty l_vl) (zeta_ty : fin l_ty -> fin m_ty)
  (zeta_vl : fin l_vl -> fin m_vl) (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl))
    (up_vl_vl sigma) x = up_vl_vl theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_vl id shift (upRen_vl_ty zeta_ty)
                (upRen_vl_vl zeta_vl) (funcomp id zeta_ty)
                (funcomp shift zeta_vl) (fun x => eq_refl) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_vl zeta_ty zeta_vl id shift
                      (funcomp id zeta_ty) (funcomp shift zeta_vl)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_vl id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_ty_vl {p : nat} {k : nat} {l_ty l_vl : nat}
  {m_ty m_vl : nat} (sigma : fin k -> vl l_ty l_vl)
  (zeta_ty : fin l_ty -> fin m_ty) (zeta_vl : fin l_vl -> fin m_vl)
  (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_list_ty_ty p zeta_ty) (upRen_list_ty_vl p zeta_vl))
    (up_list_ty_vl p sigma) x = up_list_ty_vl p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_vl (shift_p p) id (upRen_list_ty_ty p zeta_ty)
            (upRen_list_ty_vl p zeta_vl) (funcomp (shift_p p) zeta_ty)
            (funcomp id zeta_vl) (fun x => scons_p_tail' _ _ x)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_vl zeta_ty zeta_vl (shift_p p) id
                  (funcomp (shift_p p) zeta_ty) (funcomp id zeta_vl)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_vl (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_vl_ty {p : nat} {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_list_vl_ty p zeta_ty)) (up_list_vl_ty p sigma) x =
  up_list_vl_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ty id (upRen_list_vl_ty p zeta_ty) (funcomp id zeta_ty)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ty zeta_ty id (funcomp id zeta_ty)
                  (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_vl_vl {p : nat} {k : nat} {l_ty l_vl : nat}
  {m_ty m_vl : nat} (sigma : fin k -> vl l_ty l_vl)
  (zeta_ty : fin l_ty -> fin m_ty) (zeta_vl : fin l_vl -> fin m_vl)
  (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_list_vl_ty p zeta_ty) (upRen_list_vl_vl p zeta_vl))
    (up_list_vl_vl p sigma) x = up_list_vl_vl p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_vl m_ty (plus p m_vl)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_vl id (shift_p p) (upRen_list_vl_ty p zeta_ty)
                  (upRen_list_vl_vl p zeta_vl) (funcomp id zeta_ty)
                  (funcomp (shift_p p) zeta_vl) (fun x => eq_refl)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_vl zeta_ty zeta_vl id (shift_p p)
                        (funcomp id zeta_ty) (funcomp (shift_p p) zeta_vl)
                        (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
                  (ap (ren_vl id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_tm {k_ty k_vl : nat} {l_ty l_vl : nat}
{m_ty m_vl : nat} (sigma_ty : fin m_ty -> ty k_ty)
(sigma_vl : fin m_vl -> vl k_ty k_vl) (zeta_ty : fin k_ty -> fin l_ty)
(zeta_vl : fin k_vl -> fin l_vl) (theta_ty : fin m_ty -> ty l_ty)
(theta_vl : fin m_vl -> vl l_ty l_vl)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x = theta_vl x)
(s : tm m_ty m_vl) {struct s} :
ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s) =
subst_tm theta_ty theta_vl s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
  end
with compSubstRen_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
(sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
(zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl)
(theta_ty : fin m_ty -> ty l_ty) (theta_vl : fin m_vl -> vl l_ty l_vl)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x = theta_vl x)
(s : vl m_ty m_vl) {struct s} :
ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s) =
subst_vl theta_ty theta_vl s :=
  match s with
  | var_vl _ _ s0 => Eq_vl s0
  | lam _ _ s0 s1 =>
      congr_lam (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_subst_ren_vl_ty _ _ _ Eq_ty)
           (up_subst_ren_vl_vl _ _ _ _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (compSubstRen_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_subst_ren_ty_ty _ _ _ Eq_ty)
           (up_subst_ren_ty_vl _ _ _ _ Eq_vl) s0)
  end.

Lemma up_subst_subst_ty_vl {k : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma : fin k -> vl l_ty l_vl) (tau_ty : fin l_ty -> ty m_ty)
  (tau_vl : fin l_vl -> vl m_ty m_vl) (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_ty_ty tau_ty) (up_ty_vl tau_vl)) (up_ty_vl sigma) x =
  up_ty_vl theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_vl shift id (up_ty_ty tau_ty) (up_ty_vl tau_vl)
            (funcomp (up_ty_ty tau_ty) shift) (funcomp (up_ty_vl tau_vl) id)
            (fun x => eq_refl) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_vl tau_ty tau_vl shift id
                  (funcomp (ren_ty shift) tau_ty)
                  (funcomp (ren_vl shift id) tau_vl) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_vl shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_vl_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_vl_ty tau_ty)) (up_vl_ty sigma) x = up_vl_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ty id (up_vl_ty tau_ty) (funcomp (up_vl_ty tau_ty) id)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty)
                  (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_subst_vl_vl {k : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma : fin k -> vl l_ty l_vl) (tau_ty : fin l_ty -> ty m_ty)
  (tau_vl : fin l_vl -> vl m_ty m_vl) (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_vl_ty tau_ty) (up_vl_vl tau_vl)) (up_vl_vl sigma) x =
  up_vl_vl theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_vl id shift (up_vl_ty tau_ty) (up_vl_vl tau_vl)
                (funcomp (up_vl_ty tau_ty) id)
                (funcomp (up_vl_vl tau_vl) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_vl tau_ty tau_vl id shift
                      (funcomp (ren_ty id) tau_ty)
                      (funcomp (ren_vl id shift) tau_vl) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_vl id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_ty_vl {p : nat} {k : nat} {l_ty l_vl : nat}
  {m_ty m_vl : nat} (sigma : fin k -> vl l_ty l_vl)
  (tau_ty : fin l_ty -> ty m_ty) (tau_vl : fin l_vl -> vl m_ty m_vl)
  (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_list_ty_ty p tau_ty) (up_list_ty_vl p tau_vl))
    (up_list_ty_vl p sigma) x = up_list_ty_vl p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_vl (shift_p p) id (up_list_ty_ty p tau_ty)
            (up_list_ty_vl p tau_vl)
            (funcomp (up_list_ty_ty p tau_ty) (shift_p p))
            (funcomp (up_list_ty_vl p tau_vl) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_vl tau_ty tau_vl (shift_p p) id _ _
                  (fun x => eq_sym (scons_p_tail' _ _ x))
                  (fun x => eq_sym eq_refl) (sigma n)))
            (ap (ren_vl (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_vl_ty {p : nat} {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_list_vl_ty p tau_ty)) (up_list_vl_ty p sigma) x =
  up_list_vl_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ty id (up_list_vl_ty p tau_ty)
            (funcomp (up_list_vl_ty p tau_ty) id) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_ty id _ (fun x => eq_sym eq_refl)
                  (sigma n))) (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_vl_vl {p : nat} {k : nat} {l_ty l_vl : nat}
  {m_ty m_vl : nat} (sigma : fin k -> vl l_ty l_vl)
  (tau_ty : fin l_ty -> ty m_ty) (tau_vl : fin l_vl -> vl m_ty m_vl)
  (theta : fin k -> vl m_ty m_vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_list_vl_ty p tau_ty) (up_list_vl_vl p tau_vl))
    (up_list_vl_vl p sigma) x = up_list_vl_vl p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_vl l_ty (plus p l_vl)) (zero_p p)) _ _
            n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_vl id (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_vl id (shift_p p) (up_list_vl_ty p tau_ty)
                  (up_list_vl_vl p tau_vl)
                  (funcomp (up_list_vl_ty p tau_ty) id)
                  (funcomp (up_list_vl_vl p tau_vl) (shift_p p))
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_vl tau_ty tau_vl id (shift_p p) _ _
                        (fun x => eq_sym eq_refl)
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_vl id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_tm {k_ty k_vl : nat} {l_ty l_vl : nat}
{m_ty m_vl : nat} (sigma_ty : fin m_ty -> ty k_ty)
(sigma_vl : fin m_vl -> vl k_ty k_vl) (tau_ty : fin k_ty -> ty l_ty)
(tau_vl : fin k_vl -> vl l_ty l_vl) (theta_ty : fin m_ty -> ty l_ty)
(theta_vl : fin m_vl -> vl l_ty l_vl)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (subst_vl tau_ty tau_vl) sigma_vl x = theta_vl x)
(s : tm m_ty m_vl) {struct s} :
subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s) =
subst_tm theta_ty theta_vl s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt
        (compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
  end
with compSubstSubst_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
(sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
(tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl)
(theta_ty : fin m_ty -> ty l_ty) (theta_vl : fin m_vl -> vl l_ty l_vl)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (subst_vl tau_ty tau_vl) sigma_vl x = theta_vl x)
(s : vl m_ty m_vl) {struct s} :
subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s) =
subst_vl theta_ty theta_vl s :=
  match s with
  | var_vl _ _ s0 => Eq_vl s0
  | lam _ _ s0 s1 =>
      congr_lam (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (up_vl_ty tau_ty) (up_vl_vl tau_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_subst_subst_vl_ty _ _ _ Eq_ty)
           (up_subst_subst_vl_vl _ _ _ _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (compSubstSubst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (up_ty_ty tau_ty) (up_ty_vl tau_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_subst_subst_ty_ty _ _ _ Eq_ty)
           (up_subst_subst_ty_vl _ _ _ _ Eq_vl) s0)
  end.

Lemma rinstInst_up_ty_vl {m : nat} {n_ty n_vl : nat} (xi : fin m -> fin n_vl)
  (sigma : fin m -> vl n_ty n_vl)
  (Eq : forall x, funcomp (var_vl n_ty n_vl) xi x = sigma x) :
  forall x,
  funcomp (var_vl (S n_ty) n_vl) (upRen_ty_vl xi) x = up_ty_vl sigma x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma rinstInst_up_vl_ty {m : nat} {n_ty : nat} (xi : fin m -> fin n_ty)
  (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x, funcomp (var_ty n_ty) (upRen_vl_ty xi) x = up_vl_ty sigma x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma rinstInst_up_vl_vl {m : nat} {n_ty n_vl : nat} (xi : fin m -> fin n_vl)
  (sigma : fin m -> vl n_ty n_vl)
  (Eq : forall x, funcomp (var_vl n_ty n_vl) xi x = sigma x) :
  forall x,
  funcomp (var_vl n_ty (S n_vl)) (upRen_vl_vl xi) x = up_vl_vl sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_ty_vl {p : nat} {m : nat} {n_ty n_vl : nat}
  (xi : fin m -> fin n_vl) (sigma : fin m -> vl n_ty n_vl)
  (Eq : forall x, funcomp (var_vl n_ty n_vl) xi x = sigma x) :
  forall x,
  funcomp (var_vl (plus p n_ty) n_vl) (upRen_list_ty_vl p xi) x =
  up_list_ty_vl p sigma x.
Proof.
exact (fun n => ap (ren_vl (shift_p p) id) (Eq n)).
Qed.

Lemma rinstInst_up_list_vl_ty {p : nat} {m : nat} {n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty n_ty) (upRen_list_vl_ty p xi) x = up_list_vl_ty p sigma x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma rinstInst_up_list_vl_vl {p : nat} {m : nat} {n_ty n_vl : nat}
  (xi : fin m -> fin n_vl) (sigma : fin m -> vl n_ty n_vl)
  (Eq : forall x, funcomp (var_vl n_ty n_vl) xi x = sigma x) :
  forall x,
  funcomp (var_vl n_ty (plus p n_vl)) (upRen_list_vl_vl p xi) x =
  up_list_vl_vl p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_vl n_ty (plus p n_vl)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_vl id (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_tm {m_ty m_vl : nat} {n_ty n_vl : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
(sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl)
(Eq_ty : forall x, funcomp (var_ty n_ty) xi_ty x = sigma_ty x)
(Eq_vl : forall x, funcomp (var_vl n_ty n_vl) xi_vl x = sigma_vl x)
(s : tm m_ty m_vl) {struct s} :
ren_tm xi_ty xi_vl s = subst_tm sigma_ty sigma_vl s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | vt _ _ s0 =>
      congr_vt (rinst_inst_vl xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
  end
with rinst_inst_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
(sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl)
(Eq_ty : forall x, funcomp (var_ty n_ty) xi_ty x = sigma_ty x)
(Eq_vl : forall x, funcomp (var_vl n_ty n_vl) xi_vl x = sigma_vl x)
(s : vl m_ty m_vl) {struct s} :
ren_vl xi_ty xi_vl s = subst_vl sigma_ty sigma_vl s :=
  match s with
  | var_vl _ _ s0 => Eq_vl s0
  | lam _ _ s0 s1 =>
      congr_lam (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (rinstInst_up_vl_ty _ _ Eq_ty) (rinstInst_up_vl_vl _ _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (rinst_inst_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (rinstInst_up_ty_ty _ _ Eq_ty) (rinstInst_up_ty_vl _ _ Eq_vl) s0)
  end.

Lemma renRen_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl)
  (s : tm m_ty m_vl) :
  ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s.
Proof.
exact (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl)
  (s : vl m_ty m_vl) :
  ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s) =
  ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s.
Proof.
exact (compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl)
  (s : tm m_ty m_vl) :
  ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s.
Proof.
exact (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl)
  (s : vl m_ty m_vl) :
  ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s) =
  subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s.
Proof.
exact (compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl)
  (s : tm m_ty m_vl) :
  subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s.
Proof.
exact (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl)
  (s : vl m_ty m_vl) :
  subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s) =
  subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s.
Proof.
exact (compRenSubst_vl xi_ty xi_vl tau_ty tau_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl)
  (s : tm m_ty m_vl) :
  subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s.
Proof.
exact (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl)
  (s : vl m_ty m_vl) :
  subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s) =
  subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s.
Proof.
exact (compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm {m_ty m_vl : nat} {n_ty n_vl : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
  (s : tm m_ty m_vl) :
  ren_tm xi_ty xi_vl s =
  subst_tm (funcomp (var_ty n_ty) xi_ty) (funcomp (var_vl n_ty n_vl) xi_vl) s.
Proof.
exact (rinst_inst_tm xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
  (s : vl m_ty m_vl) :
  ren_vl xi_ty xi_vl s =
  subst_vl (funcomp (var_ty n_ty) xi_ty) (funcomp (var_vl n_ty n_vl) xi_vl) s.
Proof.
exact (rinst_inst_vl xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm {m_ty m_vl : nat} (s : tm m_ty m_vl) :
  subst_tm (var_ty m_ty) (var_vl m_ty m_vl) s = s.
Proof.
exact (idSubst_tm (var_ty m_ty) (var_vl m_ty m_vl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_vl {m_ty m_vl : nat} (s : vl m_ty m_vl) :
  subst_vl (var_ty m_ty) (var_vl m_ty m_vl) s = s.
Proof.
exact (idSubst_vl (var_ty m_ty) (var_vl m_ty m_vl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm {m_ty m_vl : nat} (s : tm m_ty m_vl) : ren_tm id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma rinstId'_vl {m_ty m_vl : nat} (s : vl m_ty m_vl) : ren_vl id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_vl s) (rinstInst'_vl id id s)).
Qed.

Lemma varL'_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
  (sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl)
  (x : fin m_vl) :
  subst_vl sigma_ty sigma_vl (var_vl m_ty m_vl x) = sigma_vl x.
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl)
  (x : fin m_vl) :
  ren_vl xi_ty xi_vl (var_vl m_ty m_vl x) = var_vl n_ty n_vl (xi_vl x).
Proof.
exact (eq_refl).
Qed.

Class Up_vl X Y :=
    up_vl : X -> Y.

Class Up_tm X Y :=
    up_tm : X -> Y.

Class Up_ty X Y :=
    up_ty : X -> Y.

Instance Subst_vl  {m_ty m_vl n_ty n_vl : nat}: (Subst2 _ _ _ _) :=
 (@subst_vl m_ty m_vl n_ty n_vl).

Instance Subst_tm  {m_ty m_vl n_ty n_vl : nat}: (Subst2 _ _ _ _) :=
 (@subst_tm m_ty m_vl n_ty n_vl).

Instance Up_vl_vl  {m n_ty n_vl : nat}: (Up_vl _ _) :=
 (@up_vl_vl m n_ty n_vl).

Instance Up_vl_ty  {m n_ty : nat}: (Up_ty _ _) := (@up_vl_ty m n_ty).

Instance Up_ty_vl  {m n_ty n_vl : nat}: (Up_vl _ _) :=
 (@up_ty_vl m n_ty n_vl).

Instance Ren_vl  {m_ty m_vl n_ty n_vl : nat}: (Ren2 _ _ _ _) :=
 (@ren_vl m_ty m_vl n_ty n_vl).

Instance Ren_tm  {m_ty m_vl n_ty n_vl : nat}: (Ren2 _ _ _ _) :=
 (@ren_tm m_ty m_vl n_ty n_vl).

Instance VarInstance_vl  {n_ty n_vl : nat}: (Var _ _) := (@var_vl n_ty n_vl).

Instance Subst_ty  {m_ty n_ty : nat}: (Subst1 _ _ _) := (@subst_ty m_ty n_ty).

Instance Up_ty_ty  {m n_ty : nat}: (Up_ty _ _) := (@up_ty_ty m n_ty).

Instance Ren_ty  {m_ty n_ty : nat}: (Ren1 _ _ _) := (@ren_ty m_ty n_ty).

Instance VarInstance_ty  {n_ty : nat}: (Var _ _) := (@var_ty n_ty).

Notation "[ sigma_ty ; sigma_vl ]" := (subst_vl sigma_ty sigma_vl)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_ty ; sigma_vl ]" := (subst_vl sigma_ty sigma_vl s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__vl" := up_vl (only printing) : subst_scope.

Notation "[ sigma_ty ; sigma_vl ]" := (subst_tm sigma_ty sigma_vl)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_ty ; sigma_vl ]" := (subst_tm sigma_ty sigma_vl s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__tm" := up_tm (only printing) : subst_scope.

Notation "↑__vl" := up_vl_vl (only printing) : subst_scope.

Notation "↑__ty" := up_vl_ty (only printing) : subst_scope.

Notation "↑__vl" := up_ty_vl (only printing) : subst_scope.

Notation "⟨ xi_ty ; xi_vl ⟩" := (ren_vl xi_ty xi_vl)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_ty ; xi_vl ⟩" := (ren_vl xi_ty xi_vl s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xi_ty ; xi_vl ⟩" := (ren_tm xi_ty xi_vl)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_ty ; xi_vl ⟩" := (ren_tm xi_ty xi_vl s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := var_vl ( at level 1, only printing) : subst_scope.

Notation "x '__vl'" := (@ids _ _ VarInstance_vl x)
  ( at level 5, format "x __vl", only printing) : subst_scope.

Notation "x '__vl'" := (var_vl x) ( at level 5, format "x __vl") :
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

Instance subst_vl_morphism  {m_ty m_vl : nat} {n_ty n_vl : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_vl m_ty m_vl n_ty n_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => subst_vl f_ty f_vl s = subst_vl g_ty g_vl t')
         (ext_vl f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
Qed.

Instance subst_tm_morphism  {m_ty m_vl : nat} {n_ty n_vl : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_tm m_ty m_vl n_ty n_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_ty f_vl s = subst_tm g_ty g_vl t')
         (ext_tm f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
Qed.

Instance ren_vl_morphism  {m_ty m_vl : nat} {n_ty n_vl : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_vl m_ty m_vl n_ty n_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => ren_vl f_ty f_vl s = ren_vl g_ty g_vl t')
         (extRen_vl f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
Qed.

Instance ren_tm_morphism  {m_ty m_vl : nat} {n_ty n_vl : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_tm m_ty m_vl n_ty n_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_ty f_vl s = ren_tm g_ty g_vl t')
         (extRen_tm f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
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
                      VarInstance_vl, Var, ids, Ren_tm, Ren2, ren2, Ren_vl,
                      Ren2, ren2, Up_ty_vl, Up_vl, up_vl, Up_vl_ty, Up_ty,
                      up_ty, Up_vl_vl, Up_vl, up_vl, Subst_tm, Subst2,
                      subst2, Subst_vl, Subst2, subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_ty, Var, ids,
                                            Ren_ty, Ren1, ren1, Up_ty_ty,
                                            Up_ty, up_ty, Subst_ty, Subst1,
                                            subst1, VarInstance_vl, Var, ids,
                                            Ren_tm, Ren2, ren2, Ren_vl, Ren2,
                                            ren2, Up_ty_vl, Up_vl, up_vl,
                                            Up_vl_ty, Up_ty, up_ty, Up_vl_vl,
                                            Up_vl, up_vl, Subst_tm, Subst2,
                                            subst2, Subst_vl, Subst2, subst2
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_vl
                 | progress rewrite ?substSubst_vl
                 | progress setoid_rewrite substSubst_tm
                 | progress rewrite ?substSubst_tm
                 | progress setoid_rewrite renSubst_vl
                 | progress rewrite ?renSubst_vl
                 | progress setoid_rewrite renSubst_tm
                 | progress rewrite ?renSubst_tm
                 | progress setoid_rewrite substRen_vl
                 | progress rewrite ?substRen_vl
                 | progress setoid_rewrite substRen_tm
                 | progress rewrite ?substRen_tm
                 | progress setoid_rewrite renRen_vl
                 | progress rewrite ?renRen_vl
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
                 | progress setoid_rewrite varLRen'_vl
                 | progress rewrite ?varLRen'_vl
                 | progress setoid_rewrite varL'_vl
                 | progress rewrite ?varL'_vl
                 | progress setoid_rewrite rinstId'_vl
                 | progress rewrite ?rinstId'_vl
                 | progress setoid_rewrite rinstId'_tm
                 | progress rewrite ?rinstId'_tm
                 | progress setoid_rewrite instId'_vl
                 | progress rewrite ?instId'_vl
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
                    unfold up_list_vl_vl, up_list_vl_ty, up_list_ty_vl,
                     up_vl_vl, up_vl_ty, up_ty_vl, upRen_list_vl_vl,
                     upRen_list_vl_ty, upRen_list_ty_vl, upRen_vl_vl,
                     upRen_vl_ty, upRen_ty_vl, up_list_ty_ty, up_ty_ty,
                     upRen_list_ty_ty, upRen_ty_ty, up_ren
                 | progress
                    cbn[subst_vl subst_tm ren_vl ren_tm subst_ty ren_ty]
                 | progress fsimpl
                 | repeat unfold funcomp ]).

Ltac asimpl := repeat try unfold_funcomp;
                repeat
                 unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                  Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                  VarInstance_vl, Var, ids, Ren_tm, Ren2, ren2, Ren_vl, Ren2,
                  ren2, Up_ty_vl, Up_vl, up_vl, Up_vl_ty, Up_ty, up_ty,
                  Up_vl_vl, Up_vl, up_vl, Subst_tm, Subst2, subst2, Subst_vl,
                  Subst2, subst2 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try repeat erewrite ?rinstInst'_vl;
                  try repeat erewrite ?rinstInst'_tm;
                  try repeat erewrite ?rinstInst'_ty.

Ltac renamify := auto_unfold; try repeat erewrite <- ?rinstInst'_vl;
                  try repeat erewrite <- ?rinstInst'_tm;
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

Lemma rinstInst_tm {m_ty m_vl : nat} {n_ty n_vl : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl) :
  ren_tm xi_ty xi_vl =
  subst_tm (funcomp (var_ty n_ty) xi_ty) (funcomp (var_vl n_ty n_vl) xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          rinst_inst_tm xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl)
            x)).
Qed.

Lemma rinstInst_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl) :
  ren_vl xi_ty xi_vl =
  subst_vl (funcomp (var_ty n_ty) xi_ty) (funcomp (var_vl n_ty n_vl) xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          rinst_inst_vl xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl)
            x)).
Qed.

Lemma instId_tm {m_ty m_vl : nat} :
  subst_tm (var_ty m_ty) (var_vl m_ty m_vl) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          idSubst_tm (var_ty m_ty) (var_vl m_ty m_vl) (fun n => eq_refl)
            (fun n => eq_refl) (id x))).
Qed.

Lemma instId_vl {m_ty m_vl : nat} :
  subst_vl (var_ty m_ty) (var_vl m_ty m_vl) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          idSubst_vl (var_ty m_ty) (var_vl m_ty m_vl) (fun n => eq_refl)
            (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_tm {m_ty m_vl : nat} : @ren_tm m_ty m_vl m_ty m_vl id id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _) (id _)) instId_tm).
Qed.

Lemma rinstId_vl {m_ty m_vl : nat} : @ren_vl m_ty m_vl m_ty m_vl id id = id.
Proof.
exact (eq_trans (rinstInst_vl (id _) (id _)) instId_vl).
Qed.

Lemma varL_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
  (sigma_ty : fin m_ty -> ty n_ty) (sigma_vl : fin m_vl -> vl n_ty n_vl) :
  funcomp (subst_vl sigma_ty sigma_vl) (var_vl m_ty m_vl) = sigma_vl.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_vl {m_ty m_vl : nat} {n_ty n_vl : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_vl : fin m_vl -> fin n_vl) :
  funcomp (ren_vl xi_ty xi_vl) (var_vl m_ty m_vl) =
  funcomp (var_vl n_ty n_vl) xi_vl.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl) :
  funcomp (ren_tm zeta_ty zeta_vl) (ren_tm xi_ty xi_vl) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_tm xi_ty xi_vl zeta_ty zeta_vl n)).
Qed.

Lemma renRen'_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl) :
  funcomp (ren_vl zeta_ty zeta_vl) (ren_vl xi_ty xi_vl) =
  ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_vl xi_ty xi_vl zeta_ty zeta_vl n)).
Qed.

Lemma substRen'_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl) :
  funcomp (ren_tm zeta_ty zeta_vl) (subst_tm sigma_ty sigma_vl) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_tm sigma_ty sigma_vl zeta_ty zeta_vl n)).
Qed.

Lemma substRen'_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_vl : fin k_vl -> fin l_vl) :
  funcomp (ren_vl zeta_ty zeta_vl) (subst_vl sigma_ty sigma_vl) =
  subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_vl sigma_ty sigma_vl zeta_ty zeta_vl n)).
Qed.

Lemma renSubst'_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl) :
  funcomp (subst_tm tau_ty tau_vl) (ren_tm xi_ty xi_vl) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_tm xi_ty xi_vl tau_ty tau_vl n)).
Qed.

Lemma renSubst'_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_vl : fin m_vl -> fin k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl) :
  funcomp (subst_vl tau_ty tau_vl) (ren_vl xi_ty xi_vl) =
  subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_vl xi_ty xi_vl tau_ty tau_vl n)).
Qed.

Lemma substSubst'_tm {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl) :
  funcomp (subst_tm tau_ty tau_vl) (subst_tm sigma_ty sigma_vl) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_tm sigma_ty sigma_vl tau_ty tau_vl n)).
Qed.

Lemma substSubst'_vl {k_ty k_vl : nat} {l_ty l_vl : nat} {m_ty m_vl : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_vl : fin m_vl -> vl k_ty k_vl)
  (tau_ty : fin k_ty -> ty l_ty) (tau_vl : fin k_vl -> vl l_ty l_vl) :
  funcomp (subst_vl tau_ty tau_vl) (subst_vl sigma_ty sigma_vl) =
  subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_vl sigma_ty sigma_vl tau_ty tau_vl n)).
Qed.

Ltac asimpl_fext' := repeat (first
                      [ progress setoid_rewrite substSubst_vl
                      | progress setoid_rewrite substSubst_tm
                      | progress setoid_rewrite renSubst_vl
                      | progress setoid_rewrite renSubst_tm
                      | progress setoid_rewrite substRen_vl
                      | progress setoid_rewrite substRen_tm
                      | progress setoid_rewrite renRen_vl
                      | progress setoid_rewrite renRen_tm
                      | progress setoid_rewrite substSubst_ty
                      | progress setoid_rewrite renSubst_ty
                      | progress setoid_rewrite substRen_ty
                      | progress setoid_rewrite renRen_ty
                      | progress setoid_rewrite substSubst'_vl
                      | progress setoid_rewrite substSubst'_tm
                      | progress setoid_rewrite renSubst'_vl
                      | progress setoid_rewrite renSubst'_tm
                      | progress setoid_rewrite substRen'_vl
                      | progress setoid_rewrite substRen'_tm
                      | progress setoid_rewrite renRen'_vl
                      | progress setoid_rewrite renRen'_tm
                      | progress setoid_rewrite varLRen_vl
                      | progress setoid_rewrite varL_vl
                      | progress setoid_rewrite rinstId_vl
                      | progress setoid_rewrite rinstId_tm
                      | progress setoid_rewrite instId_vl
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
                         unfold up_list_vl_vl, up_list_vl_ty, up_list_ty_vl,
                          up_vl_vl, up_vl_ty, up_ty_vl, upRen_list_vl_vl,
                          upRen_list_vl_ty, upRen_list_ty_vl, upRen_vl_vl,
                          upRen_vl_ty, upRen_ty_vl, up_list_ty_ty, up_ty_ty,
                          upRen_list_ty_ty, upRen_ty_ty, up_ren
                      | progress
                         cbn[subst_vl subst_tm ren_vl ren_tm subst_ty ren_ty]
                      | fsimpl_fext ]).

Ltac asimpl_fext := repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                       Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                       VarInstance_vl, Var, ids, Ren_tm, Ren2, ren2, Ren_vl,
                       Ren2, ren2, Up_ty_vl, Up_vl, up_vl, Up_vl_ty, Up_ty,
                       up_ty, Up_vl_vl, Up_vl, up_vl, Subst_tm, Subst2,
                       subst2, Subst_vl, Subst2, subst2 in *; asimpl_fext';
                     repeat try unfold_funcomp.

Tactic Notation "asimpl_fext" "in" hyp(J) := revert J; asimpl_fext; intros J.

Ltac substify_fext := auto_unfold; try repeat erewrite ?rinstInst_vl;
                       try repeat erewrite ?rinstInst_tm;
                       try repeat erewrite ?rinstInst_ty.

Ltac renamify_fext := auto_unfold; try repeat erewrite <- ?rinstInst_vl;
                       try repeat erewrite <- ?rinstInst_tm;
                       try repeat erewrite <- ?rinstInst_ty.

End fext.

Module interface.

Export renSubst.

Export
fext.

Arguments tlam {n_ty n_vl}.

Arguments lam {n_ty n_vl}.

Arguments var_vl {n_ty n_vl}.

Arguments vt {n_ty n_vl}.

Arguments tapp {n_ty n_vl}.

Arguments app {n_ty n_vl}.

Arguments all {n_ty}.

Arguments arr {n_ty}.

Arguments var_ty {n_ty}.

End interface.

Export interface.

