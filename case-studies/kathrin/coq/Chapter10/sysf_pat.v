Require Import axioms fintype header_extensible.
Inductive ty (n_ty : nat) : Type :=
  | var_ty : fin n_ty -> ty n_ty
  | top : ty n_ty
  | arr : ty n_ty -> ty n_ty -> ty n_ty
  | all : ty n_ty -> ty (S n_ty) -> ty n_ty
  | recty : list (prod (nat) (ty n_ty)) -> ty n_ty.
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
Lemma congr_recty {m_ty : nat} {s0 : list (prod (nat) (ty m_ty))}
  {t0 : list (prod (nat) (ty m_ty))} (H0 : s0 = t0) :
  recty m_ty s0 = recty m_ty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => recty m_ty x) H0)).
Qed.
Definition upRen_ty_ty {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n) := up_ren xi.
Definition upRen_list_ty_ty (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n) := upRen_p p xi.
Fixpoint ren_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
(s : ty m_ty) : ty n_ty :=
  match s with
  | var_ty _ s0 => var_ty n_ty (xi_ty s0)
  | top _ => top n_ty
  | arr _ s0 s1 => arr n_ty (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | all _ s0 s1 => all n_ty (ren_ty xi_ty s0) (ren_ty (upRen_ty_ty xi_ty) s1)
  | recty _ s0 =>
      recty n_ty (list_map (prod_map (fun x => x) (ren_ty xi_ty)) s0)
  end.
Definition up_ty_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty) :
  fin (S m) -> ty (S n_ty) :=
  scons (var_ty (S n_ty) var_zero) (funcomp (ren_ty shift) sigma).
Definition up_list_ty_ty (p : nat) {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) : fin (plus p m) -> ty (plus p n_ty) :=
  scons_p p (funcomp (var_ty (plus p n_ty)) (zero_p p))
    (funcomp (ren_ty (shift_p p)) sigma).
Fixpoint subst_ty {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty)
(s : ty m_ty) : ty n_ty :=
  match s with
  | var_ty _ s0 => sigma_ty s0
  | top _ => top n_ty
  | arr _ s0 s1 => arr n_ty (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | all _ s0 s1 =>
      all n_ty (subst_ty sigma_ty s0) (subst_ty (up_ty_ty sigma_ty) s1)
  | recty _ s0 =>
      recty n_ty (list_map (prod_map (fun x => x) (subst_ty sigma_ty)) s0)
  end.
Definition upId_ty_ty {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_ty_ty sigma x = var_ty (S m_ty) x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upId_list_ty_ty {p : nat} {m_ty : nat}
  (sigma : fin m_ty -> ty m_ty) (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_list_ty_ty p sigma x = var_ty (plus p m_ty) x :=
  fun n =>
  scons_p_eta (var_ty (plus p m_ty))
    (fun n => ap (ren_ty (shift_p p)) (Eq n)) (fun n => eq_refl).
Fixpoint idSubst_ty {m_ty : nat} (sigma_ty : fin m_ty -> ty m_ty)
(Eq_ty : forall x, sigma_ty x = var_ty m_ty x) (s : ty m_ty) :
subst_ty sigma_ty s = s :=
  match s with
  | var_ty _ s0 => Eq_ty s0
  | top _ => congr_top
  | arr _ s0 s1 =>
      congr_arr (idSubst_ty sigma_ty Eq_ty s0) (idSubst_ty sigma_ty Eq_ty s1)
  | all _ s0 s1 =>
      congr_all (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ Eq_ty) s1)
  | recty _ s0 =>
      congr_recty
        (list_id (prod_id (fun x => eq_refl x) (idSubst_ty sigma_ty Eq_ty))
           s0)
  end.
Definition upExtRen_ty_ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_ty xi x = upRen_ty_ty zeta x :=
  fun n =>
  match n with
  | Some fin_n => ap shift (Eq fin_n)
  | None => eq_refl
  end.
Definition upExtRen_list_ty_ty {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_ty_ty p xi x = upRen_list_ty_ty p zeta x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n)).
Fixpoint extRen_ty {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
(zeta_ty : fin m_ty -> fin n_ty) (Eq_ty : forall x, xi_ty x = zeta_ty x)
(s : ty m_ty) : ren_ty xi_ty s = ren_ty zeta_ty s :=
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
  | recty _ s0 =>
      congr_recty
        (list_ext
           (prod_ext (fun x => eq_refl x) (extRen_ty xi_ty zeta_ty Eq_ty)) s0)
  end.
Definition upExt_ty_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty)
  (tau : fin m -> ty n_ty) (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_ty sigma x = up_ty_ty tau x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upExt_list_ty_ty {p : nat} {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) (tau : fin m -> ty n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ty_ty p sigma x = up_list_ty_ty p tau x :=
  fun n =>
  scons_p_congr (fun n => eq_refl) (fun n => ap (ren_ty (shift_p p)) (Eq n)).
Fixpoint ext_ty {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty)
(tau_ty : fin m_ty -> ty n_ty) (Eq_ty : forall x, sigma_ty x = tau_ty x)
(s : ty m_ty) : subst_ty sigma_ty s = subst_ty tau_ty s :=
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
  | recty _ s0 =>
      congr_recty
        (list_ext
           (prod_ext (fun x => eq_refl x) (ext_ty sigma_ty tau_ty Eq_ty)) s0)
  end.
Definition up_ren_ren_ty_ty {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x :=
  up_ren_ren xi zeta rho Eq.
Definition up_ren_ren_list_ty_ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_ty_ty p zeta) (upRen_list_ty_ty p xi) x =
  upRen_list_ty_ty p rho x := up_ren_ren_p Eq.
Fixpoint compRenRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty)
(rho_ty : fin m_ty -> fin l_ty)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x) (s : ty m_ty) :
ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty rho_ty s :=
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
  | recty _ s0 =>
      congr_recty
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty)) s0)
  end.
Definition up_ren_subst_ty_ty {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition up_ren_subst_list_ty_ty {p : nat} {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_ty_ty p tau) (upRen_list_ty_ty p xi) x =
  up_list_ty_ty p theta x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ _ n)
    (scons_p_congr (fun z => scons_p_head' _ _ z)
       (fun z =>
        eq_trans (scons_p_tail' _ _ (xi z)) (ap (ren_ty (shift_p p)) (Eq z)))).
Fixpoint compRenSubst_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x) (s : ty m_ty) :
subst_ty tau_ty (ren_ty xi_ty s) = subst_ty theta_ty s :=
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
  | recty _ s0 =>
      congr_recty
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty)) s0)
  end.
Definition up_subst_ren_ty_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_ty_ty zeta_ty)) (up_ty_ty sigma) x =
  up_ty_ty theta x :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenRen_ty shift (upRen_ty_ty zeta_ty) (funcomp shift zeta_ty)
           (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compRenRen_ty zeta_ty shift (funcomp shift zeta_ty)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_ty shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_ren_list_ty_ty {p : nat} {k : nat} {l_ty : nat}
  {m_ty : nat} (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_list_ty_ty p zeta_ty)) (up_list_ty_ty p sigma) x =
  up_list_ty_ty p theta x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ _ n)
    (scons_p_congr (fun x => ap (var_ty (plus p m_ty)) (scons_p_head' _ _ x))
       (fun n =>
        eq_trans
          (compRenRen_ty (shift_p p) (upRen_list_ty_ty p zeta_ty)
             (funcomp (shift_p p) zeta_ty) (fun x => scons_p_tail' _ _ x)
             (sigma n))
          (eq_trans
             (eq_sym
                (compRenRen_ty zeta_ty (shift_p p)
                   (funcomp (shift_p p) zeta_ty) (fun x => eq_refl) (sigma n)))
             (ap (ren_ty (shift_p p)) (Eq n))))).
Fixpoint compSubstRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(s : ty m_ty) : ren_ty zeta_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
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
  | recty _ s0 =>
      congr_recty
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty)) s0)
  end.
Definition up_subst_subst_ty_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_ty_ty tau_ty)) (up_ty_ty sigma) x = up_ty_ty theta x :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenSubst_ty shift (up_ty_ty tau_ty)
           (funcomp (up_ty_ty tau_ty) shift) (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compSubstRen_ty tau_ty shift (funcomp (ren_ty shift) tau_ty)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_ty shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_subst_list_ty_ty {p : nat} {k : nat} {l_ty : nat}
  {m_ty : nat} (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_list_ty_ty p tau_ty)) (up_list_ty_ty p sigma) x =
  up_list_ty_ty p theta x :=
  fun n =>
  eq_trans (scons_p_comp' (funcomp (var_ty (plus p l_ty)) (zero_p p)) _ _ n)
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
             (ap (ren_ty (shift_p p)) (Eq n))))).
Fixpoint compSubstSubst_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
(sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(s : ty m_ty) : subst_ty tau_ty (subst_ty sigma_ty s) = subst_ty theta_ty s
:=
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
  | recty _ s0 =>
      congr_recty
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty)) s0)
  end.
Definition rinstInst_up_ty_ty {m : nat} {n_ty : nat} (xi : fin m -> fin n_ty)
  (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x, funcomp (var_ty (S n_ty)) (upRen_ty_ty xi) x = up_ty_ty sigma x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition rinstInst_up_list_ty_ty {p : nat} {m : nat} {n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty (plus p n_ty)) (upRen_list_ty_ty p xi) x =
  up_list_ty_ty p sigma x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ (var_ty (plus p n_ty)) n)
    (scons_p_congr (fun z => eq_refl)
       (fun n => ap (ren_ty (shift_p p)) (Eq n))).
Fixpoint rinst_inst_ty {m_ty : nat} {n_ty : nat}
(xi_ty : fin m_ty -> fin n_ty) (sigma_ty : fin m_ty -> ty n_ty)
(Eq_ty : forall x, funcomp (var_ty n_ty) xi_ty x = sigma_ty x) (s : ty m_ty)
   : ren_ty xi_ty s = subst_ty sigma_ty s :=
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
  | recty _ s0 =>
      congr_recty
        (list_ext
           (prod_ext (fun x => eq_refl x)
              (rinst_inst_ty xi_ty sigma_ty Eq_ty)) s0)
  end.
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
Lemma renRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty)
  (s : ty m_ty) :
  ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty (funcomp zeta_ty xi_ty) s.
Proof.
exact (compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma renRen'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty) :
  funcomp (ren_ty zeta_ty) (ren_ty xi_ty) = ren_ty (funcomp zeta_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_ty xi_ty zeta_ty n)).
Qed.
Lemma compRen_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty)
  (s : ty m_ty) :
  ren_ty zeta_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s.
Proof.
exact (compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma compRen'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty) :
  funcomp (ren_ty zeta_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_ty sigma_ty zeta_ty n)).
Qed.
Lemma renComp_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty) (s : ty m_ty)
  : subst_ty tau_ty (ren_ty xi_ty s) = subst_ty (funcomp tau_ty xi_ty) s.
Proof.
exact (compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma renComp'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty) :
  funcomp (subst_ty tau_ty) (ren_ty xi_ty) = subst_ty (funcomp tau_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_ty xi_ty tau_ty n)).
Qed.
Lemma compComp_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty)
  (s : ty m_ty) :
  subst_ty tau_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s.
Proof.
exact (compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma compComp'_ty {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty) :
  funcomp (subst_ty tau_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_ty sigma_ty tau_ty n)).
Qed.
Inductive pat (n_ty : nat) : Type :=
  | patvar : ty n_ty -> pat n_ty
  | patlist : list (prod (nat) (pat n_ty)) -> pat n_ty.
Lemma congr_patvar {m_ty : nat} {s0 : ty m_ty} {t0 : ty m_ty} (H0 : s0 = t0)
  : patvar m_ty s0 = patvar m_ty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => patvar m_ty x) H0)).
Qed.
Lemma congr_patlist {m_ty : nat} {s0 : list (prod (nat) (pat m_ty))}
  {t0 : list (prod (nat) (pat m_ty))} (H0 : s0 = t0) :
  patlist m_ty s0 = patlist m_ty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => patlist m_ty x) H0)).
Qed.
Fixpoint ren_pat {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
(s : pat m_ty) : pat n_ty :=
  match s with
  | patvar _ s0 => patvar n_ty (ren_ty xi_ty s0)
  | patlist _ s0 =>
      patlist n_ty (list_map (prod_map (fun x => x) (ren_pat xi_ty)) s0)
  end.
Fixpoint subst_pat {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty)
(s : pat m_ty) : pat n_ty :=
  match s with
  | patvar _ s0 => patvar n_ty (subst_ty sigma_ty s0)
  | patlist _ s0 =>
      patlist n_ty (list_map (prod_map (fun x => x) (subst_pat sigma_ty)) s0)
  end.
Fixpoint idSubst_pat {m_ty : nat} (sigma_ty : fin m_ty -> ty m_ty)
(Eq_ty : forall x, sigma_ty x = var_ty m_ty x) (s : pat m_ty) :
subst_pat sigma_ty s = s :=
  match s with
  | patvar _ s0 => congr_patvar (idSubst_ty sigma_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_id (prod_id (fun x => eq_refl x) (idSubst_pat sigma_ty Eq_ty))
           s0)
  end.
Fixpoint extRen_pat {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
(zeta_ty : fin m_ty -> fin n_ty) (Eq_ty : forall x, xi_ty x = zeta_ty x)
(s : pat m_ty) : ren_pat xi_ty s = ren_pat zeta_ty s :=
  match s with
  | patvar _ s0 => congr_patvar (extRen_ty xi_ty zeta_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_ext
           (prod_ext (fun x => eq_refl x) (extRen_pat xi_ty zeta_ty Eq_ty))
           s0)
  end.
Fixpoint ext_pat {m_ty : nat} {n_ty : nat} (sigma_ty : fin m_ty -> ty n_ty)
(tau_ty : fin m_ty -> ty n_ty) (Eq_ty : forall x, sigma_ty x = tau_ty x)
(s : pat m_ty) : subst_pat sigma_ty s = subst_pat tau_ty s :=
  match s with
  | patvar _ s0 => congr_patvar (ext_ty sigma_ty tau_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_ext
           (prod_ext (fun x => eq_refl x) (ext_pat sigma_ty tau_ty Eq_ty)) s0)
  end.
Fixpoint compRenRen_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
(xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty)
(rho_ty : fin m_ty -> fin l_ty)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x) (s : pat m_ty) :
ren_pat zeta_ty (ren_pat xi_ty s) = ren_pat rho_ty s :=
  match s with
  | patvar _ s0 => congr_patvar (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compRenRen_pat xi_ty zeta_ty rho_ty Eq_ty)) s0)
  end.
Fixpoint compRenSubst_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
(xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x) (s : pat m_ty) :
subst_pat tau_ty (ren_pat xi_ty s) = subst_pat theta_ty s :=
  match s with
  | patvar _ s0 =>
      congr_patvar (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compRenSubst_pat xi_ty tau_ty theta_ty Eq_ty)) s0)
  end.
Fixpoint compSubstRen_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
(sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(s : pat m_ty) :
ren_pat zeta_ty (subst_pat sigma_ty s) = subst_pat theta_ty s :=
  match s with
  | patvar _ s0 =>
      congr_patvar (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compSubstRen_pat sigma_ty zeta_ty theta_ty Eq_ty)) s0)
  end.
Fixpoint compSubstSubst_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
(sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty)
(theta_ty : fin m_ty -> ty l_ty)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(s : pat m_ty) :
subst_pat tau_ty (subst_pat sigma_ty s) = subst_pat theta_ty s :=
  match s with
  | patvar _ s0 =>
      congr_patvar (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compSubstSubst_pat sigma_ty tau_ty theta_ty Eq_ty)) s0)
  end.
Fixpoint rinst_inst_pat {m_ty : nat} {n_ty : nat}
(xi_ty : fin m_ty -> fin n_ty) (sigma_ty : fin m_ty -> ty n_ty)
(Eq_ty : forall x, funcomp (var_ty n_ty) xi_ty x = sigma_ty x) (s : pat m_ty)
   : ren_pat xi_ty s = subst_pat sigma_ty s :=
  match s with
  | patvar _ s0 => congr_patvar (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
  | patlist _ s0 =>
      congr_patlist
        (list_ext
           (prod_ext (fun x => eq_refl x)
              (rinst_inst_pat xi_ty sigma_ty Eq_ty)) s0)
  end.
Lemma rinstInst_pat {m_ty : nat} {n_ty : nat} (xi_ty : fin m_ty -> fin n_ty)
  : ren_pat xi_ty = subst_pat (funcomp (var_ty n_ty) xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_pat xi_ty _ (fun n => eq_refl) x)).
Qed.
Lemma instId_pat {m_ty : nat} : subst_pat (var_ty m_ty) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_pat (var_ty m_ty) (fun n => eq_refl) (id x))).
Qed.
Lemma rinstId_pat {m_ty : nat} : @ren_pat m_ty m_ty id = id.
Proof.
exact (eq_trans (rinstInst_pat (id _)) instId_pat).
Qed.
Lemma renRen_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty)
  (s : pat m_ty) :
  ren_pat zeta_ty (ren_pat xi_ty s) = ren_pat (funcomp zeta_ty xi_ty) s.
Proof.
exact (compRenRen_pat xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma renRen'_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (zeta_ty : fin k_ty -> fin l_ty) :
  funcomp (ren_pat zeta_ty) (ren_pat xi_ty) = ren_pat (funcomp zeta_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_pat xi_ty zeta_ty n)).
Qed.
Lemma compRen_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty)
  (s : pat m_ty) :
  ren_pat zeta_ty (subst_pat sigma_ty s) =
  subst_pat (funcomp (ren_ty zeta_ty) sigma_ty) s.
Proof.
exact (compSubstRen_pat sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma compRen'_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (zeta_ty : fin k_ty -> fin l_ty) :
  funcomp (ren_pat zeta_ty) (subst_pat sigma_ty) =
  subst_pat (funcomp (ren_ty zeta_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_pat sigma_ty zeta_ty n)).
Qed.
Lemma renComp_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty)
  (s : pat m_ty) :
  subst_pat tau_ty (ren_pat xi_ty s) = subst_pat (funcomp tau_ty xi_ty) s.
Proof.
exact (compRenSubst_pat xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma renComp'_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (xi_ty : fin m_ty -> fin k_ty) (tau_ty : fin k_ty -> ty l_ty) :
  funcomp (subst_pat tau_ty) (ren_pat xi_ty) =
  subst_pat (funcomp tau_ty xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_pat xi_ty tau_ty n)).
Qed.
Lemma compComp_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty)
  (s : pat m_ty) :
  subst_pat tau_ty (subst_pat sigma_ty s) =
  subst_pat (funcomp (subst_ty tau_ty) sigma_ty) s.
Proof.
exact (compSubstSubst_pat sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma compComp'_pat {k_ty : nat} {l_ty : nat} {m_ty : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (tau_ty : fin k_ty -> ty l_ty) :
  funcomp (subst_pat tau_ty) (subst_pat sigma_ty) =
  subst_pat (funcomp (subst_ty tau_ty) sigma_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_pat sigma_ty tau_ty n)).
Qed.
Inductive tm (n_ty n_tm : nat) : Type :=
  | var_tm : fin n_tm -> tm n_ty n_tm
  | app : tm n_ty n_tm -> tm n_ty n_tm -> tm n_ty n_tm
  | tapp : tm n_ty n_tm -> ty n_ty -> tm n_ty n_tm
  | abs : ty n_ty -> tm n_ty (S n_tm) -> tm n_ty n_tm
  | tabs : ty n_ty -> tm (S n_ty) n_tm -> tm n_ty n_tm
  | rectm : list (prod (nat) (tm n_ty n_tm)) -> tm n_ty n_tm
  | proj : tm n_ty n_tm -> nat -> tm n_ty n_tm
  | letpat :
      forall p : nat,
      pat n_ty -> tm n_ty n_tm -> tm n_ty (plus p n_tm) -> tm n_ty n_tm.
Lemma congr_app {m_ty m_tm : nat} {s0 : tm m_ty m_tm} {s1 : tm m_ty m_tm}
  {t0 : tm m_ty m_tm} {t1 : tm m_ty m_tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_ty m_tm s0 s1 = app m_ty m_tm t0 t1.
Proof.
exact (eq_trans
                (eq_trans eq_refl (ap (fun x => app m_ty m_tm x s1) H0))
                (ap (fun x => app m_ty m_tm t0 x) H1)).
Qed.
Lemma congr_tapp {m_ty m_tm : nat} {s0 : tm m_ty m_tm} {s1 : ty m_ty}
  {t0 : tm m_ty m_tm} {t1 : ty m_ty} (H0 : s0 = t0) (H1 : s1 = t1) :
  tapp m_ty m_tm s0 s1 = tapp m_ty m_tm t0 t1.
Proof.
exact (eq_trans
                (eq_trans eq_refl (ap (fun x => tapp m_ty m_tm x s1) H0))
                (ap (fun x => tapp m_ty m_tm t0 x) H1)).
Qed.
Lemma congr_abs {m_ty m_tm : nat} {s0 : ty m_ty} {s1 : tm m_ty (S m_tm)}
  {t0 : ty m_ty} {t1 : tm m_ty (S m_tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  abs m_ty m_tm s0 s1 = abs m_ty m_tm t0 t1.
Proof.
exact (eq_trans
                (eq_trans eq_refl (ap (fun x => abs m_ty m_tm x s1) H0))
                (ap (fun x => abs m_ty m_tm t0 x) H1)).
Qed.
Lemma congr_tabs {m_ty m_tm : nat} {s0 : ty m_ty} {s1 : tm (S m_ty) m_tm}
  {t0 : ty m_ty} {t1 : tm (S m_ty) m_tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  tabs m_ty m_tm s0 s1 = tabs m_ty m_tm t0 t1.
Proof.
exact (eq_trans
                (eq_trans eq_refl (ap (fun x => tabs m_ty m_tm x s1) H0))
                (ap (fun x => tabs m_ty m_tm t0 x) H1)).
Qed.
Lemma congr_rectm {m_ty m_tm : nat} {s0 : list (prod (nat) (tm m_ty m_tm))}
  {t0 : list (prod (nat) (tm m_ty m_tm))} (H0 : s0 = t0) :
  rectm m_ty m_tm s0 = rectm m_ty m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => rectm m_ty m_tm x) H0)).
Qed.
Lemma congr_proj {m_ty m_tm : nat} {s0 : tm m_ty m_tm} {s1 : nat}
  {t0 : tm m_ty m_tm} {t1 : nat} (H0 : s0 = t0) (H1 : s1 = t1) :
  proj m_ty m_tm s0 s1 = proj m_ty m_tm t0 t1.
Proof.
exact (eq_trans
                (eq_trans eq_refl (ap (fun x => proj m_ty m_tm x s1) H0))
                (ap (fun x => proj m_ty m_tm t0 x) H1)).
Qed.
Lemma congr_letpat {p : nat} {m_ty m_tm : nat} {s0 : pat m_ty}
  {s1 : tm m_ty m_tm} {s2 : tm m_ty (plus p m_tm)} {t0 : pat m_ty}
  {t1 : tm m_ty m_tm} {t2 : tm m_ty (plus p m_tm)} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) :
  letpat m_ty m_tm p s0 s1 s2 = letpat m_ty m_tm p t0 t1 t2.
Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans eq_refl
                      (ap (fun x => letpat m_ty m_tm p x s1 s2) H0))
                   (ap (fun x => letpat m_ty m_tm p t0 x s2) H1))
                (ap (fun x => letpat m_ty m_tm p t0 t1 x) H2)).
Qed.
Definition upRen_ty_tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n := xi.
Definition upRen_tm_ty {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n := xi.
Definition upRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n) := up_ren xi.
Definition upRen_list_ty_tm (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin m -> fin n := xi.
Definition upRen_list_tm_ty (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin m -> fin n := xi.
Definition upRen_list_tm_tm (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n) := upRen_p p xi.
Fixpoint ren_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
(s : tm m_ty m_tm) : tm n_ty n_tm :=
  match s with
  | var_tm _ _ s0 => var_tm n_ty n_tm (xi_tm s0)
  | app _ _ s0 s1 =>
      app n_ty n_tm (ren_tm xi_ty xi_tm s0) (ren_tm xi_ty xi_tm s1)
  | tapp _ _ s0 s1 =>
      tapp n_ty n_tm (ren_tm xi_ty xi_tm s0) (ren_ty xi_ty s1)
  | abs _ _ s0 s1 =>
      abs n_ty n_tm (ren_ty xi_ty s0)
        (ren_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm) s1)
  | tabs _ _ s0 s1 =>
      tabs n_ty n_tm (ren_ty xi_ty s0)
        (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm) s1)
  | rectm _ _ s0 =>
      rectm n_ty n_tm
        (list_map (prod_map (fun x => x) (ren_tm xi_ty xi_tm)) s0)
  | proj _ _ s0 s1 =>
      proj n_ty n_tm (ren_tm xi_ty xi_tm s0) ((fun x => x) s1)
  | letpat _ _ p s0 s1 s2 =>
      letpat n_ty n_tm p (ren_pat xi_ty s0) (ren_tm xi_ty xi_tm s1)
        (ren_tm (upRen_list_tm_ty p xi_ty) (upRen_list_tm_tm p xi_tm) s2)
  end.
Definition up_ty_tm {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) : fin m -> tm (S n_ty) n_tm :=
  funcomp (ren_tm shift id) sigma.
Definition up_tm_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty) :
  fin m -> ty n_ty := funcomp (ren_ty id) sigma.
Definition up_tm_tm {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) : fin (S m) -> tm n_ty (S n_tm) :=
  scons (var_tm n_ty (S n_tm) var_zero) (funcomp (ren_tm id shift) sigma).
Definition up_list_ty_tm (p : nat) {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) : fin m -> tm (plus p n_ty) n_tm :=
  funcomp (ren_tm (shift_p p) id) sigma.
Definition up_list_tm_ty (p : nat) {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) : fin m -> ty n_ty := funcomp (ren_ty id) sigma.
Definition up_list_tm_tm (p : nat) {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) :
  fin (plus p m) -> tm n_ty (plus p n_tm) :=
  scons_p p (funcomp (var_tm n_ty (plus p n_tm)) (zero_p p))
    (funcomp (ren_tm id (shift_p p)) sigma).
Fixpoint subst_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm)
(s : tm m_ty m_tm) : tm n_ty n_tm :=
  match s with
  | var_tm _ _ s0 => sigma_tm s0
  | app _ _ s0 s1 =>
      app n_ty n_tm (subst_tm sigma_ty sigma_tm s0)
        (subst_tm sigma_ty sigma_tm s1)
  | tapp _ _ s0 s1 =>
      tapp n_ty n_tm (subst_tm sigma_ty sigma_tm s0) (subst_ty sigma_ty s1)
  | abs _ _ s0 s1 =>
      abs n_ty n_tm (subst_ty sigma_ty s0)
        (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) s1)
  | tabs _ _ s0 s1 =>
      tabs n_ty n_tm (subst_ty sigma_ty s0)
        (subst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) s1)
  | rectm _ _ s0 =>
      rectm n_ty n_tm
        (list_map (prod_map (fun x => x) (subst_tm sigma_ty sigma_tm)) s0)
  | proj _ _ s0 s1 =>
      proj n_ty n_tm (subst_tm sigma_ty sigma_tm s0) ((fun x => x) s1)
  | letpat _ _ p s0 s1 s2 =>
      letpat n_ty n_tm p (subst_pat sigma_ty s0)
        (subst_tm sigma_ty sigma_tm s1)
        (subst_tm (up_list_tm_ty p sigma_ty) (up_list_tm_tm p sigma_tm) s2)
  end.
Definition upId_ty_tm {m_ty m_tm : nat} (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_ty_tm sigma x = var_tm (S m_ty) m_tm x :=
  fun n => ap (ren_tm shift id) (Eq n).
Definition upId_tm_ty {m_ty : nat} (sigma : fin m_ty -> ty m_ty)
  (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_tm_ty sigma x = var_ty m_ty x :=
  fun n => ap (ren_ty id) (Eq n).
Definition upId_tm_tm {m_ty m_tm : nat} (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_tm_tm sigma x = var_tm m_ty (S m_tm) x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upId_list_ty_tm {p : nat} {m_ty m_tm : nat}
  (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_list_ty_tm p sigma x = var_tm (plus p m_ty) m_tm x :=
  fun n => ap (ren_tm (shift_p p) id) (Eq n).
Definition upId_list_tm_ty {p : nat} {m_ty : nat}
  (sigma : fin m_ty -> ty m_ty) (Eq : forall x, sigma x = var_ty m_ty x) :
  forall x, up_list_tm_ty p sigma x = var_ty m_ty x :=
  fun n => ap (ren_ty id) (Eq n).
Definition upId_list_tm_tm {p : nat} {m_ty m_tm : nat}
  (sigma : fin m_tm -> tm m_ty m_tm)
  (Eq : forall x, sigma x = var_tm m_ty m_tm x) :
  forall x, up_list_tm_tm p sigma x = var_tm m_ty (plus p m_tm) x :=
  fun n =>
  scons_p_eta (var_tm m_ty (plus p m_tm))
    (fun n => ap (ren_tm id (shift_p p)) (Eq n)) (fun n => eq_refl).
Fixpoint idSubst_tm {m_ty m_tm : nat} (sigma_ty : fin m_ty -> ty m_ty)
(sigma_tm : fin m_tm -> tm m_ty m_tm)
(Eq_ty : forall x, sigma_ty x = var_ty m_ty x)
(Eq_tm : forall x, sigma_tm x = var_tm m_ty m_tm x) (s : tm m_ty m_tm) :
subst_tm sigma_ty sigma_tm s = s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | abs _ _ s0 s1 =>
      congr_abs (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm)
           (upId_tm_ty _ Eq_ty) (upId_tm_tm _ Eq_tm) s1)
  | tabs _ _ s0 s1 =>
      congr_tabs (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm)
           (upId_ty_ty _ Eq_ty) (upId_ty_tm _ Eq_tm) s1)
  | rectm _ _ s0 =>
      congr_rectm
        (list_id
           (prod_id (fun x => eq_refl x)
              (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (idSubst_pat sigma_ty Eq_ty s0)
        (idSubst_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
        (idSubst_tm (up_list_tm_ty p sigma_ty) (up_list_tm_tm p sigma_tm)
           (upId_list_tm_ty _ Eq_ty) (upId_list_tm_tm _ Eq_tm) s2)
  end.
Definition upExtRen_ty_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_tm xi x = upRen_ty_tm zeta x := fun n => Eq n.
Definition upExtRen_tm_ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_ty xi x = upRen_tm_ty zeta x := fun n => Eq n.
Definition upExtRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x :=
  fun n =>
  match n with
  | Some fin_n => ap shift (Eq fin_n)
  | None => eq_refl
  end.
Definition upExtRen_list_ty_tm {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_ty_tm p xi x = upRen_list_ty_tm p zeta x :=
  fun n => Eq n.
Definition upExtRen_list_tm_ty {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_ty p xi x = upRen_list_tm_ty p zeta x :=
  fun n => Eq n.
Definition upExtRen_list_tm_tm {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_tm p xi x = upRen_list_tm_tm p zeta x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n)).
Fixpoint extRen_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
(zeta_ty : fin m_ty -> fin n_ty) (zeta_tm : fin m_tm -> fin n_tm)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm m_ty m_tm) :
ren_tm xi_ty xi_tm s = ren_tm zeta_ty zeta_tm s :=
  match s with
  | var_tm _ _ s0 => ap (var_tm n_ty n_tm) (Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
        (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
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
  | rectm _ _ s0 =>
      congr_rectm
        (list_ext
           (prod_ext (fun x => eq_refl x)
              (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s0)
        ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (extRen_pat xi_ty zeta_ty Eq_ty s0)
        (extRen_tm xi_ty xi_tm zeta_ty zeta_tm Eq_ty Eq_tm s1)
        (extRen_tm (upRen_list_tm_ty p xi_ty) (upRen_list_tm_tm p xi_tm)
           (upRen_list_tm_ty p zeta_ty) (upRen_list_tm_tm p zeta_tm)
           (upExtRen_list_tm_ty _ _ Eq_ty) (upExtRen_list_tm_tm _ _ Eq_tm) s2)
  end.
Definition upExt_ty_tm {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) (tau : fin m -> tm n_ty n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_tm sigma x = up_ty_tm tau x :=
  fun n => ap (ren_tm shift id) (Eq n).
Definition upExt_tm_ty {m : nat} {n_ty : nat} (sigma : fin m -> ty n_ty)
  (tau : fin m -> ty n_ty) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_ty sigma x = up_tm_ty tau x :=
  fun n => ap (ren_ty id) (Eq n).
Definition upExt_tm_tm {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) (tau : fin m -> tm n_ty n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upExt_list_ty_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) (tau : fin m -> tm n_ty n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ty_tm p sigma x = up_list_ty_tm p tau x :=
  fun n => ap (ren_tm (shift_p p) id) (Eq n).
Definition upExt_list_tm_ty {p : nat} {m : nat} {n_ty : nat}
  (sigma : fin m -> ty n_ty) (tau : fin m -> ty n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_ty p sigma x = up_list_tm_ty p tau x :=
  fun n => ap (ren_ty id) (Eq n).
Definition upExt_list_tm_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (sigma : fin m -> tm n_ty n_tm) (tau : fin m -> tm n_ty n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_tm p sigma x = up_list_tm_tm p tau x :=
  fun n =>
  scons_p_congr (fun n => eq_refl)
    (fun n => ap (ren_tm id (shift_p p)) (Eq n)).
Fixpoint ext_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm)
(tau_ty : fin m_ty -> ty n_ty) (tau_tm : fin m_tm -> tm n_ty n_tm)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm m_ty m_tm) :
subst_tm sigma_ty sigma_tm s = subst_tm tau_ty tau_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
        (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
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
  | rectm _ _ s0 =>
      congr_rectm
        (list_ext
           (prod_ext (fun x => eq_refl x)
              (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s0)
        ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (ext_pat sigma_ty tau_ty Eq_ty s0)
        (ext_tm sigma_ty sigma_tm tau_ty tau_tm Eq_ty Eq_tm s1)
        (ext_tm (up_list_tm_ty p sigma_ty) (up_list_tm_tm p sigma_tm)
           (up_list_tm_ty p tau_ty) (up_list_tm_tm p tau_tm)
           (upExt_list_tm_ty _ _ Eq_ty) (upExt_list_tm_tm _ _ Eq_tm) s2)
  end.
Definition up_ren_ren_ty_tm {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_tm zeta) (upRen_ty_tm xi) x = upRen_ty_tm rho x :=
  Eq.
Definition up_ren_ren_tm_ty {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_ty zeta) (upRen_tm_ty xi) x = upRen_tm_ty rho x :=
  Eq.
Definition up_ren_ren_tm_tm {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x :=
  up_ren_ren xi zeta rho Eq.
Definition up_ren_ren_list_ty_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_ty_tm p zeta) (upRen_list_ty_tm p xi) x =
  upRen_list_ty_tm p rho x := Eq.
Definition up_ren_ren_list_tm_ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_ty p zeta) (upRen_list_tm_ty p xi) x =
  upRen_list_tm_ty p rho x := Eq.
Definition up_ren_ren_list_tm_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_tm p zeta) (upRen_list_tm_tm p xi) x =
  upRen_list_tm_tm p rho x := up_ren_ren_p Eq.
Fixpoint compRenRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
(xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
(zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm)
(rho_ty : fin m_ty -> fin l_ty) (rho_tm : fin m_tm -> fin l_tm)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x) (s : tm m_ty m_tm) :
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
  | rectm _ _ s0 =>
      congr_rectm
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty
                 Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s0) ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (compRenRen_pat xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm Eq_ty Eq_tm
           s1)
        (compRenRen_tm (upRen_list_tm_ty p xi_ty) (upRen_list_tm_tm p xi_tm)
           (upRen_list_tm_ty p zeta_ty) (upRen_list_tm_tm p zeta_tm)
           (upRen_list_tm_ty p rho_ty) (upRen_list_tm_tm p rho_tm) Eq_ty
           (up_ren_ren_p Eq_tm) s2)
  end.
Definition up_ren_subst_ty_tm {k : nat} {l : nat} {m_ty m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  : forall x, funcomp (up_ty_tm tau) (upRen_ty_tm xi) x = up_ty_tm theta x :=
  fun n => ap (ren_tm shift id) (Eq n).
Definition up_ren_subst_tm_ty {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_ty tau) (upRen_tm_ty xi) x = up_tm_ty theta x :=
  fun n => ap (ren_ty id) (Eq n).
Definition up_ren_subst_tm_tm {k : nat} {l : nat} {m_ty m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  : forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition up_ren_subst_list_ty_tm {p : nat} {k : nat} {l : nat}
  {m_ty m_tm : nat} (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_list_ty_tm p tau) (upRen_list_ty_tm p xi) x =
  up_list_ty_tm p theta x := fun n => ap (ren_tm (shift_p p) id) (Eq n).
Definition up_ren_subst_list_tm_ty {p : nat} {k : nat} {l : nat} {m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_ty) (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_tm_ty p tau) (upRen_list_tm_ty p xi) x =
  up_list_tm_ty p theta x := fun n => ap (ren_ty id) (Eq n).
Definition up_ren_subst_list_tm_tm {p : nat} {k : nat} {l : nat}
  {m_ty m_tm : nat} (xi : fin k -> fin l) (tau : fin l -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_list_tm_tm p tau) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p theta x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ _ n)
    (scons_p_congr (fun z => scons_p_head' _ _ z)
       (fun z =>
        eq_trans (scons_p_tail' _ _ (xi z))
          (ap (ren_tm id (shift_p p)) (Eq z)))).
Fixpoint compRenSubst_tm {k_ty k_tm : nat} {l_ty l_tm : nat}
{m_ty m_tm : nat} (xi_ty : fin m_ty -> fin k_ty)
(xi_tm : fin m_tm -> fin k_tm) (tau_ty : fin k_ty -> ty l_ty)
(tau_tm : fin k_tm -> tm l_ty l_tm) (theta_ty : fin m_ty -> ty l_ty)
(theta_tm : fin m_tm -> tm l_ty l_tm)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm m_ty m_tm) :
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
  | rectm _ _ s0 =>
      congr_rectm
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm
                 Eq_ty Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s0) ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (compRenSubst_pat xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm Eq_ty
           Eq_tm s1)
        (compRenSubst_tm (upRen_list_tm_ty p xi_ty)
           (upRen_list_tm_tm p xi_tm) (up_list_tm_ty p tau_ty)
           (up_list_tm_tm p tau_tm) (up_list_tm_ty p theta_ty)
           (up_list_tm_tm p theta_tm) (up_ren_subst_list_tm_ty _ _ _ Eq_ty)
           (up_ren_subst_list_tm_tm _ _ _ Eq_tm) s2)
  end.
Definition up_subst_ren_ty_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (zeta_ty : fin l_ty -> fin m_ty)
  (zeta_tm : fin l_tm -> fin m_tm) (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm))
    (up_ty_tm sigma) x = up_ty_tm theta x :=
  fun n =>
  eq_trans
    (compRenRen_tm shift id (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm)
       (funcomp shift zeta_ty) (funcomp id zeta_tm) (fun x => eq_refl)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_tm zeta_ty zeta_tm shift id (funcomp shift zeta_ty)
             (funcomp id zeta_tm) (fun x => eq_refl) (fun x => eq_refl)
             (sigma n))) (ap (ren_tm shift id) (Eq n))).
Definition up_subst_ren_tm_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_tm_ty zeta_ty)) (up_tm_ty sigma) x =
  up_tm_ty theta x :=
  fun n =>
  eq_trans
    (compRenRen_ty id (upRen_tm_ty zeta_ty) (funcomp id zeta_ty)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_ty zeta_ty id (funcomp id zeta_ty) (fun x => eq_refl)
             (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_ren_tm_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (zeta_ty : fin l_ty -> fin m_ty)
  (zeta_tm : fin l_tm -> fin m_tm) (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm))
    (up_tm_tm sigma) x = up_tm_tm theta x :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenRen_tm id shift (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm)
           (funcomp id zeta_ty) (funcomp shift zeta_tm) (fun x => eq_refl)
           (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compRenRen_tm zeta_ty zeta_tm id shift (funcomp id zeta_ty)
                 (funcomp shift zeta_tm) (fun x => eq_refl)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_tm id shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_ren_list_ty_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (zeta_ty : fin l_ty -> fin m_ty) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_list_ty_ty p zeta_ty) (upRen_list_ty_tm p zeta_tm))
    (up_list_ty_tm p sigma) x = up_list_ty_tm p theta x :=
  fun n =>
  eq_trans
    (compRenRen_tm (shift_p p) id (upRen_list_ty_ty p zeta_ty)
       (upRen_list_ty_tm p zeta_tm) (funcomp (shift_p p) zeta_ty)
       (funcomp id zeta_tm) (fun x => scons_p_tail' _ _ x) (fun x => eq_refl)
       (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_tm zeta_ty zeta_tm (shift_p p) id
             (funcomp (shift_p p) zeta_ty) (funcomp id zeta_tm)
             (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
       (ap (ren_tm (shift_p p) id) (Eq n))).
Definition up_subst_ren_list_tm_ty {p : nat} {k : nat} {l_ty : nat}
  {m_ty : nat} (sigma : fin k -> ty l_ty) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_list_tm_ty p zeta_ty)) (up_list_tm_ty p sigma) x =
  up_list_tm_ty p theta x :=
  fun n =>
  eq_trans
    (compRenRen_ty id (upRen_list_tm_ty p zeta_ty) (funcomp id zeta_ty)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_ty zeta_ty id (funcomp id zeta_ty) (fun x => eq_refl)
             (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_ren_list_tm_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (zeta_ty : fin l_ty -> fin m_ty) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_list_tm_ty p zeta_ty) (upRen_list_tm_tm p zeta_tm))
    (up_list_tm_tm p sigma) x = up_list_tm_tm p theta x :=
  fun n =>
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
             (ap (ren_tm id (shift_p p)) (Eq n))))).
Fixpoint compSubstRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat}
{m_ty m_tm : nat} (sigma_ty : fin m_ty -> ty k_ty)
(sigma_tm : fin m_tm -> tm k_ty k_tm) (zeta_ty : fin k_ty -> fin l_ty)
(zeta_tm : fin k_tm -> fin l_tm) (theta_ty : fin m_ty -> ty l_ty)
(theta_tm : fin m_tm -> tm l_ty l_tm)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_tm : forall x, funcomp (ren_tm zeta_ty zeta_tm) sigma_tm x = theta_tm x)
(s : tm m_ty m_tm) :
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
  | rectm _ _ s0 =>
      congr_rectm
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty
                 theta_tm Eq_ty Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s0) ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (compSubstRen_pat sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm
           Eq_ty Eq_tm s1)
        (compSubstRen_tm (up_list_tm_ty p sigma_ty)
           (up_list_tm_tm p sigma_tm) (upRen_list_tm_ty p zeta_ty)
           (upRen_list_tm_tm p zeta_tm) (up_list_tm_ty p theta_ty)
           (up_list_tm_tm p theta_tm) (up_subst_ren_list_tm_ty _ _ _ Eq_ty)
           (up_subst_ren_list_tm_tm _ _ _ _ Eq_tm) s2)
  end.
Definition up_subst_subst_ty_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (tau_ty : fin l_ty -> ty m_ty)
  (tau_tm : fin l_tm -> tm m_ty m_tm) (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_ty_ty tau_ty) (up_ty_tm tau_tm)) (up_ty_tm sigma) x =
  up_ty_tm theta x :=
  fun n =>
  eq_trans
    (compRenSubst_tm shift id (up_ty_ty tau_ty) (up_ty_tm tau_tm)
       (funcomp (up_ty_ty tau_ty) shift) (funcomp (up_ty_tm tau_tm) id)
       (fun x => eq_refl) (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compSubstRen_tm tau_ty tau_tm shift id
             (funcomp (ren_ty shift) tau_ty)
             (funcomp (ren_tm shift id) tau_tm) (fun x => eq_refl)
             (fun x => eq_refl) (sigma n))) (ap (ren_tm shift id) (Eq n))).
Definition up_subst_subst_tm_ty {k : nat} {l_ty : nat} {m_ty : nat}
  (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_tm_ty tau_ty)) (up_tm_ty sigma) x = up_tm_ty theta x :=
  fun n =>
  eq_trans
    (compRenSubst_ty id (up_tm_ty tau_ty) (funcomp (up_tm_ty tau_ty) id)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty)
             (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_subst_tm_tm {k : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma : fin k -> tm l_ty l_tm) (tau_ty : fin l_ty -> ty m_ty)
  (tau_tm : fin l_tm -> tm m_ty m_tm) (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_ty tau_ty) (up_tm_tm tau_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenSubst_tm id shift (up_tm_ty tau_ty) (up_tm_tm tau_tm)
           (funcomp (up_tm_ty tau_ty) id) (funcomp (up_tm_tm tau_tm) shift)
           (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compSubstRen_tm tau_ty tau_tm id shift
                 (funcomp (ren_ty id) tau_ty)
                 (funcomp (ren_tm id shift) tau_tm) (fun x => eq_refl)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_tm id shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_subst_list_ty_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (tau_ty : fin l_ty -> ty m_ty) (tau_tm : fin l_tm -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_ty_ty p tau_ty) (up_list_ty_tm p tau_tm))
    (up_list_ty_tm p sigma) x = up_list_ty_tm p theta x :=
  fun n =>
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
       (ap (ren_tm (shift_p p) id) (Eq n))).
Definition up_subst_subst_list_tm_ty {p : nat} {k : nat} {l_ty : nat}
  {m_ty : nat} (sigma : fin k -> ty l_ty) (tau_ty : fin l_ty -> ty m_ty)
  (theta : fin k -> ty m_ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_list_tm_ty p tau_ty)) (up_list_tm_ty p sigma) x =
  up_list_tm_ty p theta x :=
  fun n =>
  eq_trans
    (compRenSubst_ty id (up_list_tm_ty p tau_ty)
       (funcomp (up_list_tm_ty p tau_ty) id) (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compSubstRen_ty tau_ty id _ (fun x => eq_sym eq_refl) (sigma n)))
       (ap (ren_ty id) (Eq n))).
Definition up_subst_subst_list_tm_tm {p : nat} {k : nat} {l_ty l_tm : nat}
  {m_ty m_tm : nat} (sigma : fin k -> tm l_ty l_tm)
  (tau_ty : fin l_ty -> ty m_ty) (tau_tm : fin l_tm -> tm m_ty m_tm)
  (theta : fin k -> tm m_ty m_tm)
  (Eq : forall x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_tm_ty p tau_ty) (up_list_tm_tm p tau_tm))
    (up_list_tm_tm p sigma) x = up_list_tm_tm p theta x :=
  fun n =>
  eq_trans
    (scons_p_comp' (funcomp (var_tm l_ty (plus p l_tm)) (zero_p p)) _ _ n)
    (scons_p_congr
       (fun x => scons_p_head' _ (fun z => ren_tm id (shift_p p) _) x)
       (fun n =>
        eq_trans
          (compRenSubst_tm id (shift_p p) (up_list_tm_ty p tau_ty)
             (up_list_tm_tm p tau_tm) (funcomp (up_list_tm_ty p tau_ty) id)
             (funcomp (up_list_tm_tm p tau_tm) (shift_p p))
             (fun x => eq_refl) (fun x => eq_refl) (sigma n))
          (eq_trans
             (eq_sym
                (compSubstRen_tm tau_ty tau_tm id (shift_p p) _ _
                   (fun x => eq_sym eq_refl)
                   (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
             (ap (ren_tm id (shift_p p)) (Eq n))))).
Fixpoint compSubstSubst_tm {k_ty k_tm : nat} {l_ty l_tm : nat}
{m_ty m_tm : nat} (sigma_ty : fin m_ty -> ty k_ty)
(sigma_tm : fin m_tm -> tm k_ty k_tm) (tau_ty : fin k_ty -> ty l_ty)
(tau_tm : fin k_tm -> tm l_ty l_tm) (theta_ty : fin m_ty -> ty l_ty)
(theta_tm : fin m_tm -> tm l_ty l_tm)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_tm : forall x, funcomp (subst_tm tau_ty tau_tm) sigma_tm x = theta_tm x)
(s : tm m_ty m_tm) :
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
  | rectm _ _ s0 =>
      congr_rectm
        (list_comp
           (prod_comp (fun x => eq_refl x)
              (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty
                 theta_tm Eq_ty Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s0) ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (compSubstSubst_pat sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm
           Eq_ty Eq_tm s1)
        (compSubstSubst_tm (up_list_tm_ty p sigma_ty)
           (up_list_tm_tm p sigma_tm) (up_list_tm_ty p tau_ty)
           (up_list_tm_tm p tau_tm) (up_list_tm_ty p theta_ty)
           (up_list_tm_tm p theta_tm) (up_subst_subst_list_tm_ty _ _ _ Eq_ty)
           (up_subst_subst_list_tm_tm _ _ _ _ Eq_tm) s2)
  end.
Definition rinstInst_up_ty_tm {m : nat} {n_ty n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (S n_ty) n_tm) (upRen_ty_tm xi) x = up_ty_tm sigma x :=
  fun n => ap (ren_tm shift id) (Eq n).
Definition rinstInst_up_tm_ty {m : nat} {n_ty : nat} (xi : fin m -> fin n_ty)
  (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x, funcomp (var_ty n_ty) (upRen_tm_ty xi) x = up_tm_ty sigma x :=
  fun n => ap (ren_ty id) (Eq n).
Definition rinstInst_up_tm_tm {m : nat} {n_ty n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm n_ty (S n_tm)) (upRen_tm_tm xi) x = up_tm_tm sigma x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition rinstInst_up_list_ty_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (plus p n_ty) n_tm) (upRen_list_ty_tm p xi) x =
  up_list_ty_tm p sigma x := fun n => ap (ren_tm (shift_p p) id) (Eq n).
Definition rinstInst_up_list_tm_ty {p : nat} {m : nat} {n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_ty)
  (Eq : forall x, funcomp (var_ty n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty n_ty) (upRen_list_tm_ty p xi) x = up_list_tm_ty p sigma x :=
  fun n => ap (ren_ty id) (Eq n).
Definition rinstInst_up_list_tm_tm {p : nat} {m : nat} {n_ty n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_ty n_tm)
  (Eq : forall x, funcomp (var_tm n_ty n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm n_ty (plus p n_tm)) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p sigma x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ (var_tm n_ty (plus p n_tm)) n)
    (scons_p_congr (fun z => eq_refl)
       (fun n => ap (ren_tm id (shift_p p)) (Eq n))).
Fixpoint rinst_inst_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
(xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm)
(sigma_ty : fin m_ty -> ty n_ty) (sigma_tm : fin m_tm -> tm n_ty n_tm)
(Eq_ty : forall x, funcomp (var_ty n_ty) xi_ty x = sigma_ty x)
(Eq_tm : forall x, funcomp (var_tm n_ty n_tm) xi_tm x = sigma_tm x)
(s : tm m_ty m_tm) : ren_tm xi_ty xi_tm s = subst_tm sigma_ty sigma_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | app _ _ s0 s1 =>
      congr_app (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
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
  | rectm _ _ s0 =>
      congr_rectm
        (list_ext
           (prod_ext (fun x => eq_refl x)
              (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm)) s0)
  | proj _ _ s0 s1 =>
      congr_proj (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s0)
        ((fun x => eq_refl x) s1)
  | letpat _ _ p s0 s1 s2 =>
      congr_letpat (rinst_inst_pat xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm Eq_ty Eq_tm s1)
        (rinst_inst_tm (upRen_list_tm_ty p xi_ty) (upRen_list_tm_tm p xi_tm)
           (up_list_tm_ty p sigma_ty) (up_list_tm_tm p sigma_tm)
           (rinstInst_up_list_tm_ty _ _ Eq_ty)
           (rinstInst_up_list_tm_tm _ _ Eq_tm) s2)
  end.
Lemma rinstInst_tm {m_ty m_tm : nat} {n_ty n_tm : nat}
  (xi_ty : fin m_ty -> fin n_ty) (xi_tm : fin m_tm -> fin n_tm) :
  ren_tm xi_ty xi_tm =
  subst_tm (funcomp (var_ty n_ty) xi_ty) (funcomp (var_tm n_ty n_tm) xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_tm xi_ty xi_tm _ _ (fun n => eq_refl)
                   (fun n => eq_refl) x)).
Qed.
Lemma instId_tm {m_ty m_tm : nat} :
  subst_tm (var_ty m_ty) (var_tm m_ty m_tm) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_tm (var_ty m_ty) (var_tm m_ty m_tm)
                   (fun n => eq_refl) (fun n => eq_refl) (id x))).
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
Lemma renRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_ty m_tm) :
  ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
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
Lemma compRen_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
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
Lemma compRen'_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_tm : fin m_tm -> tm k_ty k_tm)
  (zeta_ty : fin k_ty -> fin l_ty) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_ty zeta_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_tm sigma_ty sigma_tm zeta_ty zeta_tm n)).
Qed.
Lemma renComp_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
  (tau_ty : fin k_ty -> ty l_ty) (tau_tm : fin k_tm -> tm l_ty l_tm)
  (s : tm m_ty m_tm) :
  subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renComp'_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (xi_ty : fin m_ty -> fin k_ty) (xi_tm : fin m_tm -> fin k_tm)
  (tau_ty : fin k_ty -> ty l_ty) (tau_tm : fin k_tm -> tm l_ty l_tm) :
  funcomp (subst_tm tau_ty tau_tm) (ren_tm xi_ty xi_tm) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_tm xi_ty xi_tm tau_ty tau_tm n)).
Qed.
Lemma compComp_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
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
Lemma compComp'_tm {k_ty k_tm : nat} {l_ty l_tm : nat} {m_ty m_tm : nat}
  (sigma_ty : fin m_ty -> ty k_ty) (sigma_tm : fin m_tm -> tm k_ty k_tm)
  (tau_ty : fin k_ty -> ty l_ty) (tau_tm : fin k_tm -> tm l_ty l_tm) :
  funcomp (subst_tm tau_ty tau_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_tm tau_ty tau_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_tm sigma_ty sigma_tm tau_ty tau_tm n)).
Qed.

Arguments var_ty {n_ty}.

Arguments top {n_ty}.

Arguments arr {n_ty}.

Arguments all {n_ty}.

Arguments recty {n_ty}.

Arguments patvar {n_ty}.

Arguments patlist {n_ty}.

Arguments var_tm {n_ty} {n_tm}.

Arguments app {n_ty} {n_tm}.

Arguments tapp {n_ty} {n_tm}.

Arguments abs {n_ty} {n_tm}.

Arguments tabs {n_ty} {n_tm}.

Arguments rectm {n_ty} {n_tm}.

Arguments proj {n_ty} {n_tm}.

Arguments letpat {n_ty} {n_tm}.

Global Instance Subst_ty { m_ty : nat } { n_ty : nat } : Subst1 ((fin) (m_ty) -> ty (n_ty)) (ty (m_ty)) (ty (n_ty)) := @subst_ty (m_ty) (n_ty) .

Global Instance Subst_pat { m_ty : nat } { n_ty : nat } : Subst1 ((fin) (m_ty) -> ty (n_ty)) (pat (m_ty)) (pat (n_ty)) := @subst_pat (m_ty) (n_ty) .

Global Instance Subst_tm { m_ty m_tm : nat } { n_ty n_tm : nat } : Subst2 ((fin) (m_ty) -> ty (n_ty)) ((fin) (m_tm) -> tm (n_ty) (n_tm)) (tm (m_ty) (m_tm)) (tm (n_ty) (n_tm)) := @subst_tm (m_ty) (m_tm) (n_ty) (n_tm) .

Global Instance Ren_ty { m_ty : nat } { n_ty : nat } : Ren1 ((fin) (m_ty) -> (fin) (n_ty)) (ty (m_ty)) (ty (n_ty)) := @ren_ty (m_ty) (n_ty) .

Global Instance Ren_pat { m_ty : nat } { n_ty : nat } : Ren1 ((fin) (m_ty) -> (fin) (n_ty)) (pat (m_ty)) (pat (n_ty)) := @ren_pat (m_ty) (n_ty) .

Global Instance Ren_tm { m_ty m_tm : nat } { n_ty n_tm : nat } : Ren2 ((fin) (m_ty) -> (fin) (n_ty)) ((fin) (m_tm) -> (fin) (n_tm)) (tm (m_ty) (m_tm)) (tm (n_ty) (n_tm)) := @ren_tm (m_ty) (m_tm) (n_ty) (n_tm) .

Global Instance VarInstance_ty { m_ty : nat } : Var ((fin) (m_ty)) (ty (m_ty)) := @var_ty (m_ty) .

Notation "x '__ty'" := (var_ty x) (at level 5, format "x __ty") : subst_scope.

Notation "x '__ty'" := (@ids (_) (_) VarInstance_ty x) (at level 5, only printing, format "x __ty") : subst_scope.

Notation "'var'" := (var_ty) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_tm { m_ty m_tm : nat } : Var ((fin) (m_tm)) (tm (m_ty) (m_tm)) := @var_tm (m_ty) (m_tm) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_ty X Y := up_ty : X -> Y.

Notation "↑__ty" := (up_ty) (only printing) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__ty" := (up_ty_ty) (only printing) : subst_scope.

Global Instance Up_ty_ty { m : nat } { n_ty : nat } : Up_ty (_) (_) := @up_ty_ty (m) (n_ty) .

Notation "↑__ty" := (up_ty_tm) (only printing) : subst_scope.

Global Instance Up_ty_tm { m : nat } { n_ty n_tm : nat } : Up_tm (_) (_) := @up_ty_tm (m) (n_ty) (n_tm) .

Notation "↑__tm" := (up_tm_ty) (only printing) : subst_scope.

Global Instance Up_tm_ty { m : nat } { n_ty : nat } : Up_ty (_) (_) := @up_tm_ty (m) (n_ty) .

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm { m : nat } { n_ty n_tm : nat } : Up_tm (_) (_) := @up_tm_tm (m) (n_ty) (n_tm) .

Notation "s [ sigmaty ]" := (subst_ty sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ]" := (subst_ty sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ⟩" := (ren_ty xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ⟩" := (ren_ty xity) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ]" := (subst_pat sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ]" := (subst_pat sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ⟩" := (ren_pat xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ⟩" := (ren_pat xity) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ; sigmatm ]" := (subst_tm sigmaty sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ; sigmatm ]" := (subst_tm sigmaty sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ; xitm ⟩" := (ren_tm xity xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ; xitm ⟩" := (ren_tm xity xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_pat,  Subst_tm,  Ren_ty,  Ren_pat,  Ren_tm,  VarInstance_ty,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_pat,  Subst_tm,  Ren_ty,  Ren_pat,  Ren_tm,  VarInstance_ty,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?instId_pat| progress rewrite ?compComp_pat| progress rewrite ?compComp'_pat| progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?rinstId_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?rinstId_pat| progress rewrite ?compRen_pat| progress rewrite ?compRen'_pat| progress rewrite ?renComp_pat| progress rewrite ?renComp'_pat| progress rewrite ?renRen_pat| progress rewrite ?renRen'_pat| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_ty| progress rewrite ?varL_tm| progress rewrite ?varLRen_ty| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_ty_ty, upRen_list_ty_ty, upRen_ty_tm, upRen_tm_ty, upRen_tm_tm, upRen_list_ty_tm, upRen_list_tm_ty, upRen_list_tm_tm, up_ty_ty, up_list_ty_ty, up_ty_tm, up_tm_ty, up_tm_tm, up_list_ty_tm, up_list_tm_ty, up_list_tm_tm)| progress (cbn [subst_ty subst_pat subst_tm ren_ty ren_pat ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?instId_pat in *| progress rewrite ?compComp_pat in *| progress rewrite ?compComp'_pat in *| progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?rinstId_pat in *| progress rewrite ?compRen_pat in *| progress rewrite ?compRen'_pat in *| progress rewrite ?renComp_pat in *| progress rewrite ?renComp'_pat in *| progress rewrite ?renRen_pat in *| progress rewrite ?renRen'_pat in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_ty in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_ty in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_ty_ty, upRen_list_ty_ty, upRen_ty_tm, upRen_tm_ty, upRen_tm_tm, upRen_list_ty_tm, upRen_list_tm_ty, upRen_list_tm_tm, up_ty_ty, up_list_ty_ty, up_ty_tm, up_tm_ty, up_tm_tm, up_list_ty_tm, up_list_tm_ty, up_list_tm_tm in *)| progress (cbn [subst_ty subst_pat subst_tm ren_ty ren_pat ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_ty); try repeat (erewrite rinstInst_pat); try repeat (erewrite rinstInst_tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_ty); try repeat (erewrite <- rinstInst_pat); try repeat (erewrite <- rinstInst_tm).
