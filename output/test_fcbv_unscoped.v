Inductive ty : Type :=
  | var_ty : forall _ : fin, ty
  | arr : forall _ : ty, forall _ : ty, ty
  | all : forall _ : ty, ty.
Lemma congr_arr {s0 : ty} {s1 : ty} {t0 : ty} {t1 : ty} (H0 : eq s0 t0)
  (H1 : eq s1 t1) : eq (arr m_ty s0 s1) (arr m_ty t0 t1).
Proof.
exact (eq_trans
                (eq_trans eq_refl (f_equal (fun x => arr m_ty x s1) H0))
                (f_equal (fun x => arr m_ty t0 x) H1)).
Qed.
Lemma congr_all {s0 : ty} {t0 : ty} (H0 : eq s0 t0) :
  eq (all m_ty s0) (all m_ty t0).
Proof.
exact (eq_trans eq_refl (f_equal (fun x => all m_ty x) H0)).
Qed.
Definition upRen_ty_ty (xi : forall _ : fin, fin) : forall _ : fin, fin :=
  up_ren xi.
Definition upRen_list_ty_ty (p : nat) (xi : forall _ : fin, fin) :
  forall _ : fin, fin := upRen_p p xi.
Fixpoint ren_ty (xi_ty : forall _ : fin, fin) (s : ty) : ty n_ty :=
  match s with
  | var_ty _ s => var_ty n_ty (xi_ty s)
  | arr _ s0 s1 => arr n_ty (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | all _ s0 => all n_ty (ren_ty (upRen_ty_ty xi_ty) s0)
  end.
Definition up_ty_ty (sigma : forall _ : fin, ty) : forall _ : fin, ty :=
  scons (var_ty (S n_ty) var_zero) (funcomp (ren_ty shift) sigma).
Definition up_list_ty_ty (p : nat) (sigma : forall _ : fin, ty) :
  forall _ : fin, ty :=
  scons_p p (funcomp (var_ty (plus p n_ty)) (zero_p p))
    (funcomp (ren_ty (shift_p p)) sigma).
Fixpoint subst_ty (sigma_ty : forall _ : fin, ty) (s : ty) : ty n_ty :=
  match s with
  | var_ty _ s => sigma_ty s
  | arr _ s0 s1 => arr (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | all _ s0 => all (subst_ty (up_ty_ty sigma_ty) s0)
  end.
Definition upId_ty_ty (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (sigma x) (var_ty m_ty x)) :
  forall x, eq (up_ty_ty sigma x) (var_ty (S m_ty) x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upId_list_ty_ty {p : nat} (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (sigma x) (var_ty m_ty x)) :
  forall x, eq (up_list_ty_ty p sigma x) (var_ty (plus p m_ty) x) :=
  fun n =>
  scons_p_eta (var_ty (plus p m_ty))
    (fun n => ap (ren_ty (shift_p p)) (Eq n)) (fun n => eq_refl).
Fixpoint idSubst_ty (sigma_ty : forall _ : fin, ty)
(Eq_ty : forall x, eq (sigma_ty x) (var_ty m_ty x)) (s : ty) :
eq (subst_ty sigma_ty s) s :=
  match s with
  | var_ty _ s => Eq_ty s
  | arr _ s0 s1 =>
      congr_arr (idSubst_ty sigma_ty Eq_ty s0) (idSubst_ty sigma_ty Eq_ty s1)
  | all _ s0 =>
      congr_all (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ Eq_ty) s0)
  end.
Definition upExtRen_ty_ty (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_ty_ty xi x) (upRen_ty_ty zeta x) :=
  fun n =>
  match n with
  | Some fin_n => ap shift (Eq fin_n)
  | None => eq_refl
  end.
Definition upExtRen_list_ty_ty {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_list_ty_ty p xi x) (upRen_list_ty_ty p zeta x) :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n)).
Fixpoint extRen_ty (xi_ty : forall _ : fin, fin)
(zeta_ty : forall _ : fin, fin) (Eq_ty : forall x, eq (xi_ty x) (zeta_ty x))
(s : ty) : eq (ren_ty xi_ty s) (ren_ty zeta_ty s) :=
  match s with
  | var_ty _ s => ap (var_ty n_ty) (Eq_ty s)
  | arr _ s0 s1 =>
      congr_arr (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (extRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upExtRen_ty_ty _ _ Eq_ty) s0)
  end.
Definition upExt_ty_ty (sigma : forall _ : fin, ty)
  (tau : forall _ : fin, ty) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_ty_ty sigma x) (up_ty_ty tau x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upExt_list_ty_ty {p : nat} (sigma : forall _ : fin, ty)
  (tau : forall _ : fin, ty) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_list_ty_ty p sigma x) (up_list_ty_ty p tau x) :=
  fun n =>
  scons_p_congr (fun n => eq_refl) (fun n => ap (ren_ty (shift_p p)) (Eq n)).
Fixpoint ext_ty (sigma_ty : forall _ : fin, ty) (tau_ty : forall _ : fin, ty)
(Eq_ty : forall x, eq (sigma_ty x) (tau_ty x)) (s : ty) :
eq (subst_ty sigma_ty s) (subst_ty tau_ty s) :=
  match s with
  | var_ty _ s => Eq_ty s
  | arr _ s0 s1 =>
      congr_arr (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (ext_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty) (upExt_ty_ty _ _ Eq_ty)
           s0)
  end.
Definition up_ren_ren_ty_ty (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x) (upRen_ty_ty rho x) :=
  up_ren_ren xi zeta rho Eq.
Definition up_ren_ren_list_ty_ty {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_list_ty_ty p zeta) (upRen_list_ty_ty p xi) x)
    (upRen_list_ty_ty p rho x) := up_ren_ren_p Eq.
Fixpoint compRenRen_ty (xi_ty : forall _ : fin, fin)
(zeta_ty : forall _ : fin, fin) (rho_ty : forall _ : fin, fin)
(Eq_ty : forall x, eq (funcomp zeta_ty xi_ty x) (rho_ty x)) (s : ty) :
eq (ren_ty zeta_ty (ren_ty xi_ty s)) (ren_ty rho_ty s) :=
  match s with
  | var_ty _ s => ap (var_ty l_ty) (Eq_ty s)
  | arr _ s0 s1 =>
      congr_arr (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compRenRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upRen_ty_ty rho_ty) (up_ren_ren _ _ _ Eq_ty) s0)
  end.
Definition up_ren_subst_ty_ty (xi : forall _ : fin, fin)
  (tau : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x, eq (funcomp (up_ty_ty tau) (upRen_ty_ty xi) x) (up_ty_ty theta x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition up_ren_subst_list_ty_ty {p : nat} (xi : forall _ : fin, fin)
  (tau : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x,
  eq (funcomp (up_list_ty_ty p tau) (upRen_list_ty_ty p xi) x)
    (up_list_ty_ty p theta x) :=
  fun n =>
  eq_trans (scons_p_comp' _ _ _ n)
    (scons_p_congr (fun z => scons_p_head' _ _ z)
       (fun z =>
        eq_trans (scons_p_tail' _ _ (xi z)) (ap (ren_ty (shift_p p)) (Eq z)))).
Fixpoint compRenSubst_ty (xi_ty : forall _ : fin, fin)
(tau_ty : forall _ : fin, ty) (theta_ty : forall _ : fin, ty)
(Eq_ty : forall x, eq (funcomp tau_ty xi_ty x) (theta_ty x)) (s : ty) :
eq (subst_ty tau_ty (ren_ty xi_ty s)) (subst_ty theta_ty s) :=
  match s with
  | var_ty _ s => Eq_ty s
  | arr _ s0 s1 =>
      congr_arr (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compRenSubst_ty (upRen_ty_ty xi_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_ren_subst_ty_ty _ _ _ Eq_ty) s0)
  end.
Definition up_subst_ren_ty_ty (sigma : forall _ : fin, ty)
  (zeta_ty : forall _ : fin, fin) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (ren_ty zeta_ty) sigma x) (theta x)) :
  forall x,
  eq (funcomp (ren_ty (upRen_ty_ty zeta_ty)) (up_ty_ty sigma) x)
    (up_ty_ty theta x) :=
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
Definition up_subst_ren_list_ty_ty {p : nat} (sigma : forall _ : fin, ty)
  (zeta_ty : forall _ : fin, fin) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (ren_ty zeta_ty) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (ren_ty (upRen_list_ty_ty p zeta_ty)) (up_list_ty_ty p sigma) x)
    (up_list_ty_ty p theta x) :=
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
Fixpoint compSubstRen_ty (sigma_ty : forall _ : fin, ty)
(zeta_ty : forall _ : fin, fin) (theta_ty : forall _ : fin, ty)
(Eq_ty : forall x, eq (funcomp (ren_ty zeta_ty) sigma_ty x) (theta_ty x))
(s : ty) : eq (ren_ty zeta_ty (subst_ty sigma_ty s)) (subst_ty theta_ty s) :=
  match s with
  | var_ty _ s => Eq_ty s
  | arr _ s0 s1 =>
      congr_arr (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compSubstRen_ty (up_ty_ty sigma_ty) (upRen_ty_ty zeta_ty)
           (up_ty_ty theta_ty) (up_subst_ren_ty_ty _ _ _ Eq_ty) s0)
  end.
Definition up_subst_subst_ty_ty (sigma : forall _ : fin, ty)
  (tau_ty : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (subst_ty tau_ty) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_ty (up_ty_ty tau_ty)) (up_ty_ty sigma) x)
    (up_ty_ty theta x) :=
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
Definition up_subst_subst_list_ty_ty {p : nat} (sigma : forall _ : fin, ty)
  (tau_ty : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (subst_ty tau_ty) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_ty (up_list_ty_ty p tau_ty)) (up_list_ty_ty p sigma) x)
    (up_list_ty_ty p theta x) :=
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
Fixpoint compSubstSubst_ty (sigma_ty : forall _ : fin, ty)
(tau_ty : forall _ : fin, ty) (theta_ty : forall _ : fin, ty)
(Eq_ty : forall x, eq (funcomp (subst_ty tau_ty) sigma_ty x) (theta_ty x))
(s : ty) : eq (subst_ty tau_ty (subst_ty sigma_ty s)) (subst_ty theta_ty s)
:=
  match s with
  | var_ty _ s => Eq_ty s
  | arr _ s0 s1 =>
      congr_arr (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (compSubstSubst_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_subst_subst_ty_ty _ _ _ Eq_ty) s0)
  end.
Definition rinstInst_up_ty_ty (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (var_ty n_ty) xi x) (sigma x)) :
  forall x,
  eq (funcomp (var_ty (S n_ty)) (upRen_ty_ty xi) x) (up_ty_ty sigma x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_ty shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition rinstInst_up_list_ty_ty {p : nat} (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (var_ty n_ty) xi x) (sigma x)) :
  forall x,
  eq (funcomp (var_ty (plus p n_ty)) (upRen_list_ty_ty p xi) x)
    (up_list_ty_ty p sigma x) :=
  fun n =>
  eq_trans (scons_p_comp' _ _ (var_ty (plus p n_ty)) n)
    (scons_p_congr (fun z => eq_refl)
       (fun n => ap (ren_ty (shift_p p)) (Eq n))).
Fixpoint rinst_inst_ty (xi_ty : forall _ : fin, fin)
(sigma_ty : forall _ : fin, ty)
(Eq_ty : forall x, eq (funcomp (var_ty n_ty) xi_ty x) (sigma_ty x)) (s : ty)
   : eq (ren_ty xi_ty s) (subst_ty sigma_ty s) :=
  match s with
  | var_ty _ s => Eq_ty s
  | arr _ s0 s1 =>
      congr_arr (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | all _ s0 =>
      congr_all
        (rinst_inst_ty (upRen_ty_ty xi_ty) (up_ty_ty sigma_ty)
           (rinstInst_up_ty_ty _ _ Eq_ty) s0)
  end.
Lemma rinstInst_ty (xi_ty : forall _ : fin, fin) :
  eq (ren_ty xi_ty) (subst_ty (funcomp (var_ty n_ty) xi_ty)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_ty xi_ty _ (fun n => eq_refl) x)).
Qed.
Lemma instId_ty : eq (subst_ty (var_ty m_ty)) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_ty (var_ty m_ty) (fun n => eq_refl) (id x))).
Qed.
Lemma rinstId_ty : eq (@ren_ty m_ty m_ty id) id.
Proof.
exact (eq_trans (rinstInst_ty (id _)) instId_ty).
Qed.
Lemma varL_ty (sigma_ty : forall _ : fin, ty) :
  eq (funcomp (subst_ty sigma_ty) (var_ty m_ty)) sigma_ty.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma varLRen_ty (xi_ty : forall _ : fin, fin) :
  eq (funcomp (ren_ty xi_ty) (var_ty m_ty)) (funcomp (var_ty n_ty) xi_ty).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma renRen_ty (xi_ty : forall _ : fin, fin) (zeta_ty : forall _ : fin, fin)
  (s : ty m_ty) :
  eq (ren_ty zeta_ty (ren_ty xi_ty s)) (ren_ty (funcomp zeta_ty xi_ty) s).
Proof.
exact (compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma renRen'_ty (xi_ty : forall _ : fin, fin)
  (zeta_ty : forall _ : fin, fin) :
  eq (funcomp (ren_ty zeta_ty) (ren_ty xi_ty))
    (ren_ty (funcomp zeta_ty xi_ty)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_ty xi_ty zeta_ty n)).
Qed.
Lemma compRen_ty (sigma_ty : forall _ : fin, ty)
  (zeta_ty : forall _ : fin, fin) (s : ty m_ty) :
  eq (ren_ty zeta_ty (subst_ty sigma_ty s))
    (subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s).
Proof.
exact (compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.
Lemma compRen'_ty (sigma_ty : forall _ : fin, ty)
  (zeta_ty : forall _ : fin, fin) :
  eq (funcomp (ren_ty zeta_ty) (subst_ty sigma_ty))
    (subst_ty (funcomp (ren_ty zeta_ty) sigma_ty)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_ty sigma_ty zeta_ty n)).
Qed.
Lemma renComp_ty (xi_ty : forall _ : fin, fin) (tau_ty : forall _ : fin, ty)
  (s : ty m_ty) :
  eq (subst_ty tau_ty (ren_ty xi_ty s)) (subst_ty (funcomp tau_ty xi_ty) s).
Proof.
exact (compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma renComp'_ty (xi_ty : forall _ : fin, fin) (tau_ty : forall _ : fin, ty)
  :
  eq (funcomp (subst_ty tau_ty) (ren_ty xi_ty))
    (subst_ty (funcomp tau_ty xi_ty)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_ty xi_ty tau_ty n)).
Qed.
Lemma compComp_ty (sigma_ty : forall _ : fin, ty)
  (tau_ty : forall _ : fin, ty) (s : ty m_ty) :
  eq (subst_ty tau_ty (subst_ty sigma_ty s))
    (subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s).
Proof.
exact (compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.
Lemma compComp'_ty (sigma_ty : forall _ : fin, ty)
  (tau_ty : forall _ : fin, ty) :
  eq (funcomp (subst_ty tau_ty) (subst_ty sigma_ty))
    (subst_ty (funcomp (subst_ty tau_ty) sigma_ty)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_ty sigma_ty tau_ty n)).
Qed.
Inductive tm : Type :=
  | app : forall _ : tm, forall _ : tm, tm
  | tapp : forall _ : tm, forall _ : ty, tm
  | vt : forall _ : vl, tm
with vl : Type :=
  | var_vl : forall _ : fin, vl
  | lam : forall _ : ty, forall _ : tm, vl
  | tlam : forall _ : tm, vl.
Lemma congr_app {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : eq s0 t0)
  (H1 : eq s1 t1) : eq (app m_ty m_vl s0 s1) (app m_ty m_vl t0 t1).
Proof.
exact (eq_trans
                (eq_trans eq_refl (f_equal (fun x => app m_ty m_vl x s1) H0))
                (f_equal (fun x => app m_ty m_vl t0 x) H1)).
Qed.
Lemma congr_tapp {s0 : tm} {s1 : ty} {t0 : tm} {t1 : ty} (H0 : eq s0 t0)
  (H1 : eq s1 t1) : eq (tapp m_ty m_vl s0 s1) (tapp m_ty m_vl t0 t1).
Proof.
exact (eq_trans
                (eq_trans eq_refl (f_equal (fun x => tapp m_ty m_vl x s1) H0))
                (f_equal (fun x => tapp m_ty m_vl t0 x) H1)).
Qed.
Lemma congr_vt {s0 : vl} {t0 : vl} (H0 : eq s0 t0) :
  eq (vt m_ty m_vl s0) (vt m_ty m_vl t0).
Proof.
exact (eq_trans eq_refl (f_equal (fun x => vt m_ty m_vl x) H0)).
Qed.
Lemma congr_lam {s0 : ty} {s1 : tm} {t0 : ty} {t1 : tm} (H0 : eq s0 t0)
  (H1 : eq s1 t1) : eq (lam m_ty m_vl s0 s1) (lam m_ty m_vl t0 t1).
Proof.
exact (eq_trans
                (eq_trans eq_refl (f_equal (fun x => lam m_ty m_vl x s1) H0))
                (f_equal (fun x => lam m_ty m_vl t0 x) H1)).
Qed.
Lemma congr_tlam {s0 : tm} {t0 : tm} (H0 : eq s0 t0) :
  eq (tlam m_ty m_vl s0) (tlam m_ty m_vl t0).
Proof.
exact (eq_trans eq_refl (f_equal (fun x => tlam m_ty m_vl x) H0)).
Qed.
Definition upRen_ty_vl (xi : forall _ : fin, fin) : forall _ : fin, fin := xi.
Definition upRen_vl_ty (xi : forall _ : fin, fin) : forall _ : fin, fin := xi.
Definition upRen_vl_vl (xi : forall _ : fin, fin) : forall _ : fin, fin :=
  up_ren xi.
Definition upRen_list_ty_vl (p : nat) (xi : forall _ : fin, fin) :
  forall _ : fin, fin := xi.
Definition upRen_list_vl_ty (p : nat) (xi : forall _ : fin, fin) :
  forall _ : fin, fin := xi.
Definition upRen_list_vl_vl (p : nat) (xi : forall _ : fin, fin) :
  forall _ : fin, fin := upRen_p p xi.
Fixpoint ren_tm (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
(s : tm) : tm n_ty n_vl :=
  match s with
  | app _ _ s0 s1 =>
      app n_ty n_vl (ren_tm xi_ty xi_vl s0) (ren_tm xi_ty xi_vl s1)
  | tapp _ _ s0 s1 =>
      tapp n_ty n_vl (ren_tm xi_ty xi_vl s0) (ren_ty xi_ty s1)
  | vt _ _ s0 => vt n_ty n_vl (ren_vl xi_ty xi_vl s0)
  end
with ren_vl (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
(s : vl) : vl n_ty n_vl :=
  match s with
  | var_vl _ _ s => var_vl n_ty n_vl (xi_vl s)
  | lam _ _ s0 s1 =>
      lam n_ty n_vl (ren_ty xi_ty s0)
        (ren_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl) s1)
  | tlam _ _ s0 =>
      tlam n_ty n_vl (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl) s0)
  end.
Definition up_ty_vl (sigma : forall _ : fin, vl) : forall _ : fin, vl :=
  funcomp (ren_vl shift id) sigma.
Definition up_vl_ty (sigma : forall _ : fin, ty) : forall _ : fin, ty :=
  funcomp (ren_ty id) sigma.
Definition up_vl_vl (sigma : forall _ : fin, vl) : forall _ : fin, vl :=
  scons (var_vl n_ty (S n_vl) var_zero) (funcomp (ren_vl id shift) sigma).
Definition up_list_ty_vl (p : nat) (sigma : forall _ : fin, vl) :
  forall _ : fin, vl := funcomp (ren_vl (shift_p p) id) sigma.
Definition up_list_vl_ty (p : nat) (sigma : forall _ : fin, ty) :
  forall _ : fin, ty := funcomp (ren_ty id) sigma.
Definition up_list_vl_vl (p : nat) (sigma : forall _ : fin, vl) :
  forall _ : fin, vl :=
  scons_p p (funcomp (var_vl n_ty (plus p n_vl)) (zero_p p))
    (funcomp (ren_vl id (shift_p p)) sigma).
Fixpoint subst_tm (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl) (s : tm) : tm n_ty n_vl :=
  match s with
  | app _ _ s0 s1 =>
      app (subst_tm sigma_ty sigma_vl s0) (subst_tm sigma_ty sigma_vl s1)
  | tapp _ _ s0 s1 =>
      tapp (subst_tm sigma_ty sigma_vl s0) (subst_ty sigma_ty s1)
  | vt _ _ s0 => vt (subst_vl sigma_ty sigma_vl s0)
  end
with subst_vl (sigma_ty : forall _ : fin, ty) (sigma_vl : forall _ : fin, vl)
(s : vl) : vl n_ty n_vl :=
  match s with
  | var_vl _ _ s => sigma_vl s
  | lam _ _ s0 s1 =>
      lam (subst_ty sigma_ty s0)
        (subst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl) s1)
  | tlam _ _ s0 => tlam (subst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl) s0)
  end.
Definition upId_ty_vl (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (sigma x) (var_vl m_ty m_vl x)) :
  forall x, eq (up_ty_vl sigma x) (var_vl (S m_ty) m_vl x) :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition upId_vl_ty (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (sigma x) (var_ty m_ty x)) :
  forall x, eq (up_vl_ty sigma x) (var_ty m_ty x) :=
  fun n => ap (ren_ty id) (Eq n).
Definition upId_vl_vl (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (sigma x) (var_vl m_ty m_vl x)) :
  forall x, eq (up_vl_vl sigma x) (var_vl m_ty (S m_vl) x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upId_list_ty_vl {p : nat} (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (sigma x) (var_vl m_ty m_vl x)) :
  forall x, eq (up_list_ty_vl p sigma x) (var_vl (plus p m_ty) m_vl x) :=
  fun n => ap (ren_vl (shift_p p) id) (Eq n).
Definition upId_list_vl_ty {p : nat} (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (sigma x) (var_ty m_ty x)) :
  forall x, eq (up_list_vl_ty p sigma x) (var_ty m_ty x) :=
  fun n => ap (ren_ty id) (Eq n).
Definition upId_list_vl_vl {p : nat} (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (sigma x) (var_vl m_ty m_vl x)) :
  forall x, eq (up_list_vl_vl p sigma x) (var_vl m_ty (plus p m_vl) x) :=
  fun n =>
  scons_p_eta (var_vl m_ty (plus p m_vl))
    (fun n => ap (ren_vl id (shift_p p)) (Eq n)) (fun n => eq_refl).
Fixpoint idSubst_tm (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (sigma_ty x) (var_ty m_ty x))
(Eq_vl : forall x, eq (sigma_vl x) (var_vl m_ty m_vl x)) (s : tm) :
eq (subst_tm sigma_ty sigma_vl s) s :=
  match s with
  | app _ _ s0 s1 =>
      congr_app (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s1)
  | tapp _ _ s0 s1 =>
      congr_tapp (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | vt _ _ s0 => congr_vt (idSubst_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
  end
with idSubst_vl (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (sigma_ty x) (var_ty m_ty x))
(Eq_vl : forall x, eq (sigma_vl x) (var_vl m_ty m_vl x)) (s : vl) :
eq (subst_vl sigma_ty sigma_vl s) s :=
  match s with
  | var_vl _ _ s => Eq_vl s
  | lam _ _ s0 s1 =>
      congr_lam (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (upId_vl_ty _ Eq_ty) (upId_vl_vl _ Eq_vl) s1)
  | tlam _ _ s0 =>
      congr_tlam
        (idSubst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (upId_ty_ty _ Eq_ty) (upId_ty_vl _ Eq_vl) s0)
  end.
Definition upExtRen_ty_vl (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_ty_vl xi x) (upRen_ty_vl zeta x) := fun n => Eq n.
Definition upExtRen_vl_ty (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_vl_ty xi x) (upRen_vl_ty zeta x) := fun n => Eq n.
Definition upExtRen_vl_vl (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_vl_vl xi x) (upRen_vl_vl zeta x) :=
  fun n =>
  match n with
  | Some fin_n => ap shift (Eq fin_n)
  | None => eq_refl
  end.
Definition upExtRen_list_ty_vl {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_list_ty_vl p xi x) (upRen_list_ty_vl p zeta x) :=
  fun n => Eq n.
Definition upExtRen_list_vl_ty {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_list_vl_ty p xi x) (upRen_list_vl_ty p zeta x) :=
  fun n => Eq n.
Definition upExtRen_list_vl_vl {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_list_vl_vl p xi x) (upRen_list_vl_vl p zeta x) :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n)).
Fixpoint extRen_tm (xi_ty : forall _ : fin, fin)
(xi_vl : forall _ : fin, fin) (zeta_ty : forall _ : fin, fin)
(zeta_vl : forall _ : fin, fin) (Eq_ty : forall x, eq (xi_ty x) (zeta_ty x))
(Eq_vl : forall x, eq (xi_vl x) (zeta_vl x)) (s : tm) :
eq (ren_tm xi_ty xi_vl s) (ren_tm zeta_ty zeta_vl s) :=
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
with extRen_vl (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
(zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin)
(Eq_ty : forall x, eq (xi_ty x) (zeta_ty x))
(Eq_vl : forall x, eq (xi_vl x) (zeta_vl x)) (s : vl) :
eq (ren_vl xi_ty xi_vl s) (ren_vl zeta_ty zeta_vl s) :=
  match s with
  | var_vl _ _ s => ap (var_vl n_ty n_vl) (Eq_vl s)
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
Definition upExt_ty_vl (sigma : forall _ : fin, vl)
  (tau : forall _ : fin, vl) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_ty_vl sigma x) (up_ty_vl tau x) :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition upExt_vl_ty (sigma : forall _ : fin, ty)
  (tau : forall _ : fin, ty) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_vl_ty sigma x) (up_vl_ty tau x) :=
  fun n => ap (ren_ty id) (Eq n).
Definition upExt_vl_vl (sigma : forall _ : fin, vl)
  (tau : forall _ : fin, vl) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_vl_vl sigma x) (up_vl_vl tau x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upExt_list_ty_vl {p : nat} (sigma : forall _ : fin, vl)
  (tau : forall _ : fin, vl) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_list_ty_vl p sigma x) (up_list_ty_vl p tau x) :=
  fun n => ap (ren_vl (shift_p p) id) (Eq n).
Definition upExt_list_vl_ty {p : nat} (sigma : forall _ : fin, ty)
  (tau : forall _ : fin, ty) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_list_vl_ty p sigma x) (up_list_vl_ty p tau x) :=
  fun n => ap (ren_ty id) (Eq n).
Definition upExt_list_vl_vl {p : nat} (sigma : forall _ : fin, vl)
  (tau : forall _ : fin, vl) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_list_vl_vl p sigma x) (up_list_vl_vl p tau x) :=
  fun n =>
  scons_p_congr (fun n => eq_refl)
    (fun n => ap (ren_vl id (shift_p p)) (Eq n)).
Fixpoint ext_tm (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl) (tau_ty : forall _ : fin, ty)
(tau_vl : forall _ : fin, vl) (Eq_ty : forall x, eq (sigma_ty x) (tau_ty x))
(Eq_vl : forall x, eq (sigma_vl x) (tau_vl x)) (s : tm) :
eq (subst_tm sigma_ty sigma_vl s) (subst_tm tau_ty tau_vl s) :=
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
with ext_vl (sigma_ty : forall _ : fin, ty) (sigma_vl : forall _ : fin, vl)
(tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (sigma_ty x) (tau_ty x))
(Eq_vl : forall x, eq (sigma_vl x) (tau_vl x)) (s : vl) :
eq (subst_vl sigma_ty sigma_vl s) (subst_vl tau_ty tau_vl s) :=
  match s with
  | var_vl _ _ s => Eq_vl s
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
Definition up_ren_ren_ty_vl (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_ty_vl zeta) (upRen_ty_vl xi) x) (upRen_ty_vl rho x) :=
  Eq.
Definition up_ren_ren_vl_ty (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_vl_ty zeta) (upRen_vl_ty xi) x) (upRen_vl_ty rho x) :=
  Eq.
Definition up_ren_ren_vl_vl (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_vl_vl zeta) (upRen_vl_vl xi) x) (upRen_vl_vl rho x) :=
  up_ren_ren xi zeta rho Eq.
Definition up_ren_ren_list_ty_vl {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_list_ty_vl p zeta) (upRen_list_ty_vl p xi) x)
    (upRen_list_ty_vl p rho x) := Eq.
Definition up_ren_ren_list_vl_ty {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_list_vl_ty p zeta) (upRen_list_vl_ty p xi) x)
    (upRen_list_vl_ty p rho x) := Eq.
Definition up_ren_ren_list_vl_vl {p : nat} (xi : forall _ : fin, fin)
  (zeta : forall _ : fin, fin) (rho : forall _ : fin, fin)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_list_vl_vl p zeta) (upRen_list_vl_vl p xi) x)
    (upRen_list_vl_vl p rho x) := up_ren_ren_p Eq.
Fixpoint compRenRen_tm (xi_ty : forall _ : fin, fin)
(xi_vl : forall _ : fin, fin) (zeta_ty : forall _ : fin, fin)
(zeta_vl : forall _ : fin, fin) (rho_ty : forall _ : fin, fin)
(rho_vl : forall _ : fin, fin)
(Eq_ty : forall x, eq (funcomp zeta_ty xi_ty x) (rho_ty x))
(Eq_vl : forall x, eq (funcomp zeta_vl xi_vl x) (rho_vl x)) (s : tm) :
eq (ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s)) (ren_tm rho_ty rho_vl s)
:=
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
with compRenRen_vl (xi_ty : forall _ : fin, fin)
(xi_vl : forall _ : fin, fin) (zeta_ty : forall _ : fin, fin)
(zeta_vl : forall _ : fin, fin) (rho_ty : forall _ : fin, fin)
(rho_vl : forall _ : fin, fin)
(Eq_ty : forall x, eq (funcomp zeta_ty xi_ty x) (rho_ty x))
(Eq_vl : forall x, eq (funcomp zeta_vl xi_vl x) (rho_vl x)) (s : vl) :
eq (ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s)) (ren_vl rho_ty rho_vl s)
:=
  match s with
  | var_vl _ _ s => ap (var_vl l_ty l_vl) (Eq_vl s)
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
Definition up_ren_subst_ty_vl (xi : forall _ : fin, fin)
  (tau : forall _ : fin, vl) (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x, eq (funcomp (up_ty_vl tau) (upRen_ty_vl xi) x) (up_ty_vl theta x) :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition up_ren_subst_vl_ty (xi : forall _ : fin, fin)
  (tau : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x, eq (funcomp (up_vl_ty tau) (upRen_vl_ty xi) x) (up_vl_ty theta x) :=
  fun n => ap (ren_ty id) (Eq n).
Definition up_ren_subst_vl_vl (xi : forall _ : fin, fin)
  (tau : forall _ : fin, vl) (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x, eq (funcomp (up_vl_vl tau) (upRen_vl_vl xi) x) (up_vl_vl theta x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition up_ren_subst_list_ty_vl {p : nat} (xi : forall _ : fin, fin)
  (tau : forall _ : fin, vl) (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x,
  eq (funcomp (up_list_ty_vl p tau) (upRen_list_ty_vl p xi) x)
    (up_list_ty_vl p theta x) := fun n => ap (ren_vl (shift_p p) id) (Eq n).
Definition up_ren_subst_list_vl_ty {p : nat} (xi : forall _ : fin, fin)
  (tau : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x,
  eq (funcomp (up_list_vl_ty p tau) (upRen_list_vl_ty p xi) x)
    (up_list_vl_ty p theta x) := fun n => ap (ren_ty id) (Eq n).
Definition up_ren_subst_list_vl_vl {p : nat} (xi : forall _ : fin, fin)
  (tau : forall _ : fin, vl) (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x,
  eq (funcomp (up_list_vl_vl p tau) (upRen_list_vl_vl p xi) x)
    (up_list_vl_vl p theta x) :=
  fun n =>
  eq_trans (scons_p_comp' _ _ _ n)
    (scons_p_congr (fun z => scons_p_head' _ _ z)
       (fun z =>
        eq_trans (scons_p_tail' _ _ (xi z))
          (ap (ren_vl id (shift_p p)) (Eq z)))).
Fixpoint compRenSubst_tm (xi_ty : forall _ : fin, fin)
(xi_vl : forall _ : fin, fin) (tau_ty : forall _ : fin, ty)
(tau_vl : forall _ : fin, vl) (theta_ty : forall _ : fin, ty)
(theta_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp tau_ty xi_ty x) (theta_ty x))
(Eq_vl : forall x, eq (funcomp tau_vl xi_vl x) (theta_vl x)) (s : tm) :
eq (subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s))
  (subst_tm theta_ty theta_vl s) :=
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
with compRenSubst_vl (xi_ty : forall _ : fin, fin)
(xi_vl : forall _ : fin, fin) (tau_ty : forall _ : fin, ty)
(tau_vl : forall _ : fin, vl) (theta_ty : forall _ : fin, ty)
(theta_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp tau_ty xi_ty x) (theta_ty x))
(Eq_vl : forall x, eq (funcomp tau_vl xi_vl x) (theta_vl x)) (s : vl) :
eq (subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s))
  (subst_vl theta_ty theta_vl s) :=
  match s with
  | var_vl _ _ s => Eq_vl s
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
Definition up_subst_ren_ty_vl (sigma : forall _ : fin, vl)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (ren_vl zeta_ty zeta_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (ren_vl (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl))
       (up_ty_vl sigma) x) (up_ty_vl theta x) :=
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
Definition up_subst_ren_vl_ty (sigma : forall _ : fin, ty)
  (zeta_ty : forall _ : fin, fin) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (ren_ty zeta_ty) sigma x) (theta x)) :
  forall x,
  eq (funcomp (ren_ty (upRen_vl_ty zeta_ty)) (up_vl_ty sigma) x)
    (up_vl_ty theta x) :=
  fun n =>
  eq_trans
    (compRenRen_ty id (upRen_vl_ty zeta_ty) (funcomp id zeta_ty)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_ty zeta_ty id (funcomp id zeta_ty) (fun x => eq_refl)
             (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_ren_vl_vl (sigma : forall _ : fin, vl)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (ren_vl zeta_ty zeta_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (ren_vl (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl))
       (up_vl_vl sigma) x) (up_vl_vl theta x) :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenRen_vl id shift (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl)
           (funcomp id zeta_ty) (funcomp shift zeta_vl) (fun x => eq_refl)
           (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compRenRen_vl zeta_ty zeta_vl id shift (funcomp id zeta_ty)
                 (funcomp shift zeta_vl) (fun x => eq_refl)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_vl id shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_ren_list_ty_vl {p : nat} (sigma : forall _ : fin, vl)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (ren_vl zeta_ty zeta_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp
       (ren_vl (upRen_list_ty_ty p zeta_ty) (upRen_list_ty_vl p zeta_vl))
       (up_list_ty_vl p sigma) x) (up_list_ty_vl p theta x) :=
  fun n =>
  eq_trans
    (compRenRen_vl (shift_p p) id (upRen_list_ty_ty p zeta_ty)
       (upRen_list_ty_vl p zeta_vl) (funcomp (shift_p p) zeta_ty)
       (funcomp id zeta_vl) (fun x => scons_p_tail' _ _ x) (fun x => eq_refl)
       (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_vl zeta_ty zeta_vl (shift_p p) id
             (funcomp (shift_p p) zeta_ty) (funcomp id zeta_vl)
             (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
       (ap (ren_vl (shift_p p) id) (Eq n))).
Definition up_subst_ren_list_vl_ty {p : nat} (sigma : forall _ : fin, ty)
  (zeta_ty : forall _ : fin, fin) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (ren_ty zeta_ty) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (ren_ty (upRen_list_vl_ty p zeta_ty)) (up_list_vl_ty p sigma) x)
    (up_list_vl_ty p theta x) :=
  fun n =>
  eq_trans
    (compRenRen_ty id (upRen_list_vl_ty p zeta_ty) (funcomp id zeta_ty)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compRenRen_ty zeta_ty id (funcomp id zeta_ty) (fun x => eq_refl)
             (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_ren_list_vl_vl {p : nat} (sigma : forall _ : fin, vl)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (ren_vl zeta_ty zeta_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp
       (ren_vl (upRen_list_vl_ty p zeta_ty) (upRen_list_vl_vl p zeta_vl))
       (up_list_vl_vl p sigma) x) (up_list_vl_vl p theta x) :=
  fun n =>
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
             (ap (ren_vl id (shift_p p)) (Eq n))))).
Fixpoint compSubstRen_tm (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl) (zeta_ty : forall _ : fin, fin)
(zeta_vl : forall _ : fin, fin) (theta_ty : forall _ : fin, ty)
(theta_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp (ren_ty zeta_ty) sigma_ty x) (theta_ty x))
(Eq_vl : forall x,
         eq (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x) (theta_vl x))
(s : tm) :
eq (ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s))
  (subst_tm theta_ty theta_vl s) :=
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
with compSubstRen_vl (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl) (zeta_ty : forall _ : fin, fin)
(zeta_vl : forall _ : fin, fin) (theta_ty : forall _ : fin, ty)
(theta_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp (ren_ty zeta_ty) sigma_ty x) (theta_ty x))
(Eq_vl : forall x,
         eq (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x) (theta_vl x))
(s : vl) :
eq (ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s))
  (subst_vl theta_ty theta_vl s) :=
  match s with
  | var_vl _ _ s => Eq_vl s
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
Definition up_subst_subst_ty_vl (sigma : forall _ : fin, vl)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (subst_vl tau_ty tau_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (subst_vl (up_ty_ty tau_ty) (up_ty_vl tau_vl)) (up_ty_vl sigma)
       x) (up_ty_vl theta x) :=
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
Definition up_subst_subst_vl_ty (sigma : forall _ : fin, ty)
  (tau_ty : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (subst_ty tau_ty) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_ty (up_vl_ty tau_ty)) (up_vl_ty sigma) x)
    (up_vl_ty theta x) :=
  fun n =>
  eq_trans
    (compRenSubst_ty id (up_vl_ty tau_ty) (funcomp (up_vl_ty tau_ty) id)
       (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty)
             (fun x => eq_refl) (sigma n))) (ap (ren_ty id) (Eq n))).
Definition up_subst_subst_vl_vl (sigma : forall _ : fin, vl)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (subst_vl tau_ty tau_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (subst_vl (up_vl_ty tau_ty) (up_vl_vl tau_vl)) (up_vl_vl sigma)
       x) (up_vl_vl theta x) :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenSubst_vl id shift (up_vl_ty tau_ty) (up_vl_vl tau_vl)
           (funcomp (up_vl_ty tau_ty) id) (funcomp (up_vl_vl tau_vl) shift)
           (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compSubstRen_vl tau_ty tau_vl id shift
                 (funcomp (ren_ty id) tau_ty)
                 (funcomp (ren_vl id shift) tau_vl) (fun x => eq_refl)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_vl id shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_subst_list_ty_vl {p : nat} (sigma : forall _ : fin, vl)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (subst_vl tau_ty tau_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (subst_vl (up_list_ty_ty p tau_ty) (up_list_ty_vl p tau_vl))
       (up_list_ty_vl p sigma) x) (up_list_ty_vl p theta x) :=
  fun n =>
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
       (ap (ren_vl (shift_p p) id) (Eq n))).
Definition up_subst_subst_list_vl_ty {p : nat} (sigma : forall _ : fin, ty)
  (tau_ty : forall _ : fin, ty) (theta : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (subst_ty tau_ty) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_ty (up_list_vl_ty p tau_ty)) (up_list_vl_ty p sigma) x)
    (up_list_vl_ty p theta x) :=
  fun n =>
  eq_trans
    (compRenSubst_ty id (up_list_vl_ty p tau_ty)
       (funcomp (up_list_vl_ty p tau_ty) id) (fun x => eq_refl) (sigma n))
    (eq_trans
       (eq_sym
          (compSubstRen_ty tau_ty id _ (fun x => eq_sym eq_refl) (sigma n)))
       (ap (ren_ty id) (Eq n))).
Definition up_subst_subst_list_vl_vl {p : nat} (sigma : forall _ : fin, vl)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl)
  (theta : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (subst_vl tau_ty tau_vl) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (subst_vl (up_list_vl_ty p tau_ty) (up_list_vl_vl p tau_vl))
       (up_list_vl_vl p sigma) x) (up_list_vl_vl p theta x) :=
  fun n =>
  eq_trans
    (scons_p_comp' (funcomp (var_vl l_ty (plus p l_vl)) (zero_p p)) _ _ n)
    (scons_p_congr
       (fun x => scons_p_head' _ (fun z => ren_vl id (shift_p p) _) x)
       (fun n =>
        eq_trans
          (compRenSubst_vl id (shift_p p) (up_list_vl_ty p tau_ty)
             (up_list_vl_vl p tau_vl) (funcomp (up_list_vl_ty p tau_ty) id)
             (funcomp (up_list_vl_vl p tau_vl) (shift_p p))
             (fun x => eq_refl) (fun x => eq_refl) (sigma n))
          (eq_trans
             (eq_sym
                (compSubstRen_vl tau_ty tau_vl id (shift_p p) _ _
                   (fun x => eq_sym eq_refl)
                   (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
             (ap (ren_vl id (shift_p p)) (Eq n))))).
Fixpoint compSubstSubst_tm (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl) (tau_ty : forall _ : fin, ty)
(tau_vl : forall _ : fin, vl) (theta_ty : forall _ : fin, ty)
(theta_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp (subst_ty tau_ty) sigma_ty x) (theta_ty x))
(Eq_vl : forall x,
         eq (funcomp (subst_vl tau_ty tau_vl) sigma_vl x) (theta_vl x))
(s : tm) :
eq (subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s))
  (subst_tm theta_ty theta_vl s) :=
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
with compSubstSubst_vl (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl) (tau_ty : forall _ : fin, ty)
(tau_vl : forall _ : fin, vl) (theta_ty : forall _ : fin, ty)
(theta_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp (subst_ty tau_ty) sigma_ty x) (theta_ty x))
(Eq_vl : forall x,
         eq (funcomp (subst_vl tau_ty tau_vl) sigma_vl x) (theta_vl x))
(s : vl) :
eq (subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s))
  (subst_vl theta_ty theta_vl s) :=
  match s with
  | var_vl _ _ s => Eq_vl s
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
Definition rinstInst_up_ty_vl (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (var_vl n_ty n_vl) xi x) (sigma x)) :
  forall x,
  eq (funcomp (var_vl (S n_ty) n_vl) (upRen_ty_vl xi) x) (up_ty_vl sigma x) :=
  fun n => ap (ren_vl shift id) (Eq n).
Definition rinstInst_up_vl_ty (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (var_ty n_ty) xi x) (sigma x)) :
  forall x, eq (funcomp (var_ty n_ty) (upRen_vl_ty xi) x) (up_vl_ty sigma x) :=
  fun n => ap (ren_ty id) (Eq n).
Definition rinstInst_up_vl_vl (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (var_vl n_ty n_vl) xi x) (sigma x)) :
  forall x,
  eq (funcomp (var_vl n_ty (S n_vl)) (upRen_vl_vl xi) x) (up_vl_vl sigma x) :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_vl id shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition rinstInst_up_list_ty_vl {p : nat} (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (var_vl n_ty n_vl) xi x) (sigma x)) :
  forall x,
  eq (funcomp (var_vl (plus p n_ty) n_vl) (upRen_list_ty_vl p xi) x)
    (up_list_ty_vl p sigma x) := fun n => ap (ren_vl (shift_p p) id) (Eq n).
Definition rinstInst_up_list_vl_ty {p : nat} (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, ty)
  (Eq : forall x, eq (funcomp (var_ty n_ty) xi x) (sigma x)) :
  forall x,
  eq (funcomp (var_ty n_ty) (upRen_list_vl_ty p xi) x)
    (up_list_vl_ty p sigma x) := fun n => ap (ren_ty id) (Eq n).
Definition rinstInst_up_list_vl_vl {p : nat} (xi : forall _ : fin, fin)
  (sigma : forall _ : fin, vl)
  (Eq : forall x, eq (funcomp (var_vl n_ty n_vl) xi x) (sigma x)) :
  forall x,
  eq (funcomp (var_vl n_ty (plus p n_vl)) (upRen_list_vl_vl p xi) x)
    (up_list_vl_vl p sigma x) :=
  fun n =>
  eq_trans (scons_p_comp' _ _ (var_vl n_ty (plus p n_vl)) n)
    (scons_p_congr (fun z => eq_refl)
       (fun n => ap (ren_vl id (shift_p p)) (Eq n))).
Fixpoint rinst_inst_tm (xi_ty : forall _ : fin, fin)
(xi_vl : forall _ : fin, fin) (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp (var_ty n_ty) xi_ty x) (sigma_ty x))
(Eq_vl : forall x, eq (funcomp (var_vl n_ty n_vl) xi_vl x) (sigma_vl x))
(s : tm) : eq (ren_tm xi_ty xi_vl s) (subst_tm sigma_ty sigma_vl s) :=
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
with rinst_inst_vl (xi_ty : forall _ : fin, fin)
(xi_vl : forall _ : fin, fin) (sigma_ty : forall _ : fin, ty)
(sigma_vl : forall _ : fin, vl)
(Eq_ty : forall x, eq (funcomp (var_ty n_ty) xi_ty x) (sigma_ty x))
(Eq_vl : forall x, eq (funcomp (var_vl n_ty n_vl) xi_vl x) (sigma_vl x))
(s : vl) : eq (ren_vl xi_ty xi_vl s) (subst_vl sigma_ty sigma_vl s) :=
  match s with
  | var_vl _ _ s => Eq_vl s
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
Lemma rinstInst_tm (xi_ty : forall _ : fin, fin)
  (xi_vl : forall _ : fin, fin) :
  eq (ren_tm xi_ty xi_vl)
    (subst_tm (funcomp (var_ty n_ty) xi_ty)
       (funcomp (var_vl n_ty n_vl) xi_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_tm xi_ty xi_vl _ _ (fun n => eq_refl)
                   (fun n => eq_refl) x)).
Qed.
Lemma rinstInst_vl (xi_ty : forall _ : fin, fin)
  (xi_vl : forall _ : fin, fin) :
  eq (ren_vl xi_ty xi_vl)
    (subst_vl (funcomp (var_ty n_ty) xi_ty)
       (funcomp (var_vl n_ty n_vl) xi_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_vl xi_ty xi_vl _ _ (fun n => eq_refl)
                   (fun n => eq_refl) x)).
Qed.
Lemma instId_tm : eq (subst_tm (var_ty m_ty) (var_vl m_ty m_vl)) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_tm (var_ty m_ty) (var_vl m_ty m_vl)
                   (fun n => eq_refl) (fun n => eq_refl) (id x))).
Qed.
Lemma instId_vl : eq (subst_vl (var_ty m_ty) (var_vl m_ty m_vl)) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_vl (var_ty m_ty) (var_vl m_ty m_vl)
                   (fun n => eq_refl) (fun n => eq_refl) (id x))).
Qed.
Lemma rinstId_tm : eq (@ren_tm m_ty m_vl m_ty m_vl id id) id.
Proof.
exact (eq_trans (rinstInst_tm (id _) (id _)) instId_tm).
Qed.
Lemma rinstId_vl : eq (@ren_vl m_ty m_vl m_ty m_vl id id) id.
Proof.
exact (eq_trans (rinstInst_vl (id _) (id _)) instId_vl).
Qed.
Lemma varL_vl (sigma_ty : forall _ : fin, ty) (sigma_vl : forall _ : fin, vl)
  : eq (funcomp (subst_vl sigma_ty sigma_vl) (var_vl m_ty m_vl)) sigma_vl.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma varLRen_vl (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  :
  eq (funcomp (ren_vl xi_ty xi_vl) (var_vl m_ty m_vl))
    (funcomp (var_vl n_ty n_vl) xi_vl).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma renRen_tm (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin)
  (s : tm m_ty m_vl) :
  eq (ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s))
    (ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s).
Proof.
exact (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renRen'_tm (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin) :
  eq (funcomp (ren_tm zeta_ty zeta_vl) (ren_tm xi_ty xi_vl))
    (ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_tm xi_ty xi_vl zeta_ty zeta_vl n)).
Qed.
Lemma renRen_vl (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin)
  (s : vl m_ty m_vl) :
  eq (ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s))
    (ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s).
Proof.
exact (compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renRen'_vl (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (zeta_ty : forall _ : fin, fin) (zeta_vl : forall _ : fin, fin) :
  eq (funcomp (ren_vl zeta_ty zeta_vl) (ren_vl xi_ty xi_vl))
    (ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_vl xi_ty xi_vl zeta_ty zeta_vl n)).
Qed.
Lemma compRen_tm (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (zeta_ty : forall _ : fin, fin)
  (zeta_vl : forall _ : fin, fin) (s : tm m_ty m_vl) :
  eq (ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s))
    (subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
       (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s).
Proof.
exact (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compRen'_tm (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (zeta_ty : forall _ : fin, fin)
  (zeta_vl : forall _ : fin, fin) :
  eq (funcomp (ren_tm zeta_ty zeta_vl) (subst_tm sigma_ty sigma_vl))
    (subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
       (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_tm sigma_ty sigma_vl zeta_ty zeta_vl n)).
Qed.
Lemma compRen_vl (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (zeta_ty : forall _ : fin, fin)
  (zeta_vl : forall _ : fin, fin) (s : vl m_ty m_vl) :
  eq (ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s))
    (subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
       (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s).
Proof.
exact (compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compRen'_vl (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (zeta_ty : forall _ : fin, fin)
  (zeta_vl : forall _ : fin, fin) :
  eq (funcomp (ren_vl zeta_ty zeta_vl) (subst_vl sigma_ty sigma_vl))
    (subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
       (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_vl sigma_ty sigma_vl zeta_ty zeta_vl n)).
Qed.
Lemma renComp_tm (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl)
  (s : tm m_ty m_vl) :
  eq (subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s))
    (subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s).
Proof.
exact (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renComp'_tm (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl) :
  eq (funcomp (subst_tm tau_ty tau_vl) (ren_tm xi_ty xi_vl))
    (subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_tm xi_ty xi_vl tau_ty tau_vl n)).
Qed.
Lemma renComp_vl (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl)
  (s : vl m_ty m_vl) :
  eq (subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s))
    (subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s).
Proof.
exact (compRenSubst_vl xi_ty xi_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma renComp'_vl (xi_ty : forall _ : fin, fin) (xi_vl : forall _ : fin, fin)
  (tau_ty : forall _ : fin, ty) (tau_vl : forall _ : fin, vl) :
  eq (funcomp (subst_vl tau_ty tau_vl) (ren_vl xi_ty xi_vl))
    (subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_vl xi_ty xi_vl tau_ty tau_vl n)).
Qed.
Lemma compComp_tm (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (tau_ty : forall _ : fin, ty)
  (tau_vl : forall _ : fin, vl) (s : tm m_ty m_vl) :
  eq (subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s))
    (subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
       (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s).
Proof.
exact (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compComp'_tm (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (tau_ty : forall _ : fin, ty)
  (tau_vl : forall _ : fin, vl) :
  eq (funcomp (subst_tm tau_ty tau_vl) (subst_tm sigma_ty sigma_vl))
    (subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
       (funcomp (subst_vl tau_ty tau_vl) sigma_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_tm sigma_ty sigma_vl tau_ty tau_vl n)).
Qed.
Lemma compComp_vl (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (tau_ty : forall _ : fin, ty)
  (tau_vl : forall _ : fin, vl) (s : vl m_ty m_vl) :
  eq (subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s))
    (subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
       (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s).
Proof.
exact (compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl _ _
                (fun n => eq_refl) (fun n => eq_refl) s).
Qed.
Lemma compComp'_vl (sigma_ty : forall _ : fin, ty)
  (sigma_vl : forall _ : fin, vl) (tau_ty : forall _ : fin, ty)
  (tau_vl : forall _ : fin, vl) :
  eq (funcomp (subst_vl tau_ty tau_vl) (subst_vl sigma_ty sigma_vl))
    (subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
       (funcomp (subst_vl tau_ty tau_vl) sigma_vl)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_vl sigma_ty sigma_vl tau_ty tau_vl n)).
Qed.
tactics
