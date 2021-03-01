Require Import axioms fintype header_extensible.
Inductive tm (n_tm : nat) : Type :=
  | var_tm : fin n_tm -> tm n_tm
  | app : tm n_tm -> tm n_tm -> tm n_tm
  | lam : tm (S n_tm) -> tm n_tm
  | const : nat -> tm n_tm
  | Plus : tm n_tm -> tm n_tm -> tm n_tm.
Lemma congr_app {m_tm : nat} {s0 : tm m_tm} {s1 : tm m_tm} {t0 : tm m_tm}
  {t1 : tm m_tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_tm s0 s1 = app m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_tm x s1) H0))
                (ap (fun x => app m_tm t0 x) H1)).
Qed.
Lemma congr_lam {m_tm : nat} {s0 : tm (S m_tm)} {t0 : tm (S m_tm)}
  (H0 : s0 = t0) : lam m_tm s0 = lam m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam m_tm x) H0)).
Qed.
Lemma congr_const {m_tm : nat} {s0 : nat} {t0 : nat} (H0 : s0 = t0) :
  const m_tm s0 = const m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => const m_tm x) H0)).
Qed.
Lemma congr_Plus {m_tm : nat} {s0 : tm m_tm} {s1 : tm m_tm} {t0 : tm m_tm}
  {t1 : tm m_tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  Plus m_tm s0 s1 = Plus m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Plus m_tm x s1) H0))
                (ap (fun x => Plus m_tm t0 x) H1)).
Qed.
Definition upRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n) := up_ren xi.
Definition upRen_list_tm_tm (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n) := upRen_p p xi.
Fixpoint ren_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
(s : tm m_tm) : tm n_tm :=
  match s with
  | var_tm _ s0 => var_tm n_tm (xi_tm s0)
  | app _ s0 s1 => app n_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | lam _ s0 => lam n_tm (ren_tm (upRen_tm_tm xi_tm) s0)
  | const _ s0 => const n_tm ((fun x => x) s0)
  | Plus _ s0 s1 => Plus n_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  end.
Definition up_tm_tm {m : nat} {n_tm : nat} (sigma : fin m -> tm n_tm) :
  fin (S m) -> tm (S n_tm) :=
  scons (var_tm (S n_tm) var_zero) (funcomp (ren_tm shift) sigma).
Definition up_list_tm_tm (p : nat) {m : nat} {n_tm : nat}
  (sigma : fin m -> tm n_tm) : fin (plus p m) -> tm (plus p n_tm) :=
  scons_p p (funcomp (var_tm (plus p n_tm)) (zero_p p))
    (funcomp (ren_tm (shift_p p)) sigma).
Fixpoint subst_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
(s : tm m_tm) : tm n_tm :=
  match s with
  | var_tm _ s0 => sigma_tm s0
  | app _ s0 s1 => app n_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | lam _ s0 => lam n_tm (subst_tm (up_tm_tm sigma_tm) s0)
  | const _ s0 => const n_tm ((fun x => x) s0)
  | Plus _ s0 s1 => Plus n_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  end.
Definition upId_tm_tm {m_tm : nat} (sigma : fin m_tm -> tm m_tm)
  (Eq : forall x, sigma x = var_tm m_tm x) :
  forall x, up_tm_tm sigma x = var_tm (S m_tm) x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upId_list_tm_tm {p : nat} {m_tm : nat}
  (sigma : fin m_tm -> tm m_tm) (Eq : forall x, sigma x = var_tm m_tm x) :
  forall x, up_list_tm_tm p sigma x = var_tm (plus p m_tm) x :=
  fun n =>
  scons_p_eta (var_tm (plus p m_tm))
    (fun n => ap (ren_tm (shift_p p)) (Eq n)) (fun n => eq_refl).
Fixpoint idSubst_tm {m_tm : nat} (sigma_tm : fin m_tm -> tm m_tm)
(Eq_tm : forall x, sigma_tm x = var_tm m_tm x) (s : tm m_tm) :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  end.
Definition upExtRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x :=
  fun n =>
  match n with
  | Some fin_n => ap shift (Eq fin_n)
  | None => eq_refl
  end.
Definition upExtRen_list_tm_tm {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_tm p xi x = upRen_list_tm_tm p zeta x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n)).
Fixpoint extRen_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
(zeta_tm : fin m_tm -> fin n_tm) (Eq_tm : forall x, xi_tm x = zeta_tm x)
(s : tm m_tm) : ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm _ s0 => ap (var_tm n_tm) (Eq_tm s0)
  | app _ s0 s1 =>
      congr_app (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  end.
Definition upExt_tm_tm {m : nat} {n_tm : nat} (sigma : fin m -> tm n_tm)
  (tau : fin m -> tm n_tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition upExt_list_tm_tm {p : nat} {m : nat} {n_tm : nat}
  (sigma : fin m -> tm n_tm) (tau : fin m -> tm n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_tm p sigma x = up_list_tm_tm p tau x :=
  fun n =>
  scons_p_congr (fun n => eq_refl) (fun n => ap (ren_tm (shift_p p)) (Eq n)).
Fixpoint ext_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
(tau_tm : fin m_tm -> tm n_tm) (Eq_tm : forall x, sigma_tm x = tau_tm x)
(s : tm m_tm) : subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  end.
Definition up_ren_ren_tm_tm {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x :=
  up_ren_ren xi zeta rho Eq.
Definition up_ren_ren_list_tm_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_tm p zeta) (upRen_list_tm_tm p xi) x =
  upRen_list_tm_tm p rho x := up_ren_ren_p Eq.
Fixpoint compRenRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
(rho_tm : fin m_tm -> fin l_tm)
(Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x) (s : tm m_tm) :
ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm _ s0 => ap (var_tm l_tm) (Eq_tm s0)
  | app _ s0 s1 =>
      congr_app (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  end.
Definition up_ren_subst_tm_tm {k : nat} {l : nat} {m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_tm) (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition up_ren_subst_list_tm_tm {p : nat} {k : nat} {l : nat} {m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_tm) (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_tm_tm p tau) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p theta x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ _ n)
    (scons_p_congr (fun z => scons_p_head' _ _ z)
       (fun z =>
        eq_trans (scons_p_tail' _ _ (xi z)) (ap (ren_tm (shift_p p)) (Eq z)))).
Fixpoint compRenSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm m_tm) :
subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  end.
Definition up_subst_ren_tm_tm {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenRen_tm shift (upRen_tm_tm zeta_tm) (funcomp shift zeta_tm)
           (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_tm shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_ren_list_tm_tm {p : nat} {k : nat} {l_tm : nat}
  {m_tm : nat} (sigma : fin k -> tm l_tm) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_list_tm_tm p zeta_tm)) (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ _ n)
    (scons_p_congr (fun x => ap (var_tm (plus p m_tm)) (scons_p_head' _ _ x))
       (fun n =>
        eq_trans
          (compRenRen_tm (shift_p p) (upRen_list_tm_tm p zeta_tm)
             (funcomp (shift_p p) zeta_tm) (fun x => scons_p_tail' _ _ x)
             (sigma n))
          (eq_trans
             (eq_sym
                (compRenRen_tm zeta_tm (shift_p p)
                   (funcomp (shift_p p) zeta_tm) (fun x => eq_refl) (sigma n)))
             (ap (ren_tm (shift_p p)) (Eq n))))).
Fixpoint compSubstRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x)
(s : tm m_tm) : ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  end.
Definition up_subst_subst_tm_tm {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (tau_tm : fin l_tm -> tm m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compRenSubst_tm shift (up_tm_tm tau_tm)
           (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compSubstRen_tm tau_tm shift (funcomp (ren_tm shift) tau_tm)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (ren_tm shift) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_subst_list_tm_tm {p : nat} {k : nat} {l_tm : nat}
  {m_tm : nat} (sigma : fin k -> tm l_tm) (tau_tm : fin l_tm -> tm m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_tm_tm p tau_tm)) (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x :=
  fun n =>
  eq_trans (scons_p_comp' (funcomp (var_tm (plus p l_tm)) (zero_p p)) _ _ n)
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
             (ap (ren_tm (shift_p p)) (Eq n))))).
Fixpoint compSubstSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm m_tm) : subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s
:=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  end.
Definition rinstInst_up_tm_tm {m : nat} {n_tm : nat} (xi : fin m -> fin n_tm)
  (sigma : fin m -> tm n_tm)
  (Eq : forall x, funcomp (var_tm n_tm) xi x = sigma x) :
  forall x, funcomp (var_tm (S n_tm)) (upRen_tm_tm xi) x = up_tm_tm sigma x :=
  fun n =>
  match n with
  | Some fin_n => ap (ren_tm shift) (Eq fin_n)
  | None => eq_refl
  end.
Definition rinstInst_up_list_tm_tm {p : nat} {m : nat} {n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_tm)
  (Eq : forall x, funcomp (var_tm n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (plus p n_tm)) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p sigma x :=
  fun n =>
  eq_trans (scons_p_comp' _ _ (var_tm (plus p n_tm)) n)
    (scons_p_congr (fun z => eq_refl)
       (fun n => ap (ren_tm (shift_p p)) (Eq n))).
Fixpoint rinst_inst_tm {m_tm : nat} {n_tm : nat}
(xi_tm : fin m_tm -> fin n_tm) (sigma_tm : fin m_tm -> tm n_tm)
(Eq_tm : forall x, funcomp (var_tm n_tm) xi_tm x = sigma_tm x) (s : tm m_tm)
   : ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  | const _ s0 => congr_const ((fun x => eq_refl x) s0)
  | Plus _ s0 s1 =>
      congr_Plus (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  end.
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
Lemma renRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.
Lemma renRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (ren_tm xi_tm) = ren_tm (funcomp zeta_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_tm xi_tm zeta_tm n)).
Qed.
Lemma compRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.
Lemma compRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_tm sigma_tm zeta_tm n)).
Qed.
Lemma renComp_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) (s : tm m_tm)
  : subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.
Lemma renComp'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  funcomp (subst_tm tau_tm) (ren_tm xi_tm) = subst_tm (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_tm xi_tm tau_tm n)).
Qed.
Lemma compComp_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
  (s : tm m_tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.
Lemma compComp'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  funcomp (subst_tm tau_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_tm sigma_tm tau_tm n)).
Qed.
