Require Import axioms fintype header_extensible.
Inductive term (n_term : nat) : Type :=
  | var_term : forall _ : fin n_term, term n_term
  | Func : forall f : nat, forall _ : cod (fin f) (term n_term), term n_term.
Lemma congr_Func {f : nat} {m_term : nat} {s0 : cod (fin f) (term m_term)}
  {t0 : cod (fin f) (term m_term)} (H0 : eq s0 t0) :
  eq (Func m_term f s0) (Func m_term f t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Func m_term f x) H0)).
Qed.
Fixpoint subst_term {m_term : nat} {n_term : nat}
(sigma_term : forall _ : fin m_term, term n_term) (s : term m_term) :
term n_term :=
  match s with
  | var_term _ s0 => sigma_term s0
  | Func _ f s0 => Func n_term f (cod_map (subst_term sigma_term) s0)
  end.
Definition up_term_term {m : nat} {n_term : nat}
  (sigma : forall _ : fin m, term n_term) :
  forall _ : fin (S m), term (S n_term) :=
  scons (var_term (S n_term) var_zero)
    (funcomp (subst_term (funcomp (var_term _) shift)) sigma).
Definition up_list_term_term (p : nat) {m : nat} {n_term : nat}
  (sigma : forall _ : fin m, term n_term) :
  forall _ : fin (plus p m), term (plus p n_term) :=
  scons_p p (funcomp (var_term (plus p n_term)) (zero_p p))
    (funcomp (subst_term (funcomp (var_term _) (shift_p p))) sigma).
Definition upId_term_term {m_term : nat}
  (sigma : forall _ : fin m_term, term m_term)
  (Eq : forall x, eq (sigma x) (var_term m_term x)) :
  forall x, eq (up_term_term sigma x) (var_term (S m_term) x) :=
  fun n =>
  match n with
  | Some fin_n => ap (subst_term (funcomp (var_term _) shift)) (Eq fin_n)
  | None => eq_refl
  end.
Definition upId_list_term_term {p : nat} {m_term : nat}
  (sigma : forall _ : fin m_term, term m_term)
  (Eq : forall x, eq (sigma x) (var_term m_term x)) :
  forall x, eq (up_list_term_term p sigma x) (var_term (plus p m_term) x) :=
  fun n =>
  scons_p_eta (var_term (plus p m_term))
    (fun n => ap (subst_term (funcomp (var_term _) (shift_p p))) (Eq n))
    (fun n => eq_refl).
Fixpoint idSubst_term {m_term : nat}
(sigma_term : forall _ : fin m_term, term m_term)
(Eq_term : forall x, eq (sigma_term x) (var_term m_term x)) (s : term m_term)
   : eq (subst_term sigma_term s) s :=
  match s with
  | var_term _ s0 => Eq_term s0
  | Func _ f s0 => congr_Func (cod_id (idSubst_term sigma_term Eq_term) s0)
  end.
Definition upExt_term_term {m : nat} {n_term : nat}
  (sigma : forall _ : fin m, term n_term)
  (tau : forall _ : fin m, term n_term) (Eq : forall x, eq (sigma x) (tau x))
  : forall x, eq (up_term_term sigma x) (up_term_term tau x) :=
  fun n =>
  match n with
  | Some fin_n => ap (subst_term (funcomp (var_term _) shift)) (Eq fin_n)
  | None => eq_refl
  end.
Definition upExt_list_term_term {p : nat} {m : nat} {n_term : nat}
  (sigma : forall _ : fin m, term n_term)
  (tau : forall _ : fin m, term n_term) (Eq : forall x, eq (sigma x) (tau x))
  : forall x, eq (up_list_term_term p sigma x) (up_list_term_term p tau x) :=
  fun n =>
  scons_p_congr (fun n => eq_refl)
    (fun n => ap (subst_term (funcomp (var_term _) (shift_p p))) (Eq n)).
Fixpoint ext_term {m_term : nat} {n_term : nat}
(sigma_term : forall _ : fin m_term, term n_term)
(tau_term : forall _ : fin m_term, term n_term)
(Eq_term : forall x, eq (sigma_term x) (tau_term x)) (s : term m_term) :
eq (subst_term sigma_term s) (subst_term tau_term s) :=
  match s with
  | var_term _ s0 => Eq_term s0
  | Func _ f s0 =>
      congr_Func (cod_ext (ext_term sigma_term tau_term Eq_term) s0)
  end.
Fixpoint compSubstSubst_term {k_term : nat} {l_term : nat} {m_term : nat}
(sigma_term : forall _ : fin m_term, term k_term)
(tau_term : forall _ : fin k_term, term l_term)
(theta_term : forall _ : fin m_term, term l_term)
(Eq_term : forall x,
           eq (funcomp (subst_term tau_term) sigma_term x) (theta_term x))
(s : term m_term) :
eq (subst_term tau_term (subst_term sigma_term s)) (subst_term theta_term s)
:=
  match s with
  | var_term _ s0 => Eq_term s0
  | Func _ f s0 =>
      congr_Func
        (cod_comp
           (compSubstSubst_term sigma_term tau_term theta_term Eq_term) s0)
  end.
Definition up_subst_subst_term_term {k : nat} {l_term : nat} {m_term : nat}
  (sigma : forall _ : fin k, term l_term)
  (tau_term : forall _ : fin l_term, term m_term)
  (theta : forall _ : fin k, term m_term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x)
    (up_term_term theta x) :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compSubstSubst_term (funcomp (var_term _) shift)
           (up_term_term tau_term) (funcomp (up_term_term tau_term) shift)
           (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compSubstSubst_term tau_term (funcomp (var_term _) shift)
                 (funcomp (subst_term (funcomp (var_term _) shift)) tau_term)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (subst_term (funcomp (var_term _) shift)) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_subst_list_term_term {p : nat} {k : nat} {l_term : nat}
  {m_term : nat} (sigma : forall _ : fin k, term l_term)
  (tau_term : forall _ : fin l_term, term m_term)
  (theta : forall _ : fin k, term m_term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (subst_term (up_list_term_term p tau_term))
       (up_list_term_term p sigma) x) (up_list_term_term p theta x) :=
  fun n =>
  eq_trans
    (scons_p_comp' (funcomp (var_term (plus p l_term)) (zero_p p)) _ _ n)
    (scons_p_congr
       (fun x =>
        scons_p_head' _
          (fun z => subst_term (funcomp (var_term _) (shift_p p)) _) x)
       (fun n =>
        eq_trans
          (compSubstSubst_term (funcomp (var_term _) (shift_p p))
             (up_list_term_term p tau_term)
             (funcomp (up_list_term_term p tau_term) (shift_p p))
             (fun x => eq_refl) (sigma n))
          (eq_trans
             (eq_sym
                (compSubstSubst_term tau_term
                   (funcomp (var_term _) (shift_p p)) _
                   (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
             (ap (subst_term (funcomp (var_term _) (shift_p p))) (Eq n))))).
Lemma instId_term {m_term : nat} : eq (subst_term (var_term m_term)) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_term (var_term m_term) (fun n => eq_refl) (id x))).
Qed.
Lemma varL_term {m_term : nat} {n_term : nat}
  (sigma_term : forall _ : fin m_term, term n_term) :
  eq (funcomp (subst_term sigma_term) (var_term m_term)) sigma_term.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Inductive form (n_term : nat) : Type :=
  | Fal : form n_term
  | Pred : forall p : nat, forall _ : cod (fin p) (term n_term), form n_term
  | Impl : forall _ : form n_term, forall _ : form n_term, form n_term
  | Conj : forall _ : form n_term, forall _ : form n_term, form n_term
  | Disj : forall _ : form n_term, forall _ : form n_term, form n_term
  | All : forall _ : form (S n_term), form n_term
  | Ex : forall _ : form (S n_term), form n_term.
Lemma congr_Fal {m_term : nat} : eq (Fal m_term) (Fal m_term).
Proof.
exact (eq_refl).
Qed.
Lemma congr_Pred {p : nat} {m_term : nat} {s0 : cod (fin p) (term m_term)}
  {t0 : cod (fin p) (term m_term)} (H0 : eq s0 t0) :
  eq (Pred m_term p s0) (Pred m_term p t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Pred m_term p x) H0)).
Qed.
Lemma congr_Impl {m_term : nat} {s0 : form m_term} {s1 : form m_term}
  {t0 : form m_term} {t1 : form m_term} (H0 : eq s0 t0) (H1 : eq s1 t1) :
  eq (Impl m_term s0 s1) (Impl m_term t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Impl m_term x s1) H0))
                (ap (fun x => Impl m_term t0 x) H1)).
Qed.
Lemma congr_Conj {m_term : nat} {s0 : form m_term} {s1 : form m_term}
  {t0 : form m_term} {t1 : form m_term} (H0 : eq s0 t0) (H1 : eq s1 t1) :
  eq (Conj m_term s0 s1) (Conj m_term t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Conj m_term x s1) H0))
                (ap (fun x => Conj m_term t0 x) H1)).
Qed.
Lemma congr_Disj {m_term : nat} {s0 : form m_term} {s1 : form m_term}
  {t0 : form m_term} {t1 : form m_term} (H0 : eq s0 t0) (H1 : eq s1 t1) :
  eq (Disj m_term s0 s1) (Disj m_term t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Disj m_term x s1) H0))
                (ap (fun x => Disj m_term t0 x) H1)).
Qed.
Lemma congr_All {m_term : nat} {s0 : form (S m_term)} {t0 : form (S m_term)}
  (H0 : eq s0 t0) : eq (All m_term s0) (All m_term t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => All m_term x) H0)).
Qed.
Lemma congr_Ex {m_term : nat} {s0 : form (S m_term)} {t0 : form (S m_term)}
  (H0 : eq s0 t0) : eq (Ex m_term s0) (Ex m_term t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Ex m_term x) H0)).
Qed.
Fixpoint subst_form {m_term : nat} {n_term : nat}
(sigma_term : forall _ : fin m_term, term n_term) (s : form m_term) :
form n_term :=
  match s with
  | Fal _ => Fal n_term
  | Pred _ p s0 => Pred n_term p (cod_map (subst_term sigma_term) s0)
  | Impl _ s0 s1 =>
      Impl n_term (subst_form sigma_term s0) (subst_form sigma_term s1)
  | Conj _ s0 s1 =>
      Conj n_term (subst_form sigma_term s0) (subst_form sigma_term s1)
  | Disj _ s0 s1 =>
      Disj n_term (subst_form sigma_term s0) (subst_form sigma_term s1)
  | All _ s0 => All n_term (subst_form (up_term_term sigma_term) s0)
  | Ex _ s0 => Ex n_term (subst_form (up_term_term sigma_term) s0)
  end.
Fixpoint idSubst_form {m_term : nat}
(sigma_term : forall _ : fin m_term, term m_term)
(Eq_term : forall x, eq (sigma_term x) (var_term m_term x)) (s : form m_term)
   : eq (subst_form sigma_term s) s :=
  match s with
  | Fal _ => congr_Fal
  | Pred _ p s0 => congr_Pred (cod_id (idSubst_term sigma_term Eq_term) s0)
  | Impl _ s0 s1 =>
      congr_Impl (idSubst_form sigma_term Eq_term s0)
        (idSubst_form sigma_term Eq_term s1)
  | Conj _ s0 s1 =>
      congr_Conj (idSubst_form sigma_term Eq_term s0)
        (idSubst_form sigma_term Eq_term s1)
  | Disj _ s0 s1 =>
      congr_Disj (idSubst_form sigma_term Eq_term s0)
        (idSubst_form sigma_term Eq_term s1)
  | All _ s0 =>
      congr_All
        (idSubst_form (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
  | Ex _ s0 =>
      congr_Ex
        (idSubst_form (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
  end.
Fixpoint ext_form {m_term : nat} {n_term : nat}
(sigma_term : forall _ : fin m_term, term n_term)
(tau_term : forall _ : fin m_term, term n_term)
(Eq_term : forall x, eq (sigma_term x) (tau_term x)) (s : form m_term) :
eq (subst_form sigma_term s) (subst_form tau_term s) :=
  match s with
  | Fal _ => congr_Fal
  | Pred _ p s0 =>
      congr_Pred (cod_ext (ext_term sigma_term tau_term Eq_term) s0)
  | Impl _ s0 s1 =>
      congr_Impl (ext_form sigma_term tau_term Eq_term s0)
        (ext_form sigma_term tau_term Eq_term s1)
  | Conj _ s0 s1 =>
      congr_Conj (ext_form sigma_term tau_term Eq_term s0)
        (ext_form sigma_term tau_term Eq_term s1)
  | Disj _ s0 s1 =>
      congr_Disj (ext_form sigma_term tau_term Eq_term s0)
        (ext_form sigma_term tau_term Eq_term s1)
  | All _ s0 =>
      congr_All
        (ext_form (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
  | Ex _ s0 =>
      congr_Ex
        (ext_form (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
  end.
Fixpoint compSubstSubst_form {k_term : nat} {l_term : nat} {m_term : nat}
(sigma_term : forall _ : fin m_term, term k_term)
(tau_term : forall _ : fin k_term, term l_term)
(theta_term : forall _ : fin m_term, term l_term)
(Eq_term : forall x,
           eq (funcomp (subst_term tau_term) sigma_term x) (theta_term x))
(s : form m_term) :
eq (subst_form tau_term (subst_form sigma_term s)) (subst_form theta_term s)
:=
  match s with
  | Fal _ => congr_Fal
  | Pred _ p s0 =>
      congr_Pred
        (cod_comp
           (compSubstSubst_term sigma_term tau_term theta_term Eq_term) s0)
  | Impl _ s0 s1 =>
      congr_Impl
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s1)
  | Conj _ s0 s1 =>
      congr_Conj
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s1)
  | Disj _ s0 s1 =>
      congr_Disj
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s1)
  | All _ s0 =>
      congr_All
        (compSubstSubst_form (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
  | Ex _ s0 =>
      congr_Ex
        (compSubstSubst_form (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
  end.
Lemma instId_form {m_term : nat} : eq (subst_form (var_term m_term)) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_form (var_term m_term) (fun n => eq_refl) (id x))).
Qed.
