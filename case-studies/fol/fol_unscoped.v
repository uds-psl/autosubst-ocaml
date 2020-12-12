Require Export unscoped.
Require Export header_extensible.
Inductive term : Type :=
  | var_term : forall _ : nat, term
  | Func : forall f : nat, forall _ : cod (fin f) (term), term.
Lemma congr_Func {f : nat} {s0 : cod (fin f) (term)}
  {t0 : cod (fin f) (term)} (H0 : eq s0 t0) : eq (Func f s0) (Func f t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Func f x) H0)).
Qed.
Fixpoint subst_term (sigma_term : forall _ : nat, term) (s : term) : term :=
  match s with
  | var_term s0 => sigma_term s0
  | Func f s0 => Func f (cod_map (subst_term sigma_term) s0)
  end.
Definition up_term_term (sigma : forall _ : nat, term) :
  forall _ : nat, term :=
  scons (var_term var_zero)
    (funcomp (subst_term (funcomp var_term shift)) sigma).
Definition upId_term_term (sigma : forall _ : nat, term)
  (Eq : forall x, eq (sigma x) (var_term x)) :
  forall x, eq (up_term_term sigma x) (var_term x) :=
  fun n =>
  match n with
  | S n' => ap (subst_term (funcomp var_term shift)) (Eq n')
  | O => eq_refl
  end.
Fixpoint idSubst_term (sigma_term : forall _ : nat, term)
(Eq_term : forall x, eq (sigma_term x) (var_term x)) (s : term) :
eq (subst_term sigma_term s) s :=
  match s with
  | var_term s0 => Eq_term s0
  | Func f s0 => congr_Func (cod_id (idSubst_term sigma_term Eq_term) s0)
  end.
Definition upExt_term_term (sigma : forall _ : nat, term)
  (tau : forall _ : nat, term) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_term_term sigma x) (up_term_term tau x) :=
  fun n =>
  match n with
  | S n' => ap (subst_term (funcomp var_term shift)) (Eq n')
  | O => eq_refl
  end.
Fixpoint ext_term (sigma_term : forall _ : nat, term)
(tau_term : forall _ : nat, term)
(Eq_term : forall x, eq (sigma_term x) (tau_term x)) (s : term) :
eq (subst_term sigma_term s) (subst_term tau_term s) :=
  match s with
  | var_term s0 => Eq_term s0
  | Func f s0 =>
      congr_Func (cod_ext (ext_term sigma_term tau_term Eq_term) s0)
  end.
Fixpoint compSubstSubst_term (sigma_term : forall _ : nat, term)
(tau_term : forall _ : nat, term) (theta_term : forall _ : nat, term)
(Eq_term : forall x,
           eq (funcomp (subst_term tau_term) sigma_term x) (theta_term x))
(s : term) :
eq (subst_term tau_term (subst_term sigma_term s)) (subst_term theta_term s)
:=
  match s with
  | var_term s0 => Eq_term s0
  | Func f s0 =>
      congr_Func
        (cod_comp
           (compSubstSubst_term sigma_term tau_term theta_term Eq_term) s0)
  end.
Definition up_subst_subst_term_term (sigma : forall _ : nat, term)
  (tau_term : forall _ : nat, term) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x)
    (up_term_term theta x) :=
  fun n =>
  match n with
  | S n' =>
      eq_trans
        (compSubstSubst_term (funcomp var_term shift) (up_term_term tau_term)
           (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
           (sigma n'))
        (eq_trans
           (eq_sym
              (compSubstSubst_term tau_term (funcomp var_term shift)
                 (funcomp (subst_term (funcomp var_term shift)) tau_term)
                 (fun x => eq_refl) (sigma n')))
           (ap (subst_term (funcomp var_term shift)) (Eq n')))
  | O => eq_refl
  end.
Lemma instId_term : eq (subst_term var_term) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_term var_term (fun n => eq_refl) (id x))).
Qed.
Lemma varL_term (sigma_term : forall _ : nat, term) :
  eq (funcomp (subst_term sigma_term) var_term) sigma_term.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Inductive form : Type :=
  | Fal : form
  | Pred : forall p : nat, forall _ : cod (fin p) (term), form
  | Impl : forall _ : form, forall _ : form, form
  | Conj : forall _ : form, forall _ : form, form
  | Disj : forall _ : form, forall _ : form, form
  | All : forall _ : form, form
  | Ex : forall _ : form, form.
Lemma congr_Fal : eq Fal Fal.
Proof.
exact (eq_refl).
Qed.
Lemma congr_Pred {p : nat} {s0 : cod (fin p) (term)}
  {t0 : cod (fin p) (term)} (H0 : eq s0 t0) : eq (Pred p s0) (Pred p t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Pred p x) H0)).
Qed.
Lemma congr_Impl {s0 : form} {s1 : form} {t0 : form} {t1 : form}
  (H0 : eq s0 t0) (H1 : eq s1 t1) : eq (Impl s0 s1) (Impl t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Impl x s1) H0))
                (ap (fun x => Impl t0 x) H1)).
Qed.
Lemma congr_Conj {s0 : form} {s1 : form} {t0 : form} {t1 : form}
  (H0 : eq s0 t0) (H1 : eq s1 t1) : eq (Conj s0 s1) (Conj t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Conj x s1) H0))
                (ap (fun x => Conj t0 x) H1)).
Qed.
Lemma congr_Disj {s0 : form} {s1 : form} {t0 : form} {t1 : form}
  (H0 : eq s0 t0) (H1 : eq s1 t1) : eq (Disj s0 s1) (Disj t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Disj x s1) H0))
                (ap (fun x => Disj t0 x) H1)).
Qed.
Lemma congr_All {s0 : form} {t0 : form} (H0 : eq s0 t0) :
  eq (All s0) (All t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => All x) H0)).
Qed.
Lemma congr_Ex {s0 : form} {t0 : form} (H0 : eq s0 t0) : eq (Ex s0) (Ex t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Ex x) H0)).
Qed.
Fixpoint subst_form (sigma_term : forall _ : nat, term) (s : form) : form :=
  match s with
  | Fal => Fal
  | Pred p s0 => Pred p (cod_map (subst_term sigma_term) s0)
  | Impl s0 s1 => Impl (subst_form sigma_term s0) (subst_form sigma_term s1)
  | Conj s0 s1 => Conj (subst_form sigma_term s0) (subst_form sigma_term s1)
  | Disj s0 s1 => Disj (subst_form sigma_term s0) (subst_form sigma_term s1)
  | All s0 => All (subst_form (up_term_term sigma_term) s0)
  | Ex s0 => Ex (subst_form (up_term_term sigma_term) s0)
  end.
Fixpoint idSubst_form (sigma_term : forall _ : nat, term)
(Eq_term : forall x, eq (sigma_term x) (var_term x)) (s : form) :
eq (subst_form sigma_term s) s :=
  match s with
  | Fal => congr_Fal
  | Pred p s0 => congr_Pred (cod_id (idSubst_term sigma_term Eq_term) s0)
  | Impl s0 s1 =>
      congr_Impl (idSubst_form sigma_term Eq_term s0)
        (idSubst_form sigma_term Eq_term s1)
  | Conj s0 s1 =>
      congr_Conj (idSubst_form sigma_term Eq_term s0)
        (idSubst_form sigma_term Eq_term s1)
  | Disj s0 s1 =>
      congr_Disj (idSubst_form sigma_term Eq_term s0)
        (idSubst_form sigma_term Eq_term s1)
  | All s0 =>
      congr_All
        (idSubst_form (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
  | Ex s0 =>
      congr_Ex
        (idSubst_form (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
  end.
Fixpoint ext_form (sigma_term : forall _ : nat, term)
(tau_term : forall _ : nat, term)
(Eq_term : forall x, eq (sigma_term x) (tau_term x)) (s : form) :
eq (subst_form sigma_term s) (subst_form tau_term s) :=
  match s with
  | Fal => congr_Fal
  | Pred p s0 =>
      congr_Pred (cod_ext (ext_term sigma_term tau_term Eq_term) s0)
  | Impl s0 s1 =>
      congr_Impl (ext_form sigma_term tau_term Eq_term s0)
        (ext_form sigma_term tau_term Eq_term s1)
  | Conj s0 s1 =>
      congr_Conj (ext_form sigma_term tau_term Eq_term s0)
        (ext_form sigma_term tau_term Eq_term s1)
  | Disj s0 s1 =>
      congr_Disj (ext_form sigma_term tau_term Eq_term s0)
        (ext_form sigma_term tau_term Eq_term s1)
  | All s0 =>
      congr_All
        (ext_form (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
  | Ex s0 =>
      congr_Ex
        (ext_form (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
  end.
Fixpoint compSubstSubst_form (sigma_term : forall _ : nat, term)
(tau_term : forall _ : nat, term) (theta_term : forall _ : nat, term)
(Eq_term : forall x,
           eq (funcomp (subst_term tau_term) sigma_term x) (theta_term x))
(s : form) :
eq (subst_form tau_term (subst_form sigma_term s)) (subst_form theta_term s)
:=
  match s with
  | Fal => congr_Fal
  | Pred p s0 =>
      congr_Pred
        (cod_comp
           (compSubstSubst_term sigma_term tau_term theta_term Eq_term) s0)
  | Impl s0 s1 =>
      congr_Impl
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s1)
  | Conj s0 s1 =>
      congr_Conj
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s1)
  | Disj s0 s1 =>
      congr_Disj
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s1)
  | All s0 =>
      congr_All
        (compSubstSubst_form (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
  | Ex s0 =>
      congr_Ex
        (compSubstSubst_form (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
  end.
Lemma instId_form : eq (subst_form var_term) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_form var_term (fun n => eq_refl) (id x))).
Qed.
