Require Import core unscoped.

Require Import core_axioms unscoped_axioms.
Require Import Setoid Morphisms Relation_Definitions.

Module renSubst.

Inductive tm : Type :=
  | var_tm : nat -> tm
  | app : tm -> tm -> tm
  | lam : tm -> tm.

Lemma congr_app {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : app s0 s1 = app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
         (ap (fun x => app t0 x) H1)).
Qed.

Lemma congr_lam {s0 : tm} {t0 : tm} (H0 : s0 = t0) : lam s0 = lam t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam x) H0)).
Qed.

Lemma upRen_tm_tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_tm (xi_tm : nat -> nat) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => var_tm (xi_tm s0)
  | app s0 s1 => app (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | lam s0 => lam (ren_tm (upRen_tm_tm xi_tm) s0)
  end.

Lemma up_tm_tm (sigma : nat -> tm) : nat -> tm.
Proof.
exact (scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm (sigma_tm : nat -> tm) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => sigma_tm s0
  | app s0 s1 => app (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | lam s0 => lam (subst_tm (up_tm_tm sigma_tm) s0)
  end.

Lemma upId_tm_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = var_tm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_tm (sigma_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | lam s0 =>
      congr_lam (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  end.

Lemma upExtRen_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm) {struct s} :
ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | app s0 s1 =>
      congr_app (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | lam s0 =>
      congr_lam
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  end.

Lemma upExt_tm_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | lam s0 =>
      congr_lam
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  end.

Lemma up_ren_ren_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(rho_tm : nat -> nat) (Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x)
(s : tm) {struct s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | app s0 s1 =>
      congr_app (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | lam s0 =>
      congr_lam
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  end.

Lemma up_ren_subst_tm_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm) {struct s} :
subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | lam s0 =>
      congr_lam
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_ren_tm_tm (sigma : nat -> tm) (zeta_tm : nat -> nat)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x) 
(s : tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | lam s0 =>
      congr_lam
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_subst_tm_tm (sigma : nat -> tm) (tau_tm : nat -> tm)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | lam s0 =>
      congr_lam
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_tm : nat -> nat) (sigma_tm : nat -> tm)
(Eq_tm : forall x, funcomp (var_tm) xi_tm x = sigma_tm x) (s : tm) {struct s}
   : ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | app s0 s1 =>
      congr_app (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | lam s0 =>
      congr_lam
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  end.

Lemma renRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm (xi_tm : nat -> nat) (s : tm) :
  ren_tm xi_tm s = subst_tm (funcomp (var_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_tm) s = s.
Proof.
exact (idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm (sigma_tm : nat -> tm) (x : nat) :
  subst_tm sigma_tm (var_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm (xi_tm : nat -> nat) (x : nat) :
  ren_tm xi_tm (var_tm x) = var_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

Instance Subst_tm : (Subst1 _ _ _) := @subst_tm.

Instance Up_tm_tm : (Up_tm _ _) := @up_tm_tm.

Instance Ren_tm : (Ren1 _ _ _) := @ren_tm.

Instance VarInstance_tm : (Var _ _) := @var_tm.

Notation "[ sigma_tm ]" := (subst_tm sigma_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__tm" := up_tm (only printing) : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing) : subst_scope.

Notation "⟨ xi_tm ⟩" := (ren_tm xi_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing) : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
  ( at level 5, format "x __tm", only printing) : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm") :
  subst_scope.

Instance subst_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

Instance ren_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm
                 | progress rewrite ?substSubst_tm
                 | progress setoid_rewrite renSubst_tm
                 | progress rewrite ?renSubst_tm
                 | progress setoid_rewrite substRen_tm
                 | progress rewrite ?substRen_tm
                 | progress setoid_rewrite renRen_tm
                 | progress rewrite ?renRen_tm
                 | progress setoid_rewrite varLRen'_tm
                 | progress rewrite ?varLRen'_tm
                 | progress setoid_rewrite varL'_tm
                 | progress rewrite ?varL'_tm
                 | progress setoid_rewrite rinstId'_tm
                 | progress rewrite ?rinstId'_tm
                 | progress setoid_rewrite instId'_tm
                 | progress rewrite ?instId'_tm
                 | progress unfold up_tm_tm, upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                 | progress fsimpl
                 | repeat unfold funcomp ]).

Ltac asimpl := repeat try unfold_funcomp;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try repeat erewrite ?rinstInst'_tm.

Ltac renamify := auto_unfold; try repeat erewrite <- ?rinstInst'_tm.

End renSubst.

Module fext.

Import
renSubst.

Lemma rinstInst_tm (xi_tm : nat -> nat) :
  ren_tm xi_tm = subst_tm (funcomp (var_tm) xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_tm xi_tm _ (fun n => eq_refl) x)).
Qed.

Lemma instId_tm : subst_tm (var_tm) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_tm (var_tm) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_tm : @ren_tm id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _)) instId_tm).
Qed.

Lemma varL_tm (sigma_tm : nat -> tm) :
  funcomp (subst_tm sigma_tm) (var_tm) = sigma_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_tm (xi_tm : nat -> nat) :
  funcomp (ren_tm xi_tm) (var_tm) = funcomp (var_tm) xi_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat) :
  funcomp (ren_tm zeta_tm) (ren_tm xi_tm) = ren_tm (funcomp zeta_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_tm xi_tm zeta_tm n)).
Qed.

Lemma substRen'_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) :
  funcomp (ren_tm zeta_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_tm sigma_tm zeta_tm n)).
Qed.

Lemma renSubst'_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm) :
  funcomp (subst_tm tau_tm) (ren_tm xi_tm) = subst_tm (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_tm xi_tm tau_tm n)).
Qed.

Lemma substSubst'_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm) :
  funcomp (subst_tm tau_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_tm sigma_tm tau_tm n)).
Qed.

Ltac asimpl_fext' := repeat (first
                      [ progress setoid_rewrite substSubst_tm
                      | progress setoid_rewrite renSubst_tm
                      | progress setoid_rewrite substRen_tm
                      | progress setoid_rewrite renRen_tm
                      | progress setoid_rewrite substSubst'_tm
                      | progress setoid_rewrite renSubst'_tm
                      | progress setoid_rewrite substRen'_tm
                      | progress setoid_rewrite renRen'_tm
                      | progress setoid_rewrite varLRen_tm
                      | progress setoid_rewrite varL_tm
                      | progress setoid_rewrite rinstId_tm
                      | progress setoid_rewrite instId_tm
                      | progress unfold up_tm_tm, upRen_tm_tm, up_ren
                      | progress cbn[subst_tm ren_tm]
                      | fsimpl_fext ]).

Ltac asimpl_fext := repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                       Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 
                       in *; asimpl_fext'; repeat try unfold_funcomp.

Tactic Notation "asimpl_fext" "in" hyp(J) := revert J; asimpl_fext; intros J.

Ltac substify_fext := auto_unfold; try repeat erewrite ?rinstInst_tm.

Ltac renamify_fext := auto_unfold; try repeat erewrite <- ?rinstInst_tm.

End fext.

Module interface.

Export renSubst.

Export fext.

End interface.

Export interface.

