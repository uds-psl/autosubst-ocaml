Require Import core core_axioms unscoped unscoped_axioms.
Require Import sysf.

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

Lemma renRen'_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat) :
  funcomp (ren_ty zeta_ty) (ren_ty xi_ty) = ren_ty (funcomp zeta_ty xi_ty).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_ty xi_ty zeta_ty n)).

Qed.

Lemma compRen'_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) :
  funcomp (ren_ty zeta_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_ty sigma_ty zeta_ty n)).

Qed.

Lemma renComp'_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty) :
  funcomp (subst_ty tau_ty) (ren_ty xi_ty) = subst_ty (funcomp tau_ty xi_ty).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_ty xi_ty tau_ty n)).

Qed.

Lemma compComp'_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty) :
  funcomp (subst_ty tau_ty) (subst_ty sigma_ty) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_ty sigma_ty tau_ty n)).

Qed.

Lemma rinstInst_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat) :
  ren_tm xi_ty xi_tm = subst_tm (funcomp var_ty xi_ty) (funcomp var_tm xi_tm).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_tm xi_ty xi_tm _ _ (fun n => eq_refl)
                   (fun n => eq_refl) x)).

Qed.

Lemma instId_tm : subst_tm var_ty var_tm = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_tm var_ty var_tm (fun n => eq_refl)
                   (fun n => eq_refl) (id x))).

Qed.

Lemma rinstId_tm : @ren_tm id id = id.

Proof.
exact (eq_trans (rinstInst_tm (id _) (id _)) instId_tm).

Qed.

Lemma varL_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm) :
  funcomp (subst_tm sigma_ty sigma_tm) var_tm = sigma_tm.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat) :
  funcomp (ren_tm xi_ty xi_tm) var_tm = funcomp var_tm xi_tm.

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

Lemma compRen'_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (zeta_ty : nat -> nat) (zeta_tm : nat -> nat) :
  funcomp (ren_tm zeta_ty zeta_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_tm sigma_ty sigma_tm zeta_ty zeta_tm n)).

Qed.

Lemma renComp'_tm (xi_ty : nat -> nat) (xi_tm : nat -> nat)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) :
  funcomp (subst_tm tau_ty tau_tm) (ren_tm xi_ty xi_tm) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_tm xi_ty xi_tm tau_ty tau_tm n)).

Qed.

Lemma compComp'_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm)
  (tau_ty : nat -> ty) (tau_tm : nat -> tm) :
  funcomp (subst_tm tau_ty tau_tm) (subst_tm sigma_ty sigma_tm) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_tm tau_ty tau_tm) sigma_tm).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_tm sigma_ty sigma_tm tau_ty tau_tm n)).

Qed.
