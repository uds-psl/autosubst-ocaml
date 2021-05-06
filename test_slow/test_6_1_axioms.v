Require Import core core_axioms fintype fintype_axioms.
Require Import test_6_1.

Lemma rinstInst_sort0 {m_sort0 : nat} {n_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin n_sort0) :
  ren_sort0 xi_sort0 = subst_sort0 (funcomp (var_sort0 n_sort0) xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort0 xi_sort0 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort1 {m_sort0 : nat} {n_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin n_sort0) :
  ren_sort1 xi_sort0 = subst_sort1 (funcomp (var_sort0 n_sort0) xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort1 xi_sort0 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort2 {m_sort0 : nat} {n_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin n_sort0) :
  ren_sort2 xi_sort0 = subst_sort2 (funcomp (var_sort0 n_sort0) xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort2 xi_sort0 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort3 {m_sort0 : nat} {n_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin n_sort0) :
  ren_sort3 xi_sort0 = subst_sort3 (funcomp (var_sort0 n_sort0) xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort3 xi_sort0 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort4 {m_sort0 : nat} {n_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin n_sort0) :
  ren_sort4 xi_sort0 = subst_sort4 (funcomp (var_sort0 n_sort0) xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort4 xi_sort0 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort5 {m_sort0 : nat} {n_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin n_sort0) :
  ren_sort5 xi_sort0 = subst_sort5 (funcomp (var_sort0 n_sort0) xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort5 xi_sort0 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort0 {m_sort0 : nat} : subst_sort0 (var_sort0 m_sort0) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort0 (var_sort0 m_sort0) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort1 {m_sort0 : nat} : subst_sort1 (var_sort0 m_sort0) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort1 (var_sort0 m_sort0) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort2 {m_sort0 : nat} : subst_sort2 (var_sort0 m_sort0) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort2 (var_sort0 m_sort0) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort3 {m_sort0 : nat} : subst_sort3 (var_sort0 m_sort0) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort3 (var_sort0 m_sort0) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort4 {m_sort0 : nat} : subst_sort4 (var_sort0 m_sort0) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort4 (var_sort0 m_sort0) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort5 {m_sort0 : nat} : subst_sort5 (var_sort0 m_sort0) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort5 (var_sort0 m_sort0) (fun n => eq_refl) (id x))).

Qed.

Lemma rinstId_sort0 {m_sort0 : nat} : @ren_sort0 m_sort0 m_sort0 id = id.

Proof.
exact (eq_trans (rinstInst_sort0 (id _)) instId_sort0).

Qed.

Lemma rinstId_sort1 {m_sort0 : nat} : @ren_sort1 m_sort0 m_sort0 id = id.

Proof.
exact (eq_trans (rinstInst_sort1 (id _)) instId_sort1).

Qed.

Lemma rinstId_sort2 {m_sort0 : nat} : @ren_sort2 m_sort0 m_sort0 id = id.

Proof.
exact (eq_trans (rinstInst_sort2 (id _)) instId_sort2).

Qed.

Lemma rinstId_sort3 {m_sort0 : nat} : @ren_sort3 m_sort0 m_sort0 id = id.

Proof.
exact (eq_trans (rinstInst_sort3 (id _)) instId_sort3).

Qed.

Lemma rinstId_sort4 {m_sort0 : nat} : @ren_sort4 m_sort0 m_sort0 id = id.

Proof.
exact (eq_trans (rinstInst_sort4 (id _)) instId_sort4).

Qed.

Lemma rinstId_sort5 {m_sort0 : nat} : @ren_sort5 m_sort0 m_sort0 id = id.

Proof.
exact (eq_trans (rinstInst_sort5 (id _)) instId_sort5).

Qed.

Lemma varL_sort0 {m_sort0 : nat} {n_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 n_sort0) :
  funcomp (subst_sort0 sigma_sort0) (var_sort0 m_sort0) = sigma_sort0.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort0 {m_sort0 : nat} {n_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin n_sort0) :
  funcomp (ren_sort0 xi_sort0) (var_sort0 m_sort0) =
  funcomp (var_sort0 n_sort0) xi_sort0.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort0 zeta_sort0) (ren_sort0 xi_sort0) =
  ren_sort0 (funcomp zeta_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort0 xi_sort0 zeta_sort0 n)).

Qed.

Lemma renRen'_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort1 zeta_sort0) (ren_sort1 xi_sort0) =
  ren_sort1 (funcomp zeta_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort1 xi_sort0 zeta_sort0 n)).

Qed.

Lemma renRen'_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort2 zeta_sort0) (ren_sort2 xi_sort0) =
  ren_sort2 (funcomp zeta_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort2 xi_sort0 zeta_sort0 n)).

Qed.

Lemma renRen'_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort3 zeta_sort0) (ren_sort3 xi_sort0) =
  ren_sort3 (funcomp zeta_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort3 xi_sort0 zeta_sort0 n)).

Qed.

Lemma renRen'_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort4 zeta_sort0) (ren_sort4 xi_sort0) =
  ren_sort4 (funcomp zeta_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort4 xi_sort0 zeta_sort0 n)).

Qed.

Lemma renRen'_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort5 zeta_sort0) (ren_sort5 xi_sort0) =
  ren_sort5 (funcomp zeta_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort5 xi_sort0 zeta_sort0 n)).

Qed.

Lemma compRen'_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort0 zeta_sort0) (subst_sort0 sigma_sort0) =
  subst_sort0 (funcomp (ren_sort0 zeta_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort0 sigma_sort0 zeta_sort0 n)).

Qed.

Lemma compRen'_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort1 zeta_sort0) (subst_sort1 sigma_sort0) =
  subst_sort1 (funcomp (ren_sort0 zeta_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort1 sigma_sort0 zeta_sort0 n)).

Qed.

Lemma compRen'_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort2 zeta_sort0) (subst_sort2 sigma_sort0) =
  subst_sort2 (funcomp (ren_sort0 zeta_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort2 sigma_sort0 zeta_sort0 n)).

Qed.

Lemma compRen'_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort3 zeta_sort0) (subst_sort3 sigma_sort0) =
  subst_sort3 (funcomp (ren_sort0 zeta_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort3 sigma_sort0 zeta_sort0 n)).

Qed.

Lemma compRen'_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort4 zeta_sort0) (subst_sort4 sigma_sort0) =
  subst_sort4 (funcomp (ren_sort0 zeta_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort4 sigma_sort0 zeta_sort0 n)).

Qed.

Lemma compRen'_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) :
  funcomp (ren_sort5 zeta_sort0) (subst_sort5 sigma_sort0) =
  subst_sort5 (funcomp (ren_sort0 zeta_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort5 sigma_sort0 zeta_sort0 n)).

Qed.

Lemma renComp'_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort0 tau_sort0) (ren_sort0 xi_sort0) =
  subst_sort0 (funcomp tau_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort0 xi_sort0 tau_sort0 n)).

Qed.

Lemma renComp'_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort1 tau_sort0) (ren_sort1 xi_sort0) =
  subst_sort1 (funcomp tau_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort1 xi_sort0 tau_sort0 n)).

Qed.

Lemma renComp'_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort2 tau_sort0) (ren_sort2 xi_sort0) =
  subst_sort2 (funcomp tau_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort2 xi_sort0 tau_sort0 n)).

Qed.

Lemma renComp'_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort3 tau_sort0) (ren_sort3 xi_sort0) =
  subst_sort3 (funcomp tau_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort3 xi_sort0 tau_sort0 n)).

Qed.

Lemma renComp'_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort4 tau_sort0) (ren_sort4 xi_sort0) =
  subst_sort4 (funcomp tau_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort4 xi_sort0 tau_sort0 n)).

Qed.

Lemma renComp'_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort5 tau_sort0) (ren_sort5 xi_sort0) =
  subst_sort5 (funcomp tau_sort0 xi_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort5 xi_sort0 tau_sort0 n)).

Qed.

Lemma compComp'_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort0 tau_sort0) (subst_sort0 sigma_sort0) =
  subst_sort0 (funcomp (subst_sort0 tau_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort0 sigma_sort0 tau_sort0 n)).

Qed.

Lemma compComp'_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort1 tau_sort0) (subst_sort1 sigma_sort0) =
  subst_sort1 (funcomp (subst_sort0 tau_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort1 sigma_sort0 tau_sort0 n)).

Qed.

Lemma compComp'_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort2 tau_sort0) (subst_sort2 sigma_sort0) =
  subst_sort2 (funcomp (subst_sort0 tau_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort2 sigma_sort0 tau_sort0 n)).

Qed.

Lemma compComp'_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort3 tau_sort0) (subst_sort3 sigma_sort0) =
  subst_sort3 (funcomp (subst_sort0 tau_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort3 sigma_sort0 tau_sort0 n)).

Qed.

Lemma compComp'_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort4 tau_sort0) (subst_sort4 sigma_sort0) =
  subst_sort4 (funcomp (subst_sort0 tau_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort4 sigma_sort0 tau_sort0 n)).

Qed.

Lemma compComp'_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) :
  funcomp (subst_sort5 tau_sort0) (subst_sort5 sigma_sort0) =
  subst_sort5 (funcomp (subst_sort0 tau_sort0) sigma_sort0).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort5 sigma_sort0 tau_sort0 n)).

Qed.
