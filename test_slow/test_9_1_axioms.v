Require Import core core_axioms fintype fintype_axioms.
Require Import test_9_1.

Lemma rinstInst_sort0 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort0 xi_sort2 = subst_sort0 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort0 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort1 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort1 xi_sort2 = subst_sort1 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort1 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort2 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort2 xi_sort2 = subst_sort2 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort2 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort3 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort3 xi_sort2 = subst_sort3 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort3 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort4 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort4 xi_sort2 = subst_sort4 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort4 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort5 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort5 xi_sort2 = subst_sort5 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort5 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort6 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort6 xi_sort2 = subst_sort6 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort6 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort7 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort7 xi_sort2 = subst_sort7 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort7 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort8 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort8 xi_sort2 = subst_sort8 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort8 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort0 {m_sort2 : nat} : subst_sort0 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort0 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort1 {m_sort2 : nat} : subst_sort1 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort1 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort2 {m_sort2 : nat} : subst_sort2 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort2 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort3 {m_sort2 : nat} : subst_sort3 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort3 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort4 {m_sort2 : nat} : subst_sort4 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort4 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort5 {m_sort2 : nat} : subst_sort5 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort5 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort6 {m_sort2 : nat} : subst_sort6 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort6 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort7 {m_sort2 : nat} : subst_sort7 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort7 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort8 {m_sort2 : nat} : subst_sort8 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort8 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma rinstId_sort0 {m_sort2 : nat} : @ren_sort0 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort0 (id _)) instId_sort0).

Qed.

Lemma rinstId_sort1 {m_sort2 : nat} : @ren_sort1 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort1 (id _)) instId_sort1).

Qed.

Lemma rinstId_sort2 {m_sort2 : nat} : @ren_sort2 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort2 (id _)) instId_sort2).

Qed.

Lemma rinstId_sort3 {m_sort2 : nat} : @ren_sort3 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort3 (id _)) instId_sort3).

Qed.

Lemma rinstId_sort4 {m_sort2 : nat} : @ren_sort4 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort4 (id _)) instId_sort4).

Qed.

Lemma rinstId_sort5 {m_sort2 : nat} : @ren_sort5 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort5 (id _)) instId_sort5).

Qed.

Lemma rinstId_sort6 {m_sort2 : nat} : @ren_sort6 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort6 (id _)) instId_sort6).

Qed.

Lemma rinstId_sort7 {m_sort2 : nat} : @ren_sort7 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort7 (id _)) instId_sort7).

Qed.

Lemma rinstId_sort8 {m_sort2 : nat} : @ren_sort8 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort8 (id _)) instId_sort8).

Qed.

Lemma varL_sort2 {m_sort2 : nat} {n_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 n_sort2) :
  funcomp (subst_sort2 sigma_sort2) (var_sort2 m_sort2) = sigma_sort2.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort2 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  funcomp (ren_sort2 xi_sort2) (var_sort2 m_sort2) =
  funcomp (var_sort2 n_sort2) xi_sort2.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort0 zeta_sort2) (ren_sort0 xi_sort2) =
  ren_sort0 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort0 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort1 zeta_sort2) (ren_sort1 xi_sort2) =
  ren_sort1 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort1 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort2 zeta_sort2) (ren_sort2 xi_sort2) =
  ren_sort2 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort2 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort3 zeta_sort2) (ren_sort3 xi_sort2) =
  ren_sort3 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort3 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort4 zeta_sort2) (ren_sort4 xi_sort2) =
  ren_sort4 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort4 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort5 zeta_sort2) (ren_sort5 xi_sort2) =
  ren_sort5 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort5 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort6 zeta_sort2) (ren_sort6 xi_sort2) =
  ren_sort6 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort6 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort7 zeta_sort2) (ren_sort7 xi_sort2) =
  ren_sort7 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort7 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort8 zeta_sort2) (ren_sort8 xi_sort2) =
  ren_sort8 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort8 xi_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort0 zeta_sort2) (subst_sort0 sigma_sort2) =
  subst_sort0 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort0 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort1 zeta_sort2) (subst_sort1 sigma_sort2) =
  subst_sort1 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort1 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort2 zeta_sort2) (subst_sort2 sigma_sort2) =
  subst_sort2 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort2 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort3 zeta_sort2) (subst_sort3 sigma_sort2) =
  subst_sort3 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort3 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort4 zeta_sort2) (subst_sort4 sigma_sort2) =
  subst_sort4 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort4 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort5 zeta_sort2) (subst_sort5 sigma_sort2) =
  subst_sort5 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort5 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort6 zeta_sort2) (subst_sort6 sigma_sort2) =
  subst_sort6 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort6 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort7 zeta_sort2) (subst_sort7 sigma_sort2) =
  subst_sort7 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort7 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort8 zeta_sort2) (subst_sort8 sigma_sort2) =
  subst_sort8 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort8 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma renComp'_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort0 tau_sort2) (ren_sort0 xi_sort2) =
  subst_sort0 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort0 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort1 tau_sort2) (ren_sort1 xi_sort2) =
  subst_sort1 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort1 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort2 tau_sort2) (ren_sort2 xi_sort2) =
  subst_sort2 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort2 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort3 tau_sort2) (ren_sort3 xi_sort2) =
  subst_sort3 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort3 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort4 tau_sort2) (ren_sort4 xi_sort2) =
  subst_sort4 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort4 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort5 tau_sort2) (ren_sort5 xi_sort2) =
  subst_sort5 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort5 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort6 tau_sort2) (ren_sort6 xi_sort2) =
  subst_sort6 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort6 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort7 tau_sort2) (ren_sort7 xi_sort2) =
  subst_sort7 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort7 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort8 tau_sort2) (ren_sort8 xi_sort2) =
  subst_sort8 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort8 xi_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort0 tau_sort2) (subst_sort0 sigma_sort2) =
  subst_sort0 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort0 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort1 tau_sort2) (subst_sort1 sigma_sort2) =
  subst_sort1 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort1 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort2 tau_sort2) (subst_sort2 sigma_sort2) =
  subst_sort2 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort2 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort3 tau_sort2) (subst_sort3 sigma_sort2) =
  subst_sort3 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort3 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort4 tau_sort2) (subst_sort4 sigma_sort2) =
  subst_sort4 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort4 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort5 tau_sort2) (subst_sort5 sigma_sort2) =
  subst_sort5 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort5 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort6 tau_sort2) (subst_sort6 sigma_sort2) =
  subst_sort6 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort6 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort7 tau_sort2) (subst_sort7 sigma_sort2) =
  subst_sort7 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort7 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort8 tau_sort2) (subst_sort8 sigma_sort2) =
  subst_sort8 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort8 sigma_sort2 tau_sort2 n)).

Qed.
