Require Import core core_axioms unscoped unscoped_axioms.
Require Import test_6_3_unscoped.

Lemma rinstInst_sort0 (xi_sort5 : nat -> nat) :
  ren_sort0 xi_sort5 = subst_sort0 (funcomp var_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort0 xi_sort5 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort1 (xi_sort5 : nat -> nat) :
  ren_sort1 xi_sort5 = subst_sort1 (funcomp var_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort1 xi_sort5 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort2 (xi_sort5 : nat -> nat) :
  ren_sort2 xi_sort5 = subst_sort2 (funcomp var_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort2 xi_sort5 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort3 (xi_sort5 : nat -> nat) :
  ren_sort3 xi_sort5 = subst_sort3 (funcomp var_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort3 xi_sort5 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort4 (xi_sort5 : nat -> nat) :
  ren_sort4 xi_sort5 = subst_sort4 (funcomp var_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort4 xi_sort5 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort5 (xi_sort5 : nat -> nat) :
  ren_sort5 xi_sort5 = subst_sort5 (funcomp var_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort5 xi_sort5 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort0 : subst_sort0 var_sort5 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort0 var_sort5 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort1 : subst_sort1 var_sort5 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort1 var_sort5 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort2 : subst_sort2 var_sort5 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort2 var_sort5 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort3 : subst_sort3 var_sort5 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort3 var_sort5 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort4 : subst_sort4 var_sort5 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort4 var_sort5 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort5 : subst_sort5 var_sort5 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort5 var_sort5 (fun n => eq_refl) (id x))).

Qed.

Lemma rinstId_sort0 : @ren_sort0 id = id.

Proof.
exact (eq_trans (rinstInst_sort0 (id _)) instId_sort0).

Qed.

Lemma rinstId_sort1 : @ren_sort1 id = id.

Proof.
exact (eq_trans (rinstInst_sort1 (id _)) instId_sort1).

Qed.

Lemma rinstId_sort2 : @ren_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort2 (id _)) instId_sort2).

Qed.

Lemma rinstId_sort3 : @ren_sort3 id = id.

Proof.
exact (eq_trans (rinstInst_sort3 (id _)) instId_sort3).

Qed.

Lemma rinstId_sort4 : @ren_sort4 id = id.

Proof.
exact (eq_trans (rinstInst_sort4 (id _)) instId_sort4).

Qed.

Lemma rinstId_sort5 : @ren_sort5 id = id.

Proof.
exact (eq_trans (rinstInst_sort5 (id _)) instId_sort5).

Qed.

Lemma varL_sort5 (sigma_sort5 : nat -> sort5) :
  funcomp (subst_sort5 sigma_sort5) var_sort5 = sigma_sort5.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort5 (xi_sort5 : nat -> nat) :
  funcomp (ren_sort5 xi_sort5) var_sort5 = funcomp var_sort5 xi_sort5.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort0 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort0 zeta_sort5) (ren_sort0 xi_sort5) =
  ren_sort0 (funcomp zeta_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort0 xi_sort5 zeta_sort5 n)).

Qed.

Lemma renRen'_sort1 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort1 zeta_sort5) (ren_sort1 xi_sort5) =
  ren_sort1 (funcomp zeta_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort1 xi_sort5 zeta_sort5 n)).

Qed.

Lemma renRen'_sort2 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort2 zeta_sort5) (ren_sort2 xi_sort5) =
  ren_sort2 (funcomp zeta_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort2 xi_sort5 zeta_sort5 n)).

Qed.

Lemma renRen'_sort3 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort3 zeta_sort5) (ren_sort3 xi_sort5) =
  ren_sort3 (funcomp zeta_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort3 xi_sort5 zeta_sort5 n)).

Qed.

Lemma renRen'_sort4 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort4 zeta_sort5) (ren_sort4 xi_sort5) =
  ren_sort4 (funcomp zeta_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort4 xi_sort5 zeta_sort5 n)).

Qed.

Lemma renRen'_sort5 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort5 zeta_sort5) (ren_sort5 xi_sort5) =
  ren_sort5 (funcomp zeta_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort5 xi_sort5 zeta_sort5 n)).

Qed.

Lemma compRen'_sort0 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort0 zeta_sort5) (subst_sort0 sigma_sort5) =
  subst_sort0 (funcomp (ren_sort5 zeta_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort0 sigma_sort5 zeta_sort5 n)).

Qed.

Lemma compRen'_sort1 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort1 zeta_sort5) (subst_sort1 sigma_sort5) =
  subst_sort1 (funcomp (ren_sort5 zeta_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort1 sigma_sort5 zeta_sort5 n)).

Qed.

Lemma compRen'_sort2 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort2 zeta_sort5) (subst_sort2 sigma_sort5) =
  subst_sort2 (funcomp (ren_sort5 zeta_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort2 sigma_sort5 zeta_sort5 n)).

Qed.

Lemma compRen'_sort3 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort3 zeta_sort5) (subst_sort3 sigma_sort5) =
  subst_sort3 (funcomp (ren_sort5 zeta_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort3 sigma_sort5 zeta_sort5 n)).

Qed.

Lemma compRen'_sort4 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort4 zeta_sort5) (subst_sort4 sigma_sort5) =
  subst_sort4 (funcomp (ren_sort5 zeta_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort4 sigma_sort5 zeta_sort5 n)).

Qed.

Lemma compRen'_sort5 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat) :
  funcomp (ren_sort5 zeta_sort5) (subst_sort5 sigma_sort5) =
  subst_sort5 (funcomp (ren_sort5 zeta_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort5 sigma_sort5 zeta_sort5 n)).

Qed.

Lemma renComp'_sort0 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5) :
  funcomp (subst_sort0 tau_sort5) (ren_sort0 xi_sort5) =
  subst_sort0 (funcomp tau_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort0 xi_sort5 tau_sort5 n)).

Qed.

Lemma renComp'_sort1 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5) :
  funcomp (subst_sort1 tau_sort5) (ren_sort1 xi_sort5) =
  subst_sort1 (funcomp tau_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort1 xi_sort5 tau_sort5 n)).

Qed.

Lemma renComp'_sort2 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5) :
  funcomp (subst_sort2 tau_sort5) (ren_sort2 xi_sort5) =
  subst_sort2 (funcomp tau_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort2 xi_sort5 tau_sort5 n)).

Qed.

Lemma renComp'_sort3 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5) :
  funcomp (subst_sort3 tau_sort5) (ren_sort3 xi_sort5) =
  subst_sort3 (funcomp tau_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort3 xi_sort5 tau_sort5 n)).

Qed.

Lemma renComp'_sort4 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5) :
  funcomp (subst_sort4 tau_sort5) (ren_sort4 xi_sort5) =
  subst_sort4 (funcomp tau_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort4 xi_sort5 tau_sort5 n)).

Qed.

Lemma renComp'_sort5 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5) :
  funcomp (subst_sort5 tau_sort5) (ren_sort5 xi_sort5) =
  subst_sort5 (funcomp tau_sort5 xi_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort5 xi_sort5 tau_sort5 n)).

Qed.

Lemma compComp'_sort0 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  :
  funcomp (subst_sort0 tau_sort5) (subst_sort0 sigma_sort5) =
  subst_sort0 (funcomp (subst_sort5 tau_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort0 sigma_sort5 tau_sort5 n)).

Qed.

Lemma compComp'_sort1 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  :
  funcomp (subst_sort1 tau_sort5) (subst_sort1 sigma_sort5) =
  subst_sort1 (funcomp (subst_sort5 tau_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort1 sigma_sort5 tau_sort5 n)).

Qed.

Lemma compComp'_sort2 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  :
  funcomp (subst_sort2 tau_sort5) (subst_sort2 sigma_sort5) =
  subst_sort2 (funcomp (subst_sort5 tau_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort2 sigma_sort5 tau_sort5 n)).

Qed.

Lemma compComp'_sort3 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  :
  funcomp (subst_sort3 tau_sort5) (subst_sort3 sigma_sort5) =
  subst_sort3 (funcomp (subst_sort5 tau_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort3 sigma_sort5 tau_sort5 n)).

Qed.

Lemma compComp'_sort4 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  :
  funcomp (subst_sort4 tau_sort5) (subst_sort4 sigma_sort5) =
  subst_sort4 (funcomp (subst_sort5 tau_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort4 sigma_sort5 tau_sort5 n)).

Qed.

Lemma compComp'_sort5 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  :
  funcomp (subst_sort5 tau_sort5) (subst_sort5 sigma_sort5) =
  subst_sort5 (funcomp (subst_sort5 tau_sort5) sigma_sort5).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort5 sigma_sort5 tau_sort5 n)).

Qed.

Lemma rinstInst_sort6 (xi_sort11 : nat -> nat) :
  ren_sort6 xi_sort11 = subst_sort6 (funcomp var_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort6 xi_sort11 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort7 (xi_sort11 : nat -> nat) :
  ren_sort7 xi_sort11 = subst_sort7 (funcomp var_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort7 xi_sort11 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort8 (xi_sort11 : nat -> nat) :
  ren_sort8 xi_sort11 = subst_sort8 (funcomp var_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort8 xi_sort11 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort9 (xi_sort11 : nat -> nat) :
  ren_sort9 xi_sort11 = subst_sort9 (funcomp var_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort9 xi_sort11 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort10 (xi_sort11 : nat -> nat) :
  ren_sort10 xi_sort11 = subst_sort10 (funcomp var_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort10 xi_sort11 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort11 (xi_sort11 : nat -> nat) :
  ren_sort11 xi_sort11 = subst_sort11 (funcomp var_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort11 xi_sort11 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort6 : subst_sort6 var_sort11 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort6 var_sort11 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort7 : subst_sort7 var_sort11 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort7 var_sort11 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort8 : subst_sort8 var_sort11 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort8 var_sort11 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort9 : subst_sort9 var_sort11 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort9 var_sort11 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort10 : subst_sort10 var_sort11 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort10 var_sort11 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort11 : subst_sort11 var_sort11 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort11 var_sort11 (fun n => eq_refl) (id x))).

Qed.

Lemma rinstId_sort6 : @ren_sort6 id = id.

Proof.
exact (eq_trans (rinstInst_sort6 (id _)) instId_sort6).

Qed.

Lemma rinstId_sort7 : @ren_sort7 id = id.

Proof.
exact (eq_trans (rinstInst_sort7 (id _)) instId_sort7).

Qed.

Lemma rinstId_sort8 : @ren_sort8 id = id.

Proof.
exact (eq_trans (rinstInst_sort8 (id _)) instId_sort8).

Qed.

Lemma rinstId_sort9 : @ren_sort9 id = id.

Proof.
exact (eq_trans (rinstInst_sort9 (id _)) instId_sort9).

Qed.

Lemma rinstId_sort10 : @ren_sort10 id = id.

Proof.
exact (eq_trans (rinstInst_sort10 (id _)) instId_sort10).

Qed.

Lemma rinstId_sort11 : @ren_sort11 id = id.

Proof.
exact (eq_trans (rinstInst_sort11 (id _)) instId_sort11).

Qed.

Lemma varL_sort11 (sigma_sort11 : nat -> sort11) :
  funcomp (subst_sort11 sigma_sort11) var_sort11 = sigma_sort11.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort11 (xi_sort11 : nat -> nat) :
  funcomp (ren_sort11 xi_sort11) var_sort11 = funcomp var_sort11 xi_sort11.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort6 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort6 zeta_sort11) (ren_sort6 xi_sort11) =
  ren_sort6 (funcomp zeta_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort6 xi_sort11 zeta_sort11 n)).

Qed.

Lemma renRen'_sort7 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort7 zeta_sort11) (ren_sort7 xi_sort11) =
  ren_sort7 (funcomp zeta_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort7 xi_sort11 zeta_sort11 n)).

Qed.

Lemma renRen'_sort8 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort8 zeta_sort11) (ren_sort8 xi_sort11) =
  ren_sort8 (funcomp zeta_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort8 xi_sort11 zeta_sort11 n)).

Qed.

Lemma renRen'_sort9 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort9 zeta_sort11) (ren_sort9 xi_sort11) =
  ren_sort9 (funcomp zeta_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort9 xi_sort11 zeta_sort11 n)).

Qed.

Lemma renRen'_sort10 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort10 zeta_sort11) (ren_sort10 xi_sort11) =
  ren_sort10 (funcomp zeta_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort10 xi_sort11 zeta_sort11 n)).

Qed.

Lemma renRen'_sort11 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort11 zeta_sort11) (ren_sort11 xi_sort11) =
  ren_sort11 (funcomp zeta_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort11 xi_sort11 zeta_sort11 n)).

Qed.

Lemma compRen'_sort6 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort6 zeta_sort11) (subst_sort6 sigma_sort11) =
  subst_sort6 (funcomp (ren_sort11 zeta_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort6 sigma_sort11 zeta_sort11 n)).

Qed.

Lemma compRen'_sort7 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort7 zeta_sort11) (subst_sort7 sigma_sort11) =
  subst_sort7 (funcomp (ren_sort11 zeta_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort7 sigma_sort11 zeta_sort11 n)).

Qed.

Lemma compRen'_sort8 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort8 zeta_sort11) (subst_sort8 sigma_sort11) =
  subst_sort8 (funcomp (ren_sort11 zeta_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort8 sigma_sort11 zeta_sort11 n)).

Qed.

Lemma compRen'_sort9 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort9 zeta_sort11) (subst_sort9 sigma_sort11) =
  subst_sort9 (funcomp (ren_sort11 zeta_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort9 sigma_sort11 zeta_sort11 n)).

Qed.

Lemma compRen'_sort10 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort10 zeta_sort11) (subst_sort10 sigma_sort11) =
  subst_sort10 (funcomp (ren_sort11 zeta_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort10 sigma_sort11 zeta_sort11 n)).

Qed.

Lemma compRen'_sort11 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) :
  funcomp (ren_sort11 zeta_sort11) (subst_sort11 sigma_sort11) =
  subst_sort11 (funcomp (ren_sort11 zeta_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort11 sigma_sort11 zeta_sort11 n)).

Qed.

Lemma renComp'_sort6 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort6 tau_sort11) (ren_sort6 xi_sort11) =
  subst_sort6 (funcomp tau_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort6 xi_sort11 tau_sort11 n)).

Qed.

Lemma renComp'_sort7 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort7 tau_sort11) (ren_sort7 xi_sort11) =
  subst_sort7 (funcomp tau_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort7 xi_sort11 tau_sort11 n)).

Qed.

Lemma renComp'_sort8 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort8 tau_sort11) (ren_sort8 xi_sort11) =
  subst_sort8 (funcomp tau_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort8 xi_sort11 tau_sort11 n)).

Qed.

Lemma renComp'_sort9 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort9 tau_sort11) (ren_sort9 xi_sort11) =
  subst_sort9 (funcomp tau_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort9 xi_sort11 tau_sort11 n)).

Qed.

Lemma renComp'_sort10 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort10 tau_sort11) (ren_sort10 xi_sort11) =
  subst_sort10 (funcomp tau_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort10 xi_sort11 tau_sort11 n)).

Qed.

Lemma renComp'_sort11 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort11 tau_sort11) (ren_sort11 xi_sort11) =
  subst_sort11 (funcomp tau_sort11 xi_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort11 xi_sort11 tau_sort11 n)).

Qed.

Lemma compComp'_sort6 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort6 tau_sort11) (subst_sort6 sigma_sort11) =
  subst_sort6 (funcomp (subst_sort11 tau_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort6 sigma_sort11 tau_sort11 n)).

Qed.

Lemma compComp'_sort7 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort7 tau_sort11) (subst_sort7 sigma_sort11) =
  subst_sort7 (funcomp (subst_sort11 tau_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort7 sigma_sort11 tau_sort11 n)).

Qed.

Lemma compComp'_sort8 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort8 tau_sort11) (subst_sort8 sigma_sort11) =
  subst_sort8 (funcomp (subst_sort11 tau_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort8 sigma_sort11 tau_sort11 n)).

Qed.

Lemma compComp'_sort9 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort9 tau_sort11) (subst_sort9 sigma_sort11) =
  subst_sort9 (funcomp (subst_sort11 tau_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort9 sigma_sort11 tau_sort11 n)).

Qed.

Lemma compComp'_sort10 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort10 tau_sort11) (subst_sort10 sigma_sort11) =
  subst_sort10 (funcomp (subst_sort11 tau_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort10 sigma_sort11 tau_sort11 n)).

Qed.

Lemma compComp'_sort11 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) :
  funcomp (subst_sort11 tau_sort11) (subst_sort11 sigma_sort11) =
  subst_sort11 (funcomp (subst_sort11 tau_sort11) sigma_sort11).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort11 sigma_sort11 tau_sort11 n)).

Qed.

Lemma rinstInst_sort12 (xi_sort12 : nat -> nat) :
  ren_sort12 xi_sort12 = subst_sort12 (funcomp var_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort12 xi_sort12 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort13 (xi_sort12 : nat -> nat) :
  ren_sort13 xi_sort12 = subst_sort13 (funcomp var_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort13 xi_sort12 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort14 (xi_sort12 : nat -> nat) :
  ren_sort14 xi_sort12 = subst_sort14 (funcomp var_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort14 xi_sort12 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort15 (xi_sort12 : nat -> nat) :
  ren_sort15 xi_sort12 = subst_sort15 (funcomp var_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort15 xi_sort12 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort16 (xi_sort12 : nat -> nat) :
  ren_sort16 xi_sort12 = subst_sort16 (funcomp var_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort16 xi_sort12 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort17 (xi_sort12 : nat -> nat) :
  ren_sort17 xi_sort12 = subst_sort17 (funcomp var_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort17 xi_sort12 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort12 : subst_sort12 var_sort12 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort12 var_sort12 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort13 : subst_sort13 var_sort12 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort13 var_sort12 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort14 : subst_sort14 var_sort12 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort14 var_sort12 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort15 : subst_sort15 var_sort12 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort15 var_sort12 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort16 : subst_sort16 var_sort12 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort16 var_sort12 (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort17 : subst_sort17 var_sort12 = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_sort17 var_sort12 (fun n => eq_refl) (id x))).

Qed.

Lemma rinstId_sort12 : @ren_sort12 id = id.

Proof.
exact (eq_trans (rinstInst_sort12 (id _)) instId_sort12).

Qed.

Lemma rinstId_sort13 : @ren_sort13 id = id.

Proof.
exact (eq_trans (rinstInst_sort13 (id _)) instId_sort13).

Qed.

Lemma rinstId_sort14 : @ren_sort14 id = id.

Proof.
exact (eq_trans (rinstInst_sort14 (id _)) instId_sort14).

Qed.

Lemma rinstId_sort15 : @ren_sort15 id = id.

Proof.
exact (eq_trans (rinstInst_sort15 (id _)) instId_sort15).

Qed.

Lemma rinstId_sort16 : @ren_sort16 id = id.

Proof.
exact (eq_trans (rinstInst_sort16 (id _)) instId_sort16).

Qed.

Lemma rinstId_sort17 : @ren_sort17 id = id.

Proof.
exact (eq_trans (rinstInst_sort17 (id _)) instId_sort17).

Qed.

Lemma varL_sort12 (sigma_sort12 : nat -> sort12) :
  funcomp (subst_sort12 sigma_sort12) var_sort12 = sigma_sort12.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort12 (xi_sort12 : nat -> nat) :
  funcomp (ren_sort12 xi_sort12) var_sort12 = funcomp var_sort12 xi_sort12.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort12 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort12 zeta_sort12) (ren_sort12 xi_sort12) =
  ren_sort12 (funcomp zeta_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort12 xi_sort12 zeta_sort12 n)).

Qed.

Lemma renRen'_sort13 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort13 zeta_sort12) (ren_sort13 xi_sort12) =
  ren_sort13 (funcomp zeta_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort13 xi_sort12 zeta_sort12 n)).

Qed.

Lemma renRen'_sort14 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort14 zeta_sort12) (ren_sort14 xi_sort12) =
  ren_sort14 (funcomp zeta_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort14 xi_sort12 zeta_sort12 n)).

Qed.

Lemma renRen'_sort15 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort15 zeta_sort12) (ren_sort15 xi_sort12) =
  ren_sort15 (funcomp zeta_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort15 xi_sort12 zeta_sort12 n)).

Qed.

Lemma renRen'_sort16 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort16 zeta_sort12) (ren_sort16 xi_sort12) =
  ren_sort16 (funcomp zeta_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort16 xi_sort12 zeta_sort12 n)).

Qed.

Lemma renRen'_sort17 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort17 zeta_sort12) (ren_sort17 xi_sort12) =
  ren_sort17 (funcomp zeta_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort17 xi_sort12 zeta_sort12 n)).

Qed.

Lemma compRen'_sort12 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort12 zeta_sort12) (subst_sort12 sigma_sort12) =
  subst_sort12 (funcomp (ren_sort12 zeta_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort12 sigma_sort12 zeta_sort12 n)).

Qed.

Lemma compRen'_sort13 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort13 zeta_sort12) (subst_sort13 sigma_sort12) =
  subst_sort13 (funcomp (ren_sort12 zeta_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort13 sigma_sort12 zeta_sort12 n)).

Qed.

Lemma compRen'_sort14 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort14 zeta_sort12) (subst_sort14 sigma_sort12) =
  subst_sort14 (funcomp (ren_sort12 zeta_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort14 sigma_sort12 zeta_sort12 n)).

Qed.

Lemma compRen'_sort15 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort15 zeta_sort12) (subst_sort15 sigma_sort12) =
  subst_sort15 (funcomp (ren_sort12 zeta_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort15 sigma_sort12 zeta_sort12 n)).

Qed.

Lemma compRen'_sort16 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort16 zeta_sort12) (subst_sort16 sigma_sort12) =
  subst_sort16 (funcomp (ren_sort12 zeta_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort16 sigma_sort12 zeta_sort12 n)).

Qed.

Lemma compRen'_sort17 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) :
  funcomp (ren_sort17 zeta_sort12) (subst_sort17 sigma_sort12) =
  subst_sort17 (funcomp (ren_sort12 zeta_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort17 sigma_sort12 zeta_sort12 n)).

Qed.

Lemma renComp'_sort12 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort12 tau_sort12) (ren_sort12 xi_sort12) =
  subst_sort12 (funcomp tau_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort12 xi_sort12 tau_sort12 n)).

Qed.

Lemma renComp'_sort13 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort13 tau_sort12) (ren_sort13 xi_sort12) =
  subst_sort13 (funcomp tau_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort13 xi_sort12 tau_sort12 n)).

Qed.

Lemma renComp'_sort14 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort14 tau_sort12) (ren_sort14 xi_sort12) =
  subst_sort14 (funcomp tau_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort14 xi_sort12 tau_sort12 n)).

Qed.

Lemma renComp'_sort15 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort15 tau_sort12) (ren_sort15 xi_sort12) =
  subst_sort15 (funcomp tau_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort15 xi_sort12 tau_sort12 n)).

Qed.

Lemma renComp'_sort16 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort16 tau_sort12) (ren_sort16 xi_sort12) =
  subst_sort16 (funcomp tau_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort16 xi_sort12 tau_sort12 n)).

Qed.

Lemma renComp'_sort17 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort17 tau_sort12) (ren_sort17 xi_sort12) =
  subst_sort17 (funcomp tau_sort12 xi_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort17 xi_sort12 tau_sort12 n)).

Qed.

Lemma compComp'_sort12 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort12 tau_sort12) (subst_sort12 sigma_sort12) =
  subst_sort12 (funcomp (subst_sort12 tau_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort12 sigma_sort12 tau_sort12 n)).

Qed.

Lemma compComp'_sort13 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort13 tau_sort12) (subst_sort13 sigma_sort12) =
  subst_sort13 (funcomp (subst_sort12 tau_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort13 sigma_sort12 tau_sort12 n)).

Qed.

Lemma compComp'_sort14 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort14 tau_sort12) (subst_sort14 sigma_sort12) =
  subst_sort14 (funcomp (subst_sort12 tau_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort14 sigma_sort12 tau_sort12 n)).

Qed.

Lemma compComp'_sort15 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort15 tau_sort12) (subst_sort15 sigma_sort12) =
  subst_sort15 (funcomp (subst_sort12 tau_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort15 sigma_sort12 tau_sort12 n)).

Qed.

Lemma compComp'_sort16 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort16 tau_sort12) (subst_sort16 sigma_sort12) =
  subst_sort16 (funcomp (subst_sort12 tau_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort16 sigma_sort12 tau_sort12 n)).

Qed.

Lemma compComp'_sort17 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) :
  funcomp (subst_sort17 tau_sort12) (subst_sort17 sigma_sort12) =
  subst_sort17 (funcomp (subst_sort12 tau_sort12) sigma_sort12).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort17 sigma_sort12 tau_sort12 n)).

Qed.
