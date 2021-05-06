Require Import core core_axioms fintype fintype_axioms.
Require Import test_50_1.

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

Lemma rinstInst_sort9 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort9 xi_sort2 = subst_sort9 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort9 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort10 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort10 xi_sort2 = subst_sort10 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort10 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort11 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort11 xi_sort2 = subst_sort11 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort11 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort12 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort12 xi_sort2 = subst_sort12 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort12 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort13 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort13 xi_sort2 = subst_sort13 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort13 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort14 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort14 xi_sort2 = subst_sort14 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort14 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort15 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort15 xi_sort2 = subst_sort15 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort15 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort16 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort16 xi_sort2 = subst_sort16 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort16 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort17 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort17 xi_sort2 = subst_sort17 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort17 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort18 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort18 xi_sort2 = subst_sort18 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort18 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort19 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort19 xi_sort2 = subst_sort19 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort19 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort20 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort20 xi_sort2 = subst_sort20 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort20 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort21 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort21 xi_sort2 = subst_sort21 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort21 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort22 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort22 xi_sort2 = subst_sort22 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort22 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort23 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort23 xi_sort2 = subst_sort23 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort23 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort24 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort24 xi_sort2 = subst_sort24 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort24 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort25 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort25 xi_sort2 = subst_sort25 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort25 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort26 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort26 xi_sort2 = subst_sort26 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort26 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort27 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort27 xi_sort2 = subst_sort27 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort27 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort28 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort28 xi_sort2 = subst_sort28 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort28 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort29 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort29 xi_sort2 = subst_sort29 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort29 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort30 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort30 xi_sort2 = subst_sort30 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort30 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort31 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort31 xi_sort2 = subst_sort31 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort31 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort32 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort32 xi_sort2 = subst_sort32 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort32 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort33 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort33 xi_sort2 = subst_sort33 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort33 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort34 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort34 xi_sort2 = subst_sort34 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort34 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort35 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort35 xi_sort2 = subst_sort35 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort35 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort36 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort36 xi_sort2 = subst_sort36 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort36 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort37 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort37 xi_sort2 = subst_sort37 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort37 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort38 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort38 xi_sort2 = subst_sort38 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort38 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort39 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort39 xi_sort2 = subst_sort39 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort39 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort40 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort40 xi_sort2 = subst_sort40 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort40 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort41 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort41 xi_sort2 = subst_sort41 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort41 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort42 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort42 xi_sort2 = subst_sort42 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort42 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort43 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort43 xi_sort2 = subst_sort43 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort43 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort44 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort44 xi_sort2 = subst_sort44 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort44 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort45 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort45 xi_sort2 = subst_sort45 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort45 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort46 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort46 xi_sort2 = subst_sort46 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort46 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort47 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort47 xi_sort2 = subst_sort47 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort47 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort48 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort48 xi_sort2 = subst_sort48 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort48 xi_sort2 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort49 {m_sort2 : nat} {n_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin n_sort2) :
  ren_sort49 xi_sort2 = subst_sort49 (funcomp (var_sort2 n_sort2) xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort49 xi_sort2 _ (fun n => eq_refl) x)).

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

Lemma instId_sort9 {m_sort2 : nat} : subst_sort9 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort9 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort10 {m_sort2 : nat} : subst_sort10 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort10 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort11 {m_sort2 : nat} : subst_sort11 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort11 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort12 {m_sort2 : nat} : subst_sort12 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort12 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort13 {m_sort2 : nat} : subst_sort13 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort13 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort14 {m_sort2 : nat} : subst_sort14 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort14 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort15 {m_sort2 : nat} : subst_sort15 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort15 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort16 {m_sort2 : nat} : subst_sort16 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort16 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort17 {m_sort2 : nat} : subst_sort17 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort17 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort18 {m_sort2 : nat} : subst_sort18 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort18 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort19 {m_sort2 : nat} : subst_sort19 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort19 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort20 {m_sort2 : nat} : subst_sort20 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort20 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort21 {m_sort2 : nat} : subst_sort21 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort21 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort22 {m_sort2 : nat} : subst_sort22 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort22 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort23 {m_sort2 : nat} : subst_sort23 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort23 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort24 {m_sort2 : nat} : subst_sort24 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort24 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort25 {m_sort2 : nat} : subst_sort25 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort25 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort26 {m_sort2 : nat} : subst_sort26 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort26 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort27 {m_sort2 : nat} : subst_sort27 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort27 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort28 {m_sort2 : nat} : subst_sort28 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort28 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort29 {m_sort2 : nat} : subst_sort29 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort29 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort30 {m_sort2 : nat} : subst_sort30 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort30 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort31 {m_sort2 : nat} : subst_sort31 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort31 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort32 {m_sort2 : nat} : subst_sort32 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort32 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort33 {m_sort2 : nat} : subst_sort33 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort33 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort34 {m_sort2 : nat} : subst_sort34 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort34 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort35 {m_sort2 : nat} : subst_sort35 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort35 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort36 {m_sort2 : nat} : subst_sort36 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort36 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort37 {m_sort2 : nat} : subst_sort37 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort37 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort38 {m_sort2 : nat} : subst_sort38 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort38 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort39 {m_sort2 : nat} : subst_sort39 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort39 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort40 {m_sort2 : nat} : subst_sort40 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort40 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort41 {m_sort2 : nat} : subst_sort41 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort41 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort42 {m_sort2 : nat} : subst_sort42 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort42 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort43 {m_sort2 : nat} : subst_sort43 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort43 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort44 {m_sort2 : nat} : subst_sort44 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort44 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort45 {m_sort2 : nat} : subst_sort45 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort45 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort46 {m_sort2 : nat} : subst_sort46 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort46 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort47 {m_sort2 : nat} : subst_sort47 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort47 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort48 {m_sort2 : nat} : subst_sort48 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort48 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

Qed.

Lemma instId_sort49 {m_sort2 : nat} : subst_sort49 (var_sort2 m_sort2) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort49 (var_sort2 m_sort2) (fun n => eq_refl) (id x))).

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

Lemma rinstId_sort9 {m_sort2 : nat} : @ren_sort9 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort9 (id _)) instId_sort9).

Qed.

Lemma rinstId_sort10 {m_sort2 : nat} : @ren_sort10 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort10 (id _)) instId_sort10).

Qed.

Lemma rinstId_sort11 {m_sort2 : nat} : @ren_sort11 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort11 (id _)) instId_sort11).

Qed.

Lemma rinstId_sort12 {m_sort2 : nat} : @ren_sort12 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort12 (id _)) instId_sort12).

Qed.

Lemma rinstId_sort13 {m_sort2 : nat} : @ren_sort13 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort13 (id _)) instId_sort13).

Qed.

Lemma rinstId_sort14 {m_sort2 : nat} : @ren_sort14 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort14 (id _)) instId_sort14).

Qed.

Lemma rinstId_sort15 {m_sort2 : nat} : @ren_sort15 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort15 (id _)) instId_sort15).

Qed.

Lemma rinstId_sort16 {m_sort2 : nat} : @ren_sort16 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort16 (id _)) instId_sort16).

Qed.

Lemma rinstId_sort17 {m_sort2 : nat} : @ren_sort17 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort17 (id _)) instId_sort17).

Qed.

Lemma rinstId_sort18 {m_sort2 : nat} : @ren_sort18 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort18 (id _)) instId_sort18).

Qed.

Lemma rinstId_sort19 {m_sort2 : nat} : @ren_sort19 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort19 (id _)) instId_sort19).

Qed.

Lemma rinstId_sort20 {m_sort2 : nat} : @ren_sort20 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort20 (id _)) instId_sort20).

Qed.

Lemma rinstId_sort21 {m_sort2 : nat} : @ren_sort21 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort21 (id _)) instId_sort21).

Qed.

Lemma rinstId_sort22 {m_sort2 : nat} : @ren_sort22 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort22 (id _)) instId_sort22).

Qed.

Lemma rinstId_sort23 {m_sort2 : nat} : @ren_sort23 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort23 (id _)) instId_sort23).

Qed.

Lemma rinstId_sort24 {m_sort2 : nat} : @ren_sort24 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort24 (id _)) instId_sort24).

Qed.

Lemma rinstId_sort25 {m_sort2 : nat} : @ren_sort25 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort25 (id _)) instId_sort25).

Qed.

Lemma rinstId_sort26 {m_sort2 : nat} : @ren_sort26 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort26 (id _)) instId_sort26).

Qed.

Lemma rinstId_sort27 {m_sort2 : nat} : @ren_sort27 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort27 (id _)) instId_sort27).

Qed.

Lemma rinstId_sort28 {m_sort2 : nat} : @ren_sort28 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort28 (id _)) instId_sort28).

Qed.

Lemma rinstId_sort29 {m_sort2 : nat} : @ren_sort29 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort29 (id _)) instId_sort29).

Qed.

Lemma rinstId_sort30 {m_sort2 : nat} : @ren_sort30 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort30 (id _)) instId_sort30).

Qed.

Lemma rinstId_sort31 {m_sort2 : nat} : @ren_sort31 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort31 (id _)) instId_sort31).

Qed.

Lemma rinstId_sort32 {m_sort2 : nat} : @ren_sort32 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort32 (id _)) instId_sort32).

Qed.

Lemma rinstId_sort33 {m_sort2 : nat} : @ren_sort33 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort33 (id _)) instId_sort33).

Qed.

Lemma rinstId_sort34 {m_sort2 : nat} : @ren_sort34 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort34 (id _)) instId_sort34).

Qed.

Lemma rinstId_sort35 {m_sort2 : nat} : @ren_sort35 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort35 (id _)) instId_sort35).

Qed.

Lemma rinstId_sort36 {m_sort2 : nat} : @ren_sort36 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort36 (id _)) instId_sort36).

Qed.

Lemma rinstId_sort37 {m_sort2 : nat} : @ren_sort37 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort37 (id _)) instId_sort37).

Qed.

Lemma rinstId_sort38 {m_sort2 : nat} : @ren_sort38 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort38 (id _)) instId_sort38).

Qed.

Lemma rinstId_sort39 {m_sort2 : nat} : @ren_sort39 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort39 (id _)) instId_sort39).

Qed.

Lemma rinstId_sort40 {m_sort2 : nat} : @ren_sort40 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort40 (id _)) instId_sort40).

Qed.

Lemma rinstId_sort41 {m_sort2 : nat} : @ren_sort41 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort41 (id _)) instId_sort41).

Qed.

Lemma rinstId_sort42 {m_sort2 : nat} : @ren_sort42 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort42 (id _)) instId_sort42).

Qed.

Lemma rinstId_sort43 {m_sort2 : nat} : @ren_sort43 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort43 (id _)) instId_sort43).

Qed.

Lemma rinstId_sort44 {m_sort2 : nat} : @ren_sort44 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort44 (id _)) instId_sort44).

Qed.

Lemma rinstId_sort45 {m_sort2 : nat} : @ren_sort45 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort45 (id _)) instId_sort45).

Qed.

Lemma rinstId_sort46 {m_sort2 : nat} : @ren_sort46 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort46 (id _)) instId_sort46).

Qed.

Lemma rinstId_sort47 {m_sort2 : nat} : @ren_sort47 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort47 (id _)) instId_sort47).

Qed.

Lemma rinstId_sort48 {m_sort2 : nat} : @ren_sort48 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort48 (id _)) instId_sort48).

Qed.

Lemma rinstId_sort49 {m_sort2 : nat} : @ren_sort49 m_sort2 m_sort2 id = id.

Proof.
exact (eq_trans (rinstInst_sort49 (id _)) instId_sort49).

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

Lemma renRen'_sort9 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort9 zeta_sort2) (ren_sort9 xi_sort2) =
  ren_sort9 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort9 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort10 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort10 zeta_sort2) (ren_sort10 xi_sort2) =
  ren_sort10 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort10 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort11 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort11 zeta_sort2) (ren_sort11 xi_sort2) =
  ren_sort11 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort11 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort12 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort12 zeta_sort2) (ren_sort12 xi_sort2) =
  ren_sort12 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort12 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort13 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort13 zeta_sort2) (ren_sort13 xi_sort2) =
  ren_sort13 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort13 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort14 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort14 zeta_sort2) (ren_sort14 xi_sort2) =
  ren_sort14 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort14 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort15 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort15 zeta_sort2) (ren_sort15 xi_sort2) =
  ren_sort15 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort15 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort16 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort16 zeta_sort2) (ren_sort16 xi_sort2) =
  ren_sort16 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort16 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort17 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort17 zeta_sort2) (ren_sort17 xi_sort2) =
  ren_sort17 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort17 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort18 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort18 zeta_sort2) (ren_sort18 xi_sort2) =
  ren_sort18 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort18 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort19 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort19 zeta_sort2) (ren_sort19 xi_sort2) =
  ren_sort19 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort19 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort20 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort20 zeta_sort2) (ren_sort20 xi_sort2) =
  ren_sort20 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort20 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort21 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort21 zeta_sort2) (ren_sort21 xi_sort2) =
  ren_sort21 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort21 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort22 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort22 zeta_sort2) (ren_sort22 xi_sort2) =
  ren_sort22 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort22 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort23 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort23 zeta_sort2) (ren_sort23 xi_sort2) =
  ren_sort23 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort23 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort24 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort24 zeta_sort2) (ren_sort24 xi_sort2) =
  ren_sort24 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort24 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort25 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort25 zeta_sort2) (ren_sort25 xi_sort2) =
  ren_sort25 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort25 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort26 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort26 zeta_sort2) (ren_sort26 xi_sort2) =
  ren_sort26 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort26 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort27 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort27 zeta_sort2) (ren_sort27 xi_sort2) =
  ren_sort27 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort27 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort28 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort28 zeta_sort2) (ren_sort28 xi_sort2) =
  ren_sort28 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort28 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort29 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort29 zeta_sort2) (ren_sort29 xi_sort2) =
  ren_sort29 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort29 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort30 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort30 zeta_sort2) (ren_sort30 xi_sort2) =
  ren_sort30 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort30 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort31 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort31 zeta_sort2) (ren_sort31 xi_sort2) =
  ren_sort31 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort31 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort32 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort32 zeta_sort2) (ren_sort32 xi_sort2) =
  ren_sort32 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort32 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort33 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort33 zeta_sort2) (ren_sort33 xi_sort2) =
  ren_sort33 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort33 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort34 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort34 zeta_sort2) (ren_sort34 xi_sort2) =
  ren_sort34 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort34 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort35 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort35 zeta_sort2) (ren_sort35 xi_sort2) =
  ren_sort35 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort35 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort36 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort36 zeta_sort2) (ren_sort36 xi_sort2) =
  ren_sort36 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort36 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort37 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort37 zeta_sort2) (ren_sort37 xi_sort2) =
  ren_sort37 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort37 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort38 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort38 zeta_sort2) (ren_sort38 xi_sort2) =
  ren_sort38 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort38 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort39 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort39 zeta_sort2) (ren_sort39 xi_sort2) =
  ren_sort39 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort39 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort40 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort40 zeta_sort2) (ren_sort40 xi_sort2) =
  ren_sort40 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort40 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort41 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort41 zeta_sort2) (ren_sort41 xi_sort2) =
  ren_sort41 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort41 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort42 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort42 zeta_sort2) (ren_sort42 xi_sort2) =
  ren_sort42 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort42 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort43 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort43 zeta_sort2) (ren_sort43 xi_sort2) =
  ren_sort43 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort43 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort44 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort44 zeta_sort2) (ren_sort44 xi_sort2) =
  ren_sort44 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort44 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort45 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort45 zeta_sort2) (ren_sort45 xi_sort2) =
  ren_sort45 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort45 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort46 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort46 zeta_sort2) (ren_sort46 xi_sort2) =
  ren_sort46 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort46 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort47 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort47 zeta_sort2) (ren_sort47 xi_sort2) =
  ren_sort47 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort47 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort48 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort48 zeta_sort2) (ren_sort48 xi_sort2) =
  ren_sort48 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort48 xi_sort2 zeta_sort2 n)).

Qed.

Lemma renRen'_sort49 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort49 zeta_sort2) (ren_sort49 xi_sort2) =
  ren_sort49 (funcomp zeta_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort49 xi_sort2 zeta_sort2 n)).

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

Lemma compRen'_sort9 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort9 zeta_sort2) (subst_sort9 sigma_sort2) =
  subst_sort9 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort9 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort10 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort10 zeta_sort2) (subst_sort10 sigma_sort2) =
  subst_sort10 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort10 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort11 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort11 zeta_sort2) (subst_sort11 sigma_sort2) =
  subst_sort11 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort11 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort12 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort12 zeta_sort2) (subst_sort12 sigma_sort2) =
  subst_sort12 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort12 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort13 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort13 zeta_sort2) (subst_sort13 sigma_sort2) =
  subst_sort13 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort13 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort14 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort14 zeta_sort2) (subst_sort14 sigma_sort2) =
  subst_sort14 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort14 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort15 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort15 zeta_sort2) (subst_sort15 sigma_sort2) =
  subst_sort15 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort15 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort16 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort16 zeta_sort2) (subst_sort16 sigma_sort2) =
  subst_sort16 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort16 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort17 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort17 zeta_sort2) (subst_sort17 sigma_sort2) =
  subst_sort17 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort17 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort18 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort18 zeta_sort2) (subst_sort18 sigma_sort2) =
  subst_sort18 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort18 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort19 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort19 zeta_sort2) (subst_sort19 sigma_sort2) =
  subst_sort19 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort19 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort20 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort20 zeta_sort2) (subst_sort20 sigma_sort2) =
  subst_sort20 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort20 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort21 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort21 zeta_sort2) (subst_sort21 sigma_sort2) =
  subst_sort21 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort21 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort22 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort22 zeta_sort2) (subst_sort22 sigma_sort2) =
  subst_sort22 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort22 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort23 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort23 zeta_sort2) (subst_sort23 sigma_sort2) =
  subst_sort23 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort23 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort24 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort24 zeta_sort2) (subst_sort24 sigma_sort2) =
  subst_sort24 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort24 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort25 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort25 zeta_sort2) (subst_sort25 sigma_sort2) =
  subst_sort25 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort25 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort26 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort26 zeta_sort2) (subst_sort26 sigma_sort2) =
  subst_sort26 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort26 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort27 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort27 zeta_sort2) (subst_sort27 sigma_sort2) =
  subst_sort27 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort27 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort28 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort28 zeta_sort2) (subst_sort28 sigma_sort2) =
  subst_sort28 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort28 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort29 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort29 zeta_sort2) (subst_sort29 sigma_sort2) =
  subst_sort29 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort29 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort30 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort30 zeta_sort2) (subst_sort30 sigma_sort2) =
  subst_sort30 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort30 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort31 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort31 zeta_sort2) (subst_sort31 sigma_sort2) =
  subst_sort31 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort31 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort32 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort32 zeta_sort2) (subst_sort32 sigma_sort2) =
  subst_sort32 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort32 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort33 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort33 zeta_sort2) (subst_sort33 sigma_sort2) =
  subst_sort33 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort33 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort34 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort34 zeta_sort2) (subst_sort34 sigma_sort2) =
  subst_sort34 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort34 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort35 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort35 zeta_sort2) (subst_sort35 sigma_sort2) =
  subst_sort35 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort35 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort36 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort36 zeta_sort2) (subst_sort36 sigma_sort2) =
  subst_sort36 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort36 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort37 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort37 zeta_sort2) (subst_sort37 sigma_sort2) =
  subst_sort37 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort37 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort38 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort38 zeta_sort2) (subst_sort38 sigma_sort2) =
  subst_sort38 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort38 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort39 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort39 zeta_sort2) (subst_sort39 sigma_sort2) =
  subst_sort39 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort39 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort40 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort40 zeta_sort2) (subst_sort40 sigma_sort2) =
  subst_sort40 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort40 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort41 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort41 zeta_sort2) (subst_sort41 sigma_sort2) =
  subst_sort41 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort41 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort42 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort42 zeta_sort2) (subst_sort42 sigma_sort2) =
  subst_sort42 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort42 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort43 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort43 zeta_sort2) (subst_sort43 sigma_sort2) =
  subst_sort43 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort43 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort44 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort44 zeta_sort2) (subst_sort44 sigma_sort2) =
  subst_sort44 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort44 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort45 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort45 zeta_sort2) (subst_sort45 sigma_sort2) =
  subst_sort45 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort45 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort46 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort46 zeta_sort2) (subst_sort46 sigma_sort2) =
  subst_sort46 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort46 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort47 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort47 zeta_sort2) (subst_sort47 sigma_sort2) =
  subst_sort47 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort47 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort48 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort48 zeta_sort2) (subst_sort48 sigma_sort2) =
  subst_sort48 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort48 sigma_sort2 zeta_sort2 n)).

Qed.

Lemma compRen'_sort49 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) :
  funcomp (ren_sort49 zeta_sort2) (subst_sort49 sigma_sort2) =
  subst_sort49 (funcomp (ren_sort2 zeta_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort49 sigma_sort2 zeta_sort2 n)).

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

Lemma renComp'_sort9 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort9 tau_sort2) (ren_sort9 xi_sort2) =
  subst_sort9 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort9 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort10 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort10 tau_sort2) (ren_sort10 xi_sort2) =
  subst_sort10 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort10 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort11 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort11 tau_sort2) (ren_sort11 xi_sort2) =
  subst_sort11 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort11 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort12 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort12 tau_sort2) (ren_sort12 xi_sort2) =
  subst_sort12 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort12 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort13 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort13 tau_sort2) (ren_sort13 xi_sort2) =
  subst_sort13 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort13 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort14 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort14 tau_sort2) (ren_sort14 xi_sort2) =
  subst_sort14 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort14 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort15 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort15 tau_sort2) (ren_sort15 xi_sort2) =
  subst_sort15 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort15 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort16 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort16 tau_sort2) (ren_sort16 xi_sort2) =
  subst_sort16 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort16 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort17 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort17 tau_sort2) (ren_sort17 xi_sort2) =
  subst_sort17 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort17 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort18 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort18 tau_sort2) (ren_sort18 xi_sort2) =
  subst_sort18 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort18 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort19 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort19 tau_sort2) (ren_sort19 xi_sort2) =
  subst_sort19 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort19 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort20 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort20 tau_sort2) (ren_sort20 xi_sort2) =
  subst_sort20 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort20 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort21 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort21 tau_sort2) (ren_sort21 xi_sort2) =
  subst_sort21 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort21 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort22 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort22 tau_sort2) (ren_sort22 xi_sort2) =
  subst_sort22 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort22 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort23 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort23 tau_sort2) (ren_sort23 xi_sort2) =
  subst_sort23 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort23 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort24 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort24 tau_sort2) (ren_sort24 xi_sort2) =
  subst_sort24 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort24 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort25 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort25 tau_sort2) (ren_sort25 xi_sort2) =
  subst_sort25 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort25 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort26 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort26 tau_sort2) (ren_sort26 xi_sort2) =
  subst_sort26 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort26 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort27 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort27 tau_sort2) (ren_sort27 xi_sort2) =
  subst_sort27 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort27 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort28 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort28 tau_sort2) (ren_sort28 xi_sort2) =
  subst_sort28 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort28 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort29 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort29 tau_sort2) (ren_sort29 xi_sort2) =
  subst_sort29 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort29 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort30 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort30 tau_sort2) (ren_sort30 xi_sort2) =
  subst_sort30 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort30 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort31 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort31 tau_sort2) (ren_sort31 xi_sort2) =
  subst_sort31 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort31 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort32 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort32 tau_sort2) (ren_sort32 xi_sort2) =
  subst_sort32 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort32 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort33 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort33 tau_sort2) (ren_sort33 xi_sort2) =
  subst_sort33 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort33 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort34 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort34 tau_sort2) (ren_sort34 xi_sort2) =
  subst_sort34 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort34 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort35 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort35 tau_sort2) (ren_sort35 xi_sort2) =
  subst_sort35 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort35 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort36 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort36 tau_sort2) (ren_sort36 xi_sort2) =
  subst_sort36 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort36 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort37 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort37 tau_sort2) (ren_sort37 xi_sort2) =
  subst_sort37 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort37 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort38 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort38 tau_sort2) (ren_sort38 xi_sort2) =
  subst_sort38 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort38 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort39 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort39 tau_sort2) (ren_sort39 xi_sort2) =
  subst_sort39 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort39 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort40 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort40 tau_sort2) (ren_sort40 xi_sort2) =
  subst_sort40 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort40 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort41 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort41 tau_sort2) (ren_sort41 xi_sort2) =
  subst_sort41 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort41 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort42 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort42 tau_sort2) (ren_sort42 xi_sort2) =
  subst_sort42 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort42 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort43 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort43 tau_sort2) (ren_sort43 xi_sort2) =
  subst_sort43 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort43 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort44 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort44 tau_sort2) (ren_sort44 xi_sort2) =
  subst_sort44 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort44 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort45 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort45 tau_sort2) (ren_sort45 xi_sort2) =
  subst_sort45 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort45 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort46 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort46 tau_sort2) (ren_sort46 xi_sort2) =
  subst_sort46 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort46 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort47 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort47 tau_sort2) (ren_sort47 xi_sort2) =
  subst_sort47 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort47 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort48 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort48 tau_sort2) (ren_sort48 xi_sort2) =
  subst_sort48 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort48 xi_sort2 tau_sort2 n)).

Qed.

Lemma renComp'_sort49 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort49 tau_sort2) (ren_sort49 xi_sort2) =
  subst_sort49 (funcomp tau_sort2 xi_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort49 xi_sort2 tau_sort2 n)).

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

Lemma compComp'_sort9 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort9 tau_sort2) (subst_sort9 sigma_sort2) =
  subst_sort9 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort9 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort10 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort10 tau_sort2) (subst_sort10 sigma_sort2) =
  subst_sort10 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort10 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort11 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort11 tau_sort2) (subst_sort11 sigma_sort2) =
  subst_sort11 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort11 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort12 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort12 tau_sort2) (subst_sort12 sigma_sort2) =
  subst_sort12 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort12 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort13 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort13 tau_sort2) (subst_sort13 sigma_sort2) =
  subst_sort13 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort13 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort14 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort14 tau_sort2) (subst_sort14 sigma_sort2) =
  subst_sort14 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort14 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort15 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort15 tau_sort2) (subst_sort15 sigma_sort2) =
  subst_sort15 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort15 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort16 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort16 tau_sort2) (subst_sort16 sigma_sort2) =
  subst_sort16 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort16 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort17 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort17 tau_sort2) (subst_sort17 sigma_sort2) =
  subst_sort17 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort17 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort18 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort18 tau_sort2) (subst_sort18 sigma_sort2) =
  subst_sort18 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort18 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort19 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort19 tau_sort2) (subst_sort19 sigma_sort2) =
  subst_sort19 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort19 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort20 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort20 tau_sort2) (subst_sort20 sigma_sort2) =
  subst_sort20 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort20 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort21 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort21 tau_sort2) (subst_sort21 sigma_sort2) =
  subst_sort21 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort21 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort22 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort22 tau_sort2) (subst_sort22 sigma_sort2) =
  subst_sort22 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort22 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort23 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort23 tau_sort2) (subst_sort23 sigma_sort2) =
  subst_sort23 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort23 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort24 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort24 tau_sort2) (subst_sort24 sigma_sort2) =
  subst_sort24 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort24 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort25 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort25 tau_sort2) (subst_sort25 sigma_sort2) =
  subst_sort25 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort25 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort26 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort26 tau_sort2) (subst_sort26 sigma_sort2) =
  subst_sort26 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort26 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort27 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort27 tau_sort2) (subst_sort27 sigma_sort2) =
  subst_sort27 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort27 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort28 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort28 tau_sort2) (subst_sort28 sigma_sort2) =
  subst_sort28 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort28 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort29 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort29 tau_sort2) (subst_sort29 sigma_sort2) =
  subst_sort29 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort29 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort30 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort30 tau_sort2) (subst_sort30 sigma_sort2) =
  subst_sort30 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort30 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort31 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort31 tau_sort2) (subst_sort31 sigma_sort2) =
  subst_sort31 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort31 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort32 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort32 tau_sort2) (subst_sort32 sigma_sort2) =
  subst_sort32 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort32 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort33 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort33 tau_sort2) (subst_sort33 sigma_sort2) =
  subst_sort33 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort33 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort34 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort34 tau_sort2) (subst_sort34 sigma_sort2) =
  subst_sort34 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort34 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort35 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort35 tau_sort2) (subst_sort35 sigma_sort2) =
  subst_sort35 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort35 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort36 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort36 tau_sort2) (subst_sort36 sigma_sort2) =
  subst_sort36 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort36 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort37 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort37 tau_sort2) (subst_sort37 sigma_sort2) =
  subst_sort37 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort37 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort38 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort38 tau_sort2) (subst_sort38 sigma_sort2) =
  subst_sort38 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort38 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort39 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort39 tau_sort2) (subst_sort39 sigma_sort2) =
  subst_sort39 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort39 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort40 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort40 tau_sort2) (subst_sort40 sigma_sort2) =
  subst_sort40 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort40 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort41 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort41 tau_sort2) (subst_sort41 sigma_sort2) =
  subst_sort41 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort41 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort42 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort42 tau_sort2) (subst_sort42 sigma_sort2) =
  subst_sort42 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort42 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort43 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort43 tau_sort2) (subst_sort43 sigma_sort2) =
  subst_sort43 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort43 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort44 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort44 tau_sort2) (subst_sort44 sigma_sort2) =
  subst_sort44 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort44 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort45 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort45 tau_sort2) (subst_sort45 sigma_sort2) =
  subst_sort45 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort45 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort46 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort46 tau_sort2) (subst_sort46 sigma_sort2) =
  subst_sort46 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort46 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort47 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort47 tau_sort2) (subst_sort47 sigma_sort2) =
  subst_sort47 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort47 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort48 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort48 tau_sort2) (subst_sort48 sigma_sort2) =
  subst_sort48 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort48 sigma_sort2 tau_sort2 n)).

Qed.

Lemma compComp'_sort49 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) :
  funcomp (subst_sort49 tau_sort2) (subst_sort49 sigma_sort2) =
  subst_sort49 (funcomp (subst_sort2 tau_sort2) sigma_sort2).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort49 sigma_sort2 tau_sort2 n)).

Qed.
