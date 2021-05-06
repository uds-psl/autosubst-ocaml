Require Import core core_axioms fintype fintype_axioms.
Require Import test_100_1.

Lemma rinstInst_sort0 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort0 xi_sort40 = subst_sort0 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort0 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort1 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort1 xi_sort40 = subst_sort1 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort1 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort2 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort2 xi_sort40 = subst_sort2 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort2 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort3 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort3 xi_sort40 = subst_sort3 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort3 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort4 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort4 xi_sort40 = subst_sort4 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort4 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort5 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort5 xi_sort40 = subst_sort5 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort5 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort6 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort6 xi_sort40 = subst_sort6 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort6 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort7 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort7 xi_sort40 = subst_sort7 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort7 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort8 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort8 xi_sort40 = subst_sort8 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort8 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort9 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort9 xi_sort40 = subst_sort9 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort9 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort10 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort10 xi_sort40 =
  subst_sort10 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort10 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort11 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort11 xi_sort40 =
  subst_sort11 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort11 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort12 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort12 xi_sort40 =
  subst_sort12 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort12 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort13 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort13 xi_sort40 =
  subst_sort13 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort13 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort14 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort14 xi_sort40 =
  subst_sort14 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort14 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort15 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort15 xi_sort40 =
  subst_sort15 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort15 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort16 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort16 xi_sort40 =
  subst_sort16 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort16 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort17 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort17 xi_sort40 =
  subst_sort17 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort17 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort18 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort18 xi_sort40 =
  subst_sort18 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort18 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort19 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort19 xi_sort40 =
  subst_sort19 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort19 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort20 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort20 xi_sort40 =
  subst_sort20 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort20 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort21 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort21 xi_sort40 =
  subst_sort21 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort21 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort22 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort22 xi_sort40 =
  subst_sort22 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort22 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort23 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort23 xi_sort40 =
  subst_sort23 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort23 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort24 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort24 xi_sort40 =
  subst_sort24 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort24 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort25 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort25 xi_sort40 =
  subst_sort25 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort25 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort26 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort26 xi_sort40 =
  subst_sort26 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort26 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort27 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort27 xi_sort40 =
  subst_sort27 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort27 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort28 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort28 xi_sort40 =
  subst_sort28 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort28 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort29 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort29 xi_sort40 =
  subst_sort29 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort29 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort30 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort30 xi_sort40 =
  subst_sort30 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort30 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort31 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort31 xi_sort40 =
  subst_sort31 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort31 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort32 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort32 xi_sort40 =
  subst_sort32 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort32 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort33 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort33 xi_sort40 =
  subst_sort33 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort33 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort34 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort34 xi_sort40 =
  subst_sort34 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort34 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort35 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort35 xi_sort40 =
  subst_sort35 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort35 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort36 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort36 xi_sort40 =
  subst_sort36 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort36 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort37 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort37 xi_sort40 =
  subst_sort37 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort37 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort38 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort38 xi_sort40 =
  subst_sort38 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort38 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort39 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort39 xi_sort40 =
  subst_sort39 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort39 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort40 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort40 xi_sort40 =
  subst_sort40 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort40 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort41 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort41 xi_sort40 =
  subst_sort41 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort41 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort42 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort42 xi_sort40 =
  subst_sort42 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort42 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort43 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort43 xi_sort40 =
  subst_sort43 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort43 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort44 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort44 xi_sort40 =
  subst_sort44 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort44 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort45 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort45 xi_sort40 =
  subst_sort45 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort45 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort46 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort46 xi_sort40 =
  subst_sort46 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort46 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort47 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort47 xi_sort40 =
  subst_sort47 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort47 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort48 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort48 xi_sort40 =
  subst_sort48 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort48 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort49 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort49 xi_sort40 =
  subst_sort49 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort49 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort50 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort50 xi_sort40 =
  subst_sort50 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort50 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort51 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort51 xi_sort40 =
  subst_sort51 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort51 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort52 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort52 xi_sort40 =
  subst_sort52 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort52 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort53 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort53 xi_sort40 =
  subst_sort53 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort53 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort54 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort54 xi_sort40 =
  subst_sort54 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort54 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort55 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort55 xi_sort40 =
  subst_sort55 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort55 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort56 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort56 xi_sort40 =
  subst_sort56 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort56 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort57 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort57 xi_sort40 =
  subst_sort57 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort57 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort58 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort58 xi_sort40 =
  subst_sort58 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort58 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort59 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort59 xi_sort40 =
  subst_sort59 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort59 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort60 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort60 xi_sort40 =
  subst_sort60 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort60 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort61 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort61 xi_sort40 =
  subst_sort61 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort61 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort62 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort62 xi_sort40 =
  subst_sort62 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort62 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort63 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort63 xi_sort40 =
  subst_sort63 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort63 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort64 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort64 xi_sort40 =
  subst_sort64 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort64 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort65 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort65 xi_sort40 =
  subst_sort65 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort65 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort66 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort66 xi_sort40 =
  subst_sort66 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort66 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort67 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort67 xi_sort40 =
  subst_sort67 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort67 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort68 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort68 xi_sort40 =
  subst_sort68 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort68 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort69 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort69 xi_sort40 =
  subst_sort69 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort69 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort70 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort70 xi_sort40 =
  subst_sort70 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort70 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort71 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort71 xi_sort40 =
  subst_sort71 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort71 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort72 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort72 xi_sort40 =
  subst_sort72 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort72 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort73 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort73 xi_sort40 =
  subst_sort73 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort73 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort74 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort74 xi_sort40 =
  subst_sort74 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort74 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort75 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort75 xi_sort40 =
  subst_sort75 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort75 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort76 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort76 xi_sort40 =
  subst_sort76 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort76 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort77 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort77 xi_sort40 =
  subst_sort77 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort77 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort78 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort78 xi_sort40 =
  subst_sort78 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort78 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort79 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort79 xi_sort40 =
  subst_sort79 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort79 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort80 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort80 xi_sort40 =
  subst_sort80 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort80 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort81 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort81 xi_sort40 =
  subst_sort81 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort81 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort82 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort82 xi_sort40 =
  subst_sort82 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort82 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort83 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort83 xi_sort40 =
  subst_sort83 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort83 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort84 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort84 xi_sort40 =
  subst_sort84 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort84 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort85 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort85 xi_sort40 =
  subst_sort85 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort85 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort86 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort86 xi_sort40 =
  subst_sort86 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort86 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort87 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort87 xi_sort40 =
  subst_sort87 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort87 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort88 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort88 xi_sort40 =
  subst_sort88 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort88 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort89 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort89 xi_sort40 =
  subst_sort89 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort89 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort90 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort90 xi_sort40 =
  subst_sort90 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort90 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort91 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort91 xi_sort40 =
  subst_sort91 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort91 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort92 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort92 xi_sort40 =
  subst_sort92 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort92 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort93 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort93 xi_sort40 =
  subst_sort93 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort93 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort94 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort94 xi_sort40 =
  subst_sort94 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort94 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort95 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort95 xi_sort40 =
  subst_sort95 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort95 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort96 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort96 xi_sort40 =
  subst_sort96 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort96 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort97 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort97 xi_sort40 =
  subst_sort97 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort97 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort98 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort98 xi_sort40 =
  subst_sort98 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort98 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort99 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  ren_sort99 xi_sort40 =
  subst_sort99 (funcomp (var_sort40 n_sort40) xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort99 xi_sort40 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort0 {m_sort40 : nat} : subst_sort0 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort0 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort1 {m_sort40 : nat} : subst_sort1 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort1 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort2 {m_sort40 : nat} : subst_sort2 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort2 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort3 {m_sort40 : nat} : subst_sort3 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort3 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort4 {m_sort40 : nat} : subst_sort4 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort4 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort5 {m_sort40 : nat} : subst_sort5 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort5 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort6 {m_sort40 : nat} : subst_sort6 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort6 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort7 {m_sort40 : nat} : subst_sort7 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort7 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort8 {m_sort40 : nat} : subst_sort8 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort8 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort9 {m_sort40 : nat} : subst_sort9 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort9 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort10 {m_sort40 : nat} :
  subst_sort10 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort10 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort11 {m_sort40 : nat} :
  subst_sort11 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort11 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort12 {m_sort40 : nat} :
  subst_sort12 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort12 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort13 {m_sort40 : nat} :
  subst_sort13 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort13 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort14 {m_sort40 : nat} :
  subst_sort14 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort14 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort15 {m_sort40 : nat} :
  subst_sort15 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort15 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort16 {m_sort40 : nat} :
  subst_sort16 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort16 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort17 {m_sort40 : nat} :
  subst_sort17 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort17 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort18 {m_sort40 : nat} :
  subst_sort18 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort18 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort19 {m_sort40 : nat} :
  subst_sort19 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort19 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort20 {m_sort40 : nat} :
  subst_sort20 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort20 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort21 {m_sort40 : nat} :
  subst_sort21 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort21 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort22 {m_sort40 : nat} :
  subst_sort22 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort22 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort23 {m_sort40 : nat} :
  subst_sort23 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort23 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort24 {m_sort40 : nat} :
  subst_sort24 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort24 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort25 {m_sort40 : nat} :
  subst_sort25 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort25 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort26 {m_sort40 : nat} :
  subst_sort26 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort26 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort27 {m_sort40 : nat} :
  subst_sort27 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort27 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort28 {m_sort40 : nat} :
  subst_sort28 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort28 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort29 {m_sort40 : nat} :
  subst_sort29 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort29 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort30 {m_sort40 : nat} :
  subst_sort30 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort30 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort31 {m_sort40 : nat} :
  subst_sort31 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort31 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort32 {m_sort40 : nat} :
  subst_sort32 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort32 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort33 {m_sort40 : nat} :
  subst_sort33 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort33 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort34 {m_sort40 : nat} :
  subst_sort34 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort34 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort35 {m_sort40 : nat} :
  subst_sort35 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort35 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort36 {m_sort40 : nat} :
  subst_sort36 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort36 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort37 {m_sort40 : nat} :
  subst_sort37 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort37 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort38 {m_sort40 : nat} :
  subst_sort38 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort38 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort39 {m_sort40 : nat} :
  subst_sort39 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort39 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort40 {m_sort40 : nat} :
  subst_sort40 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort40 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort41 {m_sort40 : nat} :
  subst_sort41 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort41 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort42 {m_sort40 : nat} :
  subst_sort42 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort42 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort43 {m_sort40 : nat} :
  subst_sort43 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort43 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort44 {m_sort40 : nat} :
  subst_sort44 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort44 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort45 {m_sort40 : nat} :
  subst_sort45 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort45 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort46 {m_sort40 : nat} :
  subst_sort46 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort46 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort47 {m_sort40 : nat} :
  subst_sort47 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort47 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort48 {m_sort40 : nat} :
  subst_sort48 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort48 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort49 {m_sort40 : nat} :
  subst_sort49 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort49 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort50 {m_sort40 : nat} :
  subst_sort50 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort50 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort51 {m_sort40 : nat} :
  subst_sort51 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort51 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort52 {m_sort40 : nat} :
  subst_sort52 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort52 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort53 {m_sort40 : nat} :
  subst_sort53 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort53 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort54 {m_sort40 : nat} :
  subst_sort54 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort54 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort55 {m_sort40 : nat} :
  subst_sort55 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort55 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort56 {m_sort40 : nat} :
  subst_sort56 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort56 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort57 {m_sort40 : nat} :
  subst_sort57 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort57 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort58 {m_sort40 : nat} :
  subst_sort58 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort58 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort59 {m_sort40 : nat} :
  subst_sort59 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort59 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort60 {m_sort40 : nat} :
  subst_sort60 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort60 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort61 {m_sort40 : nat} :
  subst_sort61 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort61 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort62 {m_sort40 : nat} :
  subst_sort62 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort62 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort63 {m_sort40 : nat} :
  subst_sort63 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort63 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort64 {m_sort40 : nat} :
  subst_sort64 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort64 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort65 {m_sort40 : nat} :
  subst_sort65 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort65 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort66 {m_sort40 : nat} :
  subst_sort66 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort66 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort67 {m_sort40 : nat} :
  subst_sort67 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort67 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort68 {m_sort40 : nat} :
  subst_sort68 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort68 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort69 {m_sort40 : nat} :
  subst_sort69 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort69 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort70 {m_sort40 : nat} :
  subst_sort70 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort70 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort71 {m_sort40 : nat} :
  subst_sort71 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort71 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort72 {m_sort40 : nat} :
  subst_sort72 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort72 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort73 {m_sort40 : nat} :
  subst_sort73 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort73 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort74 {m_sort40 : nat} :
  subst_sort74 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort74 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort75 {m_sort40 : nat} :
  subst_sort75 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort75 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort76 {m_sort40 : nat} :
  subst_sort76 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort76 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort77 {m_sort40 : nat} :
  subst_sort77 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort77 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort78 {m_sort40 : nat} :
  subst_sort78 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort78 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort79 {m_sort40 : nat} :
  subst_sort79 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort79 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort80 {m_sort40 : nat} :
  subst_sort80 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort80 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort81 {m_sort40 : nat} :
  subst_sort81 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort81 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort82 {m_sort40 : nat} :
  subst_sort82 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort82 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort83 {m_sort40 : nat} :
  subst_sort83 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort83 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort84 {m_sort40 : nat} :
  subst_sort84 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort84 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort85 {m_sort40 : nat} :
  subst_sort85 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort85 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort86 {m_sort40 : nat} :
  subst_sort86 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort86 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort87 {m_sort40 : nat} :
  subst_sort87 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort87 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort88 {m_sort40 : nat} :
  subst_sort88 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort88 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort89 {m_sort40 : nat} :
  subst_sort89 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort89 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort90 {m_sort40 : nat} :
  subst_sort90 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort90 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort91 {m_sort40 : nat} :
  subst_sort91 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort91 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort92 {m_sort40 : nat} :
  subst_sort92 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort92 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort93 {m_sort40 : nat} :
  subst_sort93 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort93 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort94 {m_sort40 : nat} :
  subst_sort94 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort94 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort95 {m_sort40 : nat} :
  subst_sort95 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort95 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort96 {m_sort40 : nat} :
  subst_sort96 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort96 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort97 {m_sort40 : nat} :
  subst_sort97 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort97 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort98 {m_sort40 : nat} :
  subst_sort98 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort98 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort99 {m_sort40 : nat} :
  subst_sort99 (var_sort40 m_sort40) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort99 (var_sort40 m_sort40) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma rinstId_sort0 {m_sort40 : nat} : @ren_sort0 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort0 (id _)) instId_sort0).

Qed.

Lemma rinstId_sort1 {m_sort40 : nat} : @ren_sort1 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort1 (id _)) instId_sort1).

Qed.

Lemma rinstId_sort2 {m_sort40 : nat} : @ren_sort2 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort2 (id _)) instId_sort2).

Qed.

Lemma rinstId_sort3 {m_sort40 : nat} : @ren_sort3 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort3 (id _)) instId_sort3).

Qed.

Lemma rinstId_sort4 {m_sort40 : nat} : @ren_sort4 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort4 (id _)) instId_sort4).

Qed.

Lemma rinstId_sort5 {m_sort40 : nat} : @ren_sort5 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort5 (id _)) instId_sort5).

Qed.

Lemma rinstId_sort6 {m_sort40 : nat} : @ren_sort6 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort6 (id _)) instId_sort6).

Qed.

Lemma rinstId_sort7 {m_sort40 : nat} : @ren_sort7 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort7 (id _)) instId_sort7).

Qed.

Lemma rinstId_sort8 {m_sort40 : nat} : @ren_sort8 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort8 (id _)) instId_sort8).

Qed.

Lemma rinstId_sort9 {m_sort40 : nat} : @ren_sort9 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort9 (id _)) instId_sort9).

Qed.

Lemma rinstId_sort10 {m_sort40 : nat} : @ren_sort10 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort10 (id _)) instId_sort10).

Qed.

Lemma rinstId_sort11 {m_sort40 : nat} : @ren_sort11 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort11 (id _)) instId_sort11).

Qed.

Lemma rinstId_sort12 {m_sort40 : nat} : @ren_sort12 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort12 (id _)) instId_sort12).

Qed.

Lemma rinstId_sort13 {m_sort40 : nat} : @ren_sort13 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort13 (id _)) instId_sort13).

Qed.

Lemma rinstId_sort14 {m_sort40 : nat} : @ren_sort14 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort14 (id _)) instId_sort14).

Qed.

Lemma rinstId_sort15 {m_sort40 : nat} : @ren_sort15 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort15 (id _)) instId_sort15).

Qed.

Lemma rinstId_sort16 {m_sort40 : nat} : @ren_sort16 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort16 (id _)) instId_sort16).

Qed.

Lemma rinstId_sort17 {m_sort40 : nat} : @ren_sort17 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort17 (id _)) instId_sort17).

Qed.

Lemma rinstId_sort18 {m_sort40 : nat} : @ren_sort18 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort18 (id _)) instId_sort18).

Qed.

Lemma rinstId_sort19 {m_sort40 : nat} : @ren_sort19 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort19 (id _)) instId_sort19).

Qed.

Lemma rinstId_sort20 {m_sort40 : nat} : @ren_sort20 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort20 (id _)) instId_sort20).

Qed.

Lemma rinstId_sort21 {m_sort40 : nat} : @ren_sort21 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort21 (id _)) instId_sort21).

Qed.

Lemma rinstId_sort22 {m_sort40 : nat} : @ren_sort22 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort22 (id _)) instId_sort22).

Qed.

Lemma rinstId_sort23 {m_sort40 : nat} : @ren_sort23 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort23 (id _)) instId_sort23).

Qed.

Lemma rinstId_sort24 {m_sort40 : nat} : @ren_sort24 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort24 (id _)) instId_sort24).

Qed.

Lemma rinstId_sort25 {m_sort40 : nat} : @ren_sort25 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort25 (id _)) instId_sort25).

Qed.

Lemma rinstId_sort26 {m_sort40 : nat} : @ren_sort26 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort26 (id _)) instId_sort26).

Qed.

Lemma rinstId_sort27 {m_sort40 : nat} : @ren_sort27 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort27 (id _)) instId_sort27).

Qed.

Lemma rinstId_sort28 {m_sort40 : nat} : @ren_sort28 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort28 (id _)) instId_sort28).

Qed.

Lemma rinstId_sort29 {m_sort40 : nat} : @ren_sort29 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort29 (id _)) instId_sort29).

Qed.

Lemma rinstId_sort30 {m_sort40 : nat} : @ren_sort30 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort30 (id _)) instId_sort30).

Qed.

Lemma rinstId_sort31 {m_sort40 : nat} : @ren_sort31 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort31 (id _)) instId_sort31).

Qed.

Lemma rinstId_sort32 {m_sort40 : nat} : @ren_sort32 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort32 (id _)) instId_sort32).

Qed.

Lemma rinstId_sort33 {m_sort40 : nat} : @ren_sort33 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort33 (id _)) instId_sort33).

Qed.

Lemma rinstId_sort34 {m_sort40 : nat} : @ren_sort34 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort34 (id _)) instId_sort34).

Qed.

Lemma rinstId_sort35 {m_sort40 : nat} : @ren_sort35 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort35 (id _)) instId_sort35).

Qed.

Lemma rinstId_sort36 {m_sort40 : nat} : @ren_sort36 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort36 (id _)) instId_sort36).

Qed.

Lemma rinstId_sort37 {m_sort40 : nat} : @ren_sort37 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort37 (id _)) instId_sort37).

Qed.

Lemma rinstId_sort38 {m_sort40 : nat} : @ren_sort38 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort38 (id _)) instId_sort38).

Qed.

Lemma rinstId_sort39 {m_sort40 : nat} : @ren_sort39 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort39 (id _)) instId_sort39).

Qed.

Lemma rinstId_sort40 {m_sort40 : nat} : @ren_sort40 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort40 (id _)) instId_sort40).

Qed.

Lemma rinstId_sort41 {m_sort40 : nat} : @ren_sort41 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort41 (id _)) instId_sort41).

Qed.

Lemma rinstId_sort42 {m_sort40 : nat} : @ren_sort42 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort42 (id _)) instId_sort42).

Qed.

Lemma rinstId_sort43 {m_sort40 : nat} : @ren_sort43 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort43 (id _)) instId_sort43).

Qed.

Lemma rinstId_sort44 {m_sort40 : nat} : @ren_sort44 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort44 (id _)) instId_sort44).

Qed.

Lemma rinstId_sort45 {m_sort40 : nat} : @ren_sort45 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort45 (id _)) instId_sort45).

Qed.

Lemma rinstId_sort46 {m_sort40 : nat} : @ren_sort46 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort46 (id _)) instId_sort46).

Qed.

Lemma rinstId_sort47 {m_sort40 : nat} : @ren_sort47 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort47 (id _)) instId_sort47).

Qed.

Lemma rinstId_sort48 {m_sort40 : nat} : @ren_sort48 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort48 (id _)) instId_sort48).

Qed.

Lemma rinstId_sort49 {m_sort40 : nat} : @ren_sort49 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort49 (id _)) instId_sort49).

Qed.

Lemma rinstId_sort50 {m_sort40 : nat} : @ren_sort50 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort50 (id _)) instId_sort50).

Qed.

Lemma rinstId_sort51 {m_sort40 : nat} : @ren_sort51 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort51 (id _)) instId_sort51).

Qed.

Lemma rinstId_sort52 {m_sort40 : nat} : @ren_sort52 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort52 (id _)) instId_sort52).

Qed.

Lemma rinstId_sort53 {m_sort40 : nat} : @ren_sort53 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort53 (id _)) instId_sort53).

Qed.

Lemma rinstId_sort54 {m_sort40 : nat} : @ren_sort54 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort54 (id _)) instId_sort54).

Qed.

Lemma rinstId_sort55 {m_sort40 : nat} : @ren_sort55 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort55 (id _)) instId_sort55).

Qed.

Lemma rinstId_sort56 {m_sort40 : nat} : @ren_sort56 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort56 (id _)) instId_sort56).

Qed.

Lemma rinstId_sort57 {m_sort40 : nat} : @ren_sort57 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort57 (id _)) instId_sort57).

Qed.

Lemma rinstId_sort58 {m_sort40 : nat} : @ren_sort58 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort58 (id _)) instId_sort58).

Qed.

Lemma rinstId_sort59 {m_sort40 : nat} : @ren_sort59 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort59 (id _)) instId_sort59).

Qed.

Lemma rinstId_sort60 {m_sort40 : nat} : @ren_sort60 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort60 (id _)) instId_sort60).

Qed.

Lemma rinstId_sort61 {m_sort40 : nat} : @ren_sort61 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort61 (id _)) instId_sort61).

Qed.

Lemma rinstId_sort62 {m_sort40 : nat} : @ren_sort62 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort62 (id _)) instId_sort62).

Qed.

Lemma rinstId_sort63 {m_sort40 : nat} : @ren_sort63 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort63 (id _)) instId_sort63).

Qed.

Lemma rinstId_sort64 {m_sort40 : nat} : @ren_sort64 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort64 (id _)) instId_sort64).

Qed.

Lemma rinstId_sort65 {m_sort40 : nat} : @ren_sort65 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort65 (id _)) instId_sort65).

Qed.

Lemma rinstId_sort66 {m_sort40 : nat} : @ren_sort66 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort66 (id _)) instId_sort66).

Qed.

Lemma rinstId_sort67 {m_sort40 : nat} : @ren_sort67 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort67 (id _)) instId_sort67).

Qed.

Lemma rinstId_sort68 {m_sort40 : nat} : @ren_sort68 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort68 (id _)) instId_sort68).

Qed.

Lemma rinstId_sort69 {m_sort40 : nat} : @ren_sort69 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort69 (id _)) instId_sort69).

Qed.

Lemma rinstId_sort70 {m_sort40 : nat} : @ren_sort70 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort70 (id _)) instId_sort70).

Qed.

Lemma rinstId_sort71 {m_sort40 : nat} : @ren_sort71 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort71 (id _)) instId_sort71).

Qed.

Lemma rinstId_sort72 {m_sort40 : nat} : @ren_sort72 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort72 (id _)) instId_sort72).

Qed.

Lemma rinstId_sort73 {m_sort40 : nat} : @ren_sort73 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort73 (id _)) instId_sort73).

Qed.

Lemma rinstId_sort74 {m_sort40 : nat} : @ren_sort74 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort74 (id _)) instId_sort74).

Qed.

Lemma rinstId_sort75 {m_sort40 : nat} : @ren_sort75 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort75 (id _)) instId_sort75).

Qed.

Lemma rinstId_sort76 {m_sort40 : nat} : @ren_sort76 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort76 (id _)) instId_sort76).

Qed.

Lemma rinstId_sort77 {m_sort40 : nat} : @ren_sort77 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort77 (id _)) instId_sort77).

Qed.

Lemma rinstId_sort78 {m_sort40 : nat} : @ren_sort78 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort78 (id _)) instId_sort78).

Qed.

Lemma rinstId_sort79 {m_sort40 : nat} : @ren_sort79 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort79 (id _)) instId_sort79).

Qed.

Lemma rinstId_sort80 {m_sort40 : nat} : @ren_sort80 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort80 (id _)) instId_sort80).

Qed.

Lemma rinstId_sort81 {m_sort40 : nat} : @ren_sort81 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort81 (id _)) instId_sort81).

Qed.

Lemma rinstId_sort82 {m_sort40 : nat} : @ren_sort82 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort82 (id _)) instId_sort82).

Qed.

Lemma rinstId_sort83 {m_sort40 : nat} : @ren_sort83 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort83 (id _)) instId_sort83).

Qed.

Lemma rinstId_sort84 {m_sort40 : nat} : @ren_sort84 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort84 (id _)) instId_sort84).

Qed.

Lemma rinstId_sort85 {m_sort40 : nat} : @ren_sort85 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort85 (id _)) instId_sort85).

Qed.

Lemma rinstId_sort86 {m_sort40 : nat} : @ren_sort86 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort86 (id _)) instId_sort86).

Qed.

Lemma rinstId_sort87 {m_sort40 : nat} : @ren_sort87 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort87 (id _)) instId_sort87).

Qed.

Lemma rinstId_sort88 {m_sort40 : nat} : @ren_sort88 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort88 (id _)) instId_sort88).

Qed.

Lemma rinstId_sort89 {m_sort40 : nat} : @ren_sort89 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort89 (id _)) instId_sort89).

Qed.

Lemma rinstId_sort90 {m_sort40 : nat} : @ren_sort90 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort90 (id _)) instId_sort90).

Qed.

Lemma rinstId_sort91 {m_sort40 : nat} : @ren_sort91 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort91 (id _)) instId_sort91).

Qed.

Lemma rinstId_sort92 {m_sort40 : nat} : @ren_sort92 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort92 (id _)) instId_sort92).

Qed.

Lemma rinstId_sort93 {m_sort40 : nat} : @ren_sort93 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort93 (id _)) instId_sort93).

Qed.

Lemma rinstId_sort94 {m_sort40 : nat} : @ren_sort94 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort94 (id _)) instId_sort94).

Qed.

Lemma rinstId_sort95 {m_sort40 : nat} : @ren_sort95 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort95 (id _)) instId_sort95).

Qed.

Lemma rinstId_sort96 {m_sort40 : nat} : @ren_sort96 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort96 (id _)) instId_sort96).

Qed.

Lemma rinstId_sort97 {m_sort40 : nat} : @ren_sort97 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort97 (id _)) instId_sort97).

Qed.

Lemma rinstId_sort98 {m_sort40 : nat} : @ren_sort98 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort98 (id _)) instId_sort98).

Qed.

Lemma rinstId_sort99 {m_sort40 : nat} : @ren_sort99 m_sort40 m_sort40 id = id.

Proof.
exact (eq_trans (rinstInst_sort99 (id _)) instId_sort99).

Qed.

Lemma varL_sort40 {m_sort40 : nat} {n_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 n_sort40) :
  funcomp (subst_sort40 sigma_sort40) (var_sort40 m_sort40) = sigma_sort40.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort40 {m_sort40 : nat} {n_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin n_sort40) :
  funcomp (ren_sort40 xi_sort40) (var_sort40 m_sort40) =
  funcomp (var_sort40 n_sort40) xi_sort40.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort0 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort0 zeta_sort40) (ren_sort0 xi_sort40) =
  ren_sort0 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort0 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort1 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort1 zeta_sort40) (ren_sort1 xi_sort40) =
  ren_sort1 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort1 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort2 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort2 zeta_sort40) (ren_sort2 xi_sort40) =
  ren_sort2 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort2 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort3 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort3 zeta_sort40) (ren_sort3 xi_sort40) =
  ren_sort3 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort3 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort4 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort4 zeta_sort40) (ren_sort4 xi_sort40) =
  ren_sort4 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort4 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort5 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort5 zeta_sort40) (ren_sort5 xi_sort40) =
  ren_sort5 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort5 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort6 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort6 zeta_sort40) (ren_sort6 xi_sort40) =
  ren_sort6 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort6 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort7 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort7 zeta_sort40) (ren_sort7 xi_sort40) =
  ren_sort7 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort7 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort8 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort8 zeta_sort40) (ren_sort8 xi_sort40) =
  ren_sort8 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort8 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort9 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort9 zeta_sort40) (ren_sort9 xi_sort40) =
  ren_sort9 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort9 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort10 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort10 zeta_sort40) (ren_sort10 xi_sort40) =
  ren_sort10 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort10 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort11 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort11 zeta_sort40) (ren_sort11 xi_sort40) =
  ren_sort11 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort11 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort12 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort12 zeta_sort40) (ren_sort12 xi_sort40) =
  ren_sort12 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort12 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort13 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort13 zeta_sort40) (ren_sort13 xi_sort40) =
  ren_sort13 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort13 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort14 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort14 zeta_sort40) (ren_sort14 xi_sort40) =
  ren_sort14 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort14 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort15 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort15 zeta_sort40) (ren_sort15 xi_sort40) =
  ren_sort15 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort15 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort16 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort16 zeta_sort40) (ren_sort16 xi_sort40) =
  ren_sort16 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort16 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort17 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort17 zeta_sort40) (ren_sort17 xi_sort40) =
  ren_sort17 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort17 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort18 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort18 zeta_sort40) (ren_sort18 xi_sort40) =
  ren_sort18 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort18 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort19 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort19 zeta_sort40) (ren_sort19 xi_sort40) =
  ren_sort19 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort19 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort20 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort20 zeta_sort40) (ren_sort20 xi_sort40) =
  ren_sort20 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort20 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort21 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort21 zeta_sort40) (ren_sort21 xi_sort40) =
  ren_sort21 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort21 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort22 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort22 zeta_sort40) (ren_sort22 xi_sort40) =
  ren_sort22 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort22 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort23 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort23 zeta_sort40) (ren_sort23 xi_sort40) =
  ren_sort23 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort23 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort24 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort24 zeta_sort40) (ren_sort24 xi_sort40) =
  ren_sort24 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort24 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort25 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort25 zeta_sort40) (ren_sort25 xi_sort40) =
  ren_sort25 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort25 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort26 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort26 zeta_sort40) (ren_sort26 xi_sort40) =
  ren_sort26 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort26 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort27 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort27 zeta_sort40) (ren_sort27 xi_sort40) =
  ren_sort27 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort27 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort28 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort28 zeta_sort40) (ren_sort28 xi_sort40) =
  ren_sort28 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort28 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort29 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort29 zeta_sort40) (ren_sort29 xi_sort40) =
  ren_sort29 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort29 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort30 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort30 zeta_sort40) (ren_sort30 xi_sort40) =
  ren_sort30 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort30 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort31 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort31 zeta_sort40) (ren_sort31 xi_sort40) =
  ren_sort31 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort31 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort32 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort32 zeta_sort40) (ren_sort32 xi_sort40) =
  ren_sort32 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort32 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort33 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort33 zeta_sort40) (ren_sort33 xi_sort40) =
  ren_sort33 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort33 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort34 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort34 zeta_sort40) (ren_sort34 xi_sort40) =
  ren_sort34 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort34 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort35 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort35 zeta_sort40) (ren_sort35 xi_sort40) =
  ren_sort35 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort35 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort36 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort36 zeta_sort40) (ren_sort36 xi_sort40) =
  ren_sort36 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort36 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort37 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort37 zeta_sort40) (ren_sort37 xi_sort40) =
  ren_sort37 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort37 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort38 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort38 zeta_sort40) (ren_sort38 xi_sort40) =
  ren_sort38 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort38 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort39 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort39 zeta_sort40) (ren_sort39 xi_sort40) =
  ren_sort39 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort39 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort40 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort40 zeta_sort40) (ren_sort40 xi_sort40) =
  ren_sort40 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort40 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort41 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort41 zeta_sort40) (ren_sort41 xi_sort40) =
  ren_sort41 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort41 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort42 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort42 zeta_sort40) (ren_sort42 xi_sort40) =
  ren_sort42 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort42 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort43 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort43 zeta_sort40) (ren_sort43 xi_sort40) =
  ren_sort43 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort43 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort44 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort44 zeta_sort40) (ren_sort44 xi_sort40) =
  ren_sort44 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort44 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort45 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort45 zeta_sort40) (ren_sort45 xi_sort40) =
  ren_sort45 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort45 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort46 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort46 zeta_sort40) (ren_sort46 xi_sort40) =
  ren_sort46 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort46 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort47 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort47 zeta_sort40) (ren_sort47 xi_sort40) =
  ren_sort47 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort47 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort48 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort48 zeta_sort40) (ren_sort48 xi_sort40) =
  ren_sort48 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort48 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort49 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort49 zeta_sort40) (ren_sort49 xi_sort40) =
  ren_sort49 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort49 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort50 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort50 zeta_sort40) (ren_sort50 xi_sort40) =
  ren_sort50 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort50 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort51 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort51 zeta_sort40) (ren_sort51 xi_sort40) =
  ren_sort51 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort51 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort52 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort52 zeta_sort40) (ren_sort52 xi_sort40) =
  ren_sort52 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort52 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort53 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort53 zeta_sort40) (ren_sort53 xi_sort40) =
  ren_sort53 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort53 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort54 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort54 zeta_sort40) (ren_sort54 xi_sort40) =
  ren_sort54 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort54 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort55 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort55 zeta_sort40) (ren_sort55 xi_sort40) =
  ren_sort55 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort55 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort56 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort56 zeta_sort40) (ren_sort56 xi_sort40) =
  ren_sort56 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort56 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort57 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort57 zeta_sort40) (ren_sort57 xi_sort40) =
  ren_sort57 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort57 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort58 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort58 zeta_sort40) (ren_sort58 xi_sort40) =
  ren_sort58 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort58 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort59 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort59 zeta_sort40) (ren_sort59 xi_sort40) =
  ren_sort59 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort59 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort60 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort60 zeta_sort40) (ren_sort60 xi_sort40) =
  ren_sort60 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort60 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort61 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort61 zeta_sort40) (ren_sort61 xi_sort40) =
  ren_sort61 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort61 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort62 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort62 zeta_sort40) (ren_sort62 xi_sort40) =
  ren_sort62 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort62 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort63 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort63 zeta_sort40) (ren_sort63 xi_sort40) =
  ren_sort63 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort63 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort64 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort64 zeta_sort40) (ren_sort64 xi_sort40) =
  ren_sort64 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort64 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort65 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort65 zeta_sort40) (ren_sort65 xi_sort40) =
  ren_sort65 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort65 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort66 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort66 zeta_sort40) (ren_sort66 xi_sort40) =
  ren_sort66 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort66 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort67 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort67 zeta_sort40) (ren_sort67 xi_sort40) =
  ren_sort67 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort67 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort68 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort68 zeta_sort40) (ren_sort68 xi_sort40) =
  ren_sort68 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort68 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort69 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort69 zeta_sort40) (ren_sort69 xi_sort40) =
  ren_sort69 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort69 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort70 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort70 zeta_sort40) (ren_sort70 xi_sort40) =
  ren_sort70 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort70 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort71 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort71 zeta_sort40) (ren_sort71 xi_sort40) =
  ren_sort71 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort71 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort72 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort72 zeta_sort40) (ren_sort72 xi_sort40) =
  ren_sort72 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort72 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort73 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort73 zeta_sort40) (ren_sort73 xi_sort40) =
  ren_sort73 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort73 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort74 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort74 zeta_sort40) (ren_sort74 xi_sort40) =
  ren_sort74 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort74 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort75 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort75 zeta_sort40) (ren_sort75 xi_sort40) =
  ren_sort75 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort75 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort76 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort76 zeta_sort40) (ren_sort76 xi_sort40) =
  ren_sort76 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort76 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort77 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort77 zeta_sort40) (ren_sort77 xi_sort40) =
  ren_sort77 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort77 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort78 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort78 zeta_sort40) (ren_sort78 xi_sort40) =
  ren_sort78 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort78 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort79 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort79 zeta_sort40) (ren_sort79 xi_sort40) =
  ren_sort79 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort79 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort80 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort80 zeta_sort40) (ren_sort80 xi_sort40) =
  ren_sort80 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort80 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort81 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort81 zeta_sort40) (ren_sort81 xi_sort40) =
  ren_sort81 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort81 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort82 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort82 zeta_sort40) (ren_sort82 xi_sort40) =
  ren_sort82 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort82 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort83 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort83 zeta_sort40) (ren_sort83 xi_sort40) =
  ren_sort83 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort83 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort84 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort84 zeta_sort40) (ren_sort84 xi_sort40) =
  ren_sort84 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort84 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort85 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort85 zeta_sort40) (ren_sort85 xi_sort40) =
  ren_sort85 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort85 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort86 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort86 zeta_sort40) (ren_sort86 xi_sort40) =
  ren_sort86 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort86 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort87 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort87 zeta_sort40) (ren_sort87 xi_sort40) =
  ren_sort87 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort87 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort88 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort88 zeta_sort40) (ren_sort88 xi_sort40) =
  ren_sort88 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort88 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort89 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort89 zeta_sort40) (ren_sort89 xi_sort40) =
  ren_sort89 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort89 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort90 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort90 zeta_sort40) (ren_sort90 xi_sort40) =
  ren_sort90 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort90 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort91 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort91 zeta_sort40) (ren_sort91 xi_sort40) =
  ren_sort91 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort91 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort92 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort92 zeta_sort40) (ren_sort92 xi_sort40) =
  ren_sort92 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort92 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort93 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort93 zeta_sort40) (ren_sort93 xi_sort40) =
  ren_sort93 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort93 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort94 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort94 zeta_sort40) (ren_sort94 xi_sort40) =
  ren_sort94 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort94 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort95 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort95 zeta_sort40) (ren_sort95 xi_sort40) =
  ren_sort95 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort95 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort96 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort96 zeta_sort40) (ren_sort96 xi_sort40) =
  ren_sort96 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort96 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort97 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort97 zeta_sort40) (ren_sort97 xi_sort40) =
  ren_sort97 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort97 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort98 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort98 zeta_sort40) (ren_sort98 xi_sort40) =
  ren_sort98 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort98 xi_sort40 zeta_sort40 n)).

Qed.

Lemma renRen'_sort99 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort99 zeta_sort40) (ren_sort99 xi_sort40) =
  ren_sort99 (funcomp zeta_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort99 xi_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort0 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort0 zeta_sort40) (subst_sort0 sigma_sort40) =
  subst_sort0 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort0 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort1 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort1 zeta_sort40) (subst_sort1 sigma_sort40) =
  subst_sort1 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort1 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort2 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort2 zeta_sort40) (subst_sort2 sigma_sort40) =
  subst_sort2 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort2 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort3 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort3 zeta_sort40) (subst_sort3 sigma_sort40) =
  subst_sort3 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort3 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort4 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort4 zeta_sort40) (subst_sort4 sigma_sort40) =
  subst_sort4 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort4 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort5 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort5 zeta_sort40) (subst_sort5 sigma_sort40) =
  subst_sort5 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort5 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort6 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort6 zeta_sort40) (subst_sort6 sigma_sort40) =
  subst_sort6 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort6 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort7 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort7 zeta_sort40) (subst_sort7 sigma_sort40) =
  subst_sort7 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort7 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort8 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort8 zeta_sort40) (subst_sort8 sigma_sort40) =
  subst_sort8 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort8 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort9 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort9 zeta_sort40) (subst_sort9 sigma_sort40) =
  subst_sort9 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort9 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort10 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort10 zeta_sort40) (subst_sort10 sigma_sort40) =
  subst_sort10 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort10 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort11 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort11 zeta_sort40) (subst_sort11 sigma_sort40) =
  subst_sort11 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort11 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort12 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort12 zeta_sort40) (subst_sort12 sigma_sort40) =
  subst_sort12 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort12 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort13 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort13 zeta_sort40) (subst_sort13 sigma_sort40) =
  subst_sort13 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort13 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort14 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort14 zeta_sort40) (subst_sort14 sigma_sort40) =
  subst_sort14 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort14 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort15 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort15 zeta_sort40) (subst_sort15 sigma_sort40) =
  subst_sort15 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort15 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort16 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort16 zeta_sort40) (subst_sort16 sigma_sort40) =
  subst_sort16 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort16 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort17 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort17 zeta_sort40) (subst_sort17 sigma_sort40) =
  subst_sort17 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort17 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort18 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort18 zeta_sort40) (subst_sort18 sigma_sort40) =
  subst_sort18 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort18 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort19 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort19 zeta_sort40) (subst_sort19 sigma_sort40) =
  subst_sort19 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort19 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort20 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort20 zeta_sort40) (subst_sort20 sigma_sort40) =
  subst_sort20 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort20 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort21 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort21 zeta_sort40) (subst_sort21 sigma_sort40) =
  subst_sort21 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort21 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort22 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort22 zeta_sort40) (subst_sort22 sigma_sort40) =
  subst_sort22 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort22 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort23 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort23 zeta_sort40) (subst_sort23 sigma_sort40) =
  subst_sort23 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort23 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort24 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort24 zeta_sort40) (subst_sort24 sigma_sort40) =
  subst_sort24 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort24 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort25 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort25 zeta_sort40) (subst_sort25 sigma_sort40) =
  subst_sort25 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort25 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort26 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort26 zeta_sort40) (subst_sort26 sigma_sort40) =
  subst_sort26 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort26 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort27 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort27 zeta_sort40) (subst_sort27 sigma_sort40) =
  subst_sort27 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort27 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort28 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort28 zeta_sort40) (subst_sort28 sigma_sort40) =
  subst_sort28 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort28 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort29 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort29 zeta_sort40) (subst_sort29 sigma_sort40) =
  subst_sort29 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort29 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort30 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort30 zeta_sort40) (subst_sort30 sigma_sort40) =
  subst_sort30 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort30 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort31 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort31 zeta_sort40) (subst_sort31 sigma_sort40) =
  subst_sort31 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort31 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort32 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort32 zeta_sort40) (subst_sort32 sigma_sort40) =
  subst_sort32 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort32 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort33 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort33 zeta_sort40) (subst_sort33 sigma_sort40) =
  subst_sort33 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort33 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort34 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort34 zeta_sort40) (subst_sort34 sigma_sort40) =
  subst_sort34 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort34 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort35 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort35 zeta_sort40) (subst_sort35 sigma_sort40) =
  subst_sort35 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort35 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort36 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort36 zeta_sort40) (subst_sort36 sigma_sort40) =
  subst_sort36 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort36 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort37 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort37 zeta_sort40) (subst_sort37 sigma_sort40) =
  subst_sort37 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort37 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort38 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort38 zeta_sort40) (subst_sort38 sigma_sort40) =
  subst_sort38 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort38 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort39 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort39 zeta_sort40) (subst_sort39 sigma_sort40) =
  subst_sort39 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort39 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort40 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort40 zeta_sort40) (subst_sort40 sigma_sort40) =
  subst_sort40 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort40 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort41 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort41 zeta_sort40) (subst_sort41 sigma_sort40) =
  subst_sort41 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort41 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort42 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort42 zeta_sort40) (subst_sort42 sigma_sort40) =
  subst_sort42 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort42 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort43 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort43 zeta_sort40) (subst_sort43 sigma_sort40) =
  subst_sort43 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort43 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort44 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort44 zeta_sort40) (subst_sort44 sigma_sort40) =
  subst_sort44 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort44 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort45 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort45 zeta_sort40) (subst_sort45 sigma_sort40) =
  subst_sort45 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort45 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort46 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort46 zeta_sort40) (subst_sort46 sigma_sort40) =
  subst_sort46 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort46 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort47 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort47 zeta_sort40) (subst_sort47 sigma_sort40) =
  subst_sort47 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort47 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort48 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort48 zeta_sort40) (subst_sort48 sigma_sort40) =
  subst_sort48 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort48 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort49 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort49 zeta_sort40) (subst_sort49 sigma_sort40) =
  subst_sort49 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort49 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort50 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort50 zeta_sort40) (subst_sort50 sigma_sort40) =
  subst_sort50 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort50 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort51 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort51 zeta_sort40) (subst_sort51 sigma_sort40) =
  subst_sort51 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort51 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort52 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort52 zeta_sort40) (subst_sort52 sigma_sort40) =
  subst_sort52 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort52 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort53 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort53 zeta_sort40) (subst_sort53 sigma_sort40) =
  subst_sort53 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort53 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort54 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort54 zeta_sort40) (subst_sort54 sigma_sort40) =
  subst_sort54 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort54 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort55 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort55 zeta_sort40) (subst_sort55 sigma_sort40) =
  subst_sort55 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort55 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort56 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort56 zeta_sort40) (subst_sort56 sigma_sort40) =
  subst_sort56 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort56 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort57 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort57 zeta_sort40) (subst_sort57 sigma_sort40) =
  subst_sort57 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort57 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort58 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort58 zeta_sort40) (subst_sort58 sigma_sort40) =
  subst_sort58 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort58 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort59 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort59 zeta_sort40) (subst_sort59 sigma_sort40) =
  subst_sort59 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort59 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort60 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort60 zeta_sort40) (subst_sort60 sigma_sort40) =
  subst_sort60 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort60 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort61 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort61 zeta_sort40) (subst_sort61 sigma_sort40) =
  subst_sort61 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort61 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort62 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort62 zeta_sort40) (subst_sort62 sigma_sort40) =
  subst_sort62 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort62 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort63 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort63 zeta_sort40) (subst_sort63 sigma_sort40) =
  subst_sort63 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort63 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort64 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort64 zeta_sort40) (subst_sort64 sigma_sort40) =
  subst_sort64 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort64 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort65 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort65 zeta_sort40) (subst_sort65 sigma_sort40) =
  subst_sort65 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort65 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort66 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort66 zeta_sort40) (subst_sort66 sigma_sort40) =
  subst_sort66 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort66 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort67 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort67 zeta_sort40) (subst_sort67 sigma_sort40) =
  subst_sort67 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort67 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort68 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort68 zeta_sort40) (subst_sort68 sigma_sort40) =
  subst_sort68 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort68 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort69 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort69 zeta_sort40) (subst_sort69 sigma_sort40) =
  subst_sort69 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort69 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort70 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort70 zeta_sort40) (subst_sort70 sigma_sort40) =
  subst_sort70 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort70 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort71 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort71 zeta_sort40) (subst_sort71 sigma_sort40) =
  subst_sort71 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort71 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort72 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort72 zeta_sort40) (subst_sort72 sigma_sort40) =
  subst_sort72 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort72 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort73 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort73 zeta_sort40) (subst_sort73 sigma_sort40) =
  subst_sort73 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort73 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort74 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort74 zeta_sort40) (subst_sort74 sigma_sort40) =
  subst_sort74 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort74 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort75 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort75 zeta_sort40) (subst_sort75 sigma_sort40) =
  subst_sort75 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort75 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort76 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort76 zeta_sort40) (subst_sort76 sigma_sort40) =
  subst_sort76 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort76 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort77 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort77 zeta_sort40) (subst_sort77 sigma_sort40) =
  subst_sort77 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort77 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort78 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort78 zeta_sort40) (subst_sort78 sigma_sort40) =
  subst_sort78 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort78 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort79 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort79 zeta_sort40) (subst_sort79 sigma_sort40) =
  subst_sort79 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort79 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort80 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort80 zeta_sort40) (subst_sort80 sigma_sort40) =
  subst_sort80 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort80 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort81 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort81 zeta_sort40) (subst_sort81 sigma_sort40) =
  subst_sort81 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort81 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort82 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort82 zeta_sort40) (subst_sort82 sigma_sort40) =
  subst_sort82 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort82 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort83 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort83 zeta_sort40) (subst_sort83 sigma_sort40) =
  subst_sort83 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort83 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort84 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort84 zeta_sort40) (subst_sort84 sigma_sort40) =
  subst_sort84 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort84 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort85 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort85 zeta_sort40) (subst_sort85 sigma_sort40) =
  subst_sort85 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort85 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort86 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort86 zeta_sort40) (subst_sort86 sigma_sort40) =
  subst_sort86 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort86 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort87 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort87 zeta_sort40) (subst_sort87 sigma_sort40) =
  subst_sort87 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort87 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort88 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort88 zeta_sort40) (subst_sort88 sigma_sort40) =
  subst_sort88 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort88 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort89 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort89 zeta_sort40) (subst_sort89 sigma_sort40) =
  subst_sort89 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort89 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort90 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort90 zeta_sort40) (subst_sort90 sigma_sort40) =
  subst_sort90 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort90 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort91 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort91 zeta_sort40) (subst_sort91 sigma_sort40) =
  subst_sort91 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort91 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort92 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort92 zeta_sort40) (subst_sort92 sigma_sort40) =
  subst_sort92 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort92 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort93 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort93 zeta_sort40) (subst_sort93 sigma_sort40) =
  subst_sort93 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort93 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort94 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort94 zeta_sort40) (subst_sort94 sigma_sort40) =
  subst_sort94 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort94 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort95 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort95 zeta_sort40) (subst_sort95 sigma_sort40) =
  subst_sort95 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort95 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort96 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort96 zeta_sort40) (subst_sort96 sigma_sort40) =
  subst_sort96 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort96 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort97 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort97 zeta_sort40) (subst_sort97 sigma_sort40) =
  subst_sort97 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort97 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort98 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort98 zeta_sort40) (subst_sort98 sigma_sort40) =
  subst_sort98 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort98 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma compRen'_sort99 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (zeta_sort40 : fin k_sort40 -> fin l_sort40) :
  funcomp (ren_sort99 zeta_sort40) (subst_sort99 sigma_sort40) =
  subst_sort99 (funcomp (ren_sort40 zeta_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort99 sigma_sort40 zeta_sort40 n)).

Qed.

Lemma renComp'_sort0 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort0 tau_sort40) (ren_sort0 xi_sort40) =
  subst_sort0 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort0 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort1 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort1 tau_sort40) (ren_sort1 xi_sort40) =
  subst_sort1 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort1 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort2 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort2 tau_sort40) (ren_sort2 xi_sort40) =
  subst_sort2 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort2 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort3 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort3 tau_sort40) (ren_sort3 xi_sort40) =
  subst_sort3 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort3 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort4 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort4 tau_sort40) (ren_sort4 xi_sort40) =
  subst_sort4 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort4 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort5 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort5 tau_sort40) (ren_sort5 xi_sort40) =
  subst_sort5 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort5 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort6 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort6 tau_sort40) (ren_sort6 xi_sort40) =
  subst_sort6 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort6 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort7 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort7 tau_sort40) (ren_sort7 xi_sort40) =
  subst_sort7 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort7 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort8 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort8 tau_sort40) (ren_sort8 xi_sort40) =
  subst_sort8 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort8 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort9 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort9 tau_sort40) (ren_sort9 xi_sort40) =
  subst_sort9 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort9 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort10 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort10 tau_sort40) (ren_sort10 xi_sort40) =
  subst_sort10 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort10 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort11 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort11 tau_sort40) (ren_sort11 xi_sort40) =
  subst_sort11 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort11 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort12 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort12 tau_sort40) (ren_sort12 xi_sort40) =
  subst_sort12 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort12 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort13 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort13 tau_sort40) (ren_sort13 xi_sort40) =
  subst_sort13 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort13 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort14 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort14 tau_sort40) (ren_sort14 xi_sort40) =
  subst_sort14 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort14 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort15 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort15 tau_sort40) (ren_sort15 xi_sort40) =
  subst_sort15 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort15 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort16 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort16 tau_sort40) (ren_sort16 xi_sort40) =
  subst_sort16 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort16 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort17 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort17 tau_sort40) (ren_sort17 xi_sort40) =
  subst_sort17 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort17 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort18 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort18 tau_sort40) (ren_sort18 xi_sort40) =
  subst_sort18 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort18 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort19 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort19 tau_sort40) (ren_sort19 xi_sort40) =
  subst_sort19 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort19 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort20 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort20 tau_sort40) (ren_sort20 xi_sort40) =
  subst_sort20 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort20 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort21 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort21 tau_sort40) (ren_sort21 xi_sort40) =
  subst_sort21 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort21 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort22 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort22 tau_sort40) (ren_sort22 xi_sort40) =
  subst_sort22 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort22 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort23 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort23 tau_sort40) (ren_sort23 xi_sort40) =
  subst_sort23 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort23 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort24 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort24 tau_sort40) (ren_sort24 xi_sort40) =
  subst_sort24 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort24 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort25 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort25 tau_sort40) (ren_sort25 xi_sort40) =
  subst_sort25 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort25 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort26 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort26 tau_sort40) (ren_sort26 xi_sort40) =
  subst_sort26 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort26 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort27 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort27 tau_sort40) (ren_sort27 xi_sort40) =
  subst_sort27 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort27 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort28 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort28 tau_sort40) (ren_sort28 xi_sort40) =
  subst_sort28 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort28 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort29 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort29 tau_sort40) (ren_sort29 xi_sort40) =
  subst_sort29 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort29 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort30 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort30 tau_sort40) (ren_sort30 xi_sort40) =
  subst_sort30 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort30 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort31 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort31 tau_sort40) (ren_sort31 xi_sort40) =
  subst_sort31 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort31 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort32 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort32 tau_sort40) (ren_sort32 xi_sort40) =
  subst_sort32 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort32 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort33 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort33 tau_sort40) (ren_sort33 xi_sort40) =
  subst_sort33 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort33 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort34 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort34 tau_sort40) (ren_sort34 xi_sort40) =
  subst_sort34 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort34 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort35 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort35 tau_sort40) (ren_sort35 xi_sort40) =
  subst_sort35 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort35 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort36 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort36 tau_sort40) (ren_sort36 xi_sort40) =
  subst_sort36 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort36 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort37 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort37 tau_sort40) (ren_sort37 xi_sort40) =
  subst_sort37 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort37 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort38 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort38 tau_sort40) (ren_sort38 xi_sort40) =
  subst_sort38 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort38 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort39 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort39 tau_sort40) (ren_sort39 xi_sort40) =
  subst_sort39 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort39 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort40 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort40 tau_sort40) (ren_sort40 xi_sort40) =
  subst_sort40 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort40 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort41 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort41 tau_sort40) (ren_sort41 xi_sort40) =
  subst_sort41 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort41 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort42 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort42 tau_sort40) (ren_sort42 xi_sort40) =
  subst_sort42 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort42 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort43 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort43 tau_sort40) (ren_sort43 xi_sort40) =
  subst_sort43 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort43 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort44 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort44 tau_sort40) (ren_sort44 xi_sort40) =
  subst_sort44 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort44 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort45 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort45 tau_sort40) (ren_sort45 xi_sort40) =
  subst_sort45 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort45 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort46 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort46 tau_sort40) (ren_sort46 xi_sort40) =
  subst_sort46 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort46 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort47 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort47 tau_sort40) (ren_sort47 xi_sort40) =
  subst_sort47 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort47 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort48 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort48 tau_sort40) (ren_sort48 xi_sort40) =
  subst_sort48 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort48 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort49 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort49 tau_sort40) (ren_sort49 xi_sort40) =
  subst_sort49 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort49 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort50 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort50 tau_sort40) (ren_sort50 xi_sort40) =
  subst_sort50 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort50 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort51 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort51 tau_sort40) (ren_sort51 xi_sort40) =
  subst_sort51 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort51 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort52 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort52 tau_sort40) (ren_sort52 xi_sort40) =
  subst_sort52 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort52 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort53 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort53 tau_sort40) (ren_sort53 xi_sort40) =
  subst_sort53 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort53 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort54 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort54 tau_sort40) (ren_sort54 xi_sort40) =
  subst_sort54 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort54 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort55 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort55 tau_sort40) (ren_sort55 xi_sort40) =
  subst_sort55 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort55 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort56 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort56 tau_sort40) (ren_sort56 xi_sort40) =
  subst_sort56 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort56 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort57 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort57 tau_sort40) (ren_sort57 xi_sort40) =
  subst_sort57 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort57 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort58 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort58 tau_sort40) (ren_sort58 xi_sort40) =
  subst_sort58 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort58 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort59 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort59 tau_sort40) (ren_sort59 xi_sort40) =
  subst_sort59 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort59 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort60 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort60 tau_sort40) (ren_sort60 xi_sort40) =
  subst_sort60 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort60 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort61 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort61 tau_sort40) (ren_sort61 xi_sort40) =
  subst_sort61 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort61 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort62 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort62 tau_sort40) (ren_sort62 xi_sort40) =
  subst_sort62 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort62 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort63 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort63 tau_sort40) (ren_sort63 xi_sort40) =
  subst_sort63 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort63 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort64 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort64 tau_sort40) (ren_sort64 xi_sort40) =
  subst_sort64 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort64 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort65 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort65 tau_sort40) (ren_sort65 xi_sort40) =
  subst_sort65 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort65 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort66 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort66 tau_sort40) (ren_sort66 xi_sort40) =
  subst_sort66 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort66 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort67 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort67 tau_sort40) (ren_sort67 xi_sort40) =
  subst_sort67 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort67 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort68 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort68 tau_sort40) (ren_sort68 xi_sort40) =
  subst_sort68 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort68 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort69 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort69 tau_sort40) (ren_sort69 xi_sort40) =
  subst_sort69 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort69 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort70 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort70 tau_sort40) (ren_sort70 xi_sort40) =
  subst_sort70 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort70 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort71 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort71 tau_sort40) (ren_sort71 xi_sort40) =
  subst_sort71 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort71 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort72 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort72 tau_sort40) (ren_sort72 xi_sort40) =
  subst_sort72 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort72 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort73 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort73 tau_sort40) (ren_sort73 xi_sort40) =
  subst_sort73 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort73 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort74 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort74 tau_sort40) (ren_sort74 xi_sort40) =
  subst_sort74 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort74 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort75 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort75 tau_sort40) (ren_sort75 xi_sort40) =
  subst_sort75 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort75 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort76 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort76 tau_sort40) (ren_sort76 xi_sort40) =
  subst_sort76 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort76 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort77 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort77 tau_sort40) (ren_sort77 xi_sort40) =
  subst_sort77 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort77 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort78 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort78 tau_sort40) (ren_sort78 xi_sort40) =
  subst_sort78 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort78 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort79 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort79 tau_sort40) (ren_sort79 xi_sort40) =
  subst_sort79 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort79 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort80 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort80 tau_sort40) (ren_sort80 xi_sort40) =
  subst_sort80 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort80 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort81 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort81 tau_sort40) (ren_sort81 xi_sort40) =
  subst_sort81 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort81 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort82 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort82 tau_sort40) (ren_sort82 xi_sort40) =
  subst_sort82 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort82 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort83 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort83 tau_sort40) (ren_sort83 xi_sort40) =
  subst_sort83 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort83 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort84 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort84 tau_sort40) (ren_sort84 xi_sort40) =
  subst_sort84 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort84 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort85 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort85 tau_sort40) (ren_sort85 xi_sort40) =
  subst_sort85 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort85 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort86 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort86 tau_sort40) (ren_sort86 xi_sort40) =
  subst_sort86 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort86 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort87 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort87 tau_sort40) (ren_sort87 xi_sort40) =
  subst_sort87 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort87 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort88 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort88 tau_sort40) (ren_sort88 xi_sort40) =
  subst_sort88 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort88 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort89 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort89 tau_sort40) (ren_sort89 xi_sort40) =
  subst_sort89 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort89 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort90 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort90 tau_sort40) (ren_sort90 xi_sort40) =
  subst_sort90 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort90 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort91 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort91 tau_sort40) (ren_sort91 xi_sort40) =
  subst_sort91 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort91 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort92 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort92 tau_sort40) (ren_sort92 xi_sort40) =
  subst_sort92 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort92 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort93 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort93 tau_sort40) (ren_sort93 xi_sort40) =
  subst_sort93 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort93 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort94 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort94 tau_sort40) (ren_sort94 xi_sort40) =
  subst_sort94 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort94 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort95 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort95 tau_sort40) (ren_sort95 xi_sort40) =
  subst_sort95 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort95 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort96 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort96 tau_sort40) (ren_sort96 xi_sort40) =
  subst_sort96 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort96 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort97 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort97 tau_sort40) (ren_sort97 xi_sort40) =
  subst_sort97 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort97 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort98 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort98 tau_sort40) (ren_sort98 xi_sort40) =
  subst_sort98 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort98 xi_sort40 tau_sort40 n)).

Qed.

Lemma renComp'_sort99 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (xi_sort40 : fin m_sort40 -> fin k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort99 tau_sort40) (ren_sort99 xi_sort40) =
  subst_sort99 (funcomp tau_sort40 xi_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort99 xi_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort0 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort0 tau_sort40) (subst_sort0 sigma_sort40) =
  subst_sort0 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort0 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort1 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort1 tau_sort40) (subst_sort1 sigma_sort40) =
  subst_sort1 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort1 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort2 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort2 tau_sort40) (subst_sort2 sigma_sort40) =
  subst_sort2 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort2 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort3 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort3 tau_sort40) (subst_sort3 sigma_sort40) =
  subst_sort3 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort3 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort4 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort4 tau_sort40) (subst_sort4 sigma_sort40) =
  subst_sort4 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort4 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort5 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort5 tau_sort40) (subst_sort5 sigma_sort40) =
  subst_sort5 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort5 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort6 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort6 tau_sort40) (subst_sort6 sigma_sort40) =
  subst_sort6 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort6 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort7 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort7 tau_sort40) (subst_sort7 sigma_sort40) =
  subst_sort7 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort7 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort8 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort8 tau_sort40) (subst_sort8 sigma_sort40) =
  subst_sort8 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort8 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort9 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort9 tau_sort40) (subst_sort9 sigma_sort40) =
  subst_sort9 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort9 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort10 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort10 tau_sort40) (subst_sort10 sigma_sort40) =
  subst_sort10 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort10 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort11 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort11 tau_sort40) (subst_sort11 sigma_sort40) =
  subst_sort11 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort11 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort12 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort12 tau_sort40) (subst_sort12 sigma_sort40) =
  subst_sort12 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort12 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort13 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort13 tau_sort40) (subst_sort13 sigma_sort40) =
  subst_sort13 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort13 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort14 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort14 tau_sort40) (subst_sort14 sigma_sort40) =
  subst_sort14 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort14 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort15 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort15 tau_sort40) (subst_sort15 sigma_sort40) =
  subst_sort15 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort15 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort16 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort16 tau_sort40) (subst_sort16 sigma_sort40) =
  subst_sort16 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort16 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort17 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort17 tau_sort40) (subst_sort17 sigma_sort40) =
  subst_sort17 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort17 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort18 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort18 tau_sort40) (subst_sort18 sigma_sort40) =
  subst_sort18 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort18 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort19 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort19 tau_sort40) (subst_sort19 sigma_sort40) =
  subst_sort19 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort19 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort20 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort20 tau_sort40) (subst_sort20 sigma_sort40) =
  subst_sort20 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort20 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort21 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort21 tau_sort40) (subst_sort21 sigma_sort40) =
  subst_sort21 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort21 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort22 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort22 tau_sort40) (subst_sort22 sigma_sort40) =
  subst_sort22 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort22 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort23 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort23 tau_sort40) (subst_sort23 sigma_sort40) =
  subst_sort23 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort23 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort24 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort24 tau_sort40) (subst_sort24 sigma_sort40) =
  subst_sort24 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort24 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort25 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort25 tau_sort40) (subst_sort25 sigma_sort40) =
  subst_sort25 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort25 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort26 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort26 tau_sort40) (subst_sort26 sigma_sort40) =
  subst_sort26 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort26 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort27 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort27 tau_sort40) (subst_sort27 sigma_sort40) =
  subst_sort27 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort27 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort28 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort28 tau_sort40) (subst_sort28 sigma_sort40) =
  subst_sort28 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort28 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort29 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort29 tau_sort40) (subst_sort29 sigma_sort40) =
  subst_sort29 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort29 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort30 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort30 tau_sort40) (subst_sort30 sigma_sort40) =
  subst_sort30 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort30 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort31 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort31 tau_sort40) (subst_sort31 sigma_sort40) =
  subst_sort31 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort31 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort32 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort32 tau_sort40) (subst_sort32 sigma_sort40) =
  subst_sort32 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort32 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort33 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort33 tau_sort40) (subst_sort33 sigma_sort40) =
  subst_sort33 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort33 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort34 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort34 tau_sort40) (subst_sort34 sigma_sort40) =
  subst_sort34 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort34 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort35 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort35 tau_sort40) (subst_sort35 sigma_sort40) =
  subst_sort35 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort35 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort36 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort36 tau_sort40) (subst_sort36 sigma_sort40) =
  subst_sort36 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort36 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort37 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort37 tau_sort40) (subst_sort37 sigma_sort40) =
  subst_sort37 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort37 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort38 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort38 tau_sort40) (subst_sort38 sigma_sort40) =
  subst_sort38 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort38 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort39 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort39 tau_sort40) (subst_sort39 sigma_sort40) =
  subst_sort39 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort39 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort40 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort40 tau_sort40) (subst_sort40 sigma_sort40) =
  subst_sort40 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort40 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort41 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort41 tau_sort40) (subst_sort41 sigma_sort40) =
  subst_sort41 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort41 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort42 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort42 tau_sort40) (subst_sort42 sigma_sort40) =
  subst_sort42 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort42 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort43 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort43 tau_sort40) (subst_sort43 sigma_sort40) =
  subst_sort43 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort43 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort44 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort44 tau_sort40) (subst_sort44 sigma_sort40) =
  subst_sort44 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort44 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort45 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort45 tau_sort40) (subst_sort45 sigma_sort40) =
  subst_sort45 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort45 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort46 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort46 tau_sort40) (subst_sort46 sigma_sort40) =
  subst_sort46 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort46 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort47 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort47 tau_sort40) (subst_sort47 sigma_sort40) =
  subst_sort47 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort47 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort48 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort48 tau_sort40) (subst_sort48 sigma_sort40) =
  subst_sort48 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort48 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort49 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort49 tau_sort40) (subst_sort49 sigma_sort40) =
  subst_sort49 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort49 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort50 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort50 tau_sort40) (subst_sort50 sigma_sort40) =
  subst_sort50 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort50 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort51 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort51 tau_sort40) (subst_sort51 sigma_sort40) =
  subst_sort51 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort51 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort52 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort52 tau_sort40) (subst_sort52 sigma_sort40) =
  subst_sort52 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort52 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort53 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort53 tau_sort40) (subst_sort53 sigma_sort40) =
  subst_sort53 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort53 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort54 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort54 tau_sort40) (subst_sort54 sigma_sort40) =
  subst_sort54 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort54 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort55 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort55 tau_sort40) (subst_sort55 sigma_sort40) =
  subst_sort55 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort55 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort56 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort56 tau_sort40) (subst_sort56 sigma_sort40) =
  subst_sort56 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort56 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort57 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort57 tau_sort40) (subst_sort57 sigma_sort40) =
  subst_sort57 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort57 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort58 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort58 tau_sort40) (subst_sort58 sigma_sort40) =
  subst_sort58 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort58 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort59 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort59 tau_sort40) (subst_sort59 sigma_sort40) =
  subst_sort59 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort59 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort60 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort60 tau_sort40) (subst_sort60 sigma_sort40) =
  subst_sort60 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort60 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort61 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort61 tau_sort40) (subst_sort61 sigma_sort40) =
  subst_sort61 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort61 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort62 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort62 tau_sort40) (subst_sort62 sigma_sort40) =
  subst_sort62 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort62 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort63 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort63 tau_sort40) (subst_sort63 sigma_sort40) =
  subst_sort63 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort63 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort64 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort64 tau_sort40) (subst_sort64 sigma_sort40) =
  subst_sort64 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort64 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort65 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort65 tau_sort40) (subst_sort65 sigma_sort40) =
  subst_sort65 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort65 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort66 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort66 tau_sort40) (subst_sort66 sigma_sort40) =
  subst_sort66 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort66 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort67 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort67 tau_sort40) (subst_sort67 sigma_sort40) =
  subst_sort67 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort67 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort68 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort68 tau_sort40) (subst_sort68 sigma_sort40) =
  subst_sort68 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort68 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort69 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort69 tau_sort40) (subst_sort69 sigma_sort40) =
  subst_sort69 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort69 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort70 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort70 tau_sort40) (subst_sort70 sigma_sort40) =
  subst_sort70 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort70 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort71 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort71 tau_sort40) (subst_sort71 sigma_sort40) =
  subst_sort71 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort71 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort72 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort72 tau_sort40) (subst_sort72 sigma_sort40) =
  subst_sort72 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort72 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort73 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort73 tau_sort40) (subst_sort73 sigma_sort40) =
  subst_sort73 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort73 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort74 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort74 tau_sort40) (subst_sort74 sigma_sort40) =
  subst_sort74 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort74 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort75 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort75 tau_sort40) (subst_sort75 sigma_sort40) =
  subst_sort75 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort75 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort76 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort76 tau_sort40) (subst_sort76 sigma_sort40) =
  subst_sort76 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort76 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort77 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort77 tau_sort40) (subst_sort77 sigma_sort40) =
  subst_sort77 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort77 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort78 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort78 tau_sort40) (subst_sort78 sigma_sort40) =
  subst_sort78 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort78 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort79 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort79 tau_sort40) (subst_sort79 sigma_sort40) =
  subst_sort79 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort79 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort80 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort80 tau_sort40) (subst_sort80 sigma_sort40) =
  subst_sort80 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort80 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort81 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort81 tau_sort40) (subst_sort81 sigma_sort40) =
  subst_sort81 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort81 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort82 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort82 tau_sort40) (subst_sort82 sigma_sort40) =
  subst_sort82 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort82 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort83 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort83 tau_sort40) (subst_sort83 sigma_sort40) =
  subst_sort83 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort83 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort84 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort84 tau_sort40) (subst_sort84 sigma_sort40) =
  subst_sort84 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort84 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort85 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort85 tau_sort40) (subst_sort85 sigma_sort40) =
  subst_sort85 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort85 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort86 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort86 tau_sort40) (subst_sort86 sigma_sort40) =
  subst_sort86 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort86 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort87 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort87 tau_sort40) (subst_sort87 sigma_sort40) =
  subst_sort87 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort87 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort88 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort88 tau_sort40) (subst_sort88 sigma_sort40) =
  subst_sort88 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort88 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort89 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort89 tau_sort40) (subst_sort89 sigma_sort40) =
  subst_sort89 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort89 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort90 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort90 tau_sort40) (subst_sort90 sigma_sort40) =
  subst_sort90 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort90 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort91 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort91 tau_sort40) (subst_sort91 sigma_sort40) =
  subst_sort91 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort91 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort92 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort92 tau_sort40) (subst_sort92 sigma_sort40) =
  subst_sort92 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort92 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort93 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort93 tau_sort40) (subst_sort93 sigma_sort40) =
  subst_sort93 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort93 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort94 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort94 tau_sort40) (subst_sort94 sigma_sort40) =
  subst_sort94 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort94 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort95 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort95 tau_sort40) (subst_sort95 sigma_sort40) =
  subst_sort95 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort95 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort96 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort96 tau_sort40) (subst_sort96 sigma_sort40) =
  subst_sort96 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort96 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort97 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort97 tau_sort40) (subst_sort97 sigma_sort40) =
  subst_sort97 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort97 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort98 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort98 tau_sort40) (subst_sort98 sigma_sort40) =
  subst_sort98 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort98 sigma_sort40 tau_sort40 n)).

Qed.

Lemma compComp'_sort99 {k_sort40 : nat} {l_sort40 : nat} {m_sort40 : nat}
  (sigma_sort40 : fin m_sort40 -> sort40 k_sort40)
  (tau_sort40 : fin k_sort40 -> sort40 l_sort40) :
  funcomp (subst_sort99 tau_sort40) (subst_sort99 sigma_sort40) =
  subst_sort99 (funcomp (subst_sort40 tau_sort40) sigma_sort40).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort99 sigma_sort40 tau_sort40 n)).

Qed.
