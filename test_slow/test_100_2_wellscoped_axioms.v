Require Import core core_axioms fintype fintype_axioms.
Require Import test_100_2_wellscoped.

Lemma rinstInst_sort0 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort0 xi_sort88 = subst_sort0 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort0 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort1 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort1 xi_sort88 = subst_sort1 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort1 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort2 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort2 xi_sort88 = subst_sort2 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort2 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort3 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort3 xi_sort88 = subst_sort3 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort3 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort4 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort4 xi_sort88 = subst_sort4 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort4 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort5 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort5 xi_sort88 = subst_sort5 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort5 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort6 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort6 xi_sort88 = subst_sort6 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort6 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort7 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort7 xi_sort88 = subst_sort7 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort7 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort8 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort8 xi_sort88 = subst_sort8 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort8 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort9 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort9 xi_sort88 = subst_sort9 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort9 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort10 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort10 xi_sort88 =
  subst_sort10 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort10 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort11 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort11 xi_sort88 =
  subst_sort11 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort11 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort12 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort12 xi_sort88 =
  subst_sort12 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort12 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort13 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort13 xi_sort88 =
  subst_sort13 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort13 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort14 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort14 xi_sort88 =
  subst_sort14 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort14 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort15 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort15 xi_sort88 =
  subst_sort15 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort15 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort16 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort16 xi_sort88 =
  subst_sort16 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort16 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort17 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort17 xi_sort88 =
  subst_sort17 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort17 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort18 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort18 xi_sort88 =
  subst_sort18 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort18 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort19 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort19 xi_sort88 =
  subst_sort19 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort19 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort20 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort20 xi_sort88 =
  subst_sort20 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort20 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort21 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort21 xi_sort88 =
  subst_sort21 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort21 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort22 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort22 xi_sort88 =
  subst_sort22 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort22 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort23 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort23 xi_sort88 =
  subst_sort23 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort23 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort24 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort24 xi_sort88 =
  subst_sort24 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort24 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort25 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort25 xi_sort88 =
  subst_sort25 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort25 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort26 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort26 xi_sort88 =
  subst_sort26 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort26 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort27 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort27 xi_sort88 =
  subst_sort27 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort27 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort28 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort28 xi_sort88 =
  subst_sort28 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort28 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort29 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort29 xi_sort88 =
  subst_sort29 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort29 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort30 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort30 xi_sort88 =
  subst_sort30 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort30 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort31 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort31 xi_sort88 =
  subst_sort31 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort31 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort32 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort32 xi_sort88 =
  subst_sort32 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort32 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort33 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort33 xi_sort88 =
  subst_sort33 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort33 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort34 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort34 xi_sort88 =
  subst_sort34 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort34 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort35 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort35 xi_sort88 =
  subst_sort35 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort35 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort36 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort36 xi_sort88 =
  subst_sort36 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort36 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort37 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort37 xi_sort88 =
  subst_sort37 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort37 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort38 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort38 xi_sort88 =
  subst_sort38 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort38 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort39 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort39 xi_sort88 =
  subst_sort39 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort39 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort40 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort40 xi_sort88 =
  subst_sort40 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort40 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort41 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort41 xi_sort88 =
  subst_sort41 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort41 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort42 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort42 xi_sort88 =
  subst_sort42 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort42 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort43 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort43 xi_sort88 =
  subst_sort43 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort43 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort44 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort44 xi_sort88 =
  subst_sort44 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort44 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort45 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort45 xi_sort88 =
  subst_sort45 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort45 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort46 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort46 xi_sort88 =
  subst_sort46 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort46 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort47 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort47 xi_sort88 =
  subst_sort47 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort47 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort48 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort48 xi_sort88 =
  subst_sort48 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort48 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort49 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort49 xi_sort88 =
  subst_sort49 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort49 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort50 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort50 xi_sort88 =
  subst_sort50 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort50 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort51 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort51 xi_sort88 =
  subst_sort51 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort51 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort52 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort52 xi_sort88 =
  subst_sort52 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort52 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort53 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort53 xi_sort88 =
  subst_sort53 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort53 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort54 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort54 xi_sort88 =
  subst_sort54 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort54 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort55 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort55 xi_sort88 =
  subst_sort55 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort55 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort56 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort56 xi_sort88 =
  subst_sort56 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort56 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort57 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort57 xi_sort88 =
  subst_sort57 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort57 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort58 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort58 xi_sort88 =
  subst_sort58 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort58 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort59 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort59 xi_sort88 =
  subst_sort59 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort59 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort60 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort60 xi_sort88 =
  subst_sort60 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort60 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort61 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort61 xi_sort88 =
  subst_sort61 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort61 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort62 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort62 xi_sort88 =
  subst_sort62 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort62 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort63 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort63 xi_sort88 =
  subst_sort63 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort63 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort64 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort64 xi_sort88 =
  subst_sort64 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort64 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort65 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort65 xi_sort88 =
  subst_sort65 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort65 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort66 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort66 xi_sort88 =
  subst_sort66 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort66 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort67 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort67 xi_sort88 =
  subst_sort67 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort67 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort68 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort68 xi_sort88 =
  subst_sort68 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort68 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort69 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort69 xi_sort88 =
  subst_sort69 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort69 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort70 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort70 xi_sort88 =
  subst_sort70 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort70 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort71 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort71 xi_sort88 =
  subst_sort71 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort71 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort72 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort72 xi_sort88 =
  subst_sort72 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort72 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort73 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort73 xi_sort88 =
  subst_sort73 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort73 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort74 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort74 xi_sort88 =
  subst_sort74 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort74 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort75 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort75 xi_sort88 =
  subst_sort75 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort75 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort76 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort76 xi_sort88 =
  subst_sort76 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort76 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort77 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort77 xi_sort88 =
  subst_sort77 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort77 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort78 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort78 xi_sort88 =
  subst_sort78 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort78 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort79 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort79 xi_sort88 =
  subst_sort79 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort79 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort80 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort80 xi_sort88 =
  subst_sort80 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort80 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort81 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort81 xi_sort88 =
  subst_sort81 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort81 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort82 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort82 xi_sort88 =
  subst_sort82 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort82 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort83 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort83 xi_sort88 =
  subst_sort83 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort83 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort84 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort84 xi_sort88 =
  subst_sort84 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort84 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort85 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort85 xi_sort88 =
  subst_sort85 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort85 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort86 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort86 xi_sort88 =
  subst_sort86 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort86 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort87 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort87 xi_sort88 =
  subst_sort87 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort87 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort88 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort88 xi_sort88 =
  subst_sort88 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort88 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort89 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort89 xi_sort88 =
  subst_sort89 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort89 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort90 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort90 xi_sort88 =
  subst_sort90 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort90 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort91 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort91 xi_sort88 =
  subst_sort91 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort91 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort92 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort92 xi_sort88 =
  subst_sort92 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort92 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort93 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort93 xi_sort88 =
  subst_sort93 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort93 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort94 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort94 xi_sort88 =
  subst_sort94 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort94 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort95 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort95 xi_sort88 =
  subst_sort95 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort95 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort96 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort96 xi_sort88 =
  subst_sort96 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort96 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort97 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort97 xi_sort88 =
  subst_sort97 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort97 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort98 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort98 xi_sort88 =
  subst_sort98 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort98 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort99 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  ren_sort99 xi_sort88 =
  subst_sort99 (funcomp (var_sort88 n_sort88) xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_sort99 xi_sort88 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort0 {m_sort88 : nat} : subst_sort0 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort0 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort1 {m_sort88 : nat} : subst_sort1 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort1 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort2 {m_sort88 : nat} : subst_sort2 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort2 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort3 {m_sort88 : nat} : subst_sort3 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort3 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort4 {m_sort88 : nat} : subst_sort4 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort4 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort5 {m_sort88 : nat} : subst_sort5 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort5 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort6 {m_sort88 : nat} : subst_sort6 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort6 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort7 {m_sort88 : nat} : subst_sort7 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort7 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort8 {m_sort88 : nat} : subst_sort8 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort8 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort9 {m_sort88 : nat} : subst_sort9 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort9 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort10 {m_sort88 : nat} :
  subst_sort10 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort10 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort11 {m_sort88 : nat} :
  subst_sort11 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort11 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort12 {m_sort88 : nat} :
  subst_sort12 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort12 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort13 {m_sort88 : nat} :
  subst_sort13 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort13 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort14 {m_sort88 : nat} :
  subst_sort14 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort14 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort15 {m_sort88 : nat} :
  subst_sort15 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort15 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort16 {m_sort88 : nat} :
  subst_sort16 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort16 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort17 {m_sort88 : nat} :
  subst_sort17 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort17 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort18 {m_sort88 : nat} :
  subst_sort18 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort18 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort19 {m_sort88 : nat} :
  subst_sort19 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort19 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort20 {m_sort88 : nat} :
  subst_sort20 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort20 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort21 {m_sort88 : nat} :
  subst_sort21 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort21 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort22 {m_sort88 : nat} :
  subst_sort22 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort22 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort23 {m_sort88 : nat} :
  subst_sort23 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort23 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort24 {m_sort88 : nat} :
  subst_sort24 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort24 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort25 {m_sort88 : nat} :
  subst_sort25 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort25 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort26 {m_sort88 : nat} :
  subst_sort26 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort26 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort27 {m_sort88 : nat} :
  subst_sort27 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort27 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort28 {m_sort88 : nat} :
  subst_sort28 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort28 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort29 {m_sort88 : nat} :
  subst_sort29 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort29 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort30 {m_sort88 : nat} :
  subst_sort30 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort30 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort31 {m_sort88 : nat} :
  subst_sort31 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort31 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort32 {m_sort88 : nat} :
  subst_sort32 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort32 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort33 {m_sort88 : nat} :
  subst_sort33 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort33 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort34 {m_sort88 : nat} :
  subst_sort34 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort34 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort35 {m_sort88 : nat} :
  subst_sort35 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort35 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort36 {m_sort88 : nat} :
  subst_sort36 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort36 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort37 {m_sort88 : nat} :
  subst_sort37 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort37 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort38 {m_sort88 : nat} :
  subst_sort38 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort38 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort39 {m_sort88 : nat} :
  subst_sort39 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort39 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort40 {m_sort88 : nat} :
  subst_sort40 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort40 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort41 {m_sort88 : nat} :
  subst_sort41 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort41 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort42 {m_sort88 : nat} :
  subst_sort42 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort42 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort43 {m_sort88 : nat} :
  subst_sort43 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort43 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort44 {m_sort88 : nat} :
  subst_sort44 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort44 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort45 {m_sort88 : nat} :
  subst_sort45 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort45 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort46 {m_sort88 : nat} :
  subst_sort46 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort46 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort47 {m_sort88 : nat} :
  subst_sort47 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort47 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort48 {m_sort88 : nat} :
  subst_sort48 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort48 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort49 {m_sort88 : nat} :
  subst_sort49 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort49 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort50 {m_sort88 : nat} :
  subst_sort50 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort50 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort51 {m_sort88 : nat} :
  subst_sort51 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort51 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort52 {m_sort88 : nat} :
  subst_sort52 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort52 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort53 {m_sort88 : nat} :
  subst_sort53 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort53 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort54 {m_sort88 : nat} :
  subst_sort54 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort54 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort55 {m_sort88 : nat} :
  subst_sort55 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort55 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort56 {m_sort88 : nat} :
  subst_sort56 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort56 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort57 {m_sort88 : nat} :
  subst_sort57 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort57 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort58 {m_sort88 : nat} :
  subst_sort58 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort58 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort59 {m_sort88 : nat} :
  subst_sort59 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort59 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort60 {m_sort88 : nat} :
  subst_sort60 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort60 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort61 {m_sort88 : nat} :
  subst_sort61 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort61 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort62 {m_sort88 : nat} :
  subst_sort62 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort62 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort63 {m_sort88 : nat} :
  subst_sort63 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort63 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort64 {m_sort88 : nat} :
  subst_sort64 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort64 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort65 {m_sort88 : nat} :
  subst_sort65 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort65 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort66 {m_sort88 : nat} :
  subst_sort66 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort66 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort67 {m_sort88 : nat} :
  subst_sort67 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort67 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort68 {m_sort88 : nat} :
  subst_sort68 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort68 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort69 {m_sort88 : nat} :
  subst_sort69 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort69 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort70 {m_sort88 : nat} :
  subst_sort70 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort70 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort71 {m_sort88 : nat} :
  subst_sort71 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort71 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort72 {m_sort88 : nat} :
  subst_sort72 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort72 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort73 {m_sort88 : nat} :
  subst_sort73 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort73 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort74 {m_sort88 : nat} :
  subst_sort74 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort74 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort75 {m_sort88 : nat} :
  subst_sort75 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort75 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort76 {m_sort88 : nat} :
  subst_sort76 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort76 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort77 {m_sort88 : nat} :
  subst_sort77 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort77 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort78 {m_sort88 : nat} :
  subst_sort78 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort78 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort79 {m_sort88 : nat} :
  subst_sort79 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort79 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort80 {m_sort88 : nat} :
  subst_sort80 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort80 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort81 {m_sort88 : nat} :
  subst_sort81 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort81 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort82 {m_sort88 : nat} :
  subst_sort82 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort82 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort83 {m_sort88 : nat} :
  subst_sort83 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort83 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort84 {m_sort88 : nat} :
  subst_sort84 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort84 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort85 {m_sort88 : nat} :
  subst_sort85 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort85 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort86 {m_sort88 : nat} :
  subst_sort86 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort86 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort87 {m_sort88 : nat} :
  subst_sort87 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort87 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort88 {m_sort88 : nat} :
  subst_sort88 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort88 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort89 {m_sort88 : nat} :
  subst_sort89 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort89 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort90 {m_sort88 : nat} :
  subst_sort90 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort90 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort91 {m_sort88 : nat} :
  subst_sort91 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort91 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort92 {m_sort88 : nat} :
  subst_sort92 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort92 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort93 {m_sort88 : nat} :
  subst_sort93 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort93 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort94 {m_sort88 : nat} :
  subst_sort94 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort94 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort95 {m_sort88 : nat} :
  subst_sort95 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort95 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort96 {m_sort88 : nat} :
  subst_sort96 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort96 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort97 {m_sort88 : nat} :
  subst_sort97 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort97 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort98 {m_sort88 : nat} :
  subst_sort98 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort98 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort99 {m_sort88 : nat} :
  subst_sort99 (var_sort88 m_sort88) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort99 (var_sort88 m_sort88) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma rinstId_sort0 {m_sort88 : nat} : @ren_sort0 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort0 (id _)) instId_sort0).

Qed.

Lemma rinstId_sort1 {m_sort88 : nat} : @ren_sort1 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort1 (id _)) instId_sort1).

Qed.

Lemma rinstId_sort2 {m_sort88 : nat} : @ren_sort2 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort2 (id _)) instId_sort2).

Qed.

Lemma rinstId_sort3 {m_sort88 : nat} : @ren_sort3 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort3 (id _)) instId_sort3).

Qed.

Lemma rinstId_sort4 {m_sort88 : nat} : @ren_sort4 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort4 (id _)) instId_sort4).

Qed.

Lemma rinstId_sort5 {m_sort88 : nat} : @ren_sort5 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort5 (id _)) instId_sort5).

Qed.

Lemma rinstId_sort6 {m_sort88 : nat} : @ren_sort6 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort6 (id _)) instId_sort6).

Qed.

Lemma rinstId_sort7 {m_sort88 : nat} : @ren_sort7 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort7 (id _)) instId_sort7).

Qed.

Lemma rinstId_sort8 {m_sort88 : nat} : @ren_sort8 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort8 (id _)) instId_sort8).

Qed.

Lemma rinstId_sort9 {m_sort88 : nat} : @ren_sort9 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort9 (id _)) instId_sort9).

Qed.

Lemma rinstId_sort10 {m_sort88 : nat} : @ren_sort10 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort10 (id _)) instId_sort10).

Qed.

Lemma rinstId_sort11 {m_sort88 : nat} : @ren_sort11 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort11 (id _)) instId_sort11).

Qed.

Lemma rinstId_sort12 {m_sort88 : nat} : @ren_sort12 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort12 (id _)) instId_sort12).

Qed.

Lemma rinstId_sort13 {m_sort88 : nat} : @ren_sort13 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort13 (id _)) instId_sort13).

Qed.

Lemma rinstId_sort14 {m_sort88 : nat} : @ren_sort14 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort14 (id _)) instId_sort14).

Qed.

Lemma rinstId_sort15 {m_sort88 : nat} : @ren_sort15 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort15 (id _)) instId_sort15).

Qed.

Lemma rinstId_sort16 {m_sort88 : nat} : @ren_sort16 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort16 (id _)) instId_sort16).

Qed.

Lemma rinstId_sort17 {m_sort88 : nat} : @ren_sort17 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort17 (id _)) instId_sort17).

Qed.

Lemma rinstId_sort18 {m_sort88 : nat} : @ren_sort18 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort18 (id _)) instId_sort18).

Qed.

Lemma rinstId_sort19 {m_sort88 : nat} : @ren_sort19 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort19 (id _)) instId_sort19).

Qed.

Lemma rinstId_sort20 {m_sort88 : nat} : @ren_sort20 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort20 (id _)) instId_sort20).

Qed.

Lemma rinstId_sort21 {m_sort88 : nat} : @ren_sort21 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort21 (id _)) instId_sort21).

Qed.

Lemma rinstId_sort22 {m_sort88 : nat} : @ren_sort22 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort22 (id _)) instId_sort22).

Qed.

Lemma rinstId_sort23 {m_sort88 : nat} : @ren_sort23 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort23 (id _)) instId_sort23).

Qed.

Lemma rinstId_sort24 {m_sort88 : nat} : @ren_sort24 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort24 (id _)) instId_sort24).

Qed.

Lemma rinstId_sort25 {m_sort88 : nat} : @ren_sort25 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort25 (id _)) instId_sort25).

Qed.

Lemma rinstId_sort26 {m_sort88 : nat} : @ren_sort26 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort26 (id _)) instId_sort26).

Qed.

Lemma rinstId_sort27 {m_sort88 : nat} : @ren_sort27 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort27 (id _)) instId_sort27).

Qed.

Lemma rinstId_sort28 {m_sort88 : nat} : @ren_sort28 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort28 (id _)) instId_sort28).

Qed.

Lemma rinstId_sort29 {m_sort88 : nat} : @ren_sort29 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort29 (id _)) instId_sort29).

Qed.

Lemma rinstId_sort30 {m_sort88 : nat} : @ren_sort30 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort30 (id _)) instId_sort30).

Qed.

Lemma rinstId_sort31 {m_sort88 : nat} : @ren_sort31 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort31 (id _)) instId_sort31).

Qed.

Lemma rinstId_sort32 {m_sort88 : nat} : @ren_sort32 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort32 (id _)) instId_sort32).

Qed.

Lemma rinstId_sort33 {m_sort88 : nat} : @ren_sort33 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort33 (id _)) instId_sort33).

Qed.

Lemma rinstId_sort34 {m_sort88 : nat} : @ren_sort34 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort34 (id _)) instId_sort34).

Qed.

Lemma rinstId_sort35 {m_sort88 : nat} : @ren_sort35 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort35 (id _)) instId_sort35).

Qed.

Lemma rinstId_sort36 {m_sort88 : nat} : @ren_sort36 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort36 (id _)) instId_sort36).

Qed.

Lemma rinstId_sort37 {m_sort88 : nat} : @ren_sort37 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort37 (id _)) instId_sort37).

Qed.

Lemma rinstId_sort38 {m_sort88 : nat} : @ren_sort38 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort38 (id _)) instId_sort38).

Qed.

Lemma rinstId_sort39 {m_sort88 : nat} : @ren_sort39 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort39 (id _)) instId_sort39).

Qed.

Lemma rinstId_sort40 {m_sort88 : nat} : @ren_sort40 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort40 (id _)) instId_sort40).

Qed.

Lemma rinstId_sort41 {m_sort88 : nat} : @ren_sort41 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort41 (id _)) instId_sort41).

Qed.

Lemma rinstId_sort42 {m_sort88 : nat} : @ren_sort42 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort42 (id _)) instId_sort42).

Qed.

Lemma rinstId_sort43 {m_sort88 : nat} : @ren_sort43 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort43 (id _)) instId_sort43).

Qed.

Lemma rinstId_sort44 {m_sort88 : nat} : @ren_sort44 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort44 (id _)) instId_sort44).

Qed.

Lemma rinstId_sort45 {m_sort88 : nat} : @ren_sort45 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort45 (id _)) instId_sort45).

Qed.

Lemma rinstId_sort46 {m_sort88 : nat} : @ren_sort46 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort46 (id _)) instId_sort46).

Qed.

Lemma rinstId_sort47 {m_sort88 : nat} : @ren_sort47 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort47 (id _)) instId_sort47).

Qed.

Lemma rinstId_sort48 {m_sort88 : nat} : @ren_sort48 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort48 (id _)) instId_sort48).

Qed.

Lemma rinstId_sort49 {m_sort88 : nat} : @ren_sort49 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort49 (id _)) instId_sort49).

Qed.

Lemma rinstId_sort50 {m_sort88 : nat} : @ren_sort50 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort50 (id _)) instId_sort50).

Qed.

Lemma rinstId_sort51 {m_sort88 : nat} : @ren_sort51 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort51 (id _)) instId_sort51).

Qed.

Lemma rinstId_sort52 {m_sort88 : nat} : @ren_sort52 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort52 (id _)) instId_sort52).

Qed.

Lemma rinstId_sort53 {m_sort88 : nat} : @ren_sort53 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort53 (id _)) instId_sort53).

Qed.

Lemma rinstId_sort54 {m_sort88 : nat} : @ren_sort54 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort54 (id _)) instId_sort54).

Qed.

Lemma rinstId_sort55 {m_sort88 : nat} : @ren_sort55 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort55 (id _)) instId_sort55).

Qed.

Lemma rinstId_sort56 {m_sort88 : nat} : @ren_sort56 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort56 (id _)) instId_sort56).

Qed.

Lemma rinstId_sort57 {m_sort88 : nat} : @ren_sort57 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort57 (id _)) instId_sort57).

Qed.

Lemma rinstId_sort58 {m_sort88 : nat} : @ren_sort58 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort58 (id _)) instId_sort58).

Qed.

Lemma rinstId_sort59 {m_sort88 : nat} : @ren_sort59 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort59 (id _)) instId_sort59).

Qed.

Lemma rinstId_sort60 {m_sort88 : nat} : @ren_sort60 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort60 (id _)) instId_sort60).

Qed.

Lemma rinstId_sort61 {m_sort88 : nat} : @ren_sort61 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort61 (id _)) instId_sort61).

Qed.

Lemma rinstId_sort62 {m_sort88 : nat} : @ren_sort62 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort62 (id _)) instId_sort62).

Qed.

Lemma rinstId_sort63 {m_sort88 : nat} : @ren_sort63 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort63 (id _)) instId_sort63).

Qed.

Lemma rinstId_sort64 {m_sort88 : nat} : @ren_sort64 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort64 (id _)) instId_sort64).

Qed.

Lemma rinstId_sort65 {m_sort88 : nat} : @ren_sort65 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort65 (id _)) instId_sort65).

Qed.

Lemma rinstId_sort66 {m_sort88 : nat} : @ren_sort66 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort66 (id _)) instId_sort66).

Qed.

Lemma rinstId_sort67 {m_sort88 : nat} : @ren_sort67 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort67 (id _)) instId_sort67).

Qed.

Lemma rinstId_sort68 {m_sort88 : nat} : @ren_sort68 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort68 (id _)) instId_sort68).

Qed.

Lemma rinstId_sort69 {m_sort88 : nat} : @ren_sort69 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort69 (id _)) instId_sort69).

Qed.

Lemma rinstId_sort70 {m_sort88 : nat} : @ren_sort70 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort70 (id _)) instId_sort70).

Qed.

Lemma rinstId_sort71 {m_sort88 : nat} : @ren_sort71 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort71 (id _)) instId_sort71).

Qed.

Lemma rinstId_sort72 {m_sort88 : nat} : @ren_sort72 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort72 (id _)) instId_sort72).

Qed.

Lemma rinstId_sort73 {m_sort88 : nat} : @ren_sort73 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort73 (id _)) instId_sort73).

Qed.

Lemma rinstId_sort74 {m_sort88 : nat} : @ren_sort74 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort74 (id _)) instId_sort74).

Qed.

Lemma rinstId_sort75 {m_sort88 : nat} : @ren_sort75 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort75 (id _)) instId_sort75).

Qed.

Lemma rinstId_sort76 {m_sort88 : nat} : @ren_sort76 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort76 (id _)) instId_sort76).

Qed.

Lemma rinstId_sort77 {m_sort88 : nat} : @ren_sort77 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort77 (id _)) instId_sort77).

Qed.

Lemma rinstId_sort78 {m_sort88 : nat} : @ren_sort78 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort78 (id _)) instId_sort78).

Qed.

Lemma rinstId_sort79 {m_sort88 : nat} : @ren_sort79 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort79 (id _)) instId_sort79).

Qed.

Lemma rinstId_sort80 {m_sort88 : nat} : @ren_sort80 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort80 (id _)) instId_sort80).

Qed.

Lemma rinstId_sort81 {m_sort88 : nat} : @ren_sort81 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort81 (id _)) instId_sort81).

Qed.

Lemma rinstId_sort82 {m_sort88 : nat} : @ren_sort82 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort82 (id _)) instId_sort82).

Qed.

Lemma rinstId_sort83 {m_sort88 : nat} : @ren_sort83 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort83 (id _)) instId_sort83).

Qed.

Lemma rinstId_sort84 {m_sort88 : nat} : @ren_sort84 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort84 (id _)) instId_sort84).

Qed.

Lemma rinstId_sort85 {m_sort88 : nat} : @ren_sort85 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort85 (id _)) instId_sort85).

Qed.

Lemma rinstId_sort86 {m_sort88 : nat} : @ren_sort86 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort86 (id _)) instId_sort86).

Qed.

Lemma rinstId_sort87 {m_sort88 : nat} : @ren_sort87 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort87 (id _)) instId_sort87).

Qed.

Lemma rinstId_sort88 {m_sort88 : nat} : @ren_sort88 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort88 (id _)) instId_sort88).

Qed.

Lemma rinstId_sort89 {m_sort88 : nat} : @ren_sort89 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort89 (id _)) instId_sort89).

Qed.

Lemma rinstId_sort90 {m_sort88 : nat} : @ren_sort90 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort90 (id _)) instId_sort90).

Qed.

Lemma rinstId_sort91 {m_sort88 : nat} : @ren_sort91 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort91 (id _)) instId_sort91).

Qed.

Lemma rinstId_sort92 {m_sort88 : nat} : @ren_sort92 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort92 (id _)) instId_sort92).

Qed.

Lemma rinstId_sort93 {m_sort88 : nat} : @ren_sort93 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort93 (id _)) instId_sort93).

Qed.

Lemma rinstId_sort94 {m_sort88 : nat} : @ren_sort94 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort94 (id _)) instId_sort94).

Qed.

Lemma rinstId_sort95 {m_sort88 : nat} : @ren_sort95 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort95 (id _)) instId_sort95).

Qed.

Lemma rinstId_sort96 {m_sort88 : nat} : @ren_sort96 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort96 (id _)) instId_sort96).

Qed.

Lemma rinstId_sort97 {m_sort88 : nat} : @ren_sort97 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort97 (id _)) instId_sort97).

Qed.

Lemma rinstId_sort98 {m_sort88 : nat} : @ren_sort98 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort98 (id _)) instId_sort98).

Qed.

Lemma rinstId_sort99 {m_sort88 : nat} : @ren_sort99 m_sort88 m_sort88 id = id.

Proof.
exact (eq_trans (rinstInst_sort99 (id _)) instId_sort99).

Qed.

Lemma varL_sort88 {m_sort88 : nat} {n_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 n_sort88) :
  funcomp (subst_sort88 sigma_sort88) (var_sort88 m_sort88) = sigma_sort88.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort88 {m_sort88 : nat} {n_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin n_sort88) :
  funcomp (ren_sort88 xi_sort88) (var_sort88 m_sort88) =
  funcomp (var_sort88 n_sort88) xi_sort88.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort0 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort0 zeta_sort88) (ren_sort0 xi_sort88) =
  ren_sort0 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort0 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort1 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort1 zeta_sort88) (ren_sort1 xi_sort88) =
  ren_sort1 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort1 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort2 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort2 zeta_sort88) (ren_sort2 xi_sort88) =
  ren_sort2 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort2 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort3 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort3 zeta_sort88) (ren_sort3 xi_sort88) =
  ren_sort3 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort3 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort4 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort4 zeta_sort88) (ren_sort4 xi_sort88) =
  ren_sort4 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort4 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort5 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort5 zeta_sort88) (ren_sort5 xi_sort88) =
  ren_sort5 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort5 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort6 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort6 zeta_sort88) (ren_sort6 xi_sort88) =
  ren_sort6 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort6 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort7 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort7 zeta_sort88) (ren_sort7 xi_sort88) =
  ren_sort7 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort7 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort8 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort8 zeta_sort88) (ren_sort8 xi_sort88) =
  ren_sort8 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort8 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort9 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort9 zeta_sort88) (ren_sort9 xi_sort88) =
  ren_sort9 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort9 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort10 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort10 zeta_sort88) (ren_sort10 xi_sort88) =
  ren_sort10 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort10 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort11 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort11 zeta_sort88) (ren_sort11 xi_sort88) =
  ren_sort11 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort11 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort12 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort12 zeta_sort88) (ren_sort12 xi_sort88) =
  ren_sort12 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort12 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort13 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort13 zeta_sort88) (ren_sort13 xi_sort88) =
  ren_sort13 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort13 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort14 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort14 zeta_sort88) (ren_sort14 xi_sort88) =
  ren_sort14 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort14 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort15 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort15 zeta_sort88) (ren_sort15 xi_sort88) =
  ren_sort15 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort15 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort16 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort16 zeta_sort88) (ren_sort16 xi_sort88) =
  ren_sort16 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort16 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort17 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort17 zeta_sort88) (ren_sort17 xi_sort88) =
  ren_sort17 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort17 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort18 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort18 zeta_sort88) (ren_sort18 xi_sort88) =
  ren_sort18 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort18 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort19 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort19 zeta_sort88) (ren_sort19 xi_sort88) =
  ren_sort19 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort19 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort20 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort20 zeta_sort88) (ren_sort20 xi_sort88) =
  ren_sort20 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort20 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort21 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort21 zeta_sort88) (ren_sort21 xi_sort88) =
  ren_sort21 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort21 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort22 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort22 zeta_sort88) (ren_sort22 xi_sort88) =
  ren_sort22 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort22 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort23 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort23 zeta_sort88) (ren_sort23 xi_sort88) =
  ren_sort23 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort23 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort24 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort24 zeta_sort88) (ren_sort24 xi_sort88) =
  ren_sort24 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort24 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort25 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort25 zeta_sort88) (ren_sort25 xi_sort88) =
  ren_sort25 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort25 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort26 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort26 zeta_sort88) (ren_sort26 xi_sort88) =
  ren_sort26 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort26 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort27 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort27 zeta_sort88) (ren_sort27 xi_sort88) =
  ren_sort27 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort27 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort28 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort28 zeta_sort88) (ren_sort28 xi_sort88) =
  ren_sort28 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort28 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort29 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort29 zeta_sort88) (ren_sort29 xi_sort88) =
  ren_sort29 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort29 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort30 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort30 zeta_sort88) (ren_sort30 xi_sort88) =
  ren_sort30 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort30 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort31 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort31 zeta_sort88) (ren_sort31 xi_sort88) =
  ren_sort31 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort31 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort32 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort32 zeta_sort88) (ren_sort32 xi_sort88) =
  ren_sort32 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort32 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort33 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort33 zeta_sort88) (ren_sort33 xi_sort88) =
  ren_sort33 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort33 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort34 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort34 zeta_sort88) (ren_sort34 xi_sort88) =
  ren_sort34 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort34 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort35 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort35 zeta_sort88) (ren_sort35 xi_sort88) =
  ren_sort35 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort35 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort36 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort36 zeta_sort88) (ren_sort36 xi_sort88) =
  ren_sort36 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort36 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort37 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort37 zeta_sort88) (ren_sort37 xi_sort88) =
  ren_sort37 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort37 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort38 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort38 zeta_sort88) (ren_sort38 xi_sort88) =
  ren_sort38 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort38 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort39 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort39 zeta_sort88) (ren_sort39 xi_sort88) =
  ren_sort39 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort39 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort40 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort40 zeta_sort88) (ren_sort40 xi_sort88) =
  ren_sort40 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort40 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort41 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort41 zeta_sort88) (ren_sort41 xi_sort88) =
  ren_sort41 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort41 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort42 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort42 zeta_sort88) (ren_sort42 xi_sort88) =
  ren_sort42 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort42 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort43 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort43 zeta_sort88) (ren_sort43 xi_sort88) =
  ren_sort43 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort43 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort44 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort44 zeta_sort88) (ren_sort44 xi_sort88) =
  ren_sort44 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort44 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort45 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort45 zeta_sort88) (ren_sort45 xi_sort88) =
  ren_sort45 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort45 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort46 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort46 zeta_sort88) (ren_sort46 xi_sort88) =
  ren_sort46 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort46 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort47 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort47 zeta_sort88) (ren_sort47 xi_sort88) =
  ren_sort47 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort47 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort48 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort48 zeta_sort88) (ren_sort48 xi_sort88) =
  ren_sort48 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort48 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort49 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort49 zeta_sort88) (ren_sort49 xi_sort88) =
  ren_sort49 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort49 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort50 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort50 zeta_sort88) (ren_sort50 xi_sort88) =
  ren_sort50 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort50 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort51 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort51 zeta_sort88) (ren_sort51 xi_sort88) =
  ren_sort51 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort51 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort52 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort52 zeta_sort88) (ren_sort52 xi_sort88) =
  ren_sort52 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort52 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort53 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort53 zeta_sort88) (ren_sort53 xi_sort88) =
  ren_sort53 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort53 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort54 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort54 zeta_sort88) (ren_sort54 xi_sort88) =
  ren_sort54 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort54 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort55 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort55 zeta_sort88) (ren_sort55 xi_sort88) =
  ren_sort55 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort55 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort56 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort56 zeta_sort88) (ren_sort56 xi_sort88) =
  ren_sort56 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort56 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort57 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort57 zeta_sort88) (ren_sort57 xi_sort88) =
  ren_sort57 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort57 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort58 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort58 zeta_sort88) (ren_sort58 xi_sort88) =
  ren_sort58 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort58 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort59 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort59 zeta_sort88) (ren_sort59 xi_sort88) =
  ren_sort59 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort59 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort60 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort60 zeta_sort88) (ren_sort60 xi_sort88) =
  ren_sort60 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort60 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort61 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort61 zeta_sort88) (ren_sort61 xi_sort88) =
  ren_sort61 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort61 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort62 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort62 zeta_sort88) (ren_sort62 xi_sort88) =
  ren_sort62 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort62 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort63 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort63 zeta_sort88) (ren_sort63 xi_sort88) =
  ren_sort63 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort63 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort64 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort64 zeta_sort88) (ren_sort64 xi_sort88) =
  ren_sort64 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort64 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort65 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort65 zeta_sort88) (ren_sort65 xi_sort88) =
  ren_sort65 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort65 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort66 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort66 zeta_sort88) (ren_sort66 xi_sort88) =
  ren_sort66 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort66 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort67 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort67 zeta_sort88) (ren_sort67 xi_sort88) =
  ren_sort67 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort67 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort68 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort68 zeta_sort88) (ren_sort68 xi_sort88) =
  ren_sort68 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort68 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort69 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort69 zeta_sort88) (ren_sort69 xi_sort88) =
  ren_sort69 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort69 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort70 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort70 zeta_sort88) (ren_sort70 xi_sort88) =
  ren_sort70 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort70 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort71 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort71 zeta_sort88) (ren_sort71 xi_sort88) =
  ren_sort71 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort71 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort72 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort72 zeta_sort88) (ren_sort72 xi_sort88) =
  ren_sort72 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort72 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort73 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort73 zeta_sort88) (ren_sort73 xi_sort88) =
  ren_sort73 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort73 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort74 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort74 zeta_sort88) (ren_sort74 xi_sort88) =
  ren_sort74 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort74 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort75 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort75 zeta_sort88) (ren_sort75 xi_sort88) =
  ren_sort75 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort75 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort76 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort76 zeta_sort88) (ren_sort76 xi_sort88) =
  ren_sort76 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort76 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort77 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort77 zeta_sort88) (ren_sort77 xi_sort88) =
  ren_sort77 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort77 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort78 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort78 zeta_sort88) (ren_sort78 xi_sort88) =
  ren_sort78 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort78 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort79 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort79 zeta_sort88) (ren_sort79 xi_sort88) =
  ren_sort79 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort79 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort80 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort80 zeta_sort88) (ren_sort80 xi_sort88) =
  ren_sort80 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort80 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort81 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort81 zeta_sort88) (ren_sort81 xi_sort88) =
  ren_sort81 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort81 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort82 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort82 zeta_sort88) (ren_sort82 xi_sort88) =
  ren_sort82 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort82 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort83 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort83 zeta_sort88) (ren_sort83 xi_sort88) =
  ren_sort83 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort83 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort84 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort84 zeta_sort88) (ren_sort84 xi_sort88) =
  ren_sort84 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort84 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort85 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort85 zeta_sort88) (ren_sort85 xi_sort88) =
  ren_sort85 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort85 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort86 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort86 zeta_sort88) (ren_sort86 xi_sort88) =
  ren_sort86 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort86 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort87 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort87 zeta_sort88) (ren_sort87 xi_sort88) =
  ren_sort87 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort87 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort88 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort88 zeta_sort88) (ren_sort88 xi_sort88) =
  ren_sort88 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort88 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort89 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort89 zeta_sort88) (ren_sort89 xi_sort88) =
  ren_sort89 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort89 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort90 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort90 zeta_sort88) (ren_sort90 xi_sort88) =
  ren_sort90 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort90 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort91 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort91 zeta_sort88) (ren_sort91 xi_sort88) =
  ren_sort91 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort91 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort92 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort92 zeta_sort88) (ren_sort92 xi_sort88) =
  ren_sort92 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort92 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort93 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort93 zeta_sort88) (ren_sort93 xi_sort88) =
  ren_sort93 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort93 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort94 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort94 zeta_sort88) (ren_sort94 xi_sort88) =
  ren_sort94 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort94 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort95 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort95 zeta_sort88) (ren_sort95 xi_sort88) =
  ren_sort95 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort95 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort96 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort96 zeta_sort88) (ren_sort96 xi_sort88) =
  ren_sort96 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort96 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort97 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort97 zeta_sort88) (ren_sort97 xi_sort88) =
  ren_sort97 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort97 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort98 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort98 zeta_sort88) (ren_sort98 xi_sort88) =
  ren_sort98 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort98 xi_sort88 zeta_sort88 n)).

Qed.

Lemma renRen'_sort99 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort99 zeta_sort88) (ren_sort99 xi_sort88) =
  ren_sort99 (funcomp zeta_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort99 xi_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort0 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort0 zeta_sort88) (subst_sort0 sigma_sort88) =
  subst_sort0 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort0 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort1 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort1 zeta_sort88) (subst_sort1 sigma_sort88) =
  subst_sort1 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort1 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort2 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort2 zeta_sort88) (subst_sort2 sigma_sort88) =
  subst_sort2 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort2 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort3 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort3 zeta_sort88) (subst_sort3 sigma_sort88) =
  subst_sort3 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort3 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort4 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort4 zeta_sort88) (subst_sort4 sigma_sort88) =
  subst_sort4 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort4 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort5 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort5 zeta_sort88) (subst_sort5 sigma_sort88) =
  subst_sort5 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort5 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort6 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort6 zeta_sort88) (subst_sort6 sigma_sort88) =
  subst_sort6 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort6 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort7 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort7 zeta_sort88) (subst_sort7 sigma_sort88) =
  subst_sort7 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort7 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort8 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort8 zeta_sort88) (subst_sort8 sigma_sort88) =
  subst_sort8 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort8 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort9 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort9 zeta_sort88) (subst_sort9 sigma_sort88) =
  subst_sort9 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort9 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort10 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort10 zeta_sort88) (subst_sort10 sigma_sort88) =
  subst_sort10 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort10 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort11 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort11 zeta_sort88) (subst_sort11 sigma_sort88) =
  subst_sort11 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort11 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort12 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort12 zeta_sort88) (subst_sort12 sigma_sort88) =
  subst_sort12 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort12 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort13 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort13 zeta_sort88) (subst_sort13 sigma_sort88) =
  subst_sort13 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort13 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort14 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort14 zeta_sort88) (subst_sort14 sigma_sort88) =
  subst_sort14 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort14 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort15 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort15 zeta_sort88) (subst_sort15 sigma_sort88) =
  subst_sort15 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort15 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort16 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort16 zeta_sort88) (subst_sort16 sigma_sort88) =
  subst_sort16 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort16 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort17 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort17 zeta_sort88) (subst_sort17 sigma_sort88) =
  subst_sort17 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort17 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort18 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort18 zeta_sort88) (subst_sort18 sigma_sort88) =
  subst_sort18 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort18 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort19 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort19 zeta_sort88) (subst_sort19 sigma_sort88) =
  subst_sort19 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort19 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort20 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort20 zeta_sort88) (subst_sort20 sigma_sort88) =
  subst_sort20 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort20 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort21 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort21 zeta_sort88) (subst_sort21 sigma_sort88) =
  subst_sort21 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort21 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort22 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort22 zeta_sort88) (subst_sort22 sigma_sort88) =
  subst_sort22 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort22 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort23 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort23 zeta_sort88) (subst_sort23 sigma_sort88) =
  subst_sort23 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort23 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort24 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort24 zeta_sort88) (subst_sort24 sigma_sort88) =
  subst_sort24 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort24 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort25 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort25 zeta_sort88) (subst_sort25 sigma_sort88) =
  subst_sort25 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort25 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort26 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort26 zeta_sort88) (subst_sort26 sigma_sort88) =
  subst_sort26 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort26 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort27 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort27 zeta_sort88) (subst_sort27 sigma_sort88) =
  subst_sort27 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort27 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort28 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort28 zeta_sort88) (subst_sort28 sigma_sort88) =
  subst_sort28 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort28 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort29 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort29 zeta_sort88) (subst_sort29 sigma_sort88) =
  subst_sort29 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort29 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort30 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort30 zeta_sort88) (subst_sort30 sigma_sort88) =
  subst_sort30 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort30 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort31 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort31 zeta_sort88) (subst_sort31 sigma_sort88) =
  subst_sort31 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort31 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort32 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort32 zeta_sort88) (subst_sort32 sigma_sort88) =
  subst_sort32 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort32 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort33 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort33 zeta_sort88) (subst_sort33 sigma_sort88) =
  subst_sort33 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort33 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort34 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort34 zeta_sort88) (subst_sort34 sigma_sort88) =
  subst_sort34 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort34 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort35 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort35 zeta_sort88) (subst_sort35 sigma_sort88) =
  subst_sort35 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort35 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort36 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort36 zeta_sort88) (subst_sort36 sigma_sort88) =
  subst_sort36 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort36 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort37 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort37 zeta_sort88) (subst_sort37 sigma_sort88) =
  subst_sort37 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort37 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort38 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort38 zeta_sort88) (subst_sort38 sigma_sort88) =
  subst_sort38 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort38 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort39 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort39 zeta_sort88) (subst_sort39 sigma_sort88) =
  subst_sort39 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort39 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort40 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort40 zeta_sort88) (subst_sort40 sigma_sort88) =
  subst_sort40 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort40 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort41 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort41 zeta_sort88) (subst_sort41 sigma_sort88) =
  subst_sort41 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort41 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort42 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort42 zeta_sort88) (subst_sort42 sigma_sort88) =
  subst_sort42 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort42 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort43 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort43 zeta_sort88) (subst_sort43 sigma_sort88) =
  subst_sort43 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort43 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort44 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort44 zeta_sort88) (subst_sort44 sigma_sort88) =
  subst_sort44 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort44 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort45 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort45 zeta_sort88) (subst_sort45 sigma_sort88) =
  subst_sort45 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort45 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort46 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort46 zeta_sort88) (subst_sort46 sigma_sort88) =
  subst_sort46 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort46 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort47 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort47 zeta_sort88) (subst_sort47 sigma_sort88) =
  subst_sort47 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort47 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort48 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort48 zeta_sort88) (subst_sort48 sigma_sort88) =
  subst_sort48 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort48 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort49 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort49 zeta_sort88) (subst_sort49 sigma_sort88) =
  subst_sort49 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort49 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort50 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort50 zeta_sort88) (subst_sort50 sigma_sort88) =
  subst_sort50 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort50 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort51 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort51 zeta_sort88) (subst_sort51 sigma_sort88) =
  subst_sort51 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort51 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort52 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort52 zeta_sort88) (subst_sort52 sigma_sort88) =
  subst_sort52 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort52 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort53 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort53 zeta_sort88) (subst_sort53 sigma_sort88) =
  subst_sort53 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort53 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort54 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort54 zeta_sort88) (subst_sort54 sigma_sort88) =
  subst_sort54 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort54 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort55 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort55 zeta_sort88) (subst_sort55 sigma_sort88) =
  subst_sort55 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort55 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort56 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort56 zeta_sort88) (subst_sort56 sigma_sort88) =
  subst_sort56 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort56 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort57 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort57 zeta_sort88) (subst_sort57 sigma_sort88) =
  subst_sort57 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort57 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort58 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort58 zeta_sort88) (subst_sort58 sigma_sort88) =
  subst_sort58 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort58 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort59 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort59 zeta_sort88) (subst_sort59 sigma_sort88) =
  subst_sort59 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort59 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort60 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort60 zeta_sort88) (subst_sort60 sigma_sort88) =
  subst_sort60 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort60 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort61 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort61 zeta_sort88) (subst_sort61 sigma_sort88) =
  subst_sort61 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort61 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort62 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort62 zeta_sort88) (subst_sort62 sigma_sort88) =
  subst_sort62 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort62 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort63 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort63 zeta_sort88) (subst_sort63 sigma_sort88) =
  subst_sort63 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort63 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort64 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort64 zeta_sort88) (subst_sort64 sigma_sort88) =
  subst_sort64 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort64 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort65 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort65 zeta_sort88) (subst_sort65 sigma_sort88) =
  subst_sort65 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort65 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort66 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort66 zeta_sort88) (subst_sort66 sigma_sort88) =
  subst_sort66 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort66 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort67 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort67 zeta_sort88) (subst_sort67 sigma_sort88) =
  subst_sort67 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort67 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort68 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort68 zeta_sort88) (subst_sort68 sigma_sort88) =
  subst_sort68 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort68 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort69 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort69 zeta_sort88) (subst_sort69 sigma_sort88) =
  subst_sort69 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort69 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort70 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort70 zeta_sort88) (subst_sort70 sigma_sort88) =
  subst_sort70 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort70 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort71 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort71 zeta_sort88) (subst_sort71 sigma_sort88) =
  subst_sort71 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort71 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort72 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort72 zeta_sort88) (subst_sort72 sigma_sort88) =
  subst_sort72 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort72 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort73 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort73 zeta_sort88) (subst_sort73 sigma_sort88) =
  subst_sort73 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort73 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort74 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort74 zeta_sort88) (subst_sort74 sigma_sort88) =
  subst_sort74 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort74 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort75 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort75 zeta_sort88) (subst_sort75 sigma_sort88) =
  subst_sort75 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort75 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort76 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort76 zeta_sort88) (subst_sort76 sigma_sort88) =
  subst_sort76 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort76 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort77 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort77 zeta_sort88) (subst_sort77 sigma_sort88) =
  subst_sort77 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort77 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort78 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort78 zeta_sort88) (subst_sort78 sigma_sort88) =
  subst_sort78 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort78 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort79 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort79 zeta_sort88) (subst_sort79 sigma_sort88) =
  subst_sort79 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort79 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort80 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort80 zeta_sort88) (subst_sort80 sigma_sort88) =
  subst_sort80 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort80 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort81 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort81 zeta_sort88) (subst_sort81 sigma_sort88) =
  subst_sort81 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort81 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort82 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort82 zeta_sort88) (subst_sort82 sigma_sort88) =
  subst_sort82 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort82 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort83 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort83 zeta_sort88) (subst_sort83 sigma_sort88) =
  subst_sort83 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort83 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort84 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort84 zeta_sort88) (subst_sort84 sigma_sort88) =
  subst_sort84 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort84 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort85 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort85 zeta_sort88) (subst_sort85 sigma_sort88) =
  subst_sort85 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort85 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort86 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort86 zeta_sort88) (subst_sort86 sigma_sort88) =
  subst_sort86 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort86 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort87 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort87 zeta_sort88) (subst_sort87 sigma_sort88) =
  subst_sort87 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort87 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort88 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort88 zeta_sort88) (subst_sort88 sigma_sort88) =
  subst_sort88 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort88 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort89 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort89 zeta_sort88) (subst_sort89 sigma_sort88) =
  subst_sort89 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort89 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort90 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort90 zeta_sort88) (subst_sort90 sigma_sort88) =
  subst_sort90 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort90 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort91 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort91 zeta_sort88) (subst_sort91 sigma_sort88) =
  subst_sort91 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort91 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort92 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort92 zeta_sort88) (subst_sort92 sigma_sort88) =
  subst_sort92 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort92 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort93 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort93 zeta_sort88) (subst_sort93 sigma_sort88) =
  subst_sort93 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort93 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort94 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort94 zeta_sort88) (subst_sort94 sigma_sort88) =
  subst_sort94 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort94 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort95 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort95 zeta_sort88) (subst_sort95 sigma_sort88) =
  subst_sort95 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort95 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort96 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort96 zeta_sort88) (subst_sort96 sigma_sort88) =
  subst_sort96 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort96 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort97 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort97 zeta_sort88) (subst_sort97 sigma_sort88) =
  subst_sort97 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort97 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort98 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort98 zeta_sort88) (subst_sort98 sigma_sort88) =
  subst_sort98 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort98 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma compRen'_sort99 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (zeta_sort88 : fin k_sort88 -> fin l_sort88) :
  funcomp (ren_sort99 zeta_sort88) (subst_sort99 sigma_sort88) =
  subst_sort99 (funcomp (ren_sort88 zeta_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort99 sigma_sort88 zeta_sort88 n)).

Qed.

Lemma renComp'_sort0 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort0 tau_sort88) (ren_sort0 xi_sort88) =
  subst_sort0 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort0 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort1 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort1 tau_sort88) (ren_sort1 xi_sort88) =
  subst_sort1 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort1 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort2 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort2 tau_sort88) (ren_sort2 xi_sort88) =
  subst_sort2 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort2 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort3 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort3 tau_sort88) (ren_sort3 xi_sort88) =
  subst_sort3 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort3 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort4 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort4 tau_sort88) (ren_sort4 xi_sort88) =
  subst_sort4 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort4 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort5 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort5 tau_sort88) (ren_sort5 xi_sort88) =
  subst_sort5 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort5 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort6 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort6 tau_sort88) (ren_sort6 xi_sort88) =
  subst_sort6 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort6 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort7 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort7 tau_sort88) (ren_sort7 xi_sort88) =
  subst_sort7 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort7 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort8 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort8 tau_sort88) (ren_sort8 xi_sort88) =
  subst_sort8 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort8 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort9 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort9 tau_sort88) (ren_sort9 xi_sort88) =
  subst_sort9 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort9 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort10 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort10 tau_sort88) (ren_sort10 xi_sort88) =
  subst_sort10 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort10 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort11 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort11 tau_sort88) (ren_sort11 xi_sort88) =
  subst_sort11 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort11 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort12 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort12 tau_sort88) (ren_sort12 xi_sort88) =
  subst_sort12 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort12 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort13 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort13 tau_sort88) (ren_sort13 xi_sort88) =
  subst_sort13 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort13 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort14 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort14 tau_sort88) (ren_sort14 xi_sort88) =
  subst_sort14 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort14 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort15 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort15 tau_sort88) (ren_sort15 xi_sort88) =
  subst_sort15 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort15 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort16 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort16 tau_sort88) (ren_sort16 xi_sort88) =
  subst_sort16 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort16 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort17 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort17 tau_sort88) (ren_sort17 xi_sort88) =
  subst_sort17 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort17 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort18 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort18 tau_sort88) (ren_sort18 xi_sort88) =
  subst_sort18 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort18 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort19 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort19 tau_sort88) (ren_sort19 xi_sort88) =
  subst_sort19 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort19 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort20 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort20 tau_sort88) (ren_sort20 xi_sort88) =
  subst_sort20 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort20 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort21 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort21 tau_sort88) (ren_sort21 xi_sort88) =
  subst_sort21 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort21 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort22 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort22 tau_sort88) (ren_sort22 xi_sort88) =
  subst_sort22 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort22 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort23 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort23 tau_sort88) (ren_sort23 xi_sort88) =
  subst_sort23 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort23 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort24 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort24 tau_sort88) (ren_sort24 xi_sort88) =
  subst_sort24 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort24 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort25 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort25 tau_sort88) (ren_sort25 xi_sort88) =
  subst_sort25 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort25 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort26 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort26 tau_sort88) (ren_sort26 xi_sort88) =
  subst_sort26 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort26 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort27 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort27 tau_sort88) (ren_sort27 xi_sort88) =
  subst_sort27 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort27 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort28 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort28 tau_sort88) (ren_sort28 xi_sort88) =
  subst_sort28 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort28 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort29 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort29 tau_sort88) (ren_sort29 xi_sort88) =
  subst_sort29 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort29 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort30 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort30 tau_sort88) (ren_sort30 xi_sort88) =
  subst_sort30 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort30 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort31 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort31 tau_sort88) (ren_sort31 xi_sort88) =
  subst_sort31 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort31 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort32 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort32 tau_sort88) (ren_sort32 xi_sort88) =
  subst_sort32 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort32 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort33 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort33 tau_sort88) (ren_sort33 xi_sort88) =
  subst_sort33 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort33 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort34 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort34 tau_sort88) (ren_sort34 xi_sort88) =
  subst_sort34 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort34 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort35 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort35 tau_sort88) (ren_sort35 xi_sort88) =
  subst_sort35 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort35 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort36 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort36 tau_sort88) (ren_sort36 xi_sort88) =
  subst_sort36 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort36 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort37 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort37 tau_sort88) (ren_sort37 xi_sort88) =
  subst_sort37 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort37 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort38 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort38 tau_sort88) (ren_sort38 xi_sort88) =
  subst_sort38 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort38 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort39 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort39 tau_sort88) (ren_sort39 xi_sort88) =
  subst_sort39 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort39 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort40 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort40 tau_sort88) (ren_sort40 xi_sort88) =
  subst_sort40 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort40 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort41 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort41 tau_sort88) (ren_sort41 xi_sort88) =
  subst_sort41 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort41 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort42 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort42 tau_sort88) (ren_sort42 xi_sort88) =
  subst_sort42 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort42 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort43 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort43 tau_sort88) (ren_sort43 xi_sort88) =
  subst_sort43 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort43 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort44 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort44 tau_sort88) (ren_sort44 xi_sort88) =
  subst_sort44 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort44 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort45 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort45 tau_sort88) (ren_sort45 xi_sort88) =
  subst_sort45 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort45 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort46 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort46 tau_sort88) (ren_sort46 xi_sort88) =
  subst_sort46 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort46 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort47 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort47 tau_sort88) (ren_sort47 xi_sort88) =
  subst_sort47 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort47 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort48 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort48 tau_sort88) (ren_sort48 xi_sort88) =
  subst_sort48 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort48 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort49 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort49 tau_sort88) (ren_sort49 xi_sort88) =
  subst_sort49 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort49 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort50 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort50 tau_sort88) (ren_sort50 xi_sort88) =
  subst_sort50 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort50 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort51 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort51 tau_sort88) (ren_sort51 xi_sort88) =
  subst_sort51 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort51 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort52 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort52 tau_sort88) (ren_sort52 xi_sort88) =
  subst_sort52 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort52 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort53 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort53 tau_sort88) (ren_sort53 xi_sort88) =
  subst_sort53 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort53 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort54 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort54 tau_sort88) (ren_sort54 xi_sort88) =
  subst_sort54 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort54 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort55 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort55 tau_sort88) (ren_sort55 xi_sort88) =
  subst_sort55 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort55 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort56 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort56 tau_sort88) (ren_sort56 xi_sort88) =
  subst_sort56 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort56 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort57 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort57 tau_sort88) (ren_sort57 xi_sort88) =
  subst_sort57 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort57 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort58 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort58 tau_sort88) (ren_sort58 xi_sort88) =
  subst_sort58 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort58 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort59 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort59 tau_sort88) (ren_sort59 xi_sort88) =
  subst_sort59 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort59 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort60 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort60 tau_sort88) (ren_sort60 xi_sort88) =
  subst_sort60 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort60 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort61 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort61 tau_sort88) (ren_sort61 xi_sort88) =
  subst_sort61 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort61 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort62 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort62 tau_sort88) (ren_sort62 xi_sort88) =
  subst_sort62 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort62 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort63 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort63 tau_sort88) (ren_sort63 xi_sort88) =
  subst_sort63 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort63 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort64 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort64 tau_sort88) (ren_sort64 xi_sort88) =
  subst_sort64 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort64 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort65 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort65 tau_sort88) (ren_sort65 xi_sort88) =
  subst_sort65 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort65 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort66 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort66 tau_sort88) (ren_sort66 xi_sort88) =
  subst_sort66 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort66 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort67 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort67 tau_sort88) (ren_sort67 xi_sort88) =
  subst_sort67 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort67 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort68 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort68 tau_sort88) (ren_sort68 xi_sort88) =
  subst_sort68 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort68 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort69 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort69 tau_sort88) (ren_sort69 xi_sort88) =
  subst_sort69 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort69 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort70 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort70 tau_sort88) (ren_sort70 xi_sort88) =
  subst_sort70 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort70 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort71 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort71 tau_sort88) (ren_sort71 xi_sort88) =
  subst_sort71 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort71 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort72 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort72 tau_sort88) (ren_sort72 xi_sort88) =
  subst_sort72 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort72 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort73 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort73 tau_sort88) (ren_sort73 xi_sort88) =
  subst_sort73 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort73 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort74 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort74 tau_sort88) (ren_sort74 xi_sort88) =
  subst_sort74 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort74 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort75 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort75 tau_sort88) (ren_sort75 xi_sort88) =
  subst_sort75 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort75 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort76 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort76 tau_sort88) (ren_sort76 xi_sort88) =
  subst_sort76 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort76 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort77 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort77 tau_sort88) (ren_sort77 xi_sort88) =
  subst_sort77 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort77 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort78 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort78 tau_sort88) (ren_sort78 xi_sort88) =
  subst_sort78 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort78 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort79 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort79 tau_sort88) (ren_sort79 xi_sort88) =
  subst_sort79 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort79 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort80 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort80 tau_sort88) (ren_sort80 xi_sort88) =
  subst_sort80 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort80 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort81 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort81 tau_sort88) (ren_sort81 xi_sort88) =
  subst_sort81 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort81 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort82 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort82 tau_sort88) (ren_sort82 xi_sort88) =
  subst_sort82 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort82 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort83 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort83 tau_sort88) (ren_sort83 xi_sort88) =
  subst_sort83 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort83 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort84 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort84 tau_sort88) (ren_sort84 xi_sort88) =
  subst_sort84 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort84 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort85 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort85 tau_sort88) (ren_sort85 xi_sort88) =
  subst_sort85 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort85 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort86 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort86 tau_sort88) (ren_sort86 xi_sort88) =
  subst_sort86 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort86 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort87 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort87 tau_sort88) (ren_sort87 xi_sort88) =
  subst_sort87 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort87 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort88 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort88 tau_sort88) (ren_sort88 xi_sort88) =
  subst_sort88 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort88 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort89 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort89 tau_sort88) (ren_sort89 xi_sort88) =
  subst_sort89 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort89 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort90 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort90 tau_sort88) (ren_sort90 xi_sort88) =
  subst_sort90 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort90 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort91 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort91 tau_sort88) (ren_sort91 xi_sort88) =
  subst_sort91 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort91 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort92 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort92 tau_sort88) (ren_sort92 xi_sort88) =
  subst_sort92 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort92 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort93 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort93 tau_sort88) (ren_sort93 xi_sort88) =
  subst_sort93 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort93 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort94 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort94 tau_sort88) (ren_sort94 xi_sort88) =
  subst_sort94 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort94 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort95 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort95 tau_sort88) (ren_sort95 xi_sort88) =
  subst_sort95 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort95 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort96 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort96 tau_sort88) (ren_sort96 xi_sort88) =
  subst_sort96 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort96 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort97 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort97 tau_sort88) (ren_sort97 xi_sort88) =
  subst_sort97 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort97 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort98 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort98 tau_sort88) (ren_sort98 xi_sort88) =
  subst_sort98 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort98 xi_sort88 tau_sort88 n)).

Qed.

Lemma renComp'_sort99 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (xi_sort88 : fin m_sort88 -> fin k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort99 tau_sort88) (ren_sort99 xi_sort88) =
  subst_sort99 (funcomp tau_sort88 xi_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort99 xi_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort0 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort0 tau_sort88) (subst_sort0 sigma_sort88) =
  subst_sort0 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort0 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort1 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort1 tau_sort88) (subst_sort1 sigma_sort88) =
  subst_sort1 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort1 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort2 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort2 tau_sort88) (subst_sort2 sigma_sort88) =
  subst_sort2 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort2 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort3 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort3 tau_sort88) (subst_sort3 sigma_sort88) =
  subst_sort3 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort3 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort4 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort4 tau_sort88) (subst_sort4 sigma_sort88) =
  subst_sort4 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort4 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort5 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort5 tau_sort88) (subst_sort5 sigma_sort88) =
  subst_sort5 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort5 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort6 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort6 tau_sort88) (subst_sort6 sigma_sort88) =
  subst_sort6 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort6 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort7 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort7 tau_sort88) (subst_sort7 sigma_sort88) =
  subst_sort7 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort7 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort8 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort8 tau_sort88) (subst_sort8 sigma_sort88) =
  subst_sort8 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort8 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort9 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort9 tau_sort88) (subst_sort9 sigma_sort88) =
  subst_sort9 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort9 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort10 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort10 tau_sort88) (subst_sort10 sigma_sort88) =
  subst_sort10 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort10 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort11 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort11 tau_sort88) (subst_sort11 sigma_sort88) =
  subst_sort11 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort11 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort12 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort12 tau_sort88) (subst_sort12 sigma_sort88) =
  subst_sort12 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort12 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort13 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort13 tau_sort88) (subst_sort13 sigma_sort88) =
  subst_sort13 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort13 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort14 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort14 tau_sort88) (subst_sort14 sigma_sort88) =
  subst_sort14 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort14 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort15 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort15 tau_sort88) (subst_sort15 sigma_sort88) =
  subst_sort15 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort15 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort16 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort16 tau_sort88) (subst_sort16 sigma_sort88) =
  subst_sort16 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort16 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort17 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort17 tau_sort88) (subst_sort17 sigma_sort88) =
  subst_sort17 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort17 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort18 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort18 tau_sort88) (subst_sort18 sigma_sort88) =
  subst_sort18 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort18 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort19 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort19 tau_sort88) (subst_sort19 sigma_sort88) =
  subst_sort19 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort19 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort20 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort20 tau_sort88) (subst_sort20 sigma_sort88) =
  subst_sort20 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort20 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort21 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort21 tau_sort88) (subst_sort21 sigma_sort88) =
  subst_sort21 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort21 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort22 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort22 tau_sort88) (subst_sort22 sigma_sort88) =
  subst_sort22 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort22 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort23 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort23 tau_sort88) (subst_sort23 sigma_sort88) =
  subst_sort23 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort23 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort24 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort24 tau_sort88) (subst_sort24 sigma_sort88) =
  subst_sort24 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort24 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort25 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort25 tau_sort88) (subst_sort25 sigma_sort88) =
  subst_sort25 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort25 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort26 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort26 tau_sort88) (subst_sort26 sigma_sort88) =
  subst_sort26 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort26 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort27 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort27 tau_sort88) (subst_sort27 sigma_sort88) =
  subst_sort27 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort27 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort28 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort28 tau_sort88) (subst_sort28 sigma_sort88) =
  subst_sort28 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort28 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort29 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort29 tau_sort88) (subst_sort29 sigma_sort88) =
  subst_sort29 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort29 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort30 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort30 tau_sort88) (subst_sort30 sigma_sort88) =
  subst_sort30 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort30 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort31 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort31 tau_sort88) (subst_sort31 sigma_sort88) =
  subst_sort31 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort31 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort32 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort32 tau_sort88) (subst_sort32 sigma_sort88) =
  subst_sort32 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort32 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort33 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort33 tau_sort88) (subst_sort33 sigma_sort88) =
  subst_sort33 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort33 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort34 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort34 tau_sort88) (subst_sort34 sigma_sort88) =
  subst_sort34 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort34 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort35 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort35 tau_sort88) (subst_sort35 sigma_sort88) =
  subst_sort35 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort35 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort36 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort36 tau_sort88) (subst_sort36 sigma_sort88) =
  subst_sort36 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort36 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort37 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort37 tau_sort88) (subst_sort37 sigma_sort88) =
  subst_sort37 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort37 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort38 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort38 tau_sort88) (subst_sort38 sigma_sort88) =
  subst_sort38 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort38 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort39 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort39 tau_sort88) (subst_sort39 sigma_sort88) =
  subst_sort39 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort39 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort40 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort40 tau_sort88) (subst_sort40 sigma_sort88) =
  subst_sort40 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort40 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort41 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort41 tau_sort88) (subst_sort41 sigma_sort88) =
  subst_sort41 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort41 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort42 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort42 tau_sort88) (subst_sort42 sigma_sort88) =
  subst_sort42 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort42 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort43 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort43 tau_sort88) (subst_sort43 sigma_sort88) =
  subst_sort43 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort43 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort44 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort44 tau_sort88) (subst_sort44 sigma_sort88) =
  subst_sort44 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort44 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort45 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort45 tau_sort88) (subst_sort45 sigma_sort88) =
  subst_sort45 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort45 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort46 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort46 tau_sort88) (subst_sort46 sigma_sort88) =
  subst_sort46 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort46 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort47 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort47 tau_sort88) (subst_sort47 sigma_sort88) =
  subst_sort47 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort47 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort48 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort48 tau_sort88) (subst_sort48 sigma_sort88) =
  subst_sort48 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort48 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort49 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort49 tau_sort88) (subst_sort49 sigma_sort88) =
  subst_sort49 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort49 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort50 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort50 tau_sort88) (subst_sort50 sigma_sort88) =
  subst_sort50 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort50 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort51 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort51 tau_sort88) (subst_sort51 sigma_sort88) =
  subst_sort51 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort51 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort52 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort52 tau_sort88) (subst_sort52 sigma_sort88) =
  subst_sort52 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort52 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort53 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort53 tau_sort88) (subst_sort53 sigma_sort88) =
  subst_sort53 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort53 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort54 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort54 tau_sort88) (subst_sort54 sigma_sort88) =
  subst_sort54 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort54 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort55 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort55 tau_sort88) (subst_sort55 sigma_sort88) =
  subst_sort55 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort55 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort56 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort56 tau_sort88) (subst_sort56 sigma_sort88) =
  subst_sort56 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort56 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort57 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort57 tau_sort88) (subst_sort57 sigma_sort88) =
  subst_sort57 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort57 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort58 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort58 tau_sort88) (subst_sort58 sigma_sort88) =
  subst_sort58 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort58 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort59 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort59 tau_sort88) (subst_sort59 sigma_sort88) =
  subst_sort59 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort59 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort60 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort60 tau_sort88) (subst_sort60 sigma_sort88) =
  subst_sort60 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort60 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort61 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort61 tau_sort88) (subst_sort61 sigma_sort88) =
  subst_sort61 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort61 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort62 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort62 tau_sort88) (subst_sort62 sigma_sort88) =
  subst_sort62 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort62 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort63 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort63 tau_sort88) (subst_sort63 sigma_sort88) =
  subst_sort63 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort63 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort64 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort64 tau_sort88) (subst_sort64 sigma_sort88) =
  subst_sort64 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort64 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort65 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort65 tau_sort88) (subst_sort65 sigma_sort88) =
  subst_sort65 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort65 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort66 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort66 tau_sort88) (subst_sort66 sigma_sort88) =
  subst_sort66 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort66 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort67 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort67 tau_sort88) (subst_sort67 sigma_sort88) =
  subst_sort67 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort67 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort68 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort68 tau_sort88) (subst_sort68 sigma_sort88) =
  subst_sort68 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort68 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort69 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort69 tau_sort88) (subst_sort69 sigma_sort88) =
  subst_sort69 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort69 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort70 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort70 tau_sort88) (subst_sort70 sigma_sort88) =
  subst_sort70 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort70 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort71 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort71 tau_sort88) (subst_sort71 sigma_sort88) =
  subst_sort71 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort71 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort72 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort72 tau_sort88) (subst_sort72 sigma_sort88) =
  subst_sort72 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort72 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort73 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort73 tau_sort88) (subst_sort73 sigma_sort88) =
  subst_sort73 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort73 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort74 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort74 tau_sort88) (subst_sort74 sigma_sort88) =
  subst_sort74 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort74 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort75 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort75 tau_sort88) (subst_sort75 sigma_sort88) =
  subst_sort75 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort75 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort76 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort76 tau_sort88) (subst_sort76 sigma_sort88) =
  subst_sort76 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort76 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort77 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort77 tau_sort88) (subst_sort77 sigma_sort88) =
  subst_sort77 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort77 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort78 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort78 tau_sort88) (subst_sort78 sigma_sort88) =
  subst_sort78 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort78 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort79 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort79 tau_sort88) (subst_sort79 sigma_sort88) =
  subst_sort79 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort79 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort80 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort80 tau_sort88) (subst_sort80 sigma_sort88) =
  subst_sort80 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort80 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort81 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort81 tau_sort88) (subst_sort81 sigma_sort88) =
  subst_sort81 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort81 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort82 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort82 tau_sort88) (subst_sort82 sigma_sort88) =
  subst_sort82 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort82 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort83 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort83 tau_sort88) (subst_sort83 sigma_sort88) =
  subst_sort83 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort83 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort84 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort84 tau_sort88) (subst_sort84 sigma_sort88) =
  subst_sort84 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort84 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort85 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort85 tau_sort88) (subst_sort85 sigma_sort88) =
  subst_sort85 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort85 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort86 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort86 tau_sort88) (subst_sort86 sigma_sort88) =
  subst_sort86 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort86 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort87 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort87 tau_sort88) (subst_sort87 sigma_sort88) =
  subst_sort87 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort87 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort88 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort88 tau_sort88) (subst_sort88 sigma_sort88) =
  subst_sort88 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort88 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort89 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort89 tau_sort88) (subst_sort89 sigma_sort88) =
  subst_sort89 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort89 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort90 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort90 tau_sort88) (subst_sort90 sigma_sort88) =
  subst_sort90 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort90 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort91 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort91 tau_sort88) (subst_sort91 sigma_sort88) =
  subst_sort91 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort91 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort92 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort92 tau_sort88) (subst_sort92 sigma_sort88) =
  subst_sort92 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort92 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort93 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort93 tau_sort88) (subst_sort93 sigma_sort88) =
  subst_sort93 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort93 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort94 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort94 tau_sort88) (subst_sort94 sigma_sort88) =
  subst_sort94 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort94 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort95 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort95 tau_sort88) (subst_sort95 sigma_sort88) =
  subst_sort95 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort95 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort96 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort96 tau_sort88) (subst_sort96 sigma_sort88) =
  subst_sort96 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort96 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort97 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort97 tau_sort88) (subst_sort97 sigma_sort88) =
  subst_sort97 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort97 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort98 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort98 tau_sort88) (subst_sort98 sigma_sort88) =
  subst_sort98 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort98 sigma_sort88 tau_sort88 n)).

Qed.

Lemma compComp'_sort99 {k_sort88 : nat} {l_sort88 : nat} {m_sort88 : nat}
  (sigma_sort88 : fin m_sort88 -> sort88 k_sort88)
  (tau_sort88 : fin k_sort88 -> sort88 l_sort88) :
  funcomp (subst_sort99 tau_sort88) (subst_sort99 sigma_sort88) =
  subst_sort99 (funcomp (subst_sort88 tau_sort88) sigma_sort88).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort99 sigma_sort88 tau_sort88 n)).

Qed.

Lemma rinstInst_sort100 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort100 xi_sort130 =
  subst_sort100 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort100 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort101 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort101 xi_sort130 =
  subst_sort101 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort101 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort102 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort102 xi_sort130 =
  subst_sort102 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort102 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort103 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort103 xi_sort130 =
  subst_sort103 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort103 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort104 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort104 xi_sort130 =
  subst_sort104 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort104 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort105 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort105 xi_sort130 =
  subst_sort105 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort105 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort106 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort106 xi_sort130 =
  subst_sort106 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort106 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort107 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort107 xi_sort130 =
  subst_sort107 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort107 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort108 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort108 xi_sort130 =
  subst_sort108 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort108 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort109 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort109 xi_sort130 =
  subst_sort109 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort109 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort110 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort110 xi_sort130 =
  subst_sort110 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort110 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort111 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort111 xi_sort130 =
  subst_sort111 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort111 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort112 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort112 xi_sort130 =
  subst_sort112 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort112 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort113 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort113 xi_sort130 =
  subst_sort113 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort113 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort114 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort114 xi_sort130 =
  subst_sort114 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort114 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort115 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort115 xi_sort130 =
  subst_sort115 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort115 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort116 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort116 xi_sort130 =
  subst_sort116 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort116 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort117 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort117 xi_sort130 =
  subst_sort117 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort117 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort118 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort118 xi_sort130 =
  subst_sort118 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort118 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort119 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort119 xi_sort130 =
  subst_sort119 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort119 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort120 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort120 xi_sort130 =
  subst_sort120 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort120 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort121 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort121 xi_sort130 =
  subst_sort121 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort121 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort122 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort122 xi_sort130 =
  subst_sort122 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort122 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort123 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort123 xi_sort130 =
  subst_sort123 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort123 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort124 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort124 xi_sort130 =
  subst_sort124 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort124 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort125 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort125 xi_sort130 =
  subst_sort125 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort125 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort126 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort126 xi_sort130 =
  subst_sort126 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort126 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort127 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort127 xi_sort130 =
  subst_sort127 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort127 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort128 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort128 xi_sort130 =
  subst_sort128 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort128 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort129 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort129 xi_sort130 =
  subst_sort129 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort129 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort130 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort130 xi_sort130 =
  subst_sort130 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort130 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort131 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort131 xi_sort130 =
  subst_sort131 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort131 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort132 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort132 xi_sort130 =
  subst_sort132 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort132 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort133 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort133 xi_sort130 =
  subst_sort133 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort133 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort134 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort134 xi_sort130 =
  subst_sort134 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort134 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort135 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort135 xi_sort130 =
  subst_sort135 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort135 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort136 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort136 xi_sort130 =
  subst_sort136 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort136 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort137 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort137 xi_sort130 =
  subst_sort137 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort137 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort138 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort138 xi_sort130 =
  subst_sort138 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort138 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort139 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort139 xi_sort130 =
  subst_sort139 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort139 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort140 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort140 xi_sort130 =
  subst_sort140 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort140 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort141 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort141 xi_sort130 =
  subst_sort141 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort141 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort142 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort142 xi_sort130 =
  subst_sort142 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort142 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort143 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort143 xi_sort130 =
  subst_sort143 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort143 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort144 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort144 xi_sort130 =
  subst_sort144 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort144 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort145 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort145 xi_sort130 =
  subst_sort145 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort145 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort146 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort146 xi_sort130 =
  subst_sort146 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort146 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort147 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort147 xi_sort130 =
  subst_sort147 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort147 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort148 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort148 xi_sort130 =
  subst_sort148 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort148 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort149 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort149 xi_sort130 =
  subst_sort149 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort149 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort150 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort150 xi_sort130 =
  subst_sort150 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort150 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort151 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort151 xi_sort130 =
  subst_sort151 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort151 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort152 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort152 xi_sort130 =
  subst_sort152 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort152 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort153 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort153 xi_sort130 =
  subst_sort153 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort153 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort154 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort154 xi_sort130 =
  subst_sort154 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort154 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort155 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort155 xi_sort130 =
  subst_sort155 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort155 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort156 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort156 xi_sort130 =
  subst_sort156 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort156 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort157 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort157 xi_sort130 =
  subst_sort157 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort157 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort158 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort158 xi_sort130 =
  subst_sort158 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort158 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort159 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort159 xi_sort130 =
  subst_sort159 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort159 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort160 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort160 xi_sort130 =
  subst_sort160 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort160 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort161 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort161 xi_sort130 =
  subst_sort161 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort161 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort162 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort162 xi_sort130 =
  subst_sort162 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort162 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort163 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort163 xi_sort130 =
  subst_sort163 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort163 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort164 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort164 xi_sort130 =
  subst_sort164 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort164 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort165 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort165 xi_sort130 =
  subst_sort165 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort165 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort166 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort166 xi_sort130 =
  subst_sort166 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort166 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort167 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort167 xi_sort130 =
  subst_sort167 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort167 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort168 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort168 xi_sort130 =
  subst_sort168 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort168 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort169 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort169 xi_sort130 =
  subst_sort169 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort169 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort170 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort170 xi_sort130 =
  subst_sort170 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort170 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort171 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort171 xi_sort130 =
  subst_sort171 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort171 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort172 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort172 xi_sort130 =
  subst_sort172 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort172 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort173 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort173 xi_sort130 =
  subst_sort173 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort173 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort174 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort174 xi_sort130 =
  subst_sort174 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort174 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort175 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort175 xi_sort130 =
  subst_sort175 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort175 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort176 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort176 xi_sort130 =
  subst_sort176 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort176 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort177 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort177 xi_sort130 =
  subst_sort177 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort177 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort178 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort178 xi_sort130 =
  subst_sort178 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort178 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort179 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort179 xi_sort130 =
  subst_sort179 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort179 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort180 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort180 xi_sort130 =
  subst_sort180 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort180 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort181 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort181 xi_sort130 =
  subst_sort181 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort181 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort182 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort182 xi_sort130 =
  subst_sort182 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort182 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort183 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort183 xi_sort130 =
  subst_sort183 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort183 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort184 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort184 xi_sort130 =
  subst_sort184 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort184 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort185 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort185 xi_sort130 =
  subst_sort185 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort185 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort186 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort186 xi_sort130 =
  subst_sort186 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort186 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort187 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort187 xi_sort130 =
  subst_sort187 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort187 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort188 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort188 xi_sort130 =
  subst_sort188 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort188 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort189 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort189 xi_sort130 =
  subst_sort189 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort189 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort190 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort190 xi_sort130 =
  subst_sort190 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort190 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort191 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort191 xi_sort130 =
  subst_sort191 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort191 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort192 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort192 xi_sort130 =
  subst_sort192 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort192 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort193 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort193 xi_sort130 =
  subst_sort193 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort193 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort194 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort194 xi_sort130 =
  subst_sort194 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort194 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort195 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort195 xi_sort130 =
  subst_sort195 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort195 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort196 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort196 xi_sort130 =
  subst_sort196 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort196 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort197 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort197 xi_sort130 =
  subst_sort197 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort197 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort198 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort198 xi_sort130 =
  subst_sort198 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort198 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma rinstInst_sort199 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  ren_sort199 xi_sort130 =
  subst_sort199 (funcomp (var_sort130 n_sort130) xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 rinst_inst_sort199 xi_sort130 _ (fun n => eq_refl) x)).

Qed.

Lemma instId_sort100 {m_sort130 : nat} :
  subst_sort100 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort100 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort101 {m_sort130 : nat} :
  subst_sort101 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort101 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort102 {m_sort130 : nat} :
  subst_sort102 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort102 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort103 {m_sort130 : nat} :
  subst_sort103 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort103 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort104 {m_sort130 : nat} :
  subst_sort104 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort104 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort105 {m_sort130 : nat} :
  subst_sort105 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort105 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort106 {m_sort130 : nat} :
  subst_sort106 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort106 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort107 {m_sort130 : nat} :
  subst_sort107 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort107 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort108 {m_sort130 : nat} :
  subst_sort108 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort108 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort109 {m_sort130 : nat} :
  subst_sort109 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort109 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort110 {m_sort130 : nat} :
  subst_sort110 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort110 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort111 {m_sort130 : nat} :
  subst_sort111 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort111 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort112 {m_sort130 : nat} :
  subst_sort112 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort112 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort113 {m_sort130 : nat} :
  subst_sort113 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort113 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort114 {m_sort130 : nat} :
  subst_sort114 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort114 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort115 {m_sort130 : nat} :
  subst_sort115 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort115 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort116 {m_sort130 : nat} :
  subst_sort116 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort116 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort117 {m_sort130 : nat} :
  subst_sort117 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort117 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort118 {m_sort130 : nat} :
  subst_sort118 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort118 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort119 {m_sort130 : nat} :
  subst_sort119 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort119 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort120 {m_sort130 : nat} :
  subst_sort120 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort120 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort121 {m_sort130 : nat} :
  subst_sort121 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort121 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort122 {m_sort130 : nat} :
  subst_sort122 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort122 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort123 {m_sort130 : nat} :
  subst_sort123 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort123 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort124 {m_sort130 : nat} :
  subst_sort124 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort124 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort125 {m_sort130 : nat} :
  subst_sort125 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort125 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort126 {m_sort130 : nat} :
  subst_sort126 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort126 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort127 {m_sort130 : nat} :
  subst_sort127 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort127 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort128 {m_sort130 : nat} :
  subst_sort128 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort128 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort129 {m_sort130 : nat} :
  subst_sort129 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort129 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort130 {m_sort130 : nat} :
  subst_sort130 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort130 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort131 {m_sort130 : nat} :
  subst_sort131 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort131 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort132 {m_sort130 : nat} :
  subst_sort132 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort132 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort133 {m_sort130 : nat} :
  subst_sort133 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort133 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort134 {m_sort130 : nat} :
  subst_sort134 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort134 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort135 {m_sort130 : nat} :
  subst_sort135 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort135 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort136 {m_sort130 : nat} :
  subst_sort136 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort136 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort137 {m_sort130 : nat} :
  subst_sort137 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort137 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort138 {m_sort130 : nat} :
  subst_sort138 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort138 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort139 {m_sort130 : nat} :
  subst_sort139 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort139 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort140 {m_sort130 : nat} :
  subst_sort140 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort140 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort141 {m_sort130 : nat} :
  subst_sort141 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort141 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort142 {m_sort130 : nat} :
  subst_sort142 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort142 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort143 {m_sort130 : nat} :
  subst_sort143 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort143 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort144 {m_sort130 : nat} :
  subst_sort144 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort144 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort145 {m_sort130 : nat} :
  subst_sort145 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort145 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort146 {m_sort130 : nat} :
  subst_sort146 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort146 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort147 {m_sort130 : nat} :
  subst_sort147 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort147 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort148 {m_sort130 : nat} :
  subst_sort148 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort148 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort149 {m_sort130 : nat} :
  subst_sort149 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort149 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort150 {m_sort130 : nat} :
  subst_sort150 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort150 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort151 {m_sort130 : nat} :
  subst_sort151 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort151 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort152 {m_sort130 : nat} :
  subst_sort152 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort152 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort153 {m_sort130 : nat} :
  subst_sort153 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort153 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort154 {m_sort130 : nat} :
  subst_sort154 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort154 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort155 {m_sort130 : nat} :
  subst_sort155 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort155 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort156 {m_sort130 : nat} :
  subst_sort156 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort156 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort157 {m_sort130 : nat} :
  subst_sort157 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort157 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort158 {m_sort130 : nat} :
  subst_sort158 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort158 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort159 {m_sort130 : nat} :
  subst_sort159 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort159 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort160 {m_sort130 : nat} :
  subst_sort160 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort160 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort161 {m_sort130 : nat} :
  subst_sort161 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort161 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort162 {m_sort130 : nat} :
  subst_sort162 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort162 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort163 {m_sort130 : nat} :
  subst_sort163 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort163 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort164 {m_sort130 : nat} :
  subst_sort164 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort164 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort165 {m_sort130 : nat} :
  subst_sort165 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort165 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort166 {m_sort130 : nat} :
  subst_sort166 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort166 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort167 {m_sort130 : nat} :
  subst_sort167 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort167 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort168 {m_sort130 : nat} :
  subst_sort168 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort168 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort169 {m_sort130 : nat} :
  subst_sort169 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort169 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort170 {m_sort130 : nat} :
  subst_sort170 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort170 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort171 {m_sort130 : nat} :
  subst_sort171 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort171 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort172 {m_sort130 : nat} :
  subst_sort172 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort172 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort173 {m_sort130 : nat} :
  subst_sort173 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort173 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort174 {m_sort130 : nat} :
  subst_sort174 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort174 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort175 {m_sort130 : nat} :
  subst_sort175 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort175 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort176 {m_sort130 : nat} :
  subst_sort176 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort176 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort177 {m_sort130 : nat} :
  subst_sort177 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort177 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort178 {m_sort130 : nat} :
  subst_sort178 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort178 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort179 {m_sort130 : nat} :
  subst_sort179 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort179 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort180 {m_sort130 : nat} :
  subst_sort180 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort180 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort181 {m_sort130 : nat} :
  subst_sort181 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort181 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort182 {m_sort130 : nat} :
  subst_sort182 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort182 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort183 {m_sort130 : nat} :
  subst_sort183 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort183 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort184 {m_sort130 : nat} :
  subst_sort184 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort184 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort185 {m_sort130 : nat} :
  subst_sort185 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort185 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort186 {m_sort130 : nat} :
  subst_sort186 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort186 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort187 {m_sort130 : nat} :
  subst_sort187 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort187 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort188 {m_sort130 : nat} :
  subst_sort188 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort188 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort189 {m_sort130 : nat} :
  subst_sort189 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort189 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort190 {m_sort130 : nat} :
  subst_sort190 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort190 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort191 {m_sort130 : nat} :
  subst_sort191 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort191 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort192 {m_sort130 : nat} :
  subst_sort192 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort192 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort193 {m_sort130 : nat} :
  subst_sort193 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort193 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort194 {m_sort130 : nat} :
  subst_sort194 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort194 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort195 {m_sort130 : nat} :
  subst_sort195 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort195 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort196 {m_sort130 : nat} :
  subst_sort196 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort196 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort197 {m_sort130 : nat} :
  subst_sort197 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort197 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort198 {m_sort130 : nat} :
  subst_sort198 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort198 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma instId_sort199 {m_sort130 : nat} :
  subst_sort199 (var_sort130 m_sort130) = id.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_sort199 (var_sort130 m_sort130) (fun n => eq_refl)
                   (id x))).

Qed.

Lemma rinstId_sort100 {m_sort130 : nat} :
  @ren_sort100 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort100 (id _)) instId_sort100).

Qed.

Lemma rinstId_sort101 {m_sort130 : nat} :
  @ren_sort101 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort101 (id _)) instId_sort101).

Qed.

Lemma rinstId_sort102 {m_sort130 : nat} :
  @ren_sort102 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort102 (id _)) instId_sort102).

Qed.

Lemma rinstId_sort103 {m_sort130 : nat} :
  @ren_sort103 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort103 (id _)) instId_sort103).

Qed.

Lemma rinstId_sort104 {m_sort130 : nat} :
  @ren_sort104 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort104 (id _)) instId_sort104).

Qed.

Lemma rinstId_sort105 {m_sort130 : nat} :
  @ren_sort105 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort105 (id _)) instId_sort105).

Qed.

Lemma rinstId_sort106 {m_sort130 : nat} :
  @ren_sort106 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort106 (id _)) instId_sort106).

Qed.

Lemma rinstId_sort107 {m_sort130 : nat} :
  @ren_sort107 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort107 (id _)) instId_sort107).

Qed.

Lemma rinstId_sort108 {m_sort130 : nat} :
  @ren_sort108 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort108 (id _)) instId_sort108).

Qed.

Lemma rinstId_sort109 {m_sort130 : nat} :
  @ren_sort109 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort109 (id _)) instId_sort109).

Qed.

Lemma rinstId_sort110 {m_sort130 : nat} :
  @ren_sort110 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort110 (id _)) instId_sort110).

Qed.

Lemma rinstId_sort111 {m_sort130 : nat} :
  @ren_sort111 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort111 (id _)) instId_sort111).

Qed.

Lemma rinstId_sort112 {m_sort130 : nat} :
  @ren_sort112 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort112 (id _)) instId_sort112).

Qed.

Lemma rinstId_sort113 {m_sort130 : nat} :
  @ren_sort113 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort113 (id _)) instId_sort113).

Qed.

Lemma rinstId_sort114 {m_sort130 : nat} :
  @ren_sort114 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort114 (id _)) instId_sort114).

Qed.

Lemma rinstId_sort115 {m_sort130 : nat} :
  @ren_sort115 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort115 (id _)) instId_sort115).

Qed.

Lemma rinstId_sort116 {m_sort130 : nat} :
  @ren_sort116 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort116 (id _)) instId_sort116).

Qed.

Lemma rinstId_sort117 {m_sort130 : nat} :
  @ren_sort117 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort117 (id _)) instId_sort117).

Qed.

Lemma rinstId_sort118 {m_sort130 : nat} :
  @ren_sort118 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort118 (id _)) instId_sort118).

Qed.

Lemma rinstId_sort119 {m_sort130 : nat} :
  @ren_sort119 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort119 (id _)) instId_sort119).

Qed.

Lemma rinstId_sort120 {m_sort130 : nat} :
  @ren_sort120 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort120 (id _)) instId_sort120).

Qed.

Lemma rinstId_sort121 {m_sort130 : nat} :
  @ren_sort121 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort121 (id _)) instId_sort121).

Qed.

Lemma rinstId_sort122 {m_sort130 : nat} :
  @ren_sort122 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort122 (id _)) instId_sort122).

Qed.

Lemma rinstId_sort123 {m_sort130 : nat} :
  @ren_sort123 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort123 (id _)) instId_sort123).

Qed.

Lemma rinstId_sort124 {m_sort130 : nat} :
  @ren_sort124 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort124 (id _)) instId_sort124).

Qed.

Lemma rinstId_sort125 {m_sort130 : nat} :
  @ren_sort125 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort125 (id _)) instId_sort125).

Qed.

Lemma rinstId_sort126 {m_sort130 : nat} :
  @ren_sort126 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort126 (id _)) instId_sort126).

Qed.

Lemma rinstId_sort127 {m_sort130 : nat} :
  @ren_sort127 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort127 (id _)) instId_sort127).

Qed.

Lemma rinstId_sort128 {m_sort130 : nat} :
  @ren_sort128 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort128 (id _)) instId_sort128).

Qed.

Lemma rinstId_sort129 {m_sort130 : nat} :
  @ren_sort129 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort129 (id _)) instId_sort129).

Qed.

Lemma rinstId_sort130 {m_sort130 : nat} :
  @ren_sort130 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort130 (id _)) instId_sort130).

Qed.

Lemma rinstId_sort131 {m_sort130 : nat} :
  @ren_sort131 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort131 (id _)) instId_sort131).

Qed.

Lemma rinstId_sort132 {m_sort130 : nat} :
  @ren_sort132 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort132 (id _)) instId_sort132).

Qed.

Lemma rinstId_sort133 {m_sort130 : nat} :
  @ren_sort133 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort133 (id _)) instId_sort133).

Qed.

Lemma rinstId_sort134 {m_sort130 : nat} :
  @ren_sort134 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort134 (id _)) instId_sort134).

Qed.

Lemma rinstId_sort135 {m_sort130 : nat} :
  @ren_sort135 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort135 (id _)) instId_sort135).

Qed.

Lemma rinstId_sort136 {m_sort130 : nat} :
  @ren_sort136 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort136 (id _)) instId_sort136).

Qed.

Lemma rinstId_sort137 {m_sort130 : nat} :
  @ren_sort137 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort137 (id _)) instId_sort137).

Qed.

Lemma rinstId_sort138 {m_sort130 : nat} :
  @ren_sort138 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort138 (id _)) instId_sort138).

Qed.

Lemma rinstId_sort139 {m_sort130 : nat} :
  @ren_sort139 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort139 (id _)) instId_sort139).

Qed.

Lemma rinstId_sort140 {m_sort130 : nat} :
  @ren_sort140 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort140 (id _)) instId_sort140).

Qed.

Lemma rinstId_sort141 {m_sort130 : nat} :
  @ren_sort141 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort141 (id _)) instId_sort141).

Qed.

Lemma rinstId_sort142 {m_sort130 : nat} :
  @ren_sort142 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort142 (id _)) instId_sort142).

Qed.

Lemma rinstId_sort143 {m_sort130 : nat} :
  @ren_sort143 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort143 (id _)) instId_sort143).

Qed.

Lemma rinstId_sort144 {m_sort130 : nat} :
  @ren_sort144 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort144 (id _)) instId_sort144).

Qed.

Lemma rinstId_sort145 {m_sort130 : nat} :
  @ren_sort145 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort145 (id _)) instId_sort145).

Qed.

Lemma rinstId_sort146 {m_sort130 : nat} :
  @ren_sort146 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort146 (id _)) instId_sort146).

Qed.

Lemma rinstId_sort147 {m_sort130 : nat} :
  @ren_sort147 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort147 (id _)) instId_sort147).

Qed.

Lemma rinstId_sort148 {m_sort130 : nat} :
  @ren_sort148 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort148 (id _)) instId_sort148).

Qed.

Lemma rinstId_sort149 {m_sort130 : nat} :
  @ren_sort149 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort149 (id _)) instId_sort149).

Qed.

Lemma rinstId_sort150 {m_sort130 : nat} :
  @ren_sort150 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort150 (id _)) instId_sort150).

Qed.

Lemma rinstId_sort151 {m_sort130 : nat} :
  @ren_sort151 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort151 (id _)) instId_sort151).

Qed.

Lemma rinstId_sort152 {m_sort130 : nat} :
  @ren_sort152 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort152 (id _)) instId_sort152).

Qed.

Lemma rinstId_sort153 {m_sort130 : nat} :
  @ren_sort153 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort153 (id _)) instId_sort153).

Qed.

Lemma rinstId_sort154 {m_sort130 : nat} :
  @ren_sort154 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort154 (id _)) instId_sort154).

Qed.

Lemma rinstId_sort155 {m_sort130 : nat} :
  @ren_sort155 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort155 (id _)) instId_sort155).

Qed.

Lemma rinstId_sort156 {m_sort130 : nat} :
  @ren_sort156 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort156 (id _)) instId_sort156).

Qed.

Lemma rinstId_sort157 {m_sort130 : nat} :
  @ren_sort157 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort157 (id _)) instId_sort157).

Qed.

Lemma rinstId_sort158 {m_sort130 : nat} :
  @ren_sort158 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort158 (id _)) instId_sort158).

Qed.

Lemma rinstId_sort159 {m_sort130 : nat} :
  @ren_sort159 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort159 (id _)) instId_sort159).

Qed.

Lemma rinstId_sort160 {m_sort130 : nat} :
  @ren_sort160 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort160 (id _)) instId_sort160).

Qed.

Lemma rinstId_sort161 {m_sort130 : nat} :
  @ren_sort161 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort161 (id _)) instId_sort161).

Qed.

Lemma rinstId_sort162 {m_sort130 : nat} :
  @ren_sort162 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort162 (id _)) instId_sort162).

Qed.

Lemma rinstId_sort163 {m_sort130 : nat} :
  @ren_sort163 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort163 (id _)) instId_sort163).

Qed.

Lemma rinstId_sort164 {m_sort130 : nat} :
  @ren_sort164 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort164 (id _)) instId_sort164).

Qed.

Lemma rinstId_sort165 {m_sort130 : nat} :
  @ren_sort165 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort165 (id _)) instId_sort165).

Qed.

Lemma rinstId_sort166 {m_sort130 : nat} :
  @ren_sort166 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort166 (id _)) instId_sort166).

Qed.

Lemma rinstId_sort167 {m_sort130 : nat} :
  @ren_sort167 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort167 (id _)) instId_sort167).

Qed.

Lemma rinstId_sort168 {m_sort130 : nat} :
  @ren_sort168 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort168 (id _)) instId_sort168).

Qed.

Lemma rinstId_sort169 {m_sort130 : nat} :
  @ren_sort169 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort169 (id _)) instId_sort169).

Qed.

Lemma rinstId_sort170 {m_sort130 : nat} :
  @ren_sort170 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort170 (id _)) instId_sort170).

Qed.

Lemma rinstId_sort171 {m_sort130 : nat} :
  @ren_sort171 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort171 (id _)) instId_sort171).

Qed.

Lemma rinstId_sort172 {m_sort130 : nat} :
  @ren_sort172 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort172 (id _)) instId_sort172).

Qed.

Lemma rinstId_sort173 {m_sort130 : nat} :
  @ren_sort173 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort173 (id _)) instId_sort173).

Qed.

Lemma rinstId_sort174 {m_sort130 : nat} :
  @ren_sort174 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort174 (id _)) instId_sort174).

Qed.

Lemma rinstId_sort175 {m_sort130 : nat} :
  @ren_sort175 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort175 (id _)) instId_sort175).

Qed.

Lemma rinstId_sort176 {m_sort130 : nat} :
  @ren_sort176 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort176 (id _)) instId_sort176).

Qed.

Lemma rinstId_sort177 {m_sort130 : nat} :
  @ren_sort177 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort177 (id _)) instId_sort177).

Qed.

Lemma rinstId_sort178 {m_sort130 : nat} :
  @ren_sort178 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort178 (id _)) instId_sort178).

Qed.

Lemma rinstId_sort179 {m_sort130 : nat} :
  @ren_sort179 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort179 (id _)) instId_sort179).

Qed.

Lemma rinstId_sort180 {m_sort130 : nat} :
  @ren_sort180 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort180 (id _)) instId_sort180).

Qed.

Lemma rinstId_sort181 {m_sort130 : nat} :
  @ren_sort181 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort181 (id _)) instId_sort181).

Qed.

Lemma rinstId_sort182 {m_sort130 : nat} :
  @ren_sort182 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort182 (id _)) instId_sort182).

Qed.

Lemma rinstId_sort183 {m_sort130 : nat} :
  @ren_sort183 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort183 (id _)) instId_sort183).

Qed.

Lemma rinstId_sort184 {m_sort130 : nat} :
  @ren_sort184 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort184 (id _)) instId_sort184).

Qed.

Lemma rinstId_sort185 {m_sort130 : nat} :
  @ren_sort185 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort185 (id _)) instId_sort185).

Qed.

Lemma rinstId_sort186 {m_sort130 : nat} :
  @ren_sort186 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort186 (id _)) instId_sort186).

Qed.

Lemma rinstId_sort187 {m_sort130 : nat} :
  @ren_sort187 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort187 (id _)) instId_sort187).

Qed.

Lemma rinstId_sort188 {m_sort130 : nat} :
  @ren_sort188 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort188 (id _)) instId_sort188).

Qed.

Lemma rinstId_sort189 {m_sort130 : nat} :
  @ren_sort189 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort189 (id _)) instId_sort189).

Qed.

Lemma rinstId_sort190 {m_sort130 : nat} :
  @ren_sort190 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort190 (id _)) instId_sort190).

Qed.

Lemma rinstId_sort191 {m_sort130 : nat} :
  @ren_sort191 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort191 (id _)) instId_sort191).

Qed.

Lemma rinstId_sort192 {m_sort130 : nat} :
  @ren_sort192 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort192 (id _)) instId_sort192).

Qed.

Lemma rinstId_sort193 {m_sort130 : nat} :
  @ren_sort193 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort193 (id _)) instId_sort193).

Qed.

Lemma rinstId_sort194 {m_sort130 : nat} :
  @ren_sort194 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort194 (id _)) instId_sort194).

Qed.

Lemma rinstId_sort195 {m_sort130 : nat} :
  @ren_sort195 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort195 (id _)) instId_sort195).

Qed.

Lemma rinstId_sort196 {m_sort130 : nat} :
  @ren_sort196 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort196 (id _)) instId_sort196).

Qed.

Lemma rinstId_sort197 {m_sort130 : nat} :
  @ren_sort197 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort197 (id _)) instId_sort197).

Qed.

Lemma rinstId_sort198 {m_sort130 : nat} :
  @ren_sort198 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort198 (id _)) instId_sort198).

Qed.

Lemma rinstId_sort199 {m_sort130 : nat} :
  @ren_sort199 m_sort130 m_sort130 id = id.

Proof.
exact (eq_trans (rinstInst_sort199 (id _)) instId_sort199).

Qed.

Lemma varL_sort130 {m_sort130 : nat} {n_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 n_sort130) :
  funcomp (subst_sort130 sigma_sort130) (var_sort130 m_sort130) =
  sigma_sort130.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma varLRen_sort130 {m_sort130 : nat} {n_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin n_sort130) :
  funcomp (ren_sort130 xi_sort130) (var_sort130 m_sort130) =
  funcomp (var_sort130 n_sort130) xi_sort130.

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).

Qed.

Lemma renRen'_sort100 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort100 zeta_sort130) (ren_sort100 xi_sort130) =
  ren_sort100 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort100 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort101 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort101 zeta_sort130) (ren_sort101 xi_sort130) =
  ren_sort101 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort101 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort102 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort102 zeta_sort130) (ren_sort102 xi_sort130) =
  ren_sort102 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort102 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort103 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort103 zeta_sort130) (ren_sort103 xi_sort130) =
  ren_sort103 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort103 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort104 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort104 zeta_sort130) (ren_sort104 xi_sort130) =
  ren_sort104 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort104 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort105 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort105 zeta_sort130) (ren_sort105 xi_sort130) =
  ren_sort105 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort105 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort106 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort106 zeta_sort130) (ren_sort106 xi_sort130) =
  ren_sort106 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort106 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort107 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort107 zeta_sort130) (ren_sort107 xi_sort130) =
  ren_sort107 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort107 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort108 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort108 zeta_sort130) (ren_sort108 xi_sort130) =
  ren_sort108 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort108 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort109 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort109 zeta_sort130) (ren_sort109 xi_sort130) =
  ren_sort109 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort109 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort110 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort110 zeta_sort130) (ren_sort110 xi_sort130) =
  ren_sort110 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort110 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort111 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort111 zeta_sort130) (ren_sort111 xi_sort130) =
  ren_sort111 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort111 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort112 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort112 zeta_sort130) (ren_sort112 xi_sort130) =
  ren_sort112 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort112 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort113 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort113 zeta_sort130) (ren_sort113 xi_sort130) =
  ren_sort113 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort113 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort114 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort114 zeta_sort130) (ren_sort114 xi_sort130) =
  ren_sort114 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort114 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort115 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort115 zeta_sort130) (ren_sort115 xi_sort130) =
  ren_sort115 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort115 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort116 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort116 zeta_sort130) (ren_sort116 xi_sort130) =
  ren_sort116 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort116 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort117 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort117 zeta_sort130) (ren_sort117 xi_sort130) =
  ren_sort117 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort117 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort118 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort118 zeta_sort130) (ren_sort118 xi_sort130) =
  ren_sort118 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort118 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort119 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort119 zeta_sort130) (ren_sort119 xi_sort130) =
  ren_sort119 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort119 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort120 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort120 zeta_sort130) (ren_sort120 xi_sort130) =
  ren_sort120 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort120 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort121 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort121 zeta_sort130) (ren_sort121 xi_sort130) =
  ren_sort121 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort121 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort122 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort122 zeta_sort130) (ren_sort122 xi_sort130) =
  ren_sort122 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort122 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort123 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort123 zeta_sort130) (ren_sort123 xi_sort130) =
  ren_sort123 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort123 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort124 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort124 zeta_sort130) (ren_sort124 xi_sort130) =
  ren_sort124 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort124 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort125 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort125 zeta_sort130) (ren_sort125 xi_sort130) =
  ren_sort125 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort125 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort126 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort126 zeta_sort130) (ren_sort126 xi_sort130) =
  ren_sort126 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort126 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort127 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort127 zeta_sort130) (ren_sort127 xi_sort130) =
  ren_sort127 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort127 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort128 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort128 zeta_sort130) (ren_sort128 xi_sort130) =
  ren_sort128 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort128 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort129 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort129 zeta_sort130) (ren_sort129 xi_sort130) =
  ren_sort129 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort129 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort130 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort130 zeta_sort130) (ren_sort130 xi_sort130) =
  ren_sort130 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort130 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort131 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort131 zeta_sort130) (ren_sort131 xi_sort130) =
  ren_sort131 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort131 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort132 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort132 zeta_sort130) (ren_sort132 xi_sort130) =
  ren_sort132 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort132 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort133 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort133 zeta_sort130) (ren_sort133 xi_sort130) =
  ren_sort133 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort133 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort134 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort134 zeta_sort130) (ren_sort134 xi_sort130) =
  ren_sort134 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort134 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort135 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort135 zeta_sort130) (ren_sort135 xi_sort130) =
  ren_sort135 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort135 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort136 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort136 zeta_sort130) (ren_sort136 xi_sort130) =
  ren_sort136 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort136 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort137 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort137 zeta_sort130) (ren_sort137 xi_sort130) =
  ren_sort137 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort137 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort138 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort138 zeta_sort130) (ren_sort138 xi_sort130) =
  ren_sort138 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort138 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort139 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort139 zeta_sort130) (ren_sort139 xi_sort130) =
  ren_sort139 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort139 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort140 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort140 zeta_sort130) (ren_sort140 xi_sort130) =
  ren_sort140 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort140 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort141 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort141 zeta_sort130) (ren_sort141 xi_sort130) =
  ren_sort141 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort141 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort142 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort142 zeta_sort130) (ren_sort142 xi_sort130) =
  ren_sort142 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort142 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort143 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort143 zeta_sort130) (ren_sort143 xi_sort130) =
  ren_sort143 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort143 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort144 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort144 zeta_sort130) (ren_sort144 xi_sort130) =
  ren_sort144 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort144 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort145 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort145 zeta_sort130) (ren_sort145 xi_sort130) =
  ren_sort145 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort145 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort146 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort146 zeta_sort130) (ren_sort146 xi_sort130) =
  ren_sort146 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort146 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort147 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort147 zeta_sort130) (ren_sort147 xi_sort130) =
  ren_sort147 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort147 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort148 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort148 zeta_sort130) (ren_sort148 xi_sort130) =
  ren_sort148 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort148 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort149 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort149 zeta_sort130) (ren_sort149 xi_sort130) =
  ren_sort149 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort149 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort150 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort150 zeta_sort130) (ren_sort150 xi_sort130) =
  ren_sort150 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort150 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort151 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort151 zeta_sort130) (ren_sort151 xi_sort130) =
  ren_sort151 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort151 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort152 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort152 zeta_sort130) (ren_sort152 xi_sort130) =
  ren_sort152 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort152 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort153 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort153 zeta_sort130) (ren_sort153 xi_sort130) =
  ren_sort153 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort153 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort154 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort154 zeta_sort130) (ren_sort154 xi_sort130) =
  ren_sort154 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort154 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort155 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort155 zeta_sort130) (ren_sort155 xi_sort130) =
  ren_sort155 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort155 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort156 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort156 zeta_sort130) (ren_sort156 xi_sort130) =
  ren_sort156 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort156 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort157 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort157 zeta_sort130) (ren_sort157 xi_sort130) =
  ren_sort157 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort157 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort158 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort158 zeta_sort130) (ren_sort158 xi_sort130) =
  ren_sort158 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort158 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort159 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort159 zeta_sort130) (ren_sort159 xi_sort130) =
  ren_sort159 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort159 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort160 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort160 zeta_sort130) (ren_sort160 xi_sort130) =
  ren_sort160 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort160 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort161 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort161 zeta_sort130) (ren_sort161 xi_sort130) =
  ren_sort161 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort161 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort162 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort162 zeta_sort130) (ren_sort162 xi_sort130) =
  ren_sort162 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort162 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort163 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort163 zeta_sort130) (ren_sort163 xi_sort130) =
  ren_sort163 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort163 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort164 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort164 zeta_sort130) (ren_sort164 xi_sort130) =
  ren_sort164 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort164 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort165 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort165 zeta_sort130) (ren_sort165 xi_sort130) =
  ren_sort165 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort165 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort166 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort166 zeta_sort130) (ren_sort166 xi_sort130) =
  ren_sort166 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort166 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort167 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort167 zeta_sort130) (ren_sort167 xi_sort130) =
  ren_sort167 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort167 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort168 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort168 zeta_sort130) (ren_sort168 xi_sort130) =
  ren_sort168 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort168 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort169 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort169 zeta_sort130) (ren_sort169 xi_sort130) =
  ren_sort169 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort169 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort170 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort170 zeta_sort130) (ren_sort170 xi_sort130) =
  ren_sort170 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort170 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort171 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort171 zeta_sort130) (ren_sort171 xi_sort130) =
  ren_sort171 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort171 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort172 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort172 zeta_sort130) (ren_sort172 xi_sort130) =
  ren_sort172 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort172 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort173 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort173 zeta_sort130) (ren_sort173 xi_sort130) =
  ren_sort173 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort173 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort174 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort174 zeta_sort130) (ren_sort174 xi_sort130) =
  ren_sort174 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort174 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort175 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort175 zeta_sort130) (ren_sort175 xi_sort130) =
  ren_sort175 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort175 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort176 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort176 zeta_sort130) (ren_sort176 xi_sort130) =
  ren_sort176 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort176 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort177 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort177 zeta_sort130) (ren_sort177 xi_sort130) =
  ren_sort177 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort177 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort178 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort178 zeta_sort130) (ren_sort178 xi_sort130) =
  ren_sort178 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort178 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort179 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort179 zeta_sort130) (ren_sort179 xi_sort130) =
  ren_sort179 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort179 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort180 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort180 zeta_sort130) (ren_sort180 xi_sort130) =
  ren_sort180 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort180 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort181 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort181 zeta_sort130) (ren_sort181 xi_sort130) =
  ren_sort181 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort181 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort182 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort182 zeta_sort130) (ren_sort182 xi_sort130) =
  ren_sort182 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort182 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort183 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort183 zeta_sort130) (ren_sort183 xi_sort130) =
  ren_sort183 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort183 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort184 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort184 zeta_sort130) (ren_sort184 xi_sort130) =
  ren_sort184 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort184 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort185 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort185 zeta_sort130) (ren_sort185 xi_sort130) =
  ren_sort185 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort185 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort186 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort186 zeta_sort130) (ren_sort186 xi_sort130) =
  ren_sort186 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort186 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort187 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort187 zeta_sort130) (ren_sort187 xi_sort130) =
  ren_sort187 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort187 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort188 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort188 zeta_sort130) (ren_sort188 xi_sort130) =
  ren_sort188 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort188 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort189 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort189 zeta_sort130) (ren_sort189 xi_sort130) =
  ren_sort189 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort189 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort190 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort190 zeta_sort130) (ren_sort190 xi_sort130) =
  ren_sort190 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort190 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort191 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort191 zeta_sort130) (ren_sort191 xi_sort130) =
  ren_sort191 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort191 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort192 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort192 zeta_sort130) (ren_sort192 xi_sort130) =
  ren_sort192 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort192 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort193 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort193 zeta_sort130) (ren_sort193 xi_sort130) =
  ren_sort193 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort193 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort194 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort194 zeta_sort130) (ren_sort194 xi_sort130) =
  ren_sort194 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort194 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort195 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort195 zeta_sort130) (ren_sort195 xi_sort130) =
  ren_sort195 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort195 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort196 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort196 zeta_sort130) (ren_sort196 xi_sort130) =
  ren_sort196 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort196 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort197 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort197 zeta_sort130) (ren_sort197 xi_sort130) =
  ren_sort197 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort197 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort198 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort198 zeta_sort130) (ren_sort198 xi_sort130) =
  ren_sort198 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort198 xi_sort130 zeta_sort130 n)).

Qed.

Lemma renRen'_sort199 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort199 zeta_sort130) (ren_sort199 xi_sort130) =
  ren_sort199 (funcomp zeta_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_sort199 xi_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort100 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort100 zeta_sort130) (subst_sort100 sigma_sort130) =
  subst_sort100 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort100 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort101 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort101 zeta_sort130) (subst_sort101 sigma_sort130) =
  subst_sort101 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort101 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort102 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort102 zeta_sort130) (subst_sort102 sigma_sort130) =
  subst_sort102 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort102 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort103 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort103 zeta_sort130) (subst_sort103 sigma_sort130) =
  subst_sort103 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort103 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort104 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort104 zeta_sort130) (subst_sort104 sigma_sort130) =
  subst_sort104 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort104 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort105 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort105 zeta_sort130) (subst_sort105 sigma_sort130) =
  subst_sort105 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort105 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort106 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort106 zeta_sort130) (subst_sort106 sigma_sort130) =
  subst_sort106 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort106 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort107 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort107 zeta_sort130) (subst_sort107 sigma_sort130) =
  subst_sort107 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort107 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort108 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort108 zeta_sort130) (subst_sort108 sigma_sort130) =
  subst_sort108 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort108 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort109 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort109 zeta_sort130) (subst_sort109 sigma_sort130) =
  subst_sort109 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort109 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort110 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort110 zeta_sort130) (subst_sort110 sigma_sort130) =
  subst_sort110 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort110 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort111 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort111 zeta_sort130) (subst_sort111 sigma_sort130) =
  subst_sort111 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort111 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort112 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort112 zeta_sort130) (subst_sort112 sigma_sort130) =
  subst_sort112 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort112 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort113 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort113 zeta_sort130) (subst_sort113 sigma_sort130) =
  subst_sort113 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort113 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort114 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort114 zeta_sort130) (subst_sort114 sigma_sort130) =
  subst_sort114 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort114 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort115 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort115 zeta_sort130) (subst_sort115 sigma_sort130) =
  subst_sort115 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort115 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort116 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort116 zeta_sort130) (subst_sort116 sigma_sort130) =
  subst_sort116 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort116 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort117 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort117 zeta_sort130) (subst_sort117 sigma_sort130) =
  subst_sort117 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort117 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort118 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort118 zeta_sort130) (subst_sort118 sigma_sort130) =
  subst_sort118 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort118 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort119 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort119 zeta_sort130) (subst_sort119 sigma_sort130) =
  subst_sort119 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort119 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort120 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort120 zeta_sort130) (subst_sort120 sigma_sort130) =
  subst_sort120 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort120 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort121 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort121 zeta_sort130) (subst_sort121 sigma_sort130) =
  subst_sort121 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort121 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort122 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort122 zeta_sort130) (subst_sort122 sigma_sort130) =
  subst_sort122 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort122 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort123 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort123 zeta_sort130) (subst_sort123 sigma_sort130) =
  subst_sort123 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort123 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort124 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort124 zeta_sort130) (subst_sort124 sigma_sort130) =
  subst_sort124 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort124 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort125 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort125 zeta_sort130) (subst_sort125 sigma_sort130) =
  subst_sort125 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort125 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort126 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort126 zeta_sort130) (subst_sort126 sigma_sort130) =
  subst_sort126 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort126 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort127 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort127 zeta_sort130) (subst_sort127 sigma_sort130) =
  subst_sort127 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort127 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort128 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort128 zeta_sort130) (subst_sort128 sigma_sort130) =
  subst_sort128 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort128 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort129 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort129 zeta_sort130) (subst_sort129 sigma_sort130) =
  subst_sort129 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort129 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort130 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort130 zeta_sort130) (subst_sort130 sigma_sort130) =
  subst_sort130 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort130 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort131 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort131 zeta_sort130) (subst_sort131 sigma_sort130) =
  subst_sort131 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort131 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort132 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort132 zeta_sort130) (subst_sort132 sigma_sort130) =
  subst_sort132 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort132 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort133 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort133 zeta_sort130) (subst_sort133 sigma_sort130) =
  subst_sort133 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort133 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort134 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort134 zeta_sort130) (subst_sort134 sigma_sort130) =
  subst_sort134 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort134 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort135 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort135 zeta_sort130) (subst_sort135 sigma_sort130) =
  subst_sort135 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort135 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort136 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort136 zeta_sort130) (subst_sort136 sigma_sort130) =
  subst_sort136 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort136 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort137 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort137 zeta_sort130) (subst_sort137 sigma_sort130) =
  subst_sort137 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort137 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort138 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort138 zeta_sort130) (subst_sort138 sigma_sort130) =
  subst_sort138 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort138 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort139 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort139 zeta_sort130) (subst_sort139 sigma_sort130) =
  subst_sort139 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort139 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort140 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort140 zeta_sort130) (subst_sort140 sigma_sort130) =
  subst_sort140 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort140 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort141 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort141 zeta_sort130) (subst_sort141 sigma_sort130) =
  subst_sort141 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort141 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort142 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort142 zeta_sort130) (subst_sort142 sigma_sort130) =
  subst_sort142 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort142 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort143 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort143 zeta_sort130) (subst_sort143 sigma_sort130) =
  subst_sort143 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort143 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort144 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort144 zeta_sort130) (subst_sort144 sigma_sort130) =
  subst_sort144 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort144 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort145 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort145 zeta_sort130) (subst_sort145 sigma_sort130) =
  subst_sort145 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort145 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort146 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort146 zeta_sort130) (subst_sort146 sigma_sort130) =
  subst_sort146 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort146 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort147 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort147 zeta_sort130) (subst_sort147 sigma_sort130) =
  subst_sort147 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort147 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort148 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort148 zeta_sort130) (subst_sort148 sigma_sort130) =
  subst_sort148 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort148 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort149 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort149 zeta_sort130) (subst_sort149 sigma_sort130) =
  subst_sort149 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort149 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort150 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort150 zeta_sort130) (subst_sort150 sigma_sort130) =
  subst_sort150 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort150 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort151 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort151 zeta_sort130) (subst_sort151 sigma_sort130) =
  subst_sort151 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort151 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort152 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort152 zeta_sort130) (subst_sort152 sigma_sort130) =
  subst_sort152 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort152 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort153 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort153 zeta_sort130) (subst_sort153 sigma_sort130) =
  subst_sort153 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort153 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort154 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort154 zeta_sort130) (subst_sort154 sigma_sort130) =
  subst_sort154 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort154 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort155 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort155 zeta_sort130) (subst_sort155 sigma_sort130) =
  subst_sort155 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort155 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort156 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort156 zeta_sort130) (subst_sort156 sigma_sort130) =
  subst_sort156 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort156 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort157 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort157 zeta_sort130) (subst_sort157 sigma_sort130) =
  subst_sort157 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort157 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort158 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort158 zeta_sort130) (subst_sort158 sigma_sort130) =
  subst_sort158 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort158 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort159 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort159 zeta_sort130) (subst_sort159 sigma_sort130) =
  subst_sort159 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort159 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort160 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort160 zeta_sort130) (subst_sort160 sigma_sort130) =
  subst_sort160 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort160 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort161 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort161 zeta_sort130) (subst_sort161 sigma_sort130) =
  subst_sort161 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort161 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort162 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort162 zeta_sort130) (subst_sort162 sigma_sort130) =
  subst_sort162 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort162 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort163 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort163 zeta_sort130) (subst_sort163 sigma_sort130) =
  subst_sort163 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort163 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort164 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort164 zeta_sort130) (subst_sort164 sigma_sort130) =
  subst_sort164 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort164 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort165 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort165 zeta_sort130) (subst_sort165 sigma_sort130) =
  subst_sort165 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort165 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort166 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort166 zeta_sort130) (subst_sort166 sigma_sort130) =
  subst_sort166 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort166 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort167 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort167 zeta_sort130) (subst_sort167 sigma_sort130) =
  subst_sort167 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort167 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort168 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort168 zeta_sort130) (subst_sort168 sigma_sort130) =
  subst_sort168 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort168 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort169 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort169 zeta_sort130) (subst_sort169 sigma_sort130) =
  subst_sort169 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort169 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort170 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort170 zeta_sort130) (subst_sort170 sigma_sort130) =
  subst_sort170 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort170 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort171 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort171 zeta_sort130) (subst_sort171 sigma_sort130) =
  subst_sort171 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort171 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort172 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort172 zeta_sort130) (subst_sort172 sigma_sort130) =
  subst_sort172 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort172 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort173 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort173 zeta_sort130) (subst_sort173 sigma_sort130) =
  subst_sort173 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort173 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort174 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort174 zeta_sort130) (subst_sort174 sigma_sort130) =
  subst_sort174 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort174 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort175 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort175 zeta_sort130) (subst_sort175 sigma_sort130) =
  subst_sort175 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort175 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort176 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort176 zeta_sort130) (subst_sort176 sigma_sort130) =
  subst_sort176 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort176 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort177 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort177 zeta_sort130) (subst_sort177 sigma_sort130) =
  subst_sort177 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort177 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort178 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort178 zeta_sort130) (subst_sort178 sigma_sort130) =
  subst_sort178 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort178 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort179 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort179 zeta_sort130) (subst_sort179 sigma_sort130) =
  subst_sort179 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort179 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort180 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort180 zeta_sort130) (subst_sort180 sigma_sort130) =
  subst_sort180 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort180 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort181 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort181 zeta_sort130) (subst_sort181 sigma_sort130) =
  subst_sort181 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort181 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort182 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort182 zeta_sort130) (subst_sort182 sigma_sort130) =
  subst_sort182 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort182 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort183 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort183 zeta_sort130) (subst_sort183 sigma_sort130) =
  subst_sort183 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort183 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort184 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort184 zeta_sort130) (subst_sort184 sigma_sort130) =
  subst_sort184 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort184 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort185 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort185 zeta_sort130) (subst_sort185 sigma_sort130) =
  subst_sort185 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort185 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort186 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort186 zeta_sort130) (subst_sort186 sigma_sort130) =
  subst_sort186 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort186 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort187 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort187 zeta_sort130) (subst_sort187 sigma_sort130) =
  subst_sort187 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort187 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort188 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort188 zeta_sort130) (subst_sort188 sigma_sort130) =
  subst_sort188 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort188 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort189 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort189 zeta_sort130) (subst_sort189 sigma_sort130) =
  subst_sort189 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort189 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort190 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort190 zeta_sort130) (subst_sort190 sigma_sort130) =
  subst_sort190 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort190 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort191 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort191 zeta_sort130) (subst_sort191 sigma_sort130) =
  subst_sort191 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort191 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort192 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort192 zeta_sort130) (subst_sort192 sigma_sort130) =
  subst_sort192 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort192 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort193 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort193 zeta_sort130) (subst_sort193 sigma_sort130) =
  subst_sort193 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort193 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort194 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort194 zeta_sort130) (subst_sort194 sigma_sort130) =
  subst_sort194 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort194 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort195 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort195 zeta_sort130) (subst_sort195 sigma_sort130) =
  subst_sort195 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort195 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort196 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort196 zeta_sort130) (subst_sort196 sigma_sort130) =
  subst_sort196 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort196 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort197 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort197 zeta_sort130) (subst_sort197 sigma_sort130) =
  subst_sort197 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort197 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort198 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort198 zeta_sort130) (subst_sort198 sigma_sort130) =
  subst_sort198 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort198 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma compRen'_sort199 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (zeta_sort130 : fin k_sort130 -> fin l_sort130) :
  funcomp (ren_sort199 zeta_sort130) (subst_sort199 sigma_sort130) =
  subst_sort199 (funcomp (ren_sort130 zeta_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_sort199 sigma_sort130 zeta_sort130 n)).

Qed.

Lemma renComp'_sort100 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort100 tau_sort130) (ren_sort100 xi_sort130) =
  subst_sort100 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort100 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort101 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort101 tau_sort130) (ren_sort101 xi_sort130) =
  subst_sort101 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort101 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort102 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort102 tau_sort130) (ren_sort102 xi_sort130) =
  subst_sort102 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort102 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort103 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort103 tau_sort130) (ren_sort103 xi_sort130) =
  subst_sort103 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort103 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort104 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort104 tau_sort130) (ren_sort104 xi_sort130) =
  subst_sort104 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort104 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort105 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort105 tau_sort130) (ren_sort105 xi_sort130) =
  subst_sort105 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort105 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort106 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort106 tau_sort130) (ren_sort106 xi_sort130) =
  subst_sort106 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort106 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort107 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort107 tau_sort130) (ren_sort107 xi_sort130) =
  subst_sort107 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort107 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort108 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort108 tau_sort130) (ren_sort108 xi_sort130) =
  subst_sort108 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort108 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort109 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort109 tau_sort130) (ren_sort109 xi_sort130) =
  subst_sort109 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort109 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort110 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort110 tau_sort130) (ren_sort110 xi_sort130) =
  subst_sort110 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort110 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort111 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort111 tau_sort130) (ren_sort111 xi_sort130) =
  subst_sort111 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort111 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort112 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort112 tau_sort130) (ren_sort112 xi_sort130) =
  subst_sort112 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort112 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort113 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort113 tau_sort130) (ren_sort113 xi_sort130) =
  subst_sort113 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort113 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort114 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort114 tau_sort130) (ren_sort114 xi_sort130) =
  subst_sort114 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort114 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort115 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort115 tau_sort130) (ren_sort115 xi_sort130) =
  subst_sort115 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort115 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort116 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort116 tau_sort130) (ren_sort116 xi_sort130) =
  subst_sort116 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort116 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort117 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort117 tau_sort130) (ren_sort117 xi_sort130) =
  subst_sort117 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort117 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort118 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort118 tau_sort130) (ren_sort118 xi_sort130) =
  subst_sort118 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort118 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort119 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort119 tau_sort130) (ren_sort119 xi_sort130) =
  subst_sort119 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort119 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort120 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort120 tau_sort130) (ren_sort120 xi_sort130) =
  subst_sort120 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort120 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort121 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort121 tau_sort130) (ren_sort121 xi_sort130) =
  subst_sort121 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort121 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort122 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort122 tau_sort130) (ren_sort122 xi_sort130) =
  subst_sort122 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort122 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort123 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort123 tau_sort130) (ren_sort123 xi_sort130) =
  subst_sort123 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort123 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort124 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort124 tau_sort130) (ren_sort124 xi_sort130) =
  subst_sort124 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort124 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort125 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort125 tau_sort130) (ren_sort125 xi_sort130) =
  subst_sort125 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort125 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort126 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort126 tau_sort130) (ren_sort126 xi_sort130) =
  subst_sort126 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort126 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort127 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort127 tau_sort130) (ren_sort127 xi_sort130) =
  subst_sort127 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort127 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort128 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort128 tau_sort130) (ren_sort128 xi_sort130) =
  subst_sort128 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort128 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort129 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort129 tau_sort130) (ren_sort129 xi_sort130) =
  subst_sort129 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort129 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort130 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort130 tau_sort130) (ren_sort130 xi_sort130) =
  subst_sort130 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort130 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort131 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort131 tau_sort130) (ren_sort131 xi_sort130) =
  subst_sort131 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort131 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort132 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort132 tau_sort130) (ren_sort132 xi_sort130) =
  subst_sort132 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort132 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort133 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort133 tau_sort130) (ren_sort133 xi_sort130) =
  subst_sort133 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort133 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort134 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort134 tau_sort130) (ren_sort134 xi_sort130) =
  subst_sort134 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort134 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort135 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort135 tau_sort130) (ren_sort135 xi_sort130) =
  subst_sort135 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort135 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort136 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort136 tau_sort130) (ren_sort136 xi_sort130) =
  subst_sort136 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort136 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort137 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort137 tau_sort130) (ren_sort137 xi_sort130) =
  subst_sort137 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort137 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort138 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort138 tau_sort130) (ren_sort138 xi_sort130) =
  subst_sort138 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort138 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort139 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort139 tau_sort130) (ren_sort139 xi_sort130) =
  subst_sort139 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort139 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort140 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort140 tau_sort130) (ren_sort140 xi_sort130) =
  subst_sort140 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort140 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort141 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort141 tau_sort130) (ren_sort141 xi_sort130) =
  subst_sort141 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort141 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort142 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort142 tau_sort130) (ren_sort142 xi_sort130) =
  subst_sort142 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort142 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort143 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort143 tau_sort130) (ren_sort143 xi_sort130) =
  subst_sort143 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort143 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort144 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort144 tau_sort130) (ren_sort144 xi_sort130) =
  subst_sort144 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort144 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort145 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort145 tau_sort130) (ren_sort145 xi_sort130) =
  subst_sort145 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort145 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort146 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort146 tau_sort130) (ren_sort146 xi_sort130) =
  subst_sort146 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort146 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort147 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort147 tau_sort130) (ren_sort147 xi_sort130) =
  subst_sort147 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort147 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort148 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort148 tau_sort130) (ren_sort148 xi_sort130) =
  subst_sort148 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort148 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort149 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort149 tau_sort130) (ren_sort149 xi_sort130) =
  subst_sort149 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort149 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort150 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort150 tau_sort130) (ren_sort150 xi_sort130) =
  subst_sort150 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort150 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort151 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort151 tau_sort130) (ren_sort151 xi_sort130) =
  subst_sort151 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort151 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort152 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort152 tau_sort130) (ren_sort152 xi_sort130) =
  subst_sort152 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort152 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort153 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort153 tau_sort130) (ren_sort153 xi_sort130) =
  subst_sort153 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort153 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort154 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort154 tau_sort130) (ren_sort154 xi_sort130) =
  subst_sort154 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort154 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort155 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort155 tau_sort130) (ren_sort155 xi_sort130) =
  subst_sort155 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort155 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort156 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort156 tau_sort130) (ren_sort156 xi_sort130) =
  subst_sort156 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort156 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort157 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort157 tau_sort130) (ren_sort157 xi_sort130) =
  subst_sort157 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort157 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort158 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort158 tau_sort130) (ren_sort158 xi_sort130) =
  subst_sort158 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort158 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort159 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort159 tau_sort130) (ren_sort159 xi_sort130) =
  subst_sort159 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort159 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort160 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort160 tau_sort130) (ren_sort160 xi_sort130) =
  subst_sort160 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort160 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort161 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort161 tau_sort130) (ren_sort161 xi_sort130) =
  subst_sort161 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort161 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort162 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort162 tau_sort130) (ren_sort162 xi_sort130) =
  subst_sort162 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort162 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort163 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort163 tau_sort130) (ren_sort163 xi_sort130) =
  subst_sort163 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort163 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort164 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort164 tau_sort130) (ren_sort164 xi_sort130) =
  subst_sort164 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort164 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort165 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort165 tau_sort130) (ren_sort165 xi_sort130) =
  subst_sort165 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort165 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort166 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort166 tau_sort130) (ren_sort166 xi_sort130) =
  subst_sort166 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort166 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort167 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort167 tau_sort130) (ren_sort167 xi_sort130) =
  subst_sort167 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort167 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort168 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort168 tau_sort130) (ren_sort168 xi_sort130) =
  subst_sort168 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort168 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort169 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort169 tau_sort130) (ren_sort169 xi_sort130) =
  subst_sort169 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort169 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort170 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort170 tau_sort130) (ren_sort170 xi_sort130) =
  subst_sort170 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort170 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort171 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort171 tau_sort130) (ren_sort171 xi_sort130) =
  subst_sort171 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort171 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort172 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort172 tau_sort130) (ren_sort172 xi_sort130) =
  subst_sort172 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort172 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort173 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort173 tau_sort130) (ren_sort173 xi_sort130) =
  subst_sort173 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort173 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort174 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort174 tau_sort130) (ren_sort174 xi_sort130) =
  subst_sort174 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort174 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort175 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort175 tau_sort130) (ren_sort175 xi_sort130) =
  subst_sort175 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort175 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort176 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort176 tau_sort130) (ren_sort176 xi_sort130) =
  subst_sort176 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort176 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort177 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort177 tau_sort130) (ren_sort177 xi_sort130) =
  subst_sort177 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort177 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort178 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort178 tau_sort130) (ren_sort178 xi_sort130) =
  subst_sort178 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort178 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort179 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort179 tau_sort130) (ren_sort179 xi_sort130) =
  subst_sort179 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort179 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort180 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort180 tau_sort130) (ren_sort180 xi_sort130) =
  subst_sort180 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort180 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort181 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort181 tau_sort130) (ren_sort181 xi_sort130) =
  subst_sort181 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort181 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort182 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort182 tau_sort130) (ren_sort182 xi_sort130) =
  subst_sort182 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort182 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort183 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort183 tau_sort130) (ren_sort183 xi_sort130) =
  subst_sort183 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort183 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort184 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort184 tau_sort130) (ren_sort184 xi_sort130) =
  subst_sort184 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort184 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort185 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort185 tau_sort130) (ren_sort185 xi_sort130) =
  subst_sort185 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort185 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort186 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort186 tau_sort130) (ren_sort186 xi_sort130) =
  subst_sort186 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort186 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort187 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort187 tau_sort130) (ren_sort187 xi_sort130) =
  subst_sort187 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort187 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort188 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort188 tau_sort130) (ren_sort188 xi_sort130) =
  subst_sort188 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort188 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort189 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort189 tau_sort130) (ren_sort189 xi_sort130) =
  subst_sort189 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort189 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort190 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort190 tau_sort130) (ren_sort190 xi_sort130) =
  subst_sort190 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort190 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort191 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort191 tau_sort130) (ren_sort191 xi_sort130) =
  subst_sort191 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort191 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort192 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort192 tau_sort130) (ren_sort192 xi_sort130) =
  subst_sort192 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort192 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort193 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort193 tau_sort130) (ren_sort193 xi_sort130) =
  subst_sort193 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort193 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort194 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort194 tau_sort130) (ren_sort194 xi_sort130) =
  subst_sort194 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort194 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort195 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort195 tau_sort130) (ren_sort195 xi_sort130) =
  subst_sort195 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort195 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort196 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort196 tau_sort130) (ren_sort196 xi_sort130) =
  subst_sort196 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort196 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort197 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort197 tau_sort130) (ren_sort197 xi_sort130) =
  subst_sort197 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort197 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort198 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort198 tau_sort130) (ren_sort198 xi_sort130) =
  subst_sort198 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort198 xi_sort130 tau_sort130 n)).

Qed.

Lemma renComp'_sort199 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (xi_sort130 : fin m_sort130 -> fin k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort199 tau_sort130) (ren_sort199 xi_sort130) =
  subst_sort199 (funcomp tau_sort130 xi_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_sort199 xi_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort100 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort100 tau_sort130) (subst_sort100 sigma_sort130) =
  subst_sort100 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort100 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort101 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort101 tau_sort130) (subst_sort101 sigma_sort130) =
  subst_sort101 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort101 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort102 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort102 tau_sort130) (subst_sort102 sigma_sort130) =
  subst_sort102 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort102 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort103 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort103 tau_sort130) (subst_sort103 sigma_sort130) =
  subst_sort103 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort103 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort104 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort104 tau_sort130) (subst_sort104 sigma_sort130) =
  subst_sort104 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort104 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort105 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort105 tau_sort130) (subst_sort105 sigma_sort130) =
  subst_sort105 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort105 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort106 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort106 tau_sort130) (subst_sort106 sigma_sort130) =
  subst_sort106 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort106 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort107 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort107 tau_sort130) (subst_sort107 sigma_sort130) =
  subst_sort107 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort107 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort108 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort108 tau_sort130) (subst_sort108 sigma_sort130) =
  subst_sort108 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort108 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort109 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort109 tau_sort130) (subst_sort109 sigma_sort130) =
  subst_sort109 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort109 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort110 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort110 tau_sort130) (subst_sort110 sigma_sort130) =
  subst_sort110 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort110 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort111 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort111 tau_sort130) (subst_sort111 sigma_sort130) =
  subst_sort111 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort111 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort112 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort112 tau_sort130) (subst_sort112 sigma_sort130) =
  subst_sort112 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort112 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort113 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort113 tau_sort130) (subst_sort113 sigma_sort130) =
  subst_sort113 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort113 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort114 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort114 tau_sort130) (subst_sort114 sigma_sort130) =
  subst_sort114 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort114 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort115 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort115 tau_sort130) (subst_sort115 sigma_sort130) =
  subst_sort115 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort115 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort116 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort116 tau_sort130) (subst_sort116 sigma_sort130) =
  subst_sort116 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort116 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort117 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort117 tau_sort130) (subst_sort117 sigma_sort130) =
  subst_sort117 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort117 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort118 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort118 tau_sort130) (subst_sort118 sigma_sort130) =
  subst_sort118 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort118 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort119 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort119 tau_sort130) (subst_sort119 sigma_sort130) =
  subst_sort119 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort119 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort120 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort120 tau_sort130) (subst_sort120 sigma_sort130) =
  subst_sort120 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort120 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort121 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort121 tau_sort130) (subst_sort121 sigma_sort130) =
  subst_sort121 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort121 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort122 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort122 tau_sort130) (subst_sort122 sigma_sort130) =
  subst_sort122 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort122 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort123 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort123 tau_sort130) (subst_sort123 sigma_sort130) =
  subst_sort123 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort123 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort124 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort124 tau_sort130) (subst_sort124 sigma_sort130) =
  subst_sort124 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort124 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort125 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort125 tau_sort130) (subst_sort125 sigma_sort130) =
  subst_sort125 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort125 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort126 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort126 tau_sort130) (subst_sort126 sigma_sort130) =
  subst_sort126 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort126 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort127 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort127 tau_sort130) (subst_sort127 sigma_sort130) =
  subst_sort127 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort127 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort128 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort128 tau_sort130) (subst_sort128 sigma_sort130) =
  subst_sort128 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort128 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort129 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort129 tau_sort130) (subst_sort129 sigma_sort130) =
  subst_sort129 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort129 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort130 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort130 tau_sort130) (subst_sort130 sigma_sort130) =
  subst_sort130 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort130 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort131 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort131 tau_sort130) (subst_sort131 sigma_sort130) =
  subst_sort131 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort131 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort132 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort132 tau_sort130) (subst_sort132 sigma_sort130) =
  subst_sort132 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort132 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort133 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort133 tau_sort130) (subst_sort133 sigma_sort130) =
  subst_sort133 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort133 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort134 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort134 tau_sort130) (subst_sort134 sigma_sort130) =
  subst_sort134 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort134 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort135 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort135 tau_sort130) (subst_sort135 sigma_sort130) =
  subst_sort135 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort135 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort136 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort136 tau_sort130) (subst_sort136 sigma_sort130) =
  subst_sort136 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort136 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort137 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort137 tau_sort130) (subst_sort137 sigma_sort130) =
  subst_sort137 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort137 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort138 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort138 tau_sort130) (subst_sort138 sigma_sort130) =
  subst_sort138 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort138 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort139 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort139 tau_sort130) (subst_sort139 sigma_sort130) =
  subst_sort139 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort139 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort140 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort140 tau_sort130) (subst_sort140 sigma_sort130) =
  subst_sort140 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort140 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort141 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort141 tau_sort130) (subst_sort141 sigma_sort130) =
  subst_sort141 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort141 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort142 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort142 tau_sort130) (subst_sort142 sigma_sort130) =
  subst_sort142 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort142 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort143 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort143 tau_sort130) (subst_sort143 sigma_sort130) =
  subst_sort143 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort143 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort144 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort144 tau_sort130) (subst_sort144 sigma_sort130) =
  subst_sort144 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort144 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort145 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort145 tau_sort130) (subst_sort145 sigma_sort130) =
  subst_sort145 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort145 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort146 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort146 tau_sort130) (subst_sort146 sigma_sort130) =
  subst_sort146 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort146 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort147 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort147 tau_sort130) (subst_sort147 sigma_sort130) =
  subst_sort147 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort147 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort148 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort148 tau_sort130) (subst_sort148 sigma_sort130) =
  subst_sort148 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort148 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort149 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort149 tau_sort130) (subst_sort149 sigma_sort130) =
  subst_sort149 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort149 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort150 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort150 tau_sort130) (subst_sort150 sigma_sort130) =
  subst_sort150 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort150 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort151 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort151 tau_sort130) (subst_sort151 sigma_sort130) =
  subst_sort151 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort151 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort152 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort152 tau_sort130) (subst_sort152 sigma_sort130) =
  subst_sort152 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort152 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort153 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort153 tau_sort130) (subst_sort153 sigma_sort130) =
  subst_sort153 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort153 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort154 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort154 tau_sort130) (subst_sort154 sigma_sort130) =
  subst_sort154 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort154 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort155 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort155 tau_sort130) (subst_sort155 sigma_sort130) =
  subst_sort155 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort155 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort156 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort156 tau_sort130) (subst_sort156 sigma_sort130) =
  subst_sort156 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort156 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort157 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort157 tau_sort130) (subst_sort157 sigma_sort130) =
  subst_sort157 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort157 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort158 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort158 tau_sort130) (subst_sort158 sigma_sort130) =
  subst_sort158 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort158 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort159 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort159 tau_sort130) (subst_sort159 sigma_sort130) =
  subst_sort159 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort159 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort160 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort160 tau_sort130) (subst_sort160 sigma_sort130) =
  subst_sort160 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort160 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort161 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort161 tau_sort130) (subst_sort161 sigma_sort130) =
  subst_sort161 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort161 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort162 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort162 tau_sort130) (subst_sort162 sigma_sort130) =
  subst_sort162 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort162 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort163 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort163 tau_sort130) (subst_sort163 sigma_sort130) =
  subst_sort163 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort163 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort164 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort164 tau_sort130) (subst_sort164 sigma_sort130) =
  subst_sort164 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort164 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort165 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort165 tau_sort130) (subst_sort165 sigma_sort130) =
  subst_sort165 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort165 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort166 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort166 tau_sort130) (subst_sort166 sigma_sort130) =
  subst_sort166 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort166 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort167 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort167 tau_sort130) (subst_sort167 sigma_sort130) =
  subst_sort167 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort167 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort168 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort168 tau_sort130) (subst_sort168 sigma_sort130) =
  subst_sort168 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort168 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort169 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort169 tau_sort130) (subst_sort169 sigma_sort130) =
  subst_sort169 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort169 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort170 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort170 tau_sort130) (subst_sort170 sigma_sort130) =
  subst_sort170 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort170 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort171 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort171 tau_sort130) (subst_sort171 sigma_sort130) =
  subst_sort171 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort171 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort172 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort172 tau_sort130) (subst_sort172 sigma_sort130) =
  subst_sort172 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort172 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort173 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort173 tau_sort130) (subst_sort173 sigma_sort130) =
  subst_sort173 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort173 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort174 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort174 tau_sort130) (subst_sort174 sigma_sort130) =
  subst_sort174 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort174 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort175 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort175 tau_sort130) (subst_sort175 sigma_sort130) =
  subst_sort175 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort175 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort176 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort176 tau_sort130) (subst_sort176 sigma_sort130) =
  subst_sort176 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort176 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort177 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort177 tau_sort130) (subst_sort177 sigma_sort130) =
  subst_sort177 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort177 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort178 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort178 tau_sort130) (subst_sort178 sigma_sort130) =
  subst_sort178 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort178 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort179 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort179 tau_sort130) (subst_sort179 sigma_sort130) =
  subst_sort179 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort179 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort180 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort180 tau_sort130) (subst_sort180 sigma_sort130) =
  subst_sort180 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort180 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort181 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort181 tau_sort130) (subst_sort181 sigma_sort130) =
  subst_sort181 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort181 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort182 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort182 tau_sort130) (subst_sort182 sigma_sort130) =
  subst_sort182 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort182 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort183 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort183 tau_sort130) (subst_sort183 sigma_sort130) =
  subst_sort183 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort183 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort184 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort184 tau_sort130) (subst_sort184 sigma_sort130) =
  subst_sort184 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort184 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort185 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort185 tau_sort130) (subst_sort185 sigma_sort130) =
  subst_sort185 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort185 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort186 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort186 tau_sort130) (subst_sort186 sigma_sort130) =
  subst_sort186 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort186 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort187 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort187 tau_sort130) (subst_sort187 sigma_sort130) =
  subst_sort187 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort187 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort188 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort188 tau_sort130) (subst_sort188 sigma_sort130) =
  subst_sort188 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort188 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort189 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort189 tau_sort130) (subst_sort189 sigma_sort130) =
  subst_sort189 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort189 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort190 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort190 tau_sort130) (subst_sort190 sigma_sort130) =
  subst_sort190 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort190 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort191 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort191 tau_sort130) (subst_sort191 sigma_sort130) =
  subst_sort191 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort191 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort192 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort192 tau_sort130) (subst_sort192 sigma_sort130) =
  subst_sort192 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort192 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort193 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort193 tau_sort130) (subst_sort193 sigma_sort130) =
  subst_sort193 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort193 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort194 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort194 tau_sort130) (subst_sort194 sigma_sort130) =
  subst_sort194 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort194 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort195 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort195 tau_sort130) (subst_sort195 sigma_sort130) =
  subst_sort195 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort195 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort196 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort196 tau_sort130) (subst_sort196 sigma_sort130) =
  subst_sort196 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort196 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort197 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort197 tau_sort130) (subst_sort197 sigma_sort130) =
  subst_sort197 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort197 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort198 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort198 tau_sort130) (subst_sort198 sigma_sort130) =
  subst_sort198 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort198 sigma_sort130 tau_sort130 n)).

Qed.

Lemma compComp'_sort199 {k_sort130 : nat} {l_sort130 : nat} {m_sort130 : nat}
  (sigma_sort130 : fin m_sort130 -> sort130 k_sort130)
  (tau_sort130 : fin k_sort130 -> sort130 l_sort130) :
  funcomp (subst_sort199 tau_sort130) (subst_sort199 sigma_sort130) =
  subst_sort199 (funcomp (subst_sort130 tau_sort130) sigma_sort130).

Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_sort199 sigma_sort130 tau_sort130 n)).

Qed.
