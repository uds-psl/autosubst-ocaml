Require Import core fintype.

Inductive sort0 (n_sort0 : nat) : Type :=
  | var_sort0 : fin n_sort0 -> sort0 n_sort0
  | cmix0 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort0 n_sort0
with sort1 (n_sort0 : nat) : Type :=
    cmix1 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort1 n_sort0
with sort2 (n_sort0 : nat) : Type :=
    cmix2 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort2 n_sort0
with sort3 (n_sort0 : nat) : Type :=
    cmix3 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort3 n_sort0
with sort4 (n_sort0 : nat) : Type :=
    cmix4 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort4 n_sort0
with sort5 (n_sort0 : nat) : Type :=
    cmix5 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort5 n_sort0
with sort6 (n_sort0 : nat) : Type :=
    cmix6 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort6 n_sort0
with sort7 (n_sort0 : nat) : Type :=
  | cmix7 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 ->
      sort4 n_sort0 ->
      sort5 n_sort0 -> sort6 n_sort0 -> sort7 n_sort0 -> sort7 n_sort0
  | clam8 : sort2 (S n_sort0) -> sort7 n_sort0.

Lemma congr_cmix0 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix0 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix0 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix0 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix0 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix0 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix0 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix0 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix0 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix0 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix0 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix1 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix1 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix1 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix1 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix1 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix1 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix1 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix1 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix1 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix1 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix1 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix2 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix2 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix2 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix2 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix2 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix2 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix2 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix2 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix2 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix2 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix2 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix3 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix3 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix3 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix3 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix3 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix3 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix3 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix3 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix3 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix3 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix3 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix4 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix4 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix4 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix4 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix4 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix4 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix4 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix4 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix4 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix4 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix4 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix5 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix5 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix5 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix5 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix5 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix5 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix5 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix5 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix5 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix5 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix5 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix6 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix6 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix6 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix6 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix6 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix6 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix6 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix6 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix6 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix6 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix6 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix7 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {s6 : sort6 m_sort0} {s7 : sort7 m_sort0}
  {t0 : sort0 m_sort0} {t1 : sort1 m_sort0} {t2 : sort2 m_sort0}
  {t3 : sort3 m_sort0} {t4 : sort4 m_sort0} {t5 : sort5 m_sort0}
  {t6 : sort6 m_sort0} {t7 : sort7 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6)
  (H7 : s7 = t7) :
  cmix7 m_sort0 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix7 m_sort0 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix7 m_sort0 x s1 s2 s3 s4 s5 s6 s7)
                                        H0))
                                  (ap
                                     (fun x =>
                                      cmix7 m_sort0 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix7 m_sort0 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x => cmix7 m_sort0 t0 t1 t2 x s4 s5 s6 s7)
                               H3))
                         (ap (fun x => cmix7 m_sort0 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix7 m_sort0 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix7 m_sort0 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix7 m_sort0 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_clam8 {m_sort0 : nat} {s0 : sort2 (S m_sort0)}
  {t0 : sort2 (S m_sort0)} (H0 : s0 = t0) :
  clam8 m_sort0 s0 = clam8 m_sort0 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam8 m_sort0 x) H0)).

Qed.

Lemma upRen_sort0_sort0 {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).

Proof.
exact (up_ren xi).

Defined.

Lemma upRen_list_sort0_sort0 (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n).

Proof.
exact (upRen_p p xi).

Defined.

Fixpoint ren_sort0 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort0 m_sort0) {struct s} :
sort0 n_sort0 :=
  match s with
  | var_sort0 _ s0 => var_sort0 n_sort0 (xi_sort0 s0)
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix0 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  end
with ren_sort1 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort1 m_sort0) {struct s} :
sort1 n_sort0 :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix1 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  end
with ren_sort2 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort2 m_sort0) {struct s} :
sort2 n_sort0 :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix2 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  end
with ren_sort3 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort3 m_sort0) {struct s} :
sort3 n_sort0 :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix3 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  end
with ren_sort4 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort4 m_sort0) {struct s} :
sort4 n_sort0 :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix4 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  end
with ren_sort5 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort5 m_sort0) {struct s} :
sort5 n_sort0 :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix5 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  end
with ren_sort6 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort6 m_sort0) {struct s} :
sort6 n_sort0 :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix6 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  end
with ren_sort7 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort7 m_sort0) {struct s} :
sort7 n_sort0 :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix7 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
        (ren_sort6 xi_sort0 s6) (ren_sort7 xi_sort0 s7)
  | clam8 _ s0 => clam8 n_sort0 (ren_sort2 (upRen_sort0_sort0 xi_sort0) s0)
  end.

Lemma up_sort0_sort0 {m : nat} {n_sort0 : nat}
  (sigma : fin m -> sort0 n_sort0) : fin (S m) -> sort0 (S n_sort0).

Proof.
exact (scons (var_sort0 (S n_sort0) var_zero)
                (funcomp (ren_sort0 shift) sigma)).

Defined.

Lemma up_list_sort0_sort0 (p : nat) {m : nat} {n_sort0 : nat}
  (sigma : fin m -> sort0 n_sort0) : fin (plus p m) -> sort0 (plus p n_sort0).

Proof.
exact (scons_p p (funcomp (var_sort0 (plus p n_sort0)) (zero_p p))
                (funcomp (ren_sort0 (shift_p p)) sigma)).

Defined.

Fixpoint subst_sort0 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort0 m_sort0) {struct s} :
sort0 n_sort0 :=
  match s with
  | var_sort0 _ s0 => sigma_sort0 s0
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix0 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  end
with subst_sort1 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort1 m_sort0) {struct s} :
sort1 n_sort0 :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix1 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  end
with subst_sort2 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort2 m_sort0) {struct s} :
sort2 n_sort0 :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix2 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  end
with subst_sort3 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort3 m_sort0) {struct s} :
sort3 n_sort0 :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix3 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  end
with subst_sort4 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort4 m_sort0) {struct s} :
sort4 n_sort0 :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix4 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  end
with subst_sort5 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort5 m_sort0) {struct s} :
sort5 n_sort0 :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix5 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  end
with subst_sort6 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort6 m_sort0) {struct s} :
sort6 n_sort0 :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix6 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  end
with subst_sort7 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort7 m_sort0) {struct s} :
sort7 n_sort0 :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix7 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
        (subst_sort6 sigma_sort0 s6) (subst_sort7 sigma_sort0 s7)
  | clam8 _ s0 => clam8 n_sort0 (subst_sort2 (up_sort0_sort0 sigma_sort0) s0)
  end.

Lemma upId_sort0_sort0 {m_sort0 : nat} (sigma : fin m_sort0 -> sort0 m_sort0)
  (Eq : forall x, sigma x = var_sort0 m_sort0 x) :
  forall x, up_sort0_sort0 sigma x = var_sort0 (S m_sort0) x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort0 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upId_list_sort0_sort0 {p : nat} {m_sort0 : nat}
  (sigma : fin m_sort0 -> sort0 m_sort0)
  (Eq : forall x, sigma x = var_sort0 m_sort0 x) :
  forall x, up_list_sort0_sort0 p sigma x = var_sort0 (plus p m_sort0) x.

Proof.
exact (fun n =>
              scons_p_eta (var_sort0 (plus p m_sort0))
                (fun n => ap (ren_sort0 (shift_p p)) (Eq n))
                (fun n => eq_refl)).

Qed.

Fixpoint idSubst_sort0 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort0 m_sort0) {struct s} : subst_sort0 sigma_sort0 s = s :=
  match s with
  | var_sort0 _ s0 => Eq_sort0 s0
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  end
with idSubst_sort1 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort1 m_sort0) {struct s} : subst_sort1 sigma_sort0 s = s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  end
with idSubst_sort2 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort2 m_sort0) {struct s} : subst_sort2 sigma_sort0 s = s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  end
with idSubst_sort3 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort3 m_sort0) {struct s} : subst_sort3 sigma_sort0 s = s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  end
with idSubst_sort4 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort4 m_sort0) {struct s} : subst_sort4 sigma_sort0 s = s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  end
with idSubst_sort5 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort5 m_sort0) {struct s} : subst_sort5 sigma_sort0 s = s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  end
with idSubst_sort6 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort6 m_sort0) {struct s} : subst_sort6 sigma_sort0 s = s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  end
with idSubst_sort7 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort7 m_sort0) {struct s} : subst_sort7 sigma_sort0 s = s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
        (idSubst_sort6 sigma_sort0 Eq_sort0 s6)
        (idSubst_sort7 sigma_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (idSubst_sort2 (up_sort0_sort0 sigma_sort0)
           (upId_sort0_sort0 _ Eq_sort0) s0)
  end.

Lemma upExtRen_sort0_sort0 {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_sort0_sort0 xi x = upRen_sort0_sort0 zeta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap shift (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExtRen_list_sort0_sort0 {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_sort0_sort0 p xi x = upRen_list_sort0_sort0 p zeta x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (shift_p p) (Eq n))).

Qed.

Fixpoint extRen_sort0 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort0 m_sort0) {struct
 s} : ren_sort0 xi_sort0 s = ren_sort0 zeta_sort0 s :=
  match s with
  | var_sort0 _ s0 => ap (var_sort0 n_sort0) (Eq_sort0 s0)
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  end
with extRen_sort1 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort1 m_sort0) {struct
 s} : ren_sort1 xi_sort0 s = ren_sort1 zeta_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  end
with extRen_sort2 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort2 m_sort0) {struct
 s} : ren_sort2 xi_sort0 s = ren_sort2 zeta_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  end
with extRen_sort3 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort3 m_sort0) {struct
 s} : ren_sort3 xi_sort0 s = ren_sort3 zeta_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  end
with extRen_sort4 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort4 m_sort0) {struct
 s} : ren_sort4 xi_sort0 s = ren_sort4 zeta_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  end
with extRen_sort5 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort5 m_sort0) {struct
 s} : ren_sort5 xi_sort0 s = ren_sort5 zeta_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  end
with extRen_sort6 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort6 m_sort0) {struct
 s} : ren_sort6 xi_sort0 s = ren_sort6 zeta_sort0 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  end
with extRen_sort7 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort7 m_sort0) {struct
 s} : ren_sort7 xi_sort0 s = ren_sort7 zeta_sort0 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
        (extRen_sort6 xi_sort0 zeta_sort0 Eq_sort0 s6)
        (extRen_sort7 xi_sort0 zeta_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (extRen_sort2 (upRen_sort0_sort0 xi_sort0)
           (upRen_sort0_sort0 zeta_sort0) (upExtRen_sort0_sort0 _ _ Eq_sort0)
           s0)
  end.

Lemma upExt_sort0_sort0 {m : nat} {n_sort0 : nat}
  (sigma : fin m -> sort0 n_sort0) (tau : fin m -> sort0 n_sort0)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_sort0_sort0 sigma x = up_sort0_sort0 tau x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort0 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExt_list_sort0_sort0 {p : nat} {m : nat} {n_sort0 : nat}
  (sigma : fin m -> sort0 n_sort0) (tau : fin m -> sort0 n_sort0)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_sort0_sort0 p sigma x = up_list_sort0_sort0 p tau x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (ren_sort0 (shift_p p)) (Eq n))).

Qed.

Fixpoint ext_sort0 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort0 m_sort0)
{struct s} : subst_sort0 sigma_sort0 s = subst_sort0 tau_sort0 s :=
  match s with
  | var_sort0 _ s0 => Eq_sort0 s0
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  end
with ext_sort1 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort1 m_sort0)
{struct s} : subst_sort1 sigma_sort0 s = subst_sort1 tau_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  end
with ext_sort2 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort2 m_sort0)
{struct s} : subst_sort2 sigma_sort0 s = subst_sort2 tau_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  end
with ext_sort3 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort3 m_sort0)
{struct s} : subst_sort3 sigma_sort0 s = subst_sort3 tau_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  end
with ext_sort4 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort4 m_sort0)
{struct s} : subst_sort4 sigma_sort0 s = subst_sort4 tau_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  end
with ext_sort5 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort5 m_sort0)
{struct s} : subst_sort5 sigma_sort0 s = subst_sort5 tau_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  end
with ext_sort6 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort6 m_sort0)
{struct s} : subst_sort6 sigma_sort0 s = subst_sort6 tau_sort0 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  end
with ext_sort7 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort7 m_sort0)
{struct s} : subst_sort7 sigma_sort0 s = subst_sort7 tau_sort0 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
        (ext_sort6 sigma_sort0 tau_sort0 Eq_sort0 s6)
        (ext_sort7 sigma_sort0 tau_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (ext_sort2 (up_sort0_sort0 sigma_sort0) (up_sort0_sort0 tau_sort0)
           (upExt_sort0_sort0 _ _ Eq_sort0) s0)
  end.

Lemma up_ren_ren_sort0_sort0 {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_sort0_sort0 zeta) (upRen_sort0_sort0 xi) x =
  upRen_sort0_sort0 rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Lemma up_ren_ren_list_sort0_sort0 {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_sort0_sort0 p zeta) (upRen_list_sort0_sort0 p xi) x =
  upRen_list_sort0_sort0 p rho x.

Proof.
exact (up_ren_ren_p Eq).

Qed.

Fixpoint compRenRen_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort0 m_sort0) {struct s} :
ren_sort0 zeta_sort0 (ren_sort0 xi_sort0 s) = ren_sort0 rho_sort0 s :=
  match s with
  | var_sort0 _ s0 => ap (var_sort0 l_sort0) (Eq_sort0 s0)
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  end
with compRenRen_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort1 m_sort0) {struct s} :
ren_sort1 zeta_sort0 (ren_sort1 xi_sort0 s) = ren_sort1 rho_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  end
with compRenRen_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort2 m_sort0) {struct s} :
ren_sort2 zeta_sort0 (ren_sort2 xi_sort0 s) = ren_sort2 rho_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  end
with compRenRen_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort3 m_sort0) {struct s} :
ren_sort3 zeta_sort0 (ren_sort3 xi_sort0 s) = ren_sort3 rho_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  end
with compRenRen_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort4 m_sort0) {struct s} :
ren_sort4 zeta_sort0 (ren_sort4 xi_sort0 s) = ren_sort4 rho_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  end
with compRenRen_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort5 m_sort0) {struct s} :
ren_sort5 zeta_sort0 (ren_sort5 xi_sort0 s) = ren_sort5 rho_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  end
with compRenRen_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort6 m_sort0) {struct s} :
ren_sort6 zeta_sort0 (ren_sort6 xi_sort0 s) = ren_sort6 rho_sort0 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  end
with compRenRen_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort7 m_sort0) {struct s} :
ren_sort7 zeta_sort0 (ren_sort7 xi_sort0 s) = ren_sort7 rho_sort0 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
        (compRenRen_sort6 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s6)
        (compRenRen_sort7 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (compRenRen_sort2 (upRen_sort0_sort0 xi_sort0)
           (upRen_sort0_sort0 zeta_sort0) (upRen_sort0_sort0 rho_sort0)
           (up_ren_ren _ _ _ Eq_sort0) s0)
  end.

Lemma up_ren_subst_sort0_sort0 {k : nat} {l : nat} {m_sort0 : nat}
  (xi : fin k -> fin l) (tau : fin l -> sort0 m_sort0)
  (theta : fin k -> sort0 m_sort0)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_sort0_sort0 tau) (upRen_sort0_sort0 xi) x =
  up_sort0_sort0 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort0 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma up_ren_subst_list_sort0_sort0 {p : nat} {k : nat} {l : nat}
  {m_sort0 : nat} (xi : fin k -> fin l) (tau : fin l -> sort0 m_sort0)
  (theta : fin k -> sort0 m_sort0)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_sort0_sort0 p tau) (upRen_list_sort0_sort0 p xi) x =
  up_list_sort0_sort0 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr (fun z => scons_p_head' _ _ z)
                   (fun z =>
                    eq_trans (scons_p_tail' _ _ (xi z))
                      (ap (ren_sort0 (shift_p p)) (Eq z))))).

Qed.

Fixpoint compRenSubst_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort0 m_sort0) {struct s} :
subst_sort0 tau_sort0 (ren_sort0 xi_sort0 s) = subst_sort0 theta_sort0 s :=
  match s with
  | var_sort0 _ s0 => Eq_sort0 s0
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compRenSubst_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort1 m_sort0) {struct s} :
subst_sort1 tau_sort0 (ren_sort1 xi_sort0 s) = subst_sort1 theta_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compRenSubst_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort2 m_sort0) {struct s} :
subst_sort2 tau_sort0 (ren_sort2 xi_sort0 s) = subst_sort2 theta_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compRenSubst_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort3 m_sort0) {struct s} :
subst_sort3 tau_sort0 (ren_sort3 xi_sort0 s) = subst_sort3 theta_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compRenSubst_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort4 m_sort0) {struct s} :
subst_sort4 tau_sort0 (ren_sort4 xi_sort0 s) = subst_sort4 theta_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compRenSubst_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort5 m_sort0) {struct s} :
subst_sort5 tau_sort0 (ren_sort5 xi_sort0 s) = subst_sort5 theta_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compRenSubst_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort6 m_sort0) {struct s} :
subst_sort6 tau_sort0 (ren_sort6 xi_sort0 s) = subst_sort6 theta_sort0 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compRenSubst_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort7 m_sort0) {struct s} :
subst_sort7 tau_sort0 (ren_sort7 xi_sort0 s) = subst_sort7 theta_sort0 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compRenSubst_sort6 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compRenSubst_sort7 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (compRenSubst_sort2 (upRen_sort0_sort0 xi_sort0)
           (up_sort0_sort0 tau_sort0) (up_sort0_sort0 theta_sort0)
           (up_ren_subst_sort0_sort0 _ _ _ Eq_sort0) s0)
  end.

Lemma up_subst_ren_sort0_sort0 {k : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma : fin k -> sort0 l_sort0) (zeta_sort0 : fin l_sort0 -> fin m_sort0)
  (theta : fin k -> sort0 m_sort0)
  (Eq : forall x, funcomp (ren_sort0 zeta_sort0) sigma x = theta x) :
  forall x,
  funcomp (ren_sort0 (upRen_sort0_sort0 zeta_sort0)) (up_sort0_sort0 sigma) x =
  up_sort0_sort0 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenRen_sort0 shift (upRen_sort0_sort0 zeta_sort0)
                       (funcomp shift zeta_sort0) (fun x => eq_refl)
                       (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compRenRen_sort0 zeta_sort0 shift
                             (funcomp shift zeta_sort0) (fun x => eq_refl)
                             (sigma fin_n)))
                       (ap (ren_sort0 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_ren_list_sort0_sort0 {p : nat} {k : nat} {l_sort0 : nat}
  {m_sort0 : nat} (sigma : fin k -> sort0 l_sort0)
  (zeta_sort0 : fin l_sort0 -> fin m_sort0) (theta : fin k -> sort0 m_sort0)
  (Eq : forall x, funcomp (ren_sort0 zeta_sort0) sigma x = theta x) :
  forall x,
  funcomp (ren_sort0 (upRen_list_sort0_sort0 p zeta_sort0))
    (up_list_sort0_sort0 p sigma) x = up_list_sort0_sort0 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr
                   (fun x =>
                    ap (var_sort0 (plus p m_sort0)) (scons_p_head' _ _ x))
                   (fun n =>
                    eq_trans
                      (compRenRen_sort0 (shift_p p)
                         (upRen_list_sort0_sort0 p zeta_sort0)
                         (funcomp (shift_p p) zeta_sort0)
                         (fun x => scons_p_tail' _ _ x) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compRenRen_sort0 zeta_sort0 (shift_p p)
                               (funcomp (shift_p p) zeta_sort0)
                               (fun x => eq_refl) (sigma n)))
                         (ap (ren_sort0 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstRen_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort0 m_sort0) {struct s} :
ren_sort0 zeta_sort0 (subst_sort0 sigma_sort0 s) = subst_sort0 theta_sort0 s
:=
  match s with
  | var_sort0 _ s0 => Eq_sort0 s0
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstRen_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort1 m_sort0) {struct s} :
ren_sort1 zeta_sort0 (subst_sort1 sigma_sort0 s) = subst_sort1 theta_sort0 s
:=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstRen_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort2 m_sort0) {struct s} :
ren_sort2 zeta_sort0 (subst_sort2 sigma_sort0 s) = subst_sort2 theta_sort0 s
:=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstRen_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort3 m_sort0) {struct s} :
ren_sort3 zeta_sort0 (subst_sort3 sigma_sort0 s) = subst_sort3 theta_sort0 s
:=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstRen_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort4 m_sort0) {struct s} :
ren_sort4 zeta_sort0 (subst_sort4 sigma_sort0 s) = subst_sort4 theta_sort0 s
:=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstRen_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort5 m_sort0) {struct s} :
ren_sort5 zeta_sort0 (subst_sort5 sigma_sort0 s) = subst_sort5 theta_sort0 s
:=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstRen_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort6 m_sort0) {struct s} :
ren_sort6 zeta_sort0 (subst_sort6 sigma_sort0 s) = subst_sort6 theta_sort0 s
:=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstRen_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (ren_sort0 zeta_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort7 m_sort0) {struct s} :
ren_sort7 zeta_sort0 (subst_sort7 sigma_sort0 s) = subst_sort7 theta_sort0 s
:=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstRen_sort6 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstRen_sort7 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (compSubstRen_sort2 (up_sort0_sort0 sigma_sort0)
           (upRen_sort0_sort0 zeta_sort0) (up_sort0_sort0 theta_sort0)
           (up_subst_ren_sort0_sort0 _ _ _ Eq_sort0) s0)
  end.

Lemma up_subst_subst_sort0_sort0 {k : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma : fin k -> sort0 l_sort0) (tau_sort0 : fin l_sort0 -> sort0 m_sort0)
  (theta : fin k -> sort0 m_sort0)
  (Eq : forall x, funcomp (subst_sort0 tau_sort0) sigma x = theta x) :
  forall x,
  funcomp (subst_sort0 (up_sort0_sort0 tau_sort0)) (up_sort0_sort0 sigma) x =
  up_sort0_sort0 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenSubst_sort0 shift (up_sort0_sort0 tau_sort0)
                       (funcomp (up_sort0_sort0 tau_sort0) shift)
                       (fun x => eq_refl) (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_sort0 tau_sort0 shift
                             (funcomp (ren_sort0 shift) tau_sort0)
                             (fun x => eq_refl) (sigma fin_n)))
                       (ap (ren_sort0 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_subst_list_sort0_sort0 {p : nat} {k : nat} {l_sort0 : nat}
  {m_sort0 : nat} (sigma : fin k -> sort0 l_sort0)
  (tau_sort0 : fin l_sort0 -> sort0 m_sort0) (theta : fin k -> sort0 m_sort0)
  (Eq : forall x, funcomp (subst_sort0 tau_sort0) sigma x = theta x) :
  forall x,
  funcomp (subst_sort0 (up_list_sort0_sort0 p tau_sort0))
    (up_list_sort0_sort0 p sigma) x = up_list_sort0_sort0 p theta x.

Proof.
exact (fun n =>
              eq_trans
                (scons_p_comp'
                   (funcomp (var_sort0 (plus p l_sort0)) (zero_p p)) _ _ n)
                (scons_p_congr
                   (fun x =>
                    scons_p_head' _ (fun z => ren_sort0 (shift_p p) _) x)
                   (fun n =>
                    eq_trans
                      (compRenSubst_sort0 (shift_p p)
                         (up_list_sort0_sort0 p tau_sort0)
                         (funcomp (up_list_sort0_sort0 p tau_sort0)
                            (shift_p p)) (fun x => eq_refl) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compSubstRen_sort0 tau_sort0 (shift_p p) _
                               (fun x => eq_sym (scons_p_tail' _ _ x))
                               (sigma n)))
                         (ap (ren_sort0 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstSubst_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort0 m_sort0) {struct s} :
subst_sort0 tau_sort0 (subst_sort0 sigma_sort0 s) = subst_sort0 theta_sort0 s
:=
  match s with
  | var_sort0 _ s0 => Eq_sort0 s0
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstSubst_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort1 m_sort0) {struct s} :
subst_sort1 tau_sort0 (subst_sort1 sigma_sort0 s) = subst_sort1 theta_sort0 s
:=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstSubst_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort2 m_sort0) {struct s} :
subst_sort2 tau_sort0 (subst_sort2 sigma_sort0 s) = subst_sort2 theta_sort0 s
:=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstSubst_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort3 m_sort0) {struct s} :
subst_sort3 tau_sort0 (subst_sort3 sigma_sort0 s) = subst_sort3 theta_sort0 s
:=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstSubst_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort4 m_sort0) {struct s} :
subst_sort4 tau_sort0 (subst_sort4 sigma_sort0 s) = subst_sort4 theta_sort0 s
:=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstSubst_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort5 m_sort0) {struct s} :
subst_sort5 tau_sort0 (subst_sort5 sigma_sort0 s) = subst_sort5 theta_sort0 s
:=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstSubst_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort6 m_sort0) {struct s} :
subst_sort6 tau_sort0 (subst_sort6 sigma_sort0 s) = subst_sort6 theta_sort0 s
:=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  end
with compSubstSubst_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x,
            funcomp (subst_sort0 tau_sort0) sigma_sort0 x = theta_sort0 x)
(s : sort7 m_sort0) {struct s} :
subst_sort7 tau_sort0 (subst_sort7 sigma_sort0 s) = subst_sort7 theta_sort0 s
:=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
        (compSubstSubst_sort6 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s6)
        (compSubstSubst_sort7 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (compSubstSubst_sort2 (up_sort0_sort0 sigma_sort0)
           (up_sort0_sort0 tau_sort0) (up_sort0_sort0 theta_sort0)
           (up_subst_subst_sort0_sort0 _ _ _ Eq_sort0) s0)
  end.

Lemma rinstInst_up_sort0_sort0 {m : nat} {n_sort0 : nat}
  (xi : fin m -> fin n_sort0) (sigma : fin m -> sort0 n_sort0)
  (Eq : forall x, funcomp (var_sort0 n_sort0) xi x = sigma x) :
  forall x,
  funcomp (var_sort0 (S n_sort0)) (upRen_sort0_sort0 xi) x =
  up_sort0_sort0 sigma x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort0 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma rinstInst_up_list_sort0_sort0 {p : nat} {m : nat} {n_sort0 : nat}
  (xi : fin m -> fin n_sort0) (sigma : fin m -> sort0 n_sort0)
  (Eq : forall x, funcomp (var_sort0 n_sort0) xi x = sigma x) :
  forall x,
  funcomp (var_sort0 (plus p n_sort0)) (upRen_list_sort0_sort0 p xi) x =
  up_list_sort0_sort0 p sigma x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ (var_sort0 (plus p n_sort0)) n)
                (scons_p_congr (fun z => eq_refl)
                   (fun n => ap (ren_sort0 (shift_p p)) (Eq n)))).

Qed.

Fixpoint rinst_inst_sort0 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort0 m_sort0) {struct s} :
ren_sort0 xi_sort0 s = subst_sort0 sigma_sort0 s :=
  match s with
  | var_sort0 _ s0 => Eq_sort0 s0
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix0 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  end
with rinst_inst_sort1 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort1 m_sort0) {struct s} :
ren_sort1 xi_sort0 s = subst_sort1 sigma_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix1 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  end
with rinst_inst_sort2 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort2 m_sort0) {struct s} :
ren_sort2 xi_sort0 s = subst_sort2 sigma_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix2 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  end
with rinst_inst_sort3 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort3 m_sort0) {struct s} :
ren_sort3 xi_sort0 s = subst_sort3 sigma_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix3 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  end
with rinst_inst_sort4 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort4 m_sort0) {struct s} :
ren_sort4 xi_sort0 s = subst_sort4 sigma_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix4 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  end
with rinst_inst_sort5 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort5 m_sort0) {struct s} :
ren_sort5 xi_sort0 s = subst_sort5 sigma_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix5 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  end
with rinst_inst_sort6 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort6 m_sort0) {struct s} :
ren_sort6 xi_sort0 s = subst_sort6 sigma_sort0 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix6 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  end
with rinst_inst_sort7 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort7 m_sort0) {struct s} :
ren_sort7 xi_sort0 s = subst_sort7 sigma_sort0 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix7 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
        (rinst_inst_sort6 xi_sort0 sigma_sort0 Eq_sort0 s6)
        (rinst_inst_sort7 xi_sort0 sigma_sort0 Eq_sort0 s7)
  | clam8 _ s0 =>
      congr_clam8
        (rinst_inst_sort2 (upRen_sort0_sort0 xi_sort0)
           (up_sort0_sort0 sigma_sort0)
           (rinstInst_up_sort0_sort0 _ _ Eq_sort0) s0)
  end.

Lemma renRen_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort0 m_sort0) :
  ren_sort0 zeta_sort0 (ren_sort0 xi_sort0 s) =
  ren_sort0 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort0 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort1 m_sort0) :
  ren_sort1 zeta_sort0 (ren_sort1 xi_sort0 s) =
  ren_sort1 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort1 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort2 m_sort0) :
  ren_sort2 zeta_sort0 (ren_sort2 xi_sort0 s) =
  ren_sort2 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort2 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort3 m_sort0) :
  ren_sort3 zeta_sort0 (ren_sort3 xi_sort0 s) =
  ren_sort3 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort3 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort4 m_sort0) :
  ren_sort4 zeta_sort0 (ren_sort4 xi_sort0 s) =
  ren_sort4 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort4 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort5 m_sort0) :
  ren_sort5 zeta_sort0 (ren_sort5 xi_sort0 s) =
  ren_sort5 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort5 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort6 m_sort0) :
  ren_sort6 zeta_sort0 (ren_sort6 xi_sort0 s) =
  ren_sort6 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort6 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort7 m_sort0) :
  ren_sort7 zeta_sort0 (ren_sort7 xi_sort0 s) =
  ren_sort7 (funcomp zeta_sort0 xi_sort0) s.

Proof.
exact (compRenRen_sort7 xi_sort0 zeta_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma compRen_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort0 m_sort0) :
  ren_sort0 zeta_sort0 (subst_sort0 sigma_sort0 s) =
  subst_sort0 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort0 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort1 m_sort0) :
  ren_sort1 zeta_sort0 (subst_sort1 sigma_sort0 s) =
  subst_sort1 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort1 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort2 m_sort0) :
  ren_sort2 zeta_sort0 (subst_sort2 sigma_sort0 s) =
  subst_sort2 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort2 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort3 m_sort0) :
  ren_sort3 zeta_sort0 (subst_sort3 sigma_sort0 s) =
  subst_sort3 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort3 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort4 m_sort0) :
  ren_sort4 zeta_sort0 (subst_sort4 sigma_sort0 s) =
  subst_sort4 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort4 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort5 m_sort0) :
  ren_sort5 zeta_sort0 (subst_sort5 sigma_sort0 s) =
  subst_sort5 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort5 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort6 m_sort0) :
  ren_sort6 zeta_sort0 (subst_sort6 sigma_sort0 s) =
  subst_sort6 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort6 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (zeta_sort0 : fin k_sort0 -> fin l_sort0) (s : sort7 m_sort0) :
  ren_sort7 zeta_sort0 (subst_sort7 sigma_sort0 s) =
  subst_sort7 (funcomp (ren_sort0 zeta_sort0) sigma_sort0) s.

Proof.
exact (compSubstRen_sort7 sigma_sort0 zeta_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma renComp_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort0 m_sort0) :
  subst_sort0 tau_sort0 (ren_sort0 xi_sort0 s) =
  subst_sort0 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort0 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort1 m_sort0) :
  subst_sort1 tau_sort0 (ren_sort1 xi_sort0 s) =
  subst_sort1 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort1 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort2 m_sort0) :
  subst_sort2 tau_sort0 (ren_sort2 xi_sort0 s) =
  subst_sort2 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort2 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort3 m_sort0) :
  subst_sort3 tau_sort0 (ren_sort3 xi_sort0 s) =
  subst_sort3 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort3 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort4 m_sort0) :
  subst_sort4 tau_sort0 (ren_sort4 xi_sort0 s) =
  subst_sort4 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort4 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort5 m_sort0) :
  subst_sort5 tau_sort0 (ren_sort5 xi_sort0 s) =
  subst_sort5 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort5 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort6 m_sort0) :
  subst_sort6 tau_sort0 (ren_sort6 xi_sort0 s) =
  subst_sort6 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort6 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (xi_sort0 : fin m_sort0 -> fin k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort7 m_sort0) :
  subst_sort7 tau_sort0 (ren_sort7 xi_sort0 s) =
  subst_sort7 (funcomp tau_sort0 xi_sort0) s.

Proof.
exact (compRenSubst_sort7 xi_sort0 tau_sort0 _ (fun n => eq_refl) s).

Qed.

Lemma compComp_sort0 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort0 m_sort0) :
  subst_sort0 tau_sort0 (subst_sort0 sigma_sort0 s) =
  subst_sort0 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort0 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort1 m_sort0) :
  subst_sort1 tau_sort0 (subst_sort1 sigma_sort0 s) =
  subst_sort1 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort1 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort2 m_sort0) :
  subst_sort2 tau_sort0 (subst_sort2 sigma_sort0 s) =
  subst_sort2 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort2 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort3 m_sort0) :
  subst_sort3 tau_sort0 (subst_sort3 sigma_sort0 s) =
  subst_sort3 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort3 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort4 m_sort0) :
  subst_sort4 tau_sort0 (subst_sort4 sigma_sort0 s) =
  subst_sort4 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort4 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort5 m_sort0) :
  subst_sort5 tau_sort0 (subst_sort5 sigma_sort0 s) =
  subst_sort5 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort5 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort6 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort6 m_sort0) :
  subst_sort6 tau_sort0 (subst_sort6 sigma_sort0 s) =
  subst_sort6 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort6 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort7 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
  (sigma_sort0 : fin m_sort0 -> sort0 k_sort0)
  (tau_sort0 : fin k_sort0 -> sort0 l_sort0) (s : sort7 m_sort0) :
  subst_sort7 tau_sort0 (subst_sort7 sigma_sort0 s) =
  subst_sort7 (funcomp (subst_sort0 tau_sort0) sigma_sort0) s.

Proof.
exact (compSubstSubst_sort7 sigma_sort0 tau_sort0 _ (fun n => eq_refl)
                s).

Qed.

Inductive sort8 (n_sort11 : nat) : Type :=
    cmix8 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 -> sort14 n_sort11 -> sort15 n_sort11 -> sort8 n_sort11
with sort9 (n_sort11 : nat) : Type :=
    cmix9 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 -> sort14 n_sort11 -> sort15 n_sort11 -> sort9 n_sort11
with sort10 (n_sort11 : nat) : Type :=
    cmix10 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 ->
      sort14 n_sort11 -> sort15 n_sort11 -> sort10 n_sort11
with sort11 (n_sort11 : nat) : Type :=
  | var_sort11 : fin n_sort11 -> sort11 n_sort11
  | cmix11 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 ->
      sort14 n_sort11 -> sort15 n_sort11 -> sort11 n_sort11
with sort12 (n_sort11 : nat) : Type :=
    cmix12 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 ->
      sort14 n_sort11 -> sort15 n_sort11 -> sort12 n_sort11
with sort13 (n_sort11 : nat) : Type :=
  | cmix13 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 ->
      sort14 n_sort11 -> sort15 n_sort11 -> sort13 n_sort11
  | clam16 : sort14 (S n_sort11) -> sort13 n_sort11
with sort14 (n_sort11 : nat) : Type :=
    cmix14 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 ->
      sort14 n_sort11 -> sort15 n_sort11 -> sort14 n_sort11
with sort15 (n_sort11 : nat) : Type :=
    cmix15 :
      sort8 n_sort11 ->
      sort9 n_sort11 ->
      sort10 n_sort11 ->
      sort11 n_sort11 ->
      sort12 n_sort11 ->
      sort13 n_sort11 ->
      sort14 n_sort11 -> sort15 n_sort11 -> sort15 n_sort11.

Lemma congr_cmix8 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix8 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix8 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix8 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix8 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix8 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix8 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap (fun x => cmix8 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix8 m_sort11 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix8 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix8 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix9 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix9 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix9 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix9 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix9 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix9 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix9 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap (fun x => cmix9 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix9 m_sort11 t0 t1 t2 t3 t4 x s6 s7) H5))
                   (ap (fun x => cmix9 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix9 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix10 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix10 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix10 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix10 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix10 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix10 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix10 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix10 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix10 m_sort11 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix10 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix10 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix11 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix11 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix11 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix11 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix11 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix11 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix11 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix11 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix11 m_sort11 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix11 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix11 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix12 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix12 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix12 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix12 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix12 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix12 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix12 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix12 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix12 m_sort11 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix12 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix12 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix13 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix13 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix13 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix13 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix13 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix13 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix13 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix13 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix13 m_sort11 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix13 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix13 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_clam16 {m_sort11 : nat} {s0 : sort14 (S m_sort11)}
  {t0 : sort14 (S m_sort11)} (H0 : s0 = t0) :
  clam16 m_sort11 s0 = clam16 m_sort11 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam16 m_sort11 x) H0)).

Qed.

Lemma congr_cmix14 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix14 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix14 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix14 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix14 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix14 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix14 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix14 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix14 m_sort11 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix14 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix14 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix15 {m_sort11 : nat} {s0 : sort8 m_sort11}
  {s1 : sort9 m_sort11} {s2 : sort10 m_sort11} {s3 : sort11 m_sort11}
  {s4 : sort12 m_sort11} {s5 : sort13 m_sort11} {s6 : sort14 m_sort11}
  {s7 : sort15 m_sort11} {t0 : sort8 m_sort11} {t1 : sort9 m_sort11}
  {t2 : sort10 m_sort11} {t3 : sort11 m_sort11} {t4 : sort12 m_sort11}
  {t5 : sort13 m_sort11} {t6 : sort14 m_sort11} {t7 : sort15 m_sort11}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix15 m_sort11 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix15 m_sort11 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix15 m_sort11 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix15 m_sort11 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix15 m_sort11 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix15 m_sort11 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix15 m_sort11 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix15 m_sort11 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix15 m_sort11 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix15 m_sort11 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma upRen_sort11_sort11 {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).

Proof.
exact (up_ren xi).

Defined.

Lemma upRen_list_sort11_sort11 (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n).

Proof.
exact (upRen_p p xi).

Defined.

Fixpoint ren_sort8 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort8 m_sort11) {struct s} :
sort8 n_sort11 :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix8 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  end
with ren_sort9 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort9 m_sort11) {struct s} :
sort9 n_sort11 :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix9 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  end
with ren_sort10 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort10 m_sort11) {struct s} :
sort10 n_sort11 :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix10 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  end
with ren_sort11 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort11 m_sort11) {struct s} :
sort11 n_sort11 :=
  match s with
  | var_sort11 _ s0 => var_sort11 n_sort11 (xi_sort11 s0)
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix11 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  end
with ren_sort12 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort12 m_sort11) {struct s} :
sort12 n_sort11 :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix12 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  end
with ren_sort13 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort13 m_sort11) {struct s} :
sort13 n_sort11 :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix13 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  | clam16 _ s0 =>
      clam16 n_sort11 (ren_sort14 (upRen_sort11_sort11 xi_sort11) s0)
  end
with ren_sort14 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort14 m_sort11) {struct s} :
sort14 n_sort11 :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix14 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  end
with ren_sort15 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11) (s : sort15 m_sort11) {struct s} :
sort15 n_sort11 :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix15 n_sort11 (ren_sort8 xi_sort11 s0) (ren_sort9 xi_sort11 s1)
        (ren_sort10 xi_sort11 s2) (ren_sort11 xi_sort11 s3)
        (ren_sort12 xi_sort11 s4) (ren_sort13 xi_sort11 s5)
        (ren_sort14 xi_sort11 s6) (ren_sort15 xi_sort11 s7)
  end.

Lemma up_sort11_sort11 {m : nat} {n_sort11 : nat}
  (sigma : fin m -> sort11 n_sort11) : fin (S m) -> sort11 (S n_sort11).

Proof.
exact (scons (var_sort11 (S n_sort11) var_zero)
                (funcomp (ren_sort11 shift) sigma)).

Defined.

Lemma up_list_sort11_sort11 (p : nat) {m : nat} {n_sort11 : nat}
  (sigma : fin m -> sort11 n_sort11) :
  fin (plus p m) -> sort11 (plus p n_sort11).

Proof.
exact (scons_p p (funcomp (var_sort11 (plus p n_sort11)) (zero_p p))
                (funcomp (ren_sort11 (shift_p p)) sigma)).

Defined.

Fixpoint subst_sort8 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort8 m_sort11) {struct
 s} : sort8 n_sort11 :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix8 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  end
with subst_sort9 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort9 m_sort11) {struct
 s} : sort9 n_sort11 :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix9 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  end
with subst_sort10 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort10 m_sort11)
{struct s} : sort10 n_sort11 :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix10 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  end
with subst_sort11 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort11 m_sort11)
{struct s} : sort11 n_sort11 :=
  match s with
  | var_sort11 _ s0 => sigma_sort11 s0
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix11 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  end
with subst_sort12 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort12 m_sort11)
{struct s} : sort12 n_sort11 :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix12 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  end
with subst_sort13 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort13 m_sort11)
{struct s} : sort13 n_sort11 :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix13 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  | clam16 _ s0 =>
      clam16 n_sort11 (subst_sort14 (up_sort11_sort11 sigma_sort11) s0)
  end
with subst_sort14 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort14 m_sort11)
{struct s} : sort14 n_sort11 :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix14 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  end
with subst_sort15 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11) (s : sort15 m_sort11)
{struct s} : sort15 n_sort11 :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix15 n_sort11 (subst_sort8 sigma_sort11 s0)
        (subst_sort9 sigma_sort11 s1) (subst_sort10 sigma_sort11 s2)
        (subst_sort11 sigma_sort11 s3) (subst_sort12 sigma_sort11 s4)
        (subst_sort13 sigma_sort11 s5) (subst_sort14 sigma_sort11 s6)
        (subst_sort15 sigma_sort11 s7)
  end.

Lemma upId_sort11_sort11 {m_sort11 : nat}
  (sigma : fin m_sort11 -> sort11 m_sort11)
  (Eq : forall x, sigma x = var_sort11 m_sort11 x) :
  forall x, up_sort11_sort11 sigma x = var_sort11 (S m_sort11) x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort11 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upId_list_sort11_sort11 {p : nat} {m_sort11 : nat}
  (sigma : fin m_sort11 -> sort11 m_sort11)
  (Eq : forall x, sigma x = var_sort11 m_sort11 x) :
  forall x, up_list_sort11_sort11 p sigma x = var_sort11 (plus p m_sort11) x.

Proof.
exact (fun n =>
              scons_p_eta (var_sort11 (plus p m_sort11))
                (fun n => ap (ren_sort11 (shift_p p)) (Eq n))
                (fun n => eq_refl)).

Qed.

Fixpoint idSubst_sort8 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort8 m_sort11) {struct s} : subst_sort8 sigma_sort11 s = s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  end
with idSubst_sort9 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort9 m_sort11) {struct s} : subst_sort9 sigma_sort11 s = s :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  end
with idSubst_sort10 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort10 m_sort11) {struct s} : subst_sort10 sigma_sort11 s = s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  end
with idSubst_sort11 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort11 m_sort11) {struct s} : subst_sort11 sigma_sort11 s = s :=
  match s with
  | var_sort11 _ s0 => Eq_sort11 s0
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  end
with idSubst_sort12 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort12 m_sort11) {struct s} : subst_sort12 sigma_sort11 s = s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  end
with idSubst_sort13 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort13 m_sort11) {struct s} : subst_sort13 sigma_sort11 s = s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  | clam16 _ s0 =>
      congr_clam16
        (idSubst_sort14 (up_sort11_sort11 sigma_sort11)
           (upId_sort11_sort11 _ Eq_sort11) s0)
  end
with idSubst_sort14 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort14 m_sort11) {struct s} : subst_sort14 sigma_sort11 s = s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  end
with idSubst_sort15 {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 m_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 m_sort11 x)
(s : sort15 m_sort11) {struct s} : subst_sort15 sigma_sort11 s = s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15 (idSubst_sort8 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort12 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort13 sigma_sort11 Eq_sort11 s5)
        (idSubst_sort14 sigma_sort11 Eq_sort11 s6)
        (idSubst_sort15 sigma_sort11 Eq_sort11 s7)
  end.

Lemma upExtRen_sort11_sort11 {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_sort11_sort11 xi x = upRen_sort11_sort11 zeta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap shift (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExtRen_list_sort11_sort11 {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x,
  upRen_list_sort11_sort11 p xi x = upRen_list_sort11_sort11 p zeta x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (shift_p p) (Eq n))).

Qed.

Fixpoint extRen_sort8 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort8 m_sort11)
{struct s} : ren_sort8 xi_sort11 s = ren_sort8 zeta_sort11 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  end
with extRen_sort9 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort9 m_sort11)
{struct s} : ren_sort9 xi_sort11 s = ren_sort9 zeta_sort11 s :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  end
with extRen_sort10 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort10 m_sort11)
{struct s} : ren_sort10 xi_sort11 s = ren_sort10 zeta_sort11 s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  end
with extRen_sort11 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort11 m_sort11)
{struct s} : ren_sort11 xi_sort11 s = ren_sort11 zeta_sort11 s :=
  match s with
  | var_sort11 _ s0 => ap (var_sort11 n_sort11) (Eq_sort11 s0)
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  end
with extRen_sort12 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort12 m_sort11)
{struct s} : ren_sort12 xi_sort11 s = ren_sort12 zeta_sort11 s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  end
with extRen_sort13 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort13 m_sort11)
{struct s} : ren_sort13 xi_sort11 s = ren_sort13 zeta_sort11 s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  | clam16 _ s0 =>
      congr_clam16
        (extRen_sort14 (upRen_sort11_sort11 xi_sort11)
           (upRen_sort11_sort11 zeta_sort11)
           (upExtRen_sort11_sort11 _ _ Eq_sort11) s0)
  end
with extRen_sort14 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort14 m_sort11)
{struct s} : ren_sort14 xi_sort11 s = ren_sort14 zeta_sort11 s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  end
with extRen_sort15 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(zeta_sort11 : fin m_sort11 -> fin n_sort11)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort15 m_sort11)
{struct s} : ren_sort15 xi_sort11 s = ren_sort15 zeta_sort11 s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15 (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort12 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort13 xi_sort11 zeta_sort11 Eq_sort11 s5)
        (extRen_sort14 xi_sort11 zeta_sort11 Eq_sort11 s6)
        (extRen_sort15 xi_sort11 zeta_sort11 Eq_sort11 s7)
  end.

Lemma upExt_sort11_sort11 {m : nat} {n_sort11 : nat}
  (sigma : fin m -> sort11 n_sort11) (tau : fin m -> sort11 n_sort11)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_sort11_sort11 sigma x = up_sort11_sort11 tau x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort11 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExt_list_sort11_sort11 {p : nat} {m : nat} {n_sort11 : nat}
  (sigma : fin m -> sort11 n_sort11) (tau : fin m -> sort11 n_sort11)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_sort11_sort11 p sigma x = up_list_sort11_sort11 p tau x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (ren_sort11 (shift_p p)) (Eq n))).

Qed.

Fixpoint ext_sort8 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort8 m_sort11)
{struct s} : subst_sort8 sigma_sort11 s = subst_sort8 tau_sort11 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  end
with ext_sort9 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort9 m_sort11)
{struct s} : subst_sort9 sigma_sort11 s = subst_sort9 tau_sort11 s :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  end
with ext_sort10 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort10 m_sort11)
{struct s} : subst_sort10 sigma_sort11 s = subst_sort10 tau_sort11 s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  end
with ext_sort11 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort11 m_sort11)
{struct s} : subst_sort11 sigma_sort11 s = subst_sort11 tau_sort11 s :=
  match s with
  | var_sort11 _ s0 => Eq_sort11 s0
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  end
with ext_sort12 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort12 m_sort11)
{struct s} : subst_sort12 sigma_sort11 s = subst_sort12 tau_sort11 s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  end
with ext_sort13 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort13 m_sort11)
{struct s} : subst_sort13 sigma_sort11 s = subst_sort13 tau_sort11 s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  | clam16 _ s0 =>
      congr_clam16
        (ext_sort14 (up_sort11_sort11 sigma_sort11)
           (up_sort11_sort11 tau_sort11) (upExt_sort11_sort11 _ _ Eq_sort11)
           s0)
  end
with ext_sort14 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort14 m_sort11)
{struct s} : subst_sort14 sigma_sort11 s = subst_sort14 tau_sort11 s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  end
with ext_sort15 {m_sort11 : nat} {n_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(tau_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort15 m_sort11)
{struct s} : subst_sort15 sigma_sort11 s = subst_sort15 tau_sort11 s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15 (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort12 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort13 sigma_sort11 tau_sort11 Eq_sort11 s5)
        (ext_sort14 sigma_sort11 tau_sort11 Eq_sort11 s6)
        (ext_sort15 sigma_sort11 tau_sort11 Eq_sort11 s7)
  end.

Lemma up_ren_ren_sort11_sort11 {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_sort11_sort11 zeta) (upRen_sort11_sort11 xi) x =
  upRen_sort11_sort11 rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Lemma up_ren_ren_list_sort11_sort11 {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_sort11_sort11 p zeta) (upRen_list_sort11_sort11 p xi) x =
  upRen_list_sort11_sort11 p rho x.

Proof.
exact (up_ren_ren_p Eq).

Qed.

Fixpoint compRenRen_sort8 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort8 m_sort11) {struct s} :
ren_sort8 zeta_sort11 (ren_sort8 xi_sort11 s) = ren_sort8 rho_sort11 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  end
with compRenRen_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort9 m_sort11) {struct s} :
ren_sort9 zeta_sort11 (ren_sort9 xi_sort11 s) = ren_sort9 rho_sort11 s :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  end
with compRenRen_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort10 m_sort11) {struct s} :
ren_sort10 zeta_sort11 (ren_sort10 xi_sort11 s) = ren_sort10 rho_sort11 s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  end
with compRenRen_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort11 m_sort11) {struct s} :
ren_sort11 zeta_sort11 (ren_sort11 xi_sort11 s) = ren_sort11 rho_sort11 s :=
  match s with
  | var_sort11 _ s0 => ap (var_sort11 l_sort11) (Eq_sort11 s0)
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  end
with compRenRen_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort12 m_sort11) {struct s} :
ren_sort12 zeta_sort11 (ren_sort12 xi_sort11 s) = ren_sort12 rho_sort11 s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  end
with compRenRen_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort13 m_sort11) {struct s} :
ren_sort13 zeta_sort11 (ren_sort13 xi_sort11 s) = ren_sort13 rho_sort11 s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  | clam16 _ s0 =>
      congr_clam16
        (compRenRen_sort14 (upRen_sort11_sort11 xi_sort11)
           (upRen_sort11_sort11 zeta_sort11) (upRen_sort11_sort11 rho_sort11)
           (up_ren_ren _ _ _ Eq_sort11) s0)
  end
with compRenRen_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort14 m_sort11) {struct s} :
ren_sort14 zeta_sort11 (ren_sort14 xi_sort11 s) = ren_sort14 rho_sort11 s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  end
with compRenRen_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(rho_sort11 : fin m_sort11 -> fin l_sort11)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort15 m_sort11) {struct s} :
ren_sort15 zeta_sort11 (ren_sort15 xi_sort11 s) = ren_sort15 rho_sort11 s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort12 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort13 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
        (compRenRen_sort14 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s6)
        (compRenRen_sort15 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s7)
  end.

Lemma up_ren_subst_sort11_sort11 {k : nat} {l : nat} {m_sort11 : nat}
  (xi : fin k -> fin l) (tau : fin l -> sort11 m_sort11)
  (theta : fin k -> sort11 m_sort11)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_sort11_sort11 tau) (upRen_sort11_sort11 xi) x =
  up_sort11_sort11 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort11 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma up_ren_subst_list_sort11_sort11 {p : nat} {k : nat} {l : nat}
  {m_sort11 : nat} (xi : fin k -> fin l) (tau : fin l -> sort11 m_sort11)
  (theta : fin k -> sort11 m_sort11)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_sort11_sort11 p tau) (upRen_list_sort11_sort11 p xi) x =
  up_list_sort11_sort11 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr (fun z => scons_p_head' _ _ z)
                   (fun z =>
                    eq_trans (scons_p_tail' _ _ (xi z))
                      (ap (ren_sort11 (shift_p p)) (Eq z))))).

Qed.

Fixpoint compRenSubst_sort8 {k_sort11 : nat} {l_sort11 : nat}
{m_sort11 : nat} (xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort8 m_sort11) {struct s} :
subst_sort8 tau_sort11 (ren_sort8 xi_sort11 s) = subst_sort8 theta_sort11 s
:=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  end
with compRenSubst_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort9 m_sort11) {struct s} :
subst_sort9 tau_sort11 (ren_sort9 xi_sort11 s) = subst_sort9 theta_sort11 s
:=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  end
with compRenSubst_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort10 m_sort11) {struct s} :
subst_sort10 tau_sort11 (ren_sort10 xi_sort11 s) =
subst_sort10 theta_sort11 s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  end
with compRenSubst_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort11 m_sort11) {struct s} :
subst_sort11 tau_sort11 (ren_sort11 xi_sort11 s) =
subst_sort11 theta_sort11 s :=
  match s with
  | var_sort11 _ s0 => Eq_sort11 s0
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  end
with compRenSubst_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort12 m_sort11) {struct s} :
subst_sort12 tau_sort11 (ren_sort12 xi_sort11 s) =
subst_sort12 theta_sort11 s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  end
with compRenSubst_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort13 m_sort11) {struct s} :
subst_sort13 tau_sort11 (ren_sort13 xi_sort11 s) =
subst_sort13 theta_sort11 s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  | clam16 _ s0 =>
      congr_clam16
        (compRenSubst_sort14 (upRen_sort11_sort11 xi_sort11)
           (up_sort11_sort11 tau_sort11) (up_sort11_sort11 theta_sort11)
           (up_ren_subst_sort11_sort11 _ _ _ Eq_sort11) s0)
  end
with compRenSubst_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort14 m_sort11) {struct s} :
subst_sort14 tau_sort11 (ren_sort14 xi_sort11 s) =
subst_sort14 theta_sort11 s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  end
with compRenSubst_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort15 m_sort11) {struct s} :
subst_sort15 tau_sort11 (ren_sort15 xi_sort11 s) =
subst_sort15 theta_sort11 s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort12 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort13 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
        (compRenSubst_sort14 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s6)
        (compRenSubst_sort15 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s7)
  end.

Lemma up_subst_ren_sort11_sort11 {k : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma : fin k -> sort11 l_sort11)
  (zeta_sort11 : fin l_sort11 -> fin m_sort11)
  (theta : fin k -> sort11 m_sort11)
  (Eq : forall x, funcomp (ren_sort11 zeta_sort11) sigma x = theta x) :
  forall x,
  funcomp (ren_sort11 (upRen_sort11_sort11 zeta_sort11))
    (up_sort11_sort11 sigma) x = up_sort11_sort11 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenRen_sort11 shift
                       (upRen_sort11_sort11 zeta_sort11)
                       (funcomp shift zeta_sort11) (fun x => eq_refl)
                       (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compRenRen_sort11 zeta_sort11 shift
                             (funcomp shift zeta_sort11) (fun x => eq_refl)
                             (sigma fin_n)))
                       (ap (ren_sort11 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_ren_list_sort11_sort11 {p : nat} {k : nat} {l_sort11 : nat}
  {m_sort11 : nat} (sigma : fin k -> sort11 l_sort11)
  (zeta_sort11 : fin l_sort11 -> fin m_sort11)
  (theta : fin k -> sort11 m_sort11)
  (Eq : forall x, funcomp (ren_sort11 zeta_sort11) sigma x = theta x) :
  forall x,
  funcomp (ren_sort11 (upRen_list_sort11_sort11 p zeta_sort11))
    (up_list_sort11_sort11 p sigma) x = up_list_sort11_sort11 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr
                   (fun x =>
                    ap (var_sort11 (plus p m_sort11)) (scons_p_head' _ _ x))
                   (fun n =>
                    eq_trans
                      (compRenRen_sort11 (shift_p p)
                         (upRen_list_sort11_sort11 p zeta_sort11)
                         (funcomp (shift_p p) zeta_sort11)
                         (fun x => scons_p_tail' _ _ x) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compRenRen_sort11 zeta_sort11 (shift_p p)
                               (funcomp (shift_p p) zeta_sort11)
                               (fun x => eq_refl) (sigma n)))
                         (ap (ren_sort11 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstRen_sort8 {k_sort11 : nat} {l_sort11 : nat}
{m_sort11 : nat} (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort8 m_sort11) {struct s} :
ren_sort8 zeta_sort11 (subst_sort8 sigma_sort11 s) =
subst_sort8 theta_sort11 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstRen_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort9 m_sort11) {struct s} :
ren_sort9 zeta_sort11 (subst_sort9 sigma_sort11 s) =
subst_sort9 theta_sort11 s :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstRen_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort10 m_sort11) {struct s} :
ren_sort10 zeta_sort11 (subst_sort10 sigma_sort11 s) =
subst_sort10 theta_sort11 s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstRen_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort11 m_sort11) {struct s} :
ren_sort11 zeta_sort11 (subst_sort11 sigma_sort11 s) =
subst_sort11 theta_sort11 s :=
  match s with
  | var_sort11 _ s0 => Eq_sort11 s0
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstRen_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort12 m_sort11) {struct s} :
ren_sort12 zeta_sort11 (subst_sort12 sigma_sort11 s) =
subst_sort12 theta_sort11 s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstRen_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort13 m_sort11) {struct s} :
ren_sort13 zeta_sort11 (subst_sort13 sigma_sort11 s) =
subst_sort13 theta_sort11 s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  | clam16 _ s0 =>
      congr_clam16
        (compSubstRen_sort14 (up_sort11_sort11 sigma_sort11)
           (upRen_sort11_sort11 zeta_sort11) (up_sort11_sort11 theta_sort11)
           (up_subst_ren_sort11_sort11 _ _ _ Eq_sort11) s0)
  end
with compSubstRen_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort14 m_sort11) {struct s} :
ren_sort14 zeta_sort11 (subst_sort14 sigma_sort11 s) =
subst_sort14 theta_sort11 s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstRen_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(zeta_sort11 : fin k_sort11 -> fin l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort15 m_sort11) {struct s} :
ren_sort15 zeta_sort11 (subst_sort15 sigma_sort11 s) =
subst_sort15 theta_sort11 s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort12 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort13 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstRen_sort14 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstRen_sort15 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s7)
  end.

Lemma up_subst_subst_sort11_sort11 {k : nat} {l_sort11 : nat}
  {m_sort11 : nat} (sigma : fin k -> sort11 l_sort11)
  (tau_sort11 : fin l_sort11 -> sort11 m_sort11)
  (theta : fin k -> sort11 m_sort11)
  (Eq : forall x, funcomp (subst_sort11 tau_sort11) sigma x = theta x) :
  forall x,
  funcomp (subst_sort11 (up_sort11_sort11 tau_sort11))
    (up_sort11_sort11 sigma) x = up_sort11_sort11 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenSubst_sort11 shift (up_sort11_sort11 tau_sort11)
                       (funcomp (up_sort11_sort11 tau_sort11) shift)
                       (fun x => eq_refl) (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_sort11 tau_sort11 shift
                             (funcomp (ren_sort11 shift) tau_sort11)
                             (fun x => eq_refl) (sigma fin_n)))
                       (ap (ren_sort11 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_subst_list_sort11_sort11 {p : nat} {k : nat} {l_sort11 : nat}
  {m_sort11 : nat} (sigma : fin k -> sort11 l_sort11)
  (tau_sort11 : fin l_sort11 -> sort11 m_sort11)
  (theta : fin k -> sort11 m_sort11)
  (Eq : forall x, funcomp (subst_sort11 tau_sort11) sigma x = theta x) :
  forall x,
  funcomp (subst_sort11 (up_list_sort11_sort11 p tau_sort11))
    (up_list_sort11_sort11 p sigma) x = up_list_sort11_sort11 p theta x.

Proof.
exact (fun n =>
              eq_trans
                (scons_p_comp'
                   (funcomp (var_sort11 (plus p l_sort11)) (zero_p p)) _ _ n)
                (scons_p_congr
                   (fun x =>
                    scons_p_head' _ (fun z => ren_sort11 (shift_p p) _) x)
                   (fun n =>
                    eq_trans
                      (compRenSubst_sort11 (shift_p p)
                         (up_list_sort11_sort11 p tau_sort11)
                         (funcomp (up_list_sort11_sort11 p tau_sort11)
                            (shift_p p)) (fun x => eq_refl) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compSubstRen_sort11 tau_sort11 (shift_p p) _
                               (fun x => eq_sym (scons_p_tail' _ _ x))
                               (sigma n)))
                         (ap (ren_sort11 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstSubst_sort8 {k_sort11 : nat} {l_sort11 : nat}
{m_sort11 : nat} (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort8 m_sort11) {struct s} :
subst_sort8 tau_sort11 (subst_sort8 sigma_sort11 s) =
subst_sort8 theta_sort11 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstSubst_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort9 m_sort11) {struct s} :
subst_sort9 tau_sort11 (subst_sort9 sigma_sort11 s) =
subst_sort9 theta_sort11 s :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstSubst_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort10 m_sort11) {struct s} :
subst_sort10 tau_sort11 (subst_sort10 sigma_sort11 s) =
subst_sort10 theta_sort11 s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstSubst_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort11 m_sort11) {struct s} :
subst_sort11 tau_sort11 (subst_sort11 sigma_sort11 s) =
subst_sort11 theta_sort11 s :=
  match s with
  | var_sort11 _ s0 => Eq_sort11 s0
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstSubst_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort12 m_sort11) {struct s} :
subst_sort12 tau_sort11 (subst_sort12 sigma_sort11 s) =
subst_sort12 theta_sort11 s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstSubst_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort13 m_sort11) {struct s} :
subst_sort13 tau_sort11 (subst_sort13 sigma_sort11 s) =
subst_sort13 theta_sort11 s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  | clam16 _ s0 =>
      congr_clam16
        (compSubstSubst_sort14 (up_sort11_sort11 sigma_sort11)
           (up_sort11_sort11 tau_sort11) (up_sort11_sort11 theta_sort11)
           (up_subst_subst_sort11_sort11 _ _ _ Eq_sort11) s0)
  end
with compSubstSubst_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort14 m_sort11) {struct s} :
subst_sort14 tau_sort11 (subst_sort14 sigma_sort11 s) =
subst_sort14 theta_sort11 s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  end
with compSubstSubst_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
(sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
(tau_sort11 : fin k_sort11 -> sort11 l_sort11)
(theta_sort11 : fin m_sort11 -> sort11 l_sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort15 m_sort11) {struct s} :
subst_sort15 tau_sort11 (subst_sort15 sigma_sort11 s) =
subst_sort15 theta_sort11 s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort12 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort13 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
        (compSubstSubst_sort14 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s6)
        (compSubstSubst_sort15 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s7)
  end.

Lemma rinstInst_up_sort11_sort11 {m : nat} {n_sort11 : nat}
  (xi : fin m -> fin n_sort11) (sigma : fin m -> sort11 n_sort11)
  (Eq : forall x, funcomp (var_sort11 n_sort11) xi x = sigma x) :
  forall x,
  funcomp (var_sort11 (S n_sort11)) (upRen_sort11_sort11 xi) x =
  up_sort11_sort11 sigma x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort11 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma rinstInst_up_list_sort11_sort11 {p : nat} {m : nat} {n_sort11 : nat}
  (xi : fin m -> fin n_sort11) (sigma : fin m -> sort11 n_sort11)
  (Eq : forall x, funcomp (var_sort11 n_sort11) xi x = sigma x) :
  forall x,
  funcomp (var_sort11 (plus p n_sort11)) (upRen_list_sort11_sort11 p xi) x =
  up_list_sort11_sort11 p sigma x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ (var_sort11 (plus p n_sort11)) n)
                (scons_p_congr (fun z => eq_refl)
                   (fun n => ap (ren_sort11 (shift_p p)) (Eq n)))).

Qed.

Fixpoint rinst_inst_sort8 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort8 m_sort11) {struct s} :
ren_sort8 xi_sort11 s = subst_sort8 sigma_sort11 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix8 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  end
with rinst_inst_sort9 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort9 m_sort11) {struct s} :
ren_sort9 xi_sort11 s = subst_sort9 sigma_sort11 s :=
  match s with
  | cmix9 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix9 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  end
with rinst_inst_sort10 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort10 m_sort11) {struct s} :
ren_sort10 xi_sort11 s = subst_sort10 sigma_sort11 s :=
  match s with
  | cmix10 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix10 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  end
with rinst_inst_sort11 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort11 m_sort11) {struct s} :
ren_sort11 xi_sort11 s = subst_sort11 sigma_sort11 s :=
  match s with
  | var_sort11 _ s0 => Eq_sort11 s0
  | cmix11 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix11 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  end
with rinst_inst_sort12 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort12 m_sort11) {struct s} :
ren_sort12 xi_sort11 s = subst_sort12 sigma_sort11 s :=
  match s with
  | cmix12 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix12 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  end
with rinst_inst_sort13 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort13 m_sort11) {struct s} :
ren_sort13 xi_sort11 s = subst_sort13 sigma_sort11 s :=
  match s with
  | cmix13 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix13 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  | clam16 _ s0 =>
      congr_clam16
        (rinst_inst_sort14 (upRen_sort11_sort11 xi_sort11)
           (up_sort11_sort11 sigma_sort11)
           (rinstInst_up_sort11_sort11 _ _ Eq_sort11) s0)
  end
with rinst_inst_sort14 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort14 m_sort11) {struct s} :
ren_sort14 xi_sort11 s = subst_sort14 sigma_sort11 s :=
  match s with
  | cmix14 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix14 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  end
with rinst_inst_sort15 {m_sort11 : nat} {n_sort11 : nat}
(xi_sort11 : fin m_sort11 -> fin n_sort11)
(sigma_sort11 : fin m_sort11 -> sort11 n_sort11)
(Eq_sort11 : forall x,
             funcomp (var_sort11 n_sort11) xi_sort11 x = sigma_sort11 x)
(s : sort15 m_sort11) {struct s} :
ren_sort15 xi_sort11 s = subst_sort15 sigma_sort11 s :=
  match s with
  | cmix15 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix15 (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort12 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort13 xi_sort11 sigma_sort11 Eq_sort11 s5)
        (rinst_inst_sort14 xi_sort11 sigma_sort11 Eq_sort11 s6)
        (rinst_inst_sort15 xi_sort11 sigma_sort11 Eq_sort11 s7)
  end.

Lemma renRen_sort8 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort8 m_sort11) :
  ren_sort8 zeta_sort11 (ren_sort8 xi_sort11 s) =
  ren_sort8 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort8 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort9 m_sort11) :
  ren_sort9 zeta_sort11 (ren_sort9 xi_sort11 s) =
  ren_sort9 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort9 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort10 m_sort11) :
  ren_sort10 zeta_sort11 (ren_sort10 xi_sort11 s) =
  ren_sort10 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort10 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort11 m_sort11) :
  ren_sort11 zeta_sort11 (ren_sort11 xi_sort11 s) =
  ren_sort11 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort11 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort12 m_sort11) :
  ren_sort12 zeta_sort11 (ren_sort12 xi_sort11 s) =
  ren_sort12 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort12 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort13 m_sort11) :
  ren_sort13 zeta_sort11 (ren_sort13 xi_sort11 s) =
  ren_sort13 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort13 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort14 m_sort11) :
  ren_sort14 zeta_sort11 (ren_sort14 xi_sort11 s) =
  ren_sort14 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort14 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort15 m_sort11) :
  ren_sort15 zeta_sort11 (ren_sort15 xi_sort11 s) =
  ren_sort15 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort15 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma compRen_sort8 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort8 m_sort11) :
  ren_sort8 zeta_sort11 (subst_sort8 sigma_sort11 s) =
  subst_sort8 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort8 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort9 m_sort11) :
  ren_sort9 zeta_sort11 (subst_sort9 sigma_sort11 s) =
  subst_sort9 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort9 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort10 m_sort11) :
  ren_sort10 zeta_sort11 (subst_sort10 sigma_sort11 s) =
  subst_sort10 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort10 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort11 m_sort11) :
  ren_sort11 zeta_sort11 (subst_sort11 sigma_sort11 s) =
  subst_sort11 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort11 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort12 m_sort11) :
  ren_sort12 zeta_sort11 (subst_sort12 sigma_sort11 s) =
  subst_sort12 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort12 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort13 m_sort11) :
  ren_sort13 zeta_sort11 (subst_sort13 sigma_sort11 s) =
  subst_sort13 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort13 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort14 m_sort11) :
  ren_sort14 zeta_sort11 (subst_sort14 sigma_sort11 s) =
  subst_sort14 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort14 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (zeta_sort11 : fin k_sort11 -> fin l_sort11) (s : sort15 m_sort11) :
  ren_sort15 zeta_sort11 (subst_sort15 sigma_sort11 s) =
  subst_sort15 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort15 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma renComp_sort8 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort8 m_sort11) :
  subst_sort8 tau_sort11 (ren_sort8 xi_sort11 s) =
  subst_sort8 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort8 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort9 m_sort11) :
  subst_sort9 tau_sort11 (ren_sort9 xi_sort11 s) =
  subst_sort9 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort9 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort10 m_sort11) :
  subst_sort10 tau_sort11 (ren_sort10 xi_sort11 s) =
  subst_sort10 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort10 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort11 m_sort11) :
  subst_sort11 tau_sort11 (ren_sort11 xi_sort11 s) =
  subst_sort11 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort11 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort12 m_sort11) :
  subst_sort12 tau_sort11 (ren_sort12 xi_sort11 s) =
  subst_sort12 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort12 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort13 m_sort11) :
  subst_sort13 tau_sort11 (ren_sort13 xi_sort11 s) =
  subst_sort13 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort13 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort14 m_sort11) :
  subst_sort14 tau_sort11 (ren_sort14 xi_sort11 s) =
  subst_sort14 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort14 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (xi_sort11 : fin m_sort11 -> fin k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort15 m_sort11) :
  subst_sort15 tau_sort11 (ren_sort15 xi_sort11 s) =
  subst_sort15 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort15 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma compComp_sort8 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort8 m_sort11) :
  subst_sort8 tau_sort11 (subst_sort8 sigma_sort11 s) =
  subst_sort8 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort8 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort9 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort9 m_sort11) :
  subst_sort9 tau_sort11 (subst_sort9 sigma_sort11 s) =
  subst_sort9 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort9 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort10 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort10 m_sort11) :
  subst_sort10 tau_sort11 (subst_sort10 sigma_sort11 s) =
  subst_sort10 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort10 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort11 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort11 m_sort11) :
  subst_sort11 tau_sort11 (subst_sort11 sigma_sort11 s) =
  subst_sort11 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort11 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort12 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort12 m_sort11) :
  subst_sort12 tau_sort11 (subst_sort12 sigma_sort11 s) =
  subst_sort12 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort12 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort13 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort13 m_sort11) :
  subst_sort13 tau_sort11 (subst_sort13 sigma_sort11 s) =
  subst_sort13 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort13 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort14 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort14 m_sort11) :
  subst_sort14 tau_sort11 (subst_sort14 sigma_sort11 s) =
  subst_sort14 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort14 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort15 {k_sort11 : nat} {l_sort11 : nat} {m_sort11 : nat}
  (sigma_sort11 : fin m_sort11 -> sort11 k_sort11)
  (tau_sort11 : fin k_sort11 -> sort11 l_sort11) (s : sort15 m_sort11) :
  subst_sort15 tau_sort11 (subst_sort15 sigma_sort11 s) =
  subst_sort15 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort15 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Inductive sort16 (n_sort17 : nat) : Type :=
  | cmix16 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort16 n_sort17
  | clam24 : sort23 (S n_sort17) -> sort16 n_sort17
with sort17 (n_sort17 : nat) : Type :=
  | var_sort17 : fin n_sort17 -> sort17 n_sort17
  | cmix17 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort17 n_sort17
with sort18 (n_sort17 : nat) : Type :=
    cmix18 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort18 n_sort17
with sort19 (n_sort17 : nat) : Type :=
    cmix19 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort19 n_sort17
with sort20 (n_sort17 : nat) : Type :=
    cmix20 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort20 n_sort17
with sort21 (n_sort17 : nat) : Type :=
    cmix21 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort21 n_sort17
with sort22 (n_sort17 : nat) : Type :=
    cmix22 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort22 n_sort17
with sort23 (n_sort17 : nat) : Type :=
    cmix23 :
      sort16 n_sort17 ->
      sort17 n_sort17 ->
      sort18 n_sort17 ->
      sort19 n_sort17 ->
      sort20 n_sort17 ->
      sort21 n_sort17 ->
      sort22 n_sort17 -> sort23 n_sort17 -> sort23 n_sort17.

Lemma congr_cmix16 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix16 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix16 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix16 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix16 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix16 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix16 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix16 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix16 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix16 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix16 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_clam24 {m_sort17 : nat} {s0 : sort23 (S m_sort17)}
  {t0 : sort23 (S m_sort17)} (H0 : s0 = t0) :
  clam24 m_sort17 s0 = clam24 m_sort17 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam24 m_sort17 x) H0)).

Qed.

Lemma congr_cmix17 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix17 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix17 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix17 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix17 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix17 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix17 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix17 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix17 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix17 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix17 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix18 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix18 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix18 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix18 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix18 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix18 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix18 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix18 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix18 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix18 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix18 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix19 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix19 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix19 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix19 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix19 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix19 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix19 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix19 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix19 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix19 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix19 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix20 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix20 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix20 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix20 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix20 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix20 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix20 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix20 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix20 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix20 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix20 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix21 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix21 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix21 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix21 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix21 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix21 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix21 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix21 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix21 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix21 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix21 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix22 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix22 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix22 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix22 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix22 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix22 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix22 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix22 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix22 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix22 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix22 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma congr_cmix23 {m_sort17 : nat} {s0 : sort16 m_sort17}
  {s1 : sort17 m_sort17} {s2 : sort18 m_sort17} {s3 : sort19 m_sort17}
  {s4 : sort20 m_sort17} {s5 : sort21 m_sort17} {s6 : sort22 m_sort17}
  {s7 : sort23 m_sort17} {t0 : sort16 m_sort17} {t1 : sort17 m_sort17}
  {t2 : sort18 m_sort17} {t3 : sort19 m_sort17} {t4 : sort20 m_sort17}
  {t5 : sort21 m_sort17} {t6 : sort22 m_sort17} {t7 : sort23 m_sort17}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7) :
  cmix23 m_sort17 s0 s1 s2 s3 s4 s5 s6 s7 =
  cmix23 m_sort17 t0 t1 t2 t3 t4 t5 t6 t7.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans eq_refl
                                     (ap
                                        (fun x =>
                                         cmix23 m_sort17 x s1 s2 s3 s4 s5 s6
                                           s7) H0))
                                  (ap
                                     (fun x =>
                                      cmix23 m_sort17 t0 x s2 s3 s4 s5 s6 s7)
                                     H1))
                               (ap
                                  (fun x =>
                                   cmix23 m_sort17 t0 t1 x s3 s4 s5 s6 s7) H2))
                            (ap
                               (fun x =>
                                cmix23 m_sort17 t0 t1 t2 x s4 s5 s6 s7) H3))
                         (ap
                            (fun x => cmix23 m_sort17 t0 t1 t2 t3 x s5 s6 s7)
                            H4))
                      (ap (fun x => cmix23 m_sort17 t0 t1 t2 t3 t4 x s6 s7)
                         H5))
                   (ap (fun x => cmix23 m_sort17 t0 t1 t2 t3 t4 t5 x s7) H6))
                (ap (fun x => cmix23 m_sort17 t0 t1 t2 t3 t4 t5 t6 x) H7)).

Qed.

Lemma upRen_sort17_sort17 {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).

Proof.
exact (up_ren xi).

Defined.

Lemma upRen_list_sort17_sort17 (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n).

Proof.
exact (upRen_p p xi).

Defined.

Fixpoint ren_sort16 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort16 m_sort17) {struct s} :
sort16 n_sort17 :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix16 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  | clam24 _ s0 =>
      clam24 n_sort17 (ren_sort23 (upRen_sort17_sort17 xi_sort17) s0)
  end
with ren_sort17 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort17 m_sort17) {struct s} :
sort17 n_sort17 :=
  match s with
  | var_sort17 _ s0 => var_sort17 n_sort17 (xi_sort17 s0)
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix17 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  end
with ren_sort18 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort18 m_sort17) {struct s} :
sort18 n_sort17 :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix18 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  end
with ren_sort19 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort19 m_sort17) {struct s} :
sort19 n_sort17 :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix19 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  end
with ren_sort20 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort20 m_sort17) {struct s} :
sort20 n_sort17 :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix20 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  end
with ren_sort21 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort21 m_sort17) {struct s} :
sort21 n_sort17 :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix21 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  end
with ren_sort22 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort22 m_sort17) {struct s} :
sort22 n_sort17 :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix22 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  end
with ren_sort23 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17) (s : sort23 m_sort17) {struct s} :
sort23 n_sort17 :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix23 n_sort17 (ren_sort16 xi_sort17 s0) (ren_sort17 xi_sort17 s1)
        (ren_sort18 xi_sort17 s2) (ren_sort19 xi_sort17 s3)
        (ren_sort20 xi_sort17 s4) (ren_sort21 xi_sort17 s5)
        (ren_sort22 xi_sort17 s6) (ren_sort23 xi_sort17 s7)
  end.

Lemma up_sort17_sort17 {m : nat} {n_sort17 : nat}
  (sigma : fin m -> sort17 n_sort17) : fin (S m) -> sort17 (S n_sort17).

Proof.
exact (scons (var_sort17 (S n_sort17) var_zero)
                (funcomp (ren_sort17 shift) sigma)).

Defined.

Lemma up_list_sort17_sort17 (p : nat) {m : nat} {n_sort17 : nat}
  (sigma : fin m -> sort17 n_sort17) :
  fin (plus p m) -> sort17 (plus p n_sort17).

Proof.
exact (scons_p p (funcomp (var_sort17 (plus p n_sort17)) (zero_p p))
                (funcomp (ren_sort17 (shift_p p)) sigma)).

Defined.

Fixpoint subst_sort16 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort16 m_sort17)
{struct s} : sort16 n_sort17 :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix16 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  | clam24 _ s0 =>
      clam24 n_sort17 (subst_sort23 (up_sort17_sort17 sigma_sort17) s0)
  end
with subst_sort17 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort17 m_sort17)
{struct s} : sort17 n_sort17 :=
  match s with
  | var_sort17 _ s0 => sigma_sort17 s0
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix17 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  end
with subst_sort18 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort18 m_sort17)
{struct s} : sort18 n_sort17 :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix18 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  end
with subst_sort19 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort19 m_sort17)
{struct s} : sort19 n_sort17 :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix19 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  end
with subst_sort20 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort20 m_sort17)
{struct s} : sort20 n_sort17 :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix20 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  end
with subst_sort21 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort21 m_sort17)
{struct s} : sort21 n_sort17 :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix21 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  end
with subst_sort22 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort22 m_sort17)
{struct s} : sort22 n_sort17 :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix22 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  end
with subst_sort23 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17) (s : sort23 m_sort17)
{struct s} : sort23 n_sort17 :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      cmix23 n_sort17 (subst_sort16 sigma_sort17 s0)
        (subst_sort17 sigma_sort17 s1) (subst_sort18 sigma_sort17 s2)
        (subst_sort19 sigma_sort17 s3) (subst_sort20 sigma_sort17 s4)
        (subst_sort21 sigma_sort17 s5) (subst_sort22 sigma_sort17 s6)
        (subst_sort23 sigma_sort17 s7)
  end.

Lemma upId_sort17_sort17 {m_sort17 : nat}
  (sigma : fin m_sort17 -> sort17 m_sort17)
  (Eq : forall x, sigma x = var_sort17 m_sort17 x) :
  forall x, up_sort17_sort17 sigma x = var_sort17 (S m_sort17) x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort17 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upId_list_sort17_sort17 {p : nat} {m_sort17 : nat}
  (sigma : fin m_sort17 -> sort17 m_sort17)
  (Eq : forall x, sigma x = var_sort17 m_sort17 x) :
  forall x, up_list_sort17_sort17 p sigma x = var_sort17 (plus p m_sort17) x.

Proof.
exact (fun n =>
              scons_p_eta (var_sort17 (plus p m_sort17))
                (fun n => ap (ren_sort17 (shift_p p)) (Eq n))
                (fun n => eq_refl)).

Qed.

Fixpoint idSubst_sort16 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort16 m_sort17) {struct s} : subst_sort16 sigma_sort17 s = s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  | clam24 _ s0 =>
      congr_clam24
        (idSubst_sort23 (up_sort17_sort17 sigma_sort17)
           (upId_sort17_sort17 _ Eq_sort17) s0)
  end
with idSubst_sort17 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort17 m_sort17) {struct s} : subst_sort17 sigma_sort17 s = s :=
  match s with
  | var_sort17 _ s0 => Eq_sort17 s0
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  end
with idSubst_sort18 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort18 m_sort17) {struct s} : subst_sort18 sigma_sort17 s = s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  end
with idSubst_sort19 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort19 m_sort17) {struct s} : subst_sort19 sigma_sort17 s = s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  end
with idSubst_sort20 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort20 m_sort17) {struct s} : subst_sort20 sigma_sort17 s = s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  end
with idSubst_sort21 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort21 m_sort17) {struct s} : subst_sort21 sigma_sort17 s = s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  end
with idSubst_sort22 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort22 m_sort17) {struct s} : subst_sort22 sigma_sort17 s = s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  end
with idSubst_sort23 {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 m_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = var_sort17 m_sort17 x)
(s : sort23 m_sort17) {struct s} : subst_sort23 sigma_sort17 s = s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23 (idSubst_sort16 sigma_sort17 Eq_sort17 s0)
        (idSubst_sort17 sigma_sort17 Eq_sort17 s1)
        (idSubst_sort18 sigma_sort17 Eq_sort17 s2)
        (idSubst_sort19 sigma_sort17 Eq_sort17 s3)
        (idSubst_sort20 sigma_sort17 Eq_sort17 s4)
        (idSubst_sort21 sigma_sort17 Eq_sort17 s5)
        (idSubst_sort22 sigma_sort17 Eq_sort17 s6)
        (idSubst_sort23 sigma_sort17 Eq_sort17 s7)
  end.

Lemma upExtRen_sort17_sort17 {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_sort17_sort17 xi x = upRen_sort17_sort17 zeta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap shift (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExtRen_list_sort17_sort17 {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x,
  upRen_list_sort17_sort17 p xi x = upRen_list_sort17_sort17 p zeta x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (shift_p p) (Eq n))).

Qed.

Fixpoint extRen_sort16 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort16 m_sort17)
{struct s} : ren_sort16 xi_sort17 s = ren_sort16 zeta_sort17 s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  | clam24 _ s0 =>
      congr_clam24
        (extRen_sort23 (upRen_sort17_sort17 xi_sort17)
           (upRen_sort17_sort17 zeta_sort17)
           (upExtRen_sort17_sort17 _ _ Eq_sort17) s0)
  end
with extRen_sort17 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort17 m_sort17)
{struct s} : ren_sort17 xi_sort17 s = ren_sort17 zeta_sort17 s :=
  match s with
  | var_sort17 _ s0 => ap (var_sort17 n_sort17) (Eq_sort17 s0)
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  end
with extRen_sort18 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort18 m_sort17)
{struct s} : ren_sort18 xi_sort17 s = ren_sort18 zeta_sort17 s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  end
with extRen_sort19 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort19 m_sort17)
{struct s} : ren_sort19 xi_sort17 s = ren_sort19 zeta_sort17 s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  end
with extRen_sort20 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort20 m_sort17)
{struct s} : ren_sort20 xi_sort17 s = ren_sort20 zeta_sort17 s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  end
with extRen_sort21 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort21 m_sort17)
{struct s} : ren_sort21 xi_sort17 s = ren_sort21 zeta_sort17 s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  end
with extRen_sort22 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort22 m_sort17)
{struct s} : ren_sort22 xi_sort17 s = ren_sort22 zeta_sort17 s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  end
with extRen_sort23 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(zeta_sort17 : fin m_sort17 -> fin n_sort17)
(Eq_sort17 : forall x, xi_sort17 x = zeta_sort17 x) (s : sort23 m_sort17)
{struct s} : ren_sort23 xi_sort17 s = ren_sort23 zeta_sort17 s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23 (extRen_sort16 xi_sort17 zeta_sort17 Eq_sort17 s0)
        (extRen_sort17 xi_sort17 zeta_sort17 Eq_sort17 s1)
        (extRen_sort18 xi_sort17 zeta_sort17 Eq_sort17 s2)
        (extRen_sort19 xi_sort17 zeta_sort17 Eq_sort17 s3)
        (extRen_sort20 xi_sort17 zeta_sort17 Eq_sort17 s4)
        (extRen_sort21 xi_sort17 zeta_sort17 Eq_sort17 s5)
        (extRen_sort22 xi_sort17 zeta_sort17 Eq_sort17 s6)
        (extRen_sort23 xi_sort17 zeta_sort17 Eq_sort17 s7)
  end.

Lemma upExt_sort17_sort17 {m : nat} {n_sort17 : nat}
  (sigma : fin m -> sort17 n_sort17) (tau : fin m -> sort17 n_sort17)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_sort17_sort17 sigma x = up_sort17_sort17 tau x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort17 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExt_list_sort17_sort17 {p : nat} {m : nat} {n_sort17 : nat}
  (sigma : fin m -> sort17 n_sort17) (tau : fin m -> sort17 n_sort17)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_sort17_sort17 p sigma x = up_list_sort17_sort17 p tau x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (ren_sort17 (shift_p p)) (Eq n))).

Qed.

Fixpoint ext_sort16 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort16 m_sort17)
{struct s} : subst_sort16 sigma_sort17 s = subst_sort16 tau_sort17 s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  | clam24 _ s0 =>
      congr_clam24
        (ext_sort23 (up_sort17_sort17 sigma_sort17)
           (up_sort17_sort17 tau_sort17) (upExt_sort17_sort17 _ _ Eq_sort17)
           s0)
  end
with ext_sort17 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort17 m_sort17)
{struct s} : subst_sort17 sigma_sort17 s = subst_sort17 tau_sort17 s :=
  match s with
  | var_sort17 _ s0 => Eq_sort17 s0
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  end
with ext_sort18 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort18 m_sort17)
{struct s} : subst_sort18 sigma_sort17 s = subst_sort18 tau_sort17 s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  end
with ext_sort19 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort19 m_sort17)
{struct s} : subst_sort19 sigma_sort17 s = subst_sort19 tau_sort17 s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  end
with ext_sort20 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort20 m_sort17)
{struct s} : subst_sort20 sigma_sort17 s = subst_sort20 tau_sort17 s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  end
with ext_sort21 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort21 m_sort17)
{struct s} : subst_sort21 sigma_sort17 s = subst_sort21 tau_sort17 s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  end
with ext_sort22 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort22 m_sort17)
{struct s} : subst_sort22 sigma_sort17 s = subst_sort22 tau_sort17 s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  end
with ext_sort23 {m_sort17 : nat} {n_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(tau_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x, sigma_sort17 x = tau_sort17 x) (s : sort23 m_sort17)
{struct s} : subst_sort23 sigma_sort17 s = subst_sort23 tau_sort17 s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23 (ext_sort16 sigma_sort17 tau_sort17 Eq_sort17 s0)
        (ext_sort17 sigma_sort17 tau_sort17 Eq_sort17 s1)
        (ext_sort18 sigma_sort17 tau_sort17 Eq_sort17 s2)
        (ext_sort19 sigma_sort17 tau_sort17 Eq_sort17 s3)
        (ext_sort20 sigma_sort17 tau_sort17 Eq_sort17 s4)
        (ext_sort21 sigma_sort17 tau_sort17 Eq_sort17 s5)
        (ext_sort22 sigma_sort17 tau_sort17 Eq_sort17 s6)
        (ext_sort23 sigma_sort17 tau_sort17 Eq_sort17 s7)
  end.

Lemma up_ren_ren_sort17_sort17 {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_sort17_sort17 zeta) (upRen_sort17_sort17 xi) x =
  upRen_sort17_sort17 rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Lemma up_ren_ren_list_sort17_sort17 {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_sort17_sort17 p zeta) (upRen_list_sort17_sort17 p xi) x =
  upRen_list_sort17_sort17 p rho x.

Proof.
exact (up_ren_ren_p Eq).

Qed.

Fixpoint compRenRen_sort16 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort16 m_sort17) {struct s} :
ren_sort16 zeta_sort17 (ren_sort16 xi_sort17 s) = ren_sort16 rho_sort17 s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  | clam24 _ s0 =>
      congr_clam24
        (compRenRen_sort23 (upRen_sort17_sort17 xi_sort17)
           (upRen_sort17_sort17 zeta_sort17) (upRen_sort17_sort17 rho_sort17)
           (up_ren_ren _ _ _ Eq_sort17) s0)
  end
with compRenRen_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort17 m_sort17) {struct s} :
ren_sort17 zeta_sort17 (ren_sort17 xi_sort17 s) = ren_sort17 rho_sort17 s :=
  match s with
  | var_sort17 _ s0 => ap (var_sort17 l_sort17) (Eq_sort17 s0)
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  end
with compRenRen_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort18 m_sort17) {struct s} :
ren_sort18 zeta_sort17 (ren_sort18 xi_sort17 s) = ren_sort18 rho_sort17 s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  end
with compRenRen_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort19 m_sort17) {struct s} :
ren_sort19 zeta_sort17 (ren_sort19 xi_sort17 s) = ren_sort19 rho_sort17 s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  end
with compRenRen_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort20 m_sort17) {struct s} :
ren_sort20 zeta_sort17 (ren_sort20 xi_sort17 s) = ren_sort20 rho_sort17 s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  end
with compRenRen_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort21 m_sort17) {struct s} :
ren_sort21 zeta_sort17 (ren_sort21 xi_sort17 s) = ren_sort21 rho_sort17 s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  end
with compRenRen_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort22 m_sort17) {struct s} :
ren_sort22 zeta_sort17 (ren_sort22 xi_sort17 s) = ren_sort22 rho_sort17 s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  end
with compRenRen_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(rho_sort17 : fin m_sort17 -> fin l_sort17)
(Eq_sort17 : forall x, funcomp zeta_sort17 xi_sort17 x = rho_sort17 x)
(s : sort23 m_sort17) {struct s} :
ren_sort23 zeta_sort17 (ren_sort23 xi_sort17 s) = ren_sort23 rho_sort17 s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23
        (compRenRen_sort16 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s0)
        (compRenRen_sort17 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s1)
        (compRenRen_sort18 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s2)
        (compRenRen_sort19 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s3)
        (compRenRen_sort20 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s4)
        (compRenRen_sort21 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s5)
        (compRenRen_sort22 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s6)
        (compRenRen_sort23 xi_sort17 zeta_sort17 rho_sort17 Eq_sort17 s7)
  end.

Lemma up_ren_subst_sort17_sort17 {k : nat} {l : nat} {m_sort17 : nat}
  (xi : fin k -> fin l) (tau : fin l -> sort17 m_sort17)
  (theta : fin k -> sort17 m_sort17)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_sort17_sort17 tau) (upRen_sort17_sort17 xi) x =
  up_sort17_sort17 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort17 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma up_ren_subst_list_sort17_sort17 {p : nat} {k : nat} {l : nat}
  {m_sort17 : nat} (xi : fin k -> fin l) (tau : fin l -> sort17 m_sort17)
  (theta : fin k -> sort17 m_sort17)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_sort17_sort17 p tau) (upRen_list_sort17_sort17 p xi) x =
  up_list_sort17_sort17 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr (fun z => scons_p_head' _ _ z)
                   (fun z =>
                    eq_trans (scons_p_tail' _ _ (xi z))
                      (ap (ren_sort17 (shift_p p)) (Eq z))))).

Qed.

Fixpoint compRenSubst_sort16 {k_sort17 : nat} {l_sort17 : nat}
{m_sort17 : nat} (xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort16 m_sort17) {struct s} :
subst_sort16 tau_sort17 (ren_sort16 xi_sort17 s) =
subst_sort16 theta_sort17 s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  | clam24 _ s0 =>
      congr_clam24
        (compRenSubst_sort23 (upRen_sort17_sort17 xi_sort17)
           (up_sort17_sort17 tau_sort17) (up_sort17_sort17 theta_sort17)
           (up_ren_subst_sort17_sort17 _ _ _ Eq_sort17) s0)
  end
with compRenSubst_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort17 m_sort17) {struct s} :
subst_sort17 tau_sort17 (ren_sort17 xi_sort17 s) =
subst_sort17 theta_sort17 s :=
  match s with
  | var_sort17 _ s0 => Eq_sort17 s0
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  end
with compRenSubst_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort18 m_sort17) {struct s} :
subst_sort18 tau_sort17 (ren_sort18 xi_sort17 s) =
subst_sort18 theta_sort17 s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  end
with compRenSubst_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort19 m_sort17) {struct s} :
subst_sort19 tau_sort17 (ren_sort19 xi_sort17 s) =
subst_sort19 theta_sort17 s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  end
with compRenSubst_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort20 m_sort17) {struct s} :
subst_sort20 tau_sort17 (ren_sort20 xi_sort17 s) =
subst_sort20 theta_sort17 s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  end
with compRenSubst_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort21 m_sort17) {struct s} :
subst_sort21 tau_sort17 (ren_sort21 xi_sort17 s) =
subst_sort21 theta_sort17 s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  end
with compRenSubst_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort22 m_sort17) {struct s} :
subst_sort22 tau_sort17 (ren_sort22 xi_sort17 s) =
subst_sort22 theta_sort17 s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  end
with compRenSubst_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x, funcomp tau_sort17 xi_sort17 x = theta_sort17 x)
(s : sort23 m_sort17) {struct s} :
subst_sort23 tau_sort17 (ren_sort23 xi_sort17 s) =
subst_sort23 theta_sort17 s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23
        (compRenSubst_sort16 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s0)
        (compRenSubst_sort17 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s1)
        (compRenSubst_sort18 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s2)
        (compRenSubst_sort19 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s3)
        (compRenSubst_sort20 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s4)
        (compRenSubst_sort21 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s5)
        (compRenSubst_sort22 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s6)
        (compRenSubst_sort23 xi_sort17 tau_sort17 theta_sort17 Eq_sort17 s7)
  end.

Lemma up_subst_ren_sort17_sort17 {k : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma : fin k -> sort17 l_sort17)
  (zeta_sort17 : fin l_sort17 -> fin m_sort17)
  (theta : fin k -> sort17 m_sort17)
  (Eq : forall x, funcomp (ren_sort17 zeta_sort17) sigma x = theta x) :
  forall x,
  funcomp (ren_sort17 (upRen_sort17_sort17 zeta_sort17))
    (up_sort17_sort17 sigma) x = up_sort17_sort17 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenRen_sort17 shift
                       (upRen_sort17_sort17 zeta_sort17)
                       (funcomp shift zeta_sort17) (fun x => eq_refl)
                       (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compRenRen_sort17 zeta_sort17 shift
                             (funcomp shift zeta_sort17) (fun x => eq_refl)
                             (sigma fin_n)))
                       (ap (ren_sort17 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_ren_list_sort17_sort17 {p : nat} {k : nat} {l_sort17 : nat}
  {m_sort17 : nat} (sigma : fin k -> sort17 l_sort17)
  (zeta_sort17 : fin l_sort17 -> fin m_sort17)
  (theta : fin k -> sort17 m_sort17)
  (Eq : forall x, funcomp (ren_sort17 zeta_sort17) sigma x = theta x) :
  forall x,
  funcomp (ren_sort17 (upRen_list_sort17_sort17 p zeta_sort17))
    (up_list_sort17_sort17 p sigma) x = up_list_sort17_sort17 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr
                   (fun x =>
                    ap (var_sort17 (plus p m_sort17)) (scons_p_head' _ _ x))
                   (fun n =>
                    eq_trans
                      (compRenRen_sort17 (shift_p p)
                         (upRen_list_sort17_sort17 p zeta_sort17)
                         (funcomp (shift_p p) zeta_sort17)
                         (fun x => scons_p_tail' _ _ x) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compRenRen_sort17 zeta_sort17 (shift_p p)
                               (funcomp (shift_p p) zeta_sort17)
                               (fun x => eq_refl) (sigma n)))
                         (ap (ren_sort17 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstRen_sort16 {k_sort17 : nat} {l_sort17 : nat}
{m_sort17 : nat} (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort16 m_sort17) {struct s} :
ren_sort16 zeta_sort17 (subst_sort16 sigma_sort17 s) =
subst_sort16 theta_sort17 s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  | clam24 _ s0 =>
      congr_clam24
        (compSubstRen_sort23 (up_sort17_sort17 sigma_sort17)
           (upRen_sort17_sort17 zeta_sort17) (up_sort17_sort17 theta_sort17)
           (up_subst_ren_sort17_sort17 _ _ _ Eq_sort17) s0)
  end
with compSubstRen_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort17 m_sort17) {struct s} :
ren_sort17 zeta_sort17 (subst_sort17 sigma_sort17 s) =
subst_sort17 theta_sort17 s :=
  match s with
  | var_sort17 _ s0 => Eq_sort17 s0
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstRen_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort18 m_sort17) {struct s} :
ren_sort18 zeta_sort17 (subst_sort18 sigma_sort17 s) =
subst_sort18 theta_sort17 s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstRen_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort19 m_sort17) {struct s} :
ren_sort19 zeta_sort17 (subst_sort19 sigma_sort17 s) =
subst_sort19 theta_sort17 s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstRen_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort20 m_sort17) {struct s} :
ren_sort20 zeta_sort17 (subst_sort20 sigma_sort17 s) =
subst_sort20 theta_sort17 s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstRen_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort21 m_sort17) {struct s} :
ren_sort21 zeta_sort17 (subst_sort21 sigma_sort17 s) =
subst_sort21 theta_sort17 s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstRen_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort22 m_sort17) {struct s} :
ren_sort22 zeta_sort17 (subst_sort22 sigma_sort17 s) =
subst_sort22 theta_sort17 s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstRen_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(zeta_sort17 : fin k_sort17 -> fin l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (ren_sort17 zeta_sort17) sigma_sort17 x = theta_sort17 x)
(s : sort23 m_sort17) {struct s} :
ren_sort23 zeta_sort17 (subst_sort23 sigma_sort17 s) =
subst_sort23 theta_sort17 s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23
        (compSubstRen_sort16 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstRen_sort17 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstRen_sort18 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstRen_sort19 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstRen_sort20 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstRen_sort21 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstRen_sort22 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstRen_sort23 sigma_sort17 zeta_sort17 theta_sort17 Eq_sort17
           s7)
  end.

Lemma up_subst_subst_sort17_sort17 {k : nat} {l_sort17 : nat}
  {m_sort17 : nat} (sigma : fin k -> sort17 l_sort17)
  (tau_sort17 : fin l_sort17 -> sort17 m_sort17)
  (theta : fin k -> sort17 m_sort17)
  (Eq : forall x, funcomp (subst_sort17 tau_sort17) sigma x = theta x) :
  forall x,
  funcomp (subst_sort17 (up_sort17_sort17 tau_sort17))
    (up_sort17_sort17 sigma) x = up_sort17_sort17 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenSubst_sort17 shift (up_sort17_sort17 tau_sort17)
                       (funcomp (up_sort17_sort17 tau_sort17) shift)
                       (fun x => eq_refl) (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_sort17 tau_sort17 shift
                             (funcomp (ren_sort17 shift) tau_sort17)
                             (fun x => eq_refl) (sigma fin_n)))
                       (ap (ren_sort17 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_subst_list_sort17_sort17 {p : nat} {k : nat} {l_sort17 : nat}
  {m_sort17 : nat} (sigma : fin k -> sort17 l_sort17)
  (tau_sort17 : fin l_sort17 -> sort17 m_sort17)
  (theta : fin k -> sort17 m_sort17)
  (Eq : forall x, funcomp (subst_sort17 tau_sort17) sigma x = theta x) :
  forall x,
  funcomp (subst_sort17 (up_list_sort17_sort17 p tau_sort17))
    (up_list_sort17_sort17 p sigma) x = up_list_sort17_sort17 p theta x.

Proof.
exact (fun n =>
              eq_trans
                (scons_p_comp'
                   (funcomp (var_sort17 (plus p l_sort17)) (zero_p p)) _ _ n)
                (scons_p_congr
                   (fun x =>
                    scons_p_head' _ (fun z => ren_sort17 (shift_p p) _) x)
                   (fun n =>
                    eq_trans
                      (compRenSubst_sort17 (shift_p p)
                         (up_list_sort17_sort17 p tau_sort17)
                         (funcomp (up_list_sort17_sort17 p tau_sort17)
                            (shift_p p)) (fun x => eq_refl) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compSubstRen_sort17 tau_sort17 (shift_p p) _
                               (fun x => eq_sym (scons_p_tail' _ _ x))
                               (sigma n)))
                         (ap (ren_sort17 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstSubst_sort16 {k_sort17 : nat} {l_sort17 : nat}
{m_sort17 : nat} (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort16 m_sort17) {struct s} :
subst_sort16 tau_sort17 (subst_sort16 sigma_sort17 s) =
subst_sort16 theta_sort17 s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  | clam24 _ s0 =>
      congr_clam24
        (compSubstSubst_sort23 (up_sort17_sort17 sigma_sort17)
           (up_sort17_sort17 tau_sort17) (up_sort17_sort17 theta_sort17)
           (up_subst_subst_sort17_sort17 _ _ _ Eq_sort17) s0)
  end
with compSubstSubst_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort17 m_sort17) {struct s} :
subst_sort17 tau_sort17 (subst_sort17 sigma_sort17 s) =
subst_sort17 theta_sort17 s :=
  match s with
  | var_sort17 _ s0 => Eq_sort17 s0
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstSubst_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort18 m_sort17) {struct s} :
subst_sort18 tau_sort17 (subst_sort18 sigma_sort17 s) =
subst_sort18 theta_sort17 s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstSubst_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort19 m_sort17) {struct s} :
subst_sort19 tau_sort17 (subst_sort19 sigma_sort17 s) =
subst_sort19 theta_sort17 s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstSubst_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort20 m_sort17) {struct s} :
subst_sort20 tau_sort17 (subst_sort20 sigma_sort17 s) =
subst_sort20 theta_sort17 s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstSubst_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort21 m_sort17) {struct s} :
subst_sort21 tau_sort17 (subst_sort21 sigma_sort17 s) =
subst_sort21 theta_sort17 s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstSubst_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort22 m_sort17) {struct s} :
subst_sort22 tau_sort17 (subst_sort22 sigma_sort17 s) =
subst_sort22 theta_sort17 s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  end
with compSubstSubst_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
(sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
(tau_sort17 : fin k_sort17 -> sort17 l_sort17)
(theta_sort17 : fin m_sort17 -> sort17 l_sort17)
(Eq_sort17 : forall x,
             funcomp (subst_sort17 tau_sort17) sigma_sort17 x =
             theta_sort17 x) (s : sort23 m_sort17) {struct s} :
subst_sort23 tau_sort17 (subst_sort23 sigma_sort17 s) =
subst_sort23 theta_sort17 s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23
        (compSubstSubst_sort16 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s0)
        (compSubstSubst_sort17 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s1)
        (compSubstSubst_sort18 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s2)
        (compSubstSubst_sort19 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s3)
        (compSubstSubst_sort20 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s4)
        (compSubstSubst_sort21 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s5)
        (compSubstSubst_sort22 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s6)
        (compSubstSubst_sort23 sigma_sort17 tau_sort17 theta_sort17 Eq_sort17
           s7)
  end.

Lemma rinstInst_up_sort17_sort17 {m : nat} {n_sort17 : nat}
  (xi : fin m -> fin n_sort17) (sigma : fin m -> sort17 n_sort17)
  (Eq : forall x, funcomp (var_sort17 n_sort17) xi x = sigma x) :
  forall x,
  funcomp (var_sort17 (S n_sort17)) (upRen_sort17_sort17 xi) x =
  up_sort17_sort17 sigma x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort17 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma rinstInst_up_list_sort17_sort17 {p : nat} {m : nat} {n_sort17 : nat}
  (xi : fin m -> fin n_sort17) (sigma : fin m -> sort17 n_sort17)
  (Eq : forall x, funcomp (var_sort17 n_sort17) xi x = sigma x) :
  forall x,
  funcomp (var_sort17 (plus p n_sort17)) (upRen_list_sort17_sort17 p xi) x =
  up_list_sort17_sort17 p sigma x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ (var_sort17 (plus p n_sort17)) n)
                (scons_p_congr (fun z => eq_refl)
                   (fun n => ap (ren_sort17 (shift_p p)) (Eq n)))).

Qed.

Fixpoint rinst_inst_sort16 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort16 m_sort17) {struct s} :
ren_sort16 xi_sort17 s = subst_sort16 sigma_sort17 s :=
  match s with
  | cmix16 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix16 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  | clam24 _ s0 =>
      congr_clam24
        (rinst_inst_sort23 (upRen_sort17_sort17 xi_sort17)
           (up_sort17_sort17 sigma_sort17)
           (rinstInst_up_sort17_sort17 _ _ Eq_sort17) s0)
  end
with rinst_inst_sort17 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort17 m_sort17) {struct s} :
ren_sort17 xi_sort17 s = subst_sort17 sigma_sort17 s :=
  match s with
  | var_sort17 _ s0 => Eq_sort17 s0
  | cmix17 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix17 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  end
with rinst_inst_sort18 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort18 m_sort17) {struct s} :
ren_sort18 xi_sort17 s = subst_sort18 sigma_sort17 s :=
  match s with
  | cmix18 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix18 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  end
with rinst_inst_sort19 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort19 m_sort17) {struct s} :
ren_sort19 xi_sort17 s = subst_sort19 sigma_sort17 s :=
  match s with
  | cmix19 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix19 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  end
with rinst_inst_sort20 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort20 m_sort17) {struct s} :
ren_sort20 xi_sort17 s = subst_sort20 sigma_sort17 s :=
  match s with
  | cmix20 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix20 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  end
with rinst_inst_sort21 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort21 m_sort17) {struct s} :
ren_sort21 xi_sort17 s = subst_sort21 sigma_sort17 s :=
  match s with
  | cmix21 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix21 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  end
with rinst_inst_sort22 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort22 m_sort17) {struct s} :
ren_sort22 xi_sort17 s = subst_sort22 sigma_sort17 s :=
  match s with
  | cmix22 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix22 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  end
with rinst_inst_sort23 {m_sort17 : nat} {n_sort17 : nat}
(xi_sort17 : fin m_sort17 -> fin n_sort17)
(sigma_sort17 : fin m_sort17 -> sort17 n_sort17)
(Eq_sort17 : forall x,
             funcomp (var_sort17 n_sort17) xi_sort17 x = sigma_sort17 x)
(s : sort23 m_sort17) {struct s} :
ren_sort23 xi_sort17 s = subst_sort23 sigma_sort17 s :=
  match s with
  | cmix23 _ s0 s1 s2 s3 s4 s5 s6 s7 =>
      congr_cmix23 (rinst_inst_sort16 xi_sort17 sigma_sort17 Eq_sort17 s0)
        (rinst_inst_sort17 xi_sort17 sigma_sort17 Eq_sort17 s1)
        (rinst_inst_sort18 xi_sort17 sigma_sort17 Eq_sort17 s2)
        (rinst_inst_sort19 xi_sort17 sigma_sort17 Eq_sort17 s3)
        (rinst_inst_sort20 xi_sort17 sigma_sort17 Eq_sort17 s4)
        (rinst_inst_sort21 xi_sort17 sigma_sort17 Eq_sort17 s5)
        (rinst_inst_sort22 xi_sort17 sigma_sort17 Eq_sort17 s6)
        (rinst_inst_sort23 xi_sort17 sigma_sort17 Eq_sort17 s7)
  end.

Lemma renRen_sort16 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort16 m_sort17) :
  ren_sort16 zeta_sort17 (ren_sort16 xi_sort17 s) =
  ren_sort16 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort16 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort17 m_sort17) :
  ren_sort17 zeta_sort17 (ren_sort17 xi_sort17 s) =
  ren_sort17 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort17 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort18 m_sort17) :
  ren_sort18 zeta_sort17 (ren_sort18 xi_sort17 s) =
  ren_sort18 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort18 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort19 m_sort17) :
  ren_sort19 zeta_sort17 (ren_sort19 xi_sort17 s) =
  ren_sort19 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort19 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort20 m_sort17) :
  ren_sort20 zeta_sort17 (ren_sort20 xi_sort17 s) =
  ren_sort20 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort20 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort21 m_sort17) :
  ren_sort21 zeta_sort17 (ren_sort21 xi_sort17 s) =
  ren_sort21 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort21 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort22 m_sort17) :
  ren_sort22 zeta_sort17 (ren_sort22 xi_sort17 s) =
  ren_sort22 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort22 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort23 m_sort17) :
  ren_sort23 zeta_sort17 (ren_sort23 xi_sort17 s) =
  ren_sort23 (funcomp zeta_sort17 xi_sort17) s.

Proof.
exact (compRenRen_sort23 xi_sort17 zeta_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma compRen_sort16 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort16 m_sort17) :
  ren_sort16 zeta_sort17 (subst_sort16 sigma_sort17 s) =
  subst_sort16 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort16 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort17 m_sort17) :
  ren_sort17 zeta_sort17 (subst_sort17 sigma_sort17 s) =
  subst_sort17 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort17 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort18 m_sort17) :
  ren_sort18 zeta_sort17 (subst_sort18 sigma_sort17 s) =
  subst_sort18 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort18 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort19 m_sort17) :
  ren_sort19 zeta_sort17 (subst_sort19 sigma_sort17 s) =
  subst_sort19 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort19 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort20 m_sort17) :
  ren_sort20 zeta_sort17 (subst_sort20 sigma_sort17 s) =
  subst_sort20 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort20 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort21 m_sort17) :
  ren_sort21 zeta_sort17 (subst_sort21 sigma_sort17 s) =
  subst_sort21 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort21 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort22 m_sort17) :
  ren_sort22 zeta_sort17 (subst_sort22 sigma_sort17 s) =
  subst_sort22 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort22 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (zeta_sort17 : fin k_sort17 -> fin l_sort17) (s : sort23 m_sort17) :
  ren_sort23 zeta_sort17 (subst_sort23 sigma_sort17 s) =
  subst_sort23 (funcomp (ren_sort17 zeta_sort17) sigma_sort17) s.

Proof.
exact (compSubstRen_sort23 sigma_sort17 zeta_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma renComp_sort16 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort16 m_sort17) :
  subst_sort16 tau_sort17 (ren_sort16 xi_sort17 s) =
  subst_sort16 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort16 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort17 m_sort17) :
  subst_sort17 tau_sort17 (ren_sort17 xi_sort17 s) =
  subst_sort17 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort17 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort18 m_sort17) :
  subst_sort18 tau_sort17 (ren_sort18 xi_sort17 s) =
  subst_sort18 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort18 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort19 m_sort17) :
  subst_sort19 tau_sort17 (ren_sort19 xi_sort17 s) =
  subst_sort19 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort19 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort20 m_sort17) :
  subst_sort20 tau_sort17 (ren_sort20 xi_sort17 s) =
  subst_sort20 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort20 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort21 m_sort17) :
  subst_sort21 tau_sort17 (ren_sort21 xi_sort17 s) =
  subst_sort21 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort21 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort22 m_sort17) :
  subst_sort22 tau_sort17 (ren_sort22 xi_sort17 s) =
  subst_sort22 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort22 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (xi_sort17 : fin m_sort17 -> fin k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort23 m_sort17) :
  subst_sort23 tau_sort17 (ren_sort23 xi_sort17 s) =
  subst_sort23 (funcomp tau_sort17 xi_sort17) s.

Proof.
exact (compRenSubst_sort23 xi_sort17 tau_sort17 _ (fun n => eq_refl) s).

Qed.

Lemma compComp_sort16 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort16 m_sort17) :
  subst_sort16 tau_sort17 (subst_sort16 sigma_sort17 s) =
  subst_sort16 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort16 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort17 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort17 m_sort17) :
  subst_sort17 tau_sort17 (subst_sort17 sigma_sort17 s) =
  subst_sort17 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort17 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort18 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort18 m_sort17) :
  subst_sort18 tau_sort17 (subst_sort18 sigma_sort17 s) =
  subst_sort18 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort18 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort19 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort19 m_sort17) :
  subst_sort19 tau_sort17 (subst_sort19 sigma_sort17 s) =
  subst_sort19 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort19 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort20 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort20 m_sort17) :
  subst_sort20 tau_sort17 (subst_sort20 sigma_sort17 s) =
  subst_sort20 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort20 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort21 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort21 m_sort17) :
  subst_sort21 tau_sort17 (subst_sort21 sigma_sort17 s) =
  subst_sort21 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort21 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort22 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort22 m_sort17) :
  subst_sort22 tau_sort17 (subst_sort22 sigma_sort17 s) =
  subst_sort22 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort22 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort23 {k_sort17 : nat} {l_sort17 : nat} {m_sort17 : nat}
  (sigma_sort17 : fin m_sort17 -> sort17 k_sort17)
  (tau_sort17 : fin k_sort17 -> sort17 l_sort17) (s : sort23 m_sort17) :
  subst_sort23 tau_sort17 (subst_sort23 sigma_sort17 s) =
  subst_sort23 (funcomp (subst_sort17 tau_sort17) sigma_sort17) s.

Proof.
exact (compSubstSubst_sort23 sigma_sort17 tau_sort17 _
                (fun n => eq_refl) s).

Qed.
