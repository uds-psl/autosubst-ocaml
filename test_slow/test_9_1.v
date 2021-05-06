Require Import core fintype.

Inductive sort0 (n_sort2 : nat) : Type :=
    cmix0 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort0 n_sort2
with sort1 (n_sort2 : nat) : Type :=
    cmix1 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort1 n_sort2
with sort2 (n_sort2 : nat) : Type :=
  | var_sort2 : fin n_sort2 -> sort2 n_sort2
  | cmix2 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort2 n_sort2
with sort3 (n_sort2 : nat) : Type :=
    cmix3 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort3 n_sort2
with sort4 (n_sort2 : nat) : Type :=
    cmix4 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort4 n_sort2
with sort5 (n_sort2 : nat) : Type :=
  | cmix5 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort5 n_sort2
  | clam9 : sort7 (S n_sort2) -> sort5 n_sort2
with sort6 (n_sort2 : nat) : Type :=
    cmix6 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort6 n_sort2
with sort7 (n_sort2 : nat) : Type :=
    cmix7 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort7 n_sort2
with sort8 (n_sort2 : nat) : Type :=
    cmix8 :
      sort0 n_sort2 ->
      sort1 n_sort2 ->
      sort2 n_sort2 ->
      sort3 n_sort2 ->
      sort4 n_sort2 ->
      sort5 n_sort2 ->
      sort6 n_sort2 -> sort7 n_sort2 -> sort8 n_sort2 -> sort8 n_sort2.

Lemma congr_cmix0 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix0 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix0 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix0 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix0 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix0 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix0 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix0 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix0 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix0 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix0 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix0 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_cmix1 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix1 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix1 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix1 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix1 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix1 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix1 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix1 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix1 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix1 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix1 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix1 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_cmix2 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix2 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix2 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix2 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix2 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix2 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix2 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix2 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix2 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix2 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix2 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix2 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_cmix3 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix3 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix3 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix3 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix3 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix3 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix3 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix3 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix3 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix3 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix3 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix3 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_cmix4 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix4 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix4 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix4 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix4 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix4 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix4 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix4 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix4 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix4 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix4 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix4 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_cmix5 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix5 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix5 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix5 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix5 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix5 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix5 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix5 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix5 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix5 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix5 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix5 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_clam9 {m_sort2 : nat} {s0 : sort7 (S m_sort2)}
  {t0 : sort7 (S m_sort2)} (H0 : s0 = t0) :
  clam9 m_sort2 s0 = clam9 m_sort2 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam9 m_sort2 x) H0)).

Qed.

Lemma congr_cmix6 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix6 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix6 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix6 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix6 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix6 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix6 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix6 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix6 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix6 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix6 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix6 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_cmix7 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix7 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix7 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix7 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix7 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix7 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix7 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix7 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix7 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix7 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix7 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix7 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma congr_cmix8 {m_sort2 : nat} {s0 : sort0 m_sort2} {s1 : sort1 m_sort2}
  {s2 : sort2 m_sort2} {s3 : sort3 m_sort2} {s4 : sort4 m_sort2}
  {s5 : sort5 m_sort2} {s6 : sort6 m_sort2} {s7 : sort7 m_sort2}
  {s8 : sort8 m_sort2} {t0 : sort0 m_sort2} {t1 : sort1 m_sort2}
  {t2 : sort2 m_sort2} {t3 : sort3 m_sort2} {t4 : sort4 m_sort2}
  {t5 : sort5 m_sort2} {t6 : sort6 m_sort2} {t7 : sort7 m_sort2}
  {t8 : sort8 m_sort2} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) (H6 : s6 = t6) (H7 : s7 = t7)
  (H8 : s8 = t8) :
  cmix8 m_sort2 s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  cmix8 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 t8.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans
                               (eq_trans
                                  (eq_trans
                                     (eq_trans eq_refl
                                        (ap
                                           (fun x =>
                                            cmix8 m_sort2 x s1 s2 s3 s4 s5 s6
                                              s7 s8) H0))
                                     (ap
                                        (fun x =>
                                         cmix8 m_sort2 t0 x s2 s3 s4 s5 s6 s7
                                           s8) H1))
                                  (ap
                                     (fun x =>
                                      cmix8 m_sort2 t0 t1 x s3 s4 s5 s6 s7 s8)
                                     H2))
                               (ap
                                  (fun x =>
                                   cmix8 m_sort2 t0 t1 t2 x s4 s5 s6 s7 s8)
                                  H3))
                            (ap
                               (fun x =>
                                cmix8 m_sort2 t0 t1 t2 t3 x s5 s6 s7 s8) H4))
                         (ap
                            (fun x => cmix8 m_sort2 t0 t1 t2 t3 t4 x s6 s7 s8)
                            H5))
                      (ap (fun x => cmix8 m_sort2 t0 t1 t2 t3 t4 t5 x s7 s8)
                         H6))
                   (ap (fun x => cmix8 m_sort2 t0 t1 t2 t3 t4 t5 t6 x s8) H7))
                (ap (fun x => cmix8 m_sort2 t0 t1 t2 t3 t4 t5 t6 t7 x) H8)).

Qed.

Lemma upRen_sort2_sort2 {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).

Proof.
exact (up_ren xi).

Defined.

Lemma upRen_list_sort2_sort2 (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n).

Proof.
exact (upRen_p p xi).

Defined.

Fixpoint ren_sort0 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort0 m_sort2) {struct s} :
sort0 n_sort2 :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix0 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end
with ren_sort1 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort1 m_sort2) {struct s} :
sort1 n_sort2 :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix1 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end
with ren_sort2 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort2 m_sort2) {struct s} :
sort2 n_sort2 :=
  match s with
  | var_sort2 _ s0 => var_sort2 n_sort2 (xi_sort2 s0)
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix2 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end
with ren_sort3 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort3 m_sort2) {struct s} :
sort3 n_sort2 :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix3 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end
with ren_sort4 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort4 m_sort2) {struct s} :
sort4 n_sort2 :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix4 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end
with ren_sort5 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort5 m_sort2) {struct s} :
sort5 n_sort2 :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix5 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  | clam9 _ s0 => clam9 n_sort2 (ren_sort7 (upRen_sort2_sort2 xi_sort2) s0)
  end
with ren_sort6 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort6 m_sort2) {struct s} :
sort6 n_sort2 :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix6 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end
with ren_sort7 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort7 m_sort2) {struct s} :
sort7 n_sort2 :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix7 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end
with ren_sort8 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2) (s : sort8 m_sort2) {struct s} :
sort8 n_sort2 :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix8 n_sort2 (ren_sort0 xi_sort2 s0) (ren_sort1 xi_sort2 s1)
        (ren_sort2 xi_sort2 s2) (ren_sort3 xi_sort2 s3)
        (ren_sort4 xi_sort2 s4) (ren_sort5 xi_sort2 s5)
        (ren_sort6 xi_sort2 s6) (ren_sort7 xi_sort2 s7)
        (ren_sort8 xi_sort2 s8)
  end.

Lemma up_sort2_sort2 {m : nat} {n_sort2 : nat}
  (sigma : fin m -> sort2 n_sort2) : fin (S m) -> sort2 (S n_sort2).

Proof.
exact (scons (var_sort2 (S n_sort2) var_zero)
                (funcomp (ren_sort2 shift) sigma)).

Defined.

Lemma up_list_sort2_sort2 (p : nat) {m : nat} {n_sort2 : nat}
  (sigma : fin m -> sort2 n_sort2) : fin (plus p m) -> sort2 (plus p n_sort2).

Proof.
exact (scons_p p (funcomp (var_sort2 (plus p n_sort2)) (zero_p p))
                (funcomp (ren_sort2 (shift_p p)) sigma)).

Defined.

Fixpoint subst_sort0 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort0 m_sort2) {struct s} :
sort0 n_sort2 :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix0 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end
with subst_sort1 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort1 m_sort2) {struct s} :
sort1 n_sort2 :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix1 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end
with subst_sort2 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort2 m_sort2) {struct s} :
sort2 n_sort2 :=
  match s with
  | var_sort2 _ s0 => sigma_sort2 s0
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix2 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end
with subst_sort3 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort3 m_sort2) {struct s} :
sort3 n_sort2 :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix3 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end
with subst_sort4 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort4 m_sort2) {struct s} :
sort4 n_sort2 :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix4 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end
with subst_sort5 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort5 m_sort2) {struct s} :
sort5 n_sort2 :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix5 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  | clam9 _ s0 => clam9 n_sort2 (subst_sort7 (up_sort2_sort2 sigma_sort2) s0)
  end
with subst_sort6 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort6 m_sort2) {struct s} :
sort6 n_sort2 :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix6 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end
with subst_sort7 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort7 m_sort2) {struct s} :
sort7 n_sort2 :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix7 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end
with subst_sort8 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2) (s : sort8 m_sort2) {struct s} :
sort8 n_sort2 :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      cmix8 n_sort2 (subst_sort0 sigma_sort2 s0) (subst_sort1 sigma_sort2 s1)
        (subst_sort2 sigma_sort2 s2) (subst_sort3 sigma_sort2 s3)
        (subst_sort4 sigma_sort2 s4) (subst_sort5 sigma_sort2 s5)
        (subst_sort6 sigma_sort2 s6) (subst_sort7 sigma_sort2 s7)
        (subst_sort8 sigma_sort2 s8)
  end.

Lemma upId_sort2_sort2 {m_sort2 : nat} (sigma : fin m_sort2 -> sort2 m_sort2)
  (Eq : forall x, sigma x = var_sort2 m_sort2 x) :
  forall x, up_sort2_sort2 sigma x = var_sort2 (S m_sort2) x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort2 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upId_list_sort2_sort2 {p : nat} {m_sort2 : nat}
  (sigma : fin m_sort2 -> sort2 m_sort2)
  (Eq : forall x, sigma x = var_sort2 m_sort2 x) :
  forall x, up_list_sort2_sort2 p sigma x = var_sort2 (plus p m_sort2) x.

Proof.
exact (fun n =>
              scons_p_eta (var_sort2 (plus p m_sort2))
                (fun n => ap (ren_sort2 (shift_p p)) (Eq n))
                (fun n => eq_refl)).

Qed.

Fixpoint idSubst_sort0 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort0 m_sort2) {struct s} : subst_sort0 sigma_sort2 s = s :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end
with idSubst_sort1 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort1 m_sort2) {struct s} : subst_sort1 sigma_sort2 s = s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end
with idSubst_sort2 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort2 m_sort2) {struct s} : subst_sort2 sigma_sort2 s = s :=
  match s with
  | var_sort2 _ s0 => Eq_sort2 s0
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end
with idSubst_sort3 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort3 m_sort2) {struct s} : subst_sort3 sigma_sort2 s = s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end
with idSubst_sort4 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort4 m_sort2) {struct s} : subst_sort4 sigma_sort2 s = s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end
with idSubst_sort5 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort5 m_sort2) {struct s} : subst_sort5 sigma_sort2 s = s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (idSubst_sort7 (up_sort2_sort2 sigma_sort2)
           (upId_sort2_sort2 _ Eq_sort2) s0)
  end
with idSubst_sort6 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort6 m_sort2) {struct s} : subst_sort6 sigma_sort2 s = s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end
with idSubst_sort7 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort7 m_sort2) {struct s} : subst_sort7 sigma_sort2 s = s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end
with idSubst_sort8 {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 m_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = var_sort2 m_sort2 x)
(s : sort8 m_sort2) {struct s} : subst_sort8 sigma_sort2 s = s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8 (idSubst_sort0 sigma_sort2 Eq_sort2 s0)
        (idSubst_sort1 sigma_sort2 Eq_sort2 s1)
        (idSubst_sort2 sigma_sort2 Eq_sort2 s2)
        (idSubst_sort3 sigma_sort2 Eq_sort2 s3)
        (idSubst_sort4 sigma_sort2 Eq_sort2 s4)
        (idSubst_sort5 sigma_sort2 Eq_sort2 s5)
        (idSubst_sort6 sigma_sort2 Eq_sort2 s6)
        (idSubst_sort7 sigma_sort2 Eq_sort2 s7)
        (idSubst_sort8 sigma_sort2 Eq_sort2 s8)
  end.

Lemma upExtRen_sort2_sort2 {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_sort2_sort2 xi x = upRen_sort2_sort2 zeta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap shift (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExtRen_list_sort2_sort2 {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_sort2_sort2 p xi x = upRen_list_sort2_sort2 p zeta x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (shift_p p) (Eq n))).

Qed.

Fixpoint extRen_sort0 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort0 m_sort2) {struct
 s} : ren_sort0 xi_sort2 s = ren_sort0 zeta_sort2 s :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end
with extRen_sort1 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort1 m_sort2) {struct
 s} : ren_sort1 xi_sort2 s = ren_sort1 zeta_sort2 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end
with extRen_sort2 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort2 m_sort2) {struct
 s} : ren_sort2 xi_sort2 s = ren_sort2 zeta_sort2 s :=
  match s with
  | var_sort2 _ s0 => ap (var_sort2 n_sort2) (Eq_sort2 s0)
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end
with extRen_sort3 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort3 m_sort2) {struct
 s} : ren_sort3 xi_sort2 s = ren_sort3 zeta_sort2 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end
with extRen_sort4 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort4 m_sort2) {struct
 s} : ren_sort4 xi_sort2 s = ren_sort4 zeta_sort2 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end
with extRen_sort5 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort5 m_sort2) {struct
 s} : ren_sort5 xi_sort2 s = ren_sort5 zeta_sort2 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (extRen_sort7 (upRen_sort2_sort2 xi_sort2)
           (upRen_sort2_sort2 zeta_sort2) (upExtRen_sort2_sort2 _ _ Eq_sort2)
           s0)
  end
with extRen_sort6 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort6 m_sort2) {struct
 s} : ren_sort6 xi_sort2 s = ren_sort6 zeta_sort2 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end
with extRen_sort7 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort7 m_sort2) {struct
 s} : ren_sort7 xi_sort2 s = ren_sort7 zeta_sort2 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end
with extRen_sort8 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(zeta_sort2 : fin m_sort2 -> fin n_sort2)
(Eq_sort2 : forall x, xi_sort2 x = zeta_sort2 x) (s : sort8 m_sort2) {struct
 s} : ren_sort8 xi_sort2 s = ren_sort8 zeta_sort2 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8 (extRen_sort0 xi_sort2 zeta_sort2 Eq_sort2 s0)
        (extRen_sort1 xi_sort2 zeta_sort2 Eq_sort2 s1)
        (extRen_sort2 xi_sort2 zeta_sort2 Eq_sort2 s2)
        (extRen_sort3 xi_sort2 zeta_sort2 Eq_sort2 s3)
        (extRen_sort4 xi_sort2 zeta_sort2 Eq_sort2 s4)
        (extRen_sort5 xi_sort2 zeta_sort2 Eq_sort2 s5)
        (extRen_sort6 xi_sort2 zeta_sort2 Eq_sort2 s6)
        (extRen_sort7 xi_sort2 zeta_sort2 Eq_sort2 s7)
        (extRen_sort8 xi_sort2 zeta_sort2 Eq_sort2 s8)
  end.

Lemma upExt_sort2_sort2 {m : nat} {n_sort2 : nat}
  (sigma : fin m -> sort2 n_sort2) (tau : fin m -> sort2 n_sort2)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_sort2_sort2 sigma x = up_sort2_sort2 tau x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort2 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma upExt_list_sort2_sort2 {p : nat} {m : nat} {n_sort2 : nat}
  (sigma : fin m -> sort2 n_sort2) (tau : fin m -> sort2 n_sort2)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_sort2_sort2 p sigma x = up_list_sort2_sort2 p tau x.

Proof.
exact (fun n =>
              scons_p_congr (fun n => eq_refl)
                (fun n => ap (ren_sort2 (shift_p p)) (Eq n))).

Qed.

Fixpoint ext_sort0 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort0 m_sort2)
{struct s} : subst_sort0 sigma_sort2 s = subst_sort0 tau_sort2 s :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end
with ext_sort1 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort1 m_sort2)
{struct s} : subst_sort1 sigma_sort2 s = subst_sort1 tau_sort2 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end
with ext_sort2 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort2 m_sort2)
{struct s} : subst_sort2 sigma_sort2 s = subst_sort2 tau_sort2 s :=
  match s with
  | var_sort2 _ s0 => Eq_sort2 s0
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end
with ext_sort3 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort3 m_sort2)
{struct s} : subst_sort3 sigma_sort2 s = subst_sort3 tau_sort2 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end
with ext_sort4 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort4 m_sort2)
{struct s} : subst_sort4 sigma_sort2 s = subst_sort4 tau_sort2 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end
with ext_sort5 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort5 m_sort2)
{struct s} : subst_sort5 sigma_sort2 s = subst_sort5 tau_sort2 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (ext_sort7 (up_sort2_sort2 sigma_sort2) (up_sort2_sort2 tau_sort2)
           (upExt_sort2_sort2 _ _ Eq_sort2) s0)
  end
with ext_sort6 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort6 m_sort2)
{struct s} : subst_sort6 sigma_sort2 s = subst_sort6 tau_sort2 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end
with ext_sort7 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort7 m_sort2)
{struct s} : subst_sort7 sigma_sort2 s = subst_sort7 tau_sort2 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end
with ext_sort8 {m_sort2 : nat} {n_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(tau_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, sigma_sort2 x = tau_sort2 x) (s : sort8 m_sort2)
{struct s} : subst_sort8 sigma_sort2 s = subst_sort8 tau_sort2 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8 (ext_sort0 sigma_sort2 tau_sort2 Eq_sort2 s0)
        (ext_sort1 sigma_sort2 tau_sort2 Eq_sort2 s1)
        (ext_sort2 sigma_sort2 tau_sort2 Eq_sort2 s2)
        (ext_sort3 sigma_sort2 tau_sort2 Eq_sort2 s3)
        (ext_sort4 sigma_sort2 tau_sort2 Eq_sort2 s4)
        (ext_sort5 sigma_sort2 tau_sort2 Eq_sort2 s5)
        (ext_sort6 sigma_sort2 tau_sort2 Eq_sort2 s6)
        (ext_sort7 sigma_sort2 tau_sort2 Eq_sort2 s7)
        (ext_sort8 sigma_sort2 tau_sort2 Eq_sort2 s8)
  end.

Lemma up_ren_ren_sort2_sort2 {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_sort2_sort2 zeta) (upRen_sort2_sort2 xi) x =
  upRen_sort2_sort2 rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Lemma up_ren_ren_list_sort2_sort2 {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_sort2_sort2 p zeta) (upRen_list_sort2_sort2 p xi) x =
  upRen_list_sort2_sort2 p rho x.

Proof.
exact (up_ren_ren_p Eq).

Qed.

Fixpoint compRenRen_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort0 m_sort2) {struct s} :
ren_sort0 zeta_sort2 (ren_sort0 xi_sort2 s) = ren_sort0 rho_sort2 s :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end
with compRenRen_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort1 m_sort2) {struct s} :
ren_sort1 zeta_sort2 (ren_sort1 xi_sort2 s) = ren_sort1 rho_sort2 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end
with compRenRen_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort2 m_sort2) {struct s} :
ren_sort2 zeta_sort2 (ren_sort2 xi_sort2 s) = ren_sort2 rho_sort2 s :=
  match s with
  | var_sort2 _ s0 => ap (var_sort2 l_sort2) (Eq_sort2 s0)
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end
with compRenRen_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort3 m_sort2) {struct s} :
ren_sort3 zeta_sort2 (ren_sort3 xi_sort2 s) = ren_sort3 rho_sort2 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end
with compRenRen_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort4 m_sort2) {struct s} :
ren_sort4 zeta_sort2 (ren_sort4 xi_sort2 s) = ren_sort4 rho_sort2 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end
with compRenRen_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort5 m_sort2) {struct s} :
ren_sort5 zeta_sort2 (ren_sort5 xi_sort2 s) = ren_sort5 rho_sort2 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (compRenRen_sort7 (upRen_sort2_sort2 xi_sort2)
           (upRen_sort2_sort2 zeta_sort2) (upRen_sort2_sort2 rho_sort2)
           (up_ren_ren _ _ _ Eq_sort2) s0)
  end
with compRenRen_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort6 m_sort2) {struct s} :
ren_sort6 zeta_sort2 (ren_sort6 xi_sort2 s) = ren_sort6 rho_sort2 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end
with compRenRen_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort7 m_sort2) {struct s} :
ren_sort7 zeta_sort2 (ren_sort7 xi_sort2 s) = ren_sort7 rho_sort2 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end
with compRenRen_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(rho_sort2 : fin m_sort2 -> fin l_sort2)
(Eq_sort2 : forall x, funcomp zeta_sort2 xi_sort2 x = rho_sort2 x)
(s : sort8 m_sort2) {struct s} :
ren_sort8 zeta_sort2 (ren_sort8 xi_sort2 s) = ren_sort8 rho_sort2 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8
        (compRenRen_sort0 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s0)
        (compRenRen_sort1 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s1)
        (compRenRen_sort2 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s2)
        (compRenRen_sort3 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s3)
        (compRenRen_sort4 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s4)
        (compRenRen_sort5 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s5)
        (compRenRen_sort6 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s6)
        (compRenRen_sort7 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s7)
        (compRenRen_sort8 xi_sort2 zeta_sort2 rho_sort2 Eq_sort2 s8)
  end.

Lemma up_ren_subst_sort2_sort2 {k : nat} {l : nat} {m_sort2 : nat}
  (xi : fin k -> fin l) (tau : fin l -> sort2 m_sort2)
  (theta : fin k -> sort2 m_sort2)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_sort2_sort2 tau) (upRen_sort2_sort2 xi) x =
  up_sort2_sort2 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort2 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma up_ren_subst_list_sort2_sort2 {p : nat} {k : nat} {l : nat}
  {m_sort2 : nat} (xi : fin k -> fin l) (tau : fin l -> sort2 m_sort2)
  (theta : fin k -> sort2 m_sort2)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_sort2_sort2 p tau) (upRen_list_sort2_sort2 p xi) x =
  up_list_sort2_sort2 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr (fun z => scons_p_head' _ _ z)
                   (fun z =>
                    eq_trans (scons_p_tail' _ _ (xi z))
                      (ap (ren_sort2 (shift_p p)) (Eq z))))).

Qed.

Fixpoint compRenSubst_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort0 m_sort2) {struct s} :
subst_sort0 tau_sort2 (ren_sort0 xi_sort2 s) = subst_sort0 theta_sort2 s :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compRenSubst_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort1 m_sort2) {struct s} :
subst_sort1 tau_sort2 (ren_sort1 xi_sort2 s) = subst_sort1 theta_sort2 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compRenSubst_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort2 m_sort2) {struct s} :
subst_sort2 tau_sort2 (ren_sort2 xi_sort2 s) = subst_sort2 theta_sort2 s :=
  match s with
  | var_sort2 _ s0 => Eq_sort2 s0
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compRenSubst_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort3 m_sort2) {struct s} :
subst_sort3 tau_sort2 (ren_sort3 xi_sort2 s) = subst_sort3 theta_sort2 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compRenSubst_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort4 m_sort2) {struct s} :
subst_sort4 tau_sort2 (ren_sort4 xi_sort2 s) = subst_sort4 theta_sort2 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compRenSubst_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort5 m_sort2) {struct s} :
subst_sort5 tau_sort2 (ren_sort5 xi_sort2 s) = subst_sort5 theta_sort2 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (compRenSubst_sort7 (upRen_sort2_sort2 xi_sort2)
           (up_sort2_sort2 tau_sort2) (up_sort2_sort2 theta_sort2)
           (up_ren_subst_sort2_sort2 _ _ _ Eq_sort2) s0)
  end
with compRenSubst_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort6 m_sort2) {struct s} :
subst_sort6 tau_sort2 (ren_sort6 xi_sort2 s) = subst_sort6 theta_sort2 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compRenSubst_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort7 m_sort2) {struct s} :
subst_sort7 tau_sort2 (ren_sort7 xi_sort2 s) = subst_sort7 theta_sort2 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compRenSubst_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x, funcomp tau_sort2 xi_sort2 x = theta_sort2 x)
(s : sort8 m_sort2) {struct s} :
subst_sort8 tau_sort2 (ren_sort8 xi_sort2 s) = subst_sort8 theta_sort2 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8
        (compRenSubst_sort0 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compRenSubst_sort1 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compRenSubst_sort2 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compRenSubst_sort3 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compRenSubst_sort4 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compRenSubst_sort5 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compRenSubst_sort6 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compRenSubst_sort7 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compRenSubst_sort8 xi_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end.

Lemma up_subst_ren_sort2_sort2 {k : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma : fin k -> sort2 l_sort2) (zeta_sort2 : fin l_sort2 -> fin m_sort2)
  (theta : fin k -> sort2 m_sort2)
  (Eq : forall x, funcomp (ren_sort2 zeta_sort2) sigma x = theta x) :
  forall x,
  funcomp (ren_sort2 (upRen_sort2_sort2 zeta_sort2)) (up_sort2_sort2 sigma) x =
  up_sort2_sort2 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenRen_sort2 shift (upRen_sort2_sort2 zeta_sort2)
                       (funcomp shift zeta_sort2) (fun x => eq_refl)
                       (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compRenRen_sort2 zeta_sort2 shift
                             (funcomp shift zeta_sort2) (fun x => eq_refl)
                             (sigma fin_n)))
                       (ap (ren_sort2 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_ren_list_sort2_sort2 {p : nat} {k : nat} {l_sort2 : nat}
  {m_sort2 : nat} (sigma : fin k -> sort2 l_sort2)
  (zeta_sort2 : fin l_sort2 -> fin m_sort2) (theta : fin k -> sort2 m_sort2)
  (Eq : forall x, funcomp (ren_sort2 zeta_sort2) sigma x = theta x) :
  forall x,
  funcomp (ren_sort2 (upRen_list_sort2_sort2 p zeta_sort2))
    (up_list_sort2_sort2 p sigma) x = up_list_sort2_sort2 p theta x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ _ n)
                (scons_p_congr
                   (fun x =>
                    ap (var_sort2 (plus p m_sort2)) (scons_p_head' _ _ x))
                   (fun n =>
                    eq_trans
                      (compRenRen_sort2 (shift_p p)
                         (upRen_list_sort2_sort2 p zeta_sort2)
                         (funcomp (shift_p p) zeta_sort2)
                         (fun x => scons_p_tail' _ _ x) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compRenRen_sort2 zeta_sort2 (shift_p p)
                               (funcomp (shift_p p) zeta_sort2)
                               (fun x => eq_refl) (sigma n)))
                         (ap (ren_sort2 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstRen_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort0 m_sort2) {struct s} :
ren_sort0 zeta_sort2 (subst_sort0 sigma_sort2 s) = subst_sort0 theta_sort2 s
:=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstRen_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort1 m_sort2) {struct s} :
ren_sort1 zeta_sort2 (subst_sort1 sigma_sort2 s) = subst_sort1 theta_sort2 s
:=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstRen_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort2 m_sort2) {struct s} :
ren_sort2 zeta_sort2 (subst_sort2 sigma_sort2 s) = subst_sort2 theta_sort2 s
:=
  match s with
  | var_sort2 _ s0 => Eq_sort2 s0
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstRen_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort3 m_sort2) {struct s} :
ren_sort3 zeta_sort2 (subst_sort3 sigma_sort2 s) = subst_sort3 theta_sort2 s
:=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstRen_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort4 m_sort2) {struct s} :
ren_sort4 zeta_sort2 (subst_sort4 sigma_sort2 s) = subst_sort4 theta_sort2 s
:=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstRen_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort5 m_sort2) {struct s} :
ren_sort5 zeta_sort2 (subst_sort5 sigma_sort2 s) = subst_sort5 theta_sort2 s
:=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (compSubstRen_sort7 (up_sort2_sort2 sigma_sort2)
           (upRen_sort2_sort2 zeta_sort2) (up_sort2_sort2 theta_sort2)
           (up_subst_ren_sort2_sort2 _ _ _ Eq_sort2) s0)
  end
with compSubstRen_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort6 m_sort2) {struct s} :
ren_sort6 zeta_sort2 (subst_sort6 sigma_sort2 s) = subst_sort6 theta_sort2 s
:=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstRen_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort7 m_sort2) {struct s} :
ren_sort7 zeta_sort2 (subst_sort7 sigma_sort2 s) = subst_sort7 theta_sort2 s
:=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstRen_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(zeta_sort2 : fin k_sort2 -> fin l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (ren_sort2 zeta_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort8 m_sort2) {struct s} :
ren_sort8 zeta_sort2 (subst_sort8 sigma_sort2 s) = subst_sort8 theta_sort2 s
:=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8
        (compSubstRen_sort0 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstRen_sort1 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstRen_sort2 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstRen_sort3 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstRen_sort4 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstRen_sort5 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstRen_sort6 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstRen_sort7 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstRen_sort8 sigma_sort2 zeta_sort2 theta_sort2 Eq_sort2 s8)
  end.

Lemma up_subst_subst_sort2_sort2 {k : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma : fin k -> sort2 l_sort2) (tau_sort2 : fin l_sort2 -> sort2 m_sort2)
  (theta : fin k -> sort2 m_sort2)
  (Eq : forall x, funcomp (subst_sort2 tau_sort2) sigma x = theta x) :
  forall x,
  funcomp (subst_sort2 (up_sort2_sort2 tau_sort2)) (up_sort2_sort2 sigma) x =
  up_sort2_sort2 theta x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n =>
                  eq_trans
                    (compRenSubst_sort2 shift (up_sort2_sort2 tau_sort2)
                       (funcomp (up_sort2_sort2 tau_sort2) shift)
                       (fun x => eq_refl) (sigma fin_n))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_sort2 tau_sort2 shift
                             (funcomp (ren_sort2 shift) tau_sort2)
                             (fun x => eq_refl) (sigma fin_n)))
                       (ap (ren_sort2 shift) (Eq fin_n)))
              | None => eq_refl
              end).

Qed.

Lemma up_subst_subst_list_sort2_sort2 {p : nat} {k : nat} {l_sort2 : nat}
  {m_sort2 : nat} (sigma : fin k -> sort2 l_sort2)
  (tau_sort2 : fin l_sort2 -> sort2 m_sort2) (theta : fin k -> sort2 m_sort2)
  (Eq : forall x, funcomp (subst_sort2 tau_sort2) sigma x = theta x) :
  forall x,
  funcomp (subst_sort2 (up_list_sort2_sort2 p tau_sort2))
    (up_list_sort2_sort2 p sigma) x = up_list_sort2_sort2 p theta x.

Proof.
exact (fun n =>
              eq_trans
                (scons_p_comp'
                   (funcomp (var_sort2 (plus p l_sort2)) (zero_p p)) _ _ n)
                (scons_p_congr
                   (fun x =>
                    scons_p_head' _ (fun z => ren_sort2 (shift_p p) _) x)
                   (fun n =>
                    eq_trans
                      (compRenSubst_sort2 (shift_p p)
                         (up_list_sort2_sort2 p tau_sort2)
                         (funcomp (up_list_sort2_sort2 p tau_sort2)
                            (shift_p p)) (fun x => eq_refl) (sigma n))
                      (eq_trans
                         (eq_sym
                            (compSubstRen_sort2 tau_sort2 (shift_p p) _
                               (fun x => eq_sym (scons_p_tail' _ _ x))
                               (sigma n)))
                         (ap (ren_sort2 (shift_p p)) (Eq n)))))).

Qed.

Fixpoint compSubstSubst_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort0 m_sort2) {struct s} :
subst_sort0 tau_sort2 (subst_sort0 sigma_sort2 s) = subst_sort0 theta_sort2 s
:=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstSubst_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort1 m_sort2) {struct s} :
subst_sort1 tau_sort2 (subst_sort1 sigma_sort2 s) = subst_sort1 theta_sort2 s
:=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstSubst_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort2 m_sort2) {struct s} :
subst_sort2 tau_sort2 (subst_sort2 sigma_sort2 s) = subst_sort2 theta_sort2 s
:=
  match s with
  | var_sort2 _ s0 => Eq_sort2 s0
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstSubst_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort3 m_sort2) {struct s} :
subst_sort3 tau_sort2 (subst_sort3 sigma_sort2 s) = subst_sort3 theta_sort2 s
:=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstSubst_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort4 m_sort2) {struct s} :
subst_sort4 tau_sort2 (subst_sort4 sigma_sort2 s) = subst_sort4 theta_sort2 s
:=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstSubst_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort5 m_sort2) {struct s} :
subst_sort5 tau_sort2 (subst_sort5 sigma_sort2 s) = subst_sort5 theta_sort2 s
:=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (compSubstSubst_sort7 (up_sort2_sort2 sigma_sort2)
           (up_sort2_sort2 tau_sort2) (up_sort2_sort2 theta_sort2)
           (up_subst_subst_sort2_sort2 _ _ _ Eq_sort2) s0)
  end
with compSubstSubst_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort6 m_sort2) {struct s} :
subst_sort6 tau_sort2 (subst_sort6 sigma_sort2 s) = subst_sort6 theta_sort2 s
:=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstSubst_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort7 m_sort2) {struct s} :
subst_sort7 tau_sort2 (subst_sort7 sigma_sort2 s) = subst_sort7 theta_sort2 s
:=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end
with compSubstSubst_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
(sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
(tau_sort2 : fin k_sort2 -> sort2 l_sort2)
(theta_sort2 : fin m_sort2 -> sort2 l_sort2)
(Eq_sort2 : forall x,
            funcomp (subst_sort2 tau_sort2) sigma_sort2 x = theta_sort2 x)
(s : sort8 m_sort2) {struct s} :
subst_sort8 tau_sort2 (subst_sort8 sigma_sort2 s) = subst_sort8 theta_sort2 s
:=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8
        (compSubstSubst_sort0 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s0)
        (compSubstSubst_sort1 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s1)
        (compSubstSubst_sort2 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s2)
        (compSubstSubst_sort3 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s3)
        (compSubstSubst_sort4 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s4)
        (compSubstSubst_sort5 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s5)
        (compSubstSubst_sort6 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s6)
        (compSubstSubst_sort7 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s7)
        (compSubstSubst_sort8 sigma_sort2 tau_sort2 theta_sort2 Eq_sort2 s8)
  end.

Lemma rinstInst_up_sort2_sort2 {m : nat} {n_sort2 : nat}
  (xi : fin m -> fin n_sort2) (sigma : fin m -> sort2 n_sort2)
  (Eq : forall x, funcomp (var_sort2 n_sort2) xi x = sigma x) :
  forall x,
  funcomp (var_sort2 (S n_sort2)) (upRen_sort2_sort2 xi) x =
  up_sort2_sort2 sigma x.

Proof.
exact (fun n =>
              match n with
              | Some fin_n => ap (ren_sort2 shift) (Eq fin_n)
              | None => eq_refl
              end).

Qed.

Lemma rinstInst_up_list_sort2_sort2 {p : nat} {m : nat} {n_sort2 : nat}
  (xi : fin m -> fin n_sort2) (sigma : fin m -> sort2 n_sort2)
  (Eq : forall x, funcomp (var_sort2 n_sort2) xi x = sigma x) :
  forall x,
  funcomp (var_sort2 (plus p n_sort2)) (upRen_list_sort2_sort2 p xi) x =
  up_list_sort2_sort2 p sigma x.

Proof.
exact (fun n =>
              eq_trans (scons_p_comp' _ _ (var_sort2 (plus p n_sort2)) n)
                (scons_p_congr (fun z => eq_refl)
                   (fun n => ap (ren_sort2 (shift_p p)) (Eq n)))).

Qed.

Fixpoint rinst_inst_sort0 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort0 m_sort2) {struct s} :
ren_sort0 xi_sort2 s = subst_sort0 sigma_sort2 s :=
  match s with
  | cmix0 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix0 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end
with rinst_inst_sort1 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort1 m_sort2) {struct s} :
ren_sort1 xi_sort2 s = subst_sort1 sigma_sort2 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix1 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end
with rinst_inst_sort2 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort2 m_sort2) {struct s} :
ren_sort2 xi_sort2 s = subst_sort2 sigma_sort2 s :=
  match s with
  | var_sort2 _ s0 => Eq_sort2 s0
  | cmix2 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix2 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end
with rinst_inst_sort3 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort3 m_sort2) {struct s} :
ren_sort3 xi_sort2 s = subst_sort3 sigma_sort2 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix3 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end
with rinst_inst_sort4 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort4 m_sort2) {struct s} :
ren_sort4 xi_sort2 s = subst_sort4 sigma_sort2 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix4 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end
with rinst_inst_sort5 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort5 m_sort2) {struct s} :
ren_sort5 xi_sort2 s = subst_sort5 sigma_sort2 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix5 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  | clam9 _ s0 =>
      congr_clam9
        (rinst_inst_sort7 (upRen_sort2_sort2 xi_sort2)
           (up_sort2_sort2 sigma_sort2)
           (rinstInst_up_sort2_sort2 _ _ Eq_sort2) s0)
  end
with rinst_inst_sort6 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort6 m_sort2) {struct s} :
ren_sort6 xi_sort2 s = subst_sort6 sigma_sort2 s :=
  match s with
  | cmix6 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix6 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end
with rinst_inst_sort7 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort7 m_sort2) {struct s} :
ren_sort7 xi_sort2 s = subst_sort7 sigma_sort2 s :=
  match s with
  | cmix7 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix7 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end
with rinst_inst_sort8 {m_sort2 : nat} {n_sort2 : nat}
(xi_sort2 : fin m_sort2 -> fin n_sort2)
(sigma_sort2 : fin m_sort2 -> sort2 n_sort2)
(Eq_sort2 : forall x, funcomp (var_sort2 n_sort2) xi_sort2 x = sigma_sort2 x)
(s : sort8 m_sort2) {struct s} :
ren_sort8 xi_sort2 s = subst_sort8 sigma_sort2 s :=
  match s with
  | cmix8 _ s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
      congr_cmix8 (rinst_inst_sort0 xi_sort2 sigma_sort2 Eq_sort2 s0)
        (rinst_inst_sort1 xi_sort2 sigma_sort2 Eq_sort2 s1)
        (rinst_inst_sort2 xi_sort2 sigma_sort2 Eq_sort2 s2)
        (rinst_inst_sort3 xi_sort2 sigma_sort2 Eq_sort2 s3)
        (rinst_inst_sort4 xi_sort2 sigma_sort2 Eq_sort2 s4)
        (rinst_inst_sort5 xi_sort2 sigma_sort2 Eq_sort2 s5)
        (rinst_inst_sort6 xi_sort2 sigma_sort2 Eq_sort2 s6)
        (rinst_inst_sort7 xi_sort2 sigma_sort2 Eq_sort2 s7)
        (rinst_inst_sort8 xi_sort2 sigma_sort2 Eq_sort2 s8)
  end.

Lemma renRen_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort0 m_sort2) :
  ren_sort0 zeta_sort2 (ren_sort0 xi_sort2 s) =
  ren_sort0 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort0 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort1 m_sort2) :
  ren_sort1 zeta_sort2 (ren_sort1 xi_sort2 s) =
  ren_sort1 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort1 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort2 m_sort2) :
  ren_sort2 zeta_sort2 (ren_sort2 xi_sort2 s) =
  ren_sort2 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort2 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort3 m_sort2) :
  ren_sort3 zeta_sort2 (ren_sort3 xi_sort2 s) =
  ren_sort3 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort3 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort4 m_sort2) :
  ren_sort4 zeta_sort2 (ren_sort4 xi_sort2 s) =
  ren_sort4 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort4 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort5 m_sort2) :
  ren_sort5 zeta_sort2 (ren_sort5 xi_sort2 s) =
  ren_sort5 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort5 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort6 m_sort2) :
  ren_sort6 zeta_sort2 (ren_sort6 xi_sort2 s) =
  ren_sort6 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort6 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort7 m_sort2) :
  ren_sort7 zeta_sort2 (ren_sort7 xi_sort2 s) =
  ren_sort7 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort7 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort8 m_sort2) :
  ren_sort8 zeta_sort2 (ren_sort8 xi_sort2 s) =
  ren_sort8 (funcomp zeta_sort2 xi_sort2) s.

Proof.
exact (compRenRen_sort8 xi_sort2 zeta_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma compRen_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort0 m_sort2) :
  ren_sort0 zeta_sort2 (subst_sort0 sigma_sort2 s) =
  subst_sort0 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort0 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort1 m_sort2) :
  ren_sort1 zeta_sort2 (subst_sort1 sigma_sort2 s) =
  subst_sort1 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort1 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort2 m_sort2) :
  ren_sort2 zeta_sort2 (subst_sort2 sigma_sort2 s) =
  subst_sort2 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort2 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort3 m_sort2) :
  ren_sort3 zeta_sort2 (subst_sort3 sigma_sort2 s) =
  subst_sort3 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort3 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort4 m_sort2) :
  ren_sort4 zeta_sort2 (subst_sort4 sigma_sort2 s) =
  subst_sort4 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort4 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort5 m_sort2) :
  ren_sort5 zeta_sort2 (subst_sort5 sigma_sort2 s) =
  subst_sort5 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort5 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort6 m_sort2) :
  ren_sort6 zeta_sort2 (subst_sort6 sigma_sort2 s) =
  subst_sort6 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort6 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort7 m_sort2) :
  ren_sort7 zeta_sort2 (subst_sort7 sigma_sort2 s) =
  subst_sort7 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort7 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (zeta_sort2 : fin k_sort2 -> fin l_sort2) (s : sort8 m_sort2) :
  ren_sort8 zeta_sort2 (subst_sort8 sigma_sort2 s) =
  subst_sort8 (funcomp (ren_sort2 zeta_sort2) sigma_sort2) s.

Proof.
exact (compSubstRen_sort8 sigma_sort2 zeta_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma renComp_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort0 m_sort2) :
  subst_sort0 tau_sort2 (ren_sort0 xi_sort2 s) =
  subst_sort0 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort0 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort1 m_sort2) :
  subst_sort1 tau_sort2 (ren_sort1 xi_sort2 s) =
  subst_sort1 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort1 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort2 m_sort2) :
  subst_sort2 tau_sort2 (ren_sort2 xi_sort2 s) =
  subst_sort2 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort2 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort3 m_sort2) :
  subst_sort3 tau_sort2 (ren_sort3 xi_sort2 s) =
  subst_sort3 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort3 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort4 m_sort2) :
  subst_sort4 tau_sort2 (ren_sort4 xi_sort2 s) =
  subst_sort4 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort4 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort5 m_sort2) :
  subst_sort5 tau_sort2 (ren_sort5 xi_sort2 s) =
  subst_sort5 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort5 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort6 m_sort2) :
  subst_sort6 tau_sort2 (ren_sort6 xi_sort2 s) =
  subst_sort6 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort6 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort7 m_sort2) :
  subst_sort7 tau_sort2 (ren_sort7 xi_sort2 s) =
  subst_sort7 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort7 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (xi_sort2 : fin m_sort2 -> fin k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort8 m_sort2) :
  subst_sort8 tau_sort2 (ren_sort8 xi_sort2 s) =
  subst_sort8 (funcomp tau_sort2 xi_sort2) s.

Proof.
exact (compRenSubst_sort8 xi_sort2 tau_sort2 _ (fun n => eq_refl) s).

Qed.

Lemma compComp_sort0 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort0 m_sort2) :
  subst_sort0 tau_sort2 (subst_sort0 sigma_sort2 s) =
  subst_sort0 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort0 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort1 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort1 m_sort2) :
  subst_sort1 tau_sort2 (subst_sort1 sigma_sort2 s) =
  subst_sort1 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort1 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort2 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort2 m_sort2) :
  subst_sort2 tau_sort2 (subst_sort2 sigma_sort2 s) =
  subst_sort2 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort2 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort3 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort3 m_sort2) :
  subst_sort3 tau_sort2 (subst_sort3 sigma_sort2 s) =
  subst_sort3 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort3 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort4 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort4 m_sort2) :
  subst_sort4 tau_sort2 (subst_sort4 sigma_sort2 s) =
  subst_sort4 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort4 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort5 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort5 m_sort2) :
  subst_sort5 tau_sort2 (subst_sort5 sigma_sort2 s) =
  subst_sort5 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort5 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort6 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort6 m_sort2) :
  subst_sort6 tau_sort2 (subst_sort6 sigma_sort2 s) =
  subst_sort6 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort6 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort7 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort7 m_sort2) :
  subst_sort7 tau_sort2 (subst_sort7 sigma_sort2 s) =
  subst_sort7 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort7 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort8 {k_sort2 : nat} {l_sort2 : nat} {m_sort2 : nat}
  (sigma_sort2 : fin m_sort2 -> sort2 k_sort2)
  (tau_sort2 : fin k_sort2 -> sort2 l_sort2) (s : sort8 m_sort2) :
  subst_sort8 tau_sort2 (subst_sort8 sigma_sort2 s) =
  subst_sort8 (funcomp (subst_sort2 tau_sort2) sigma_sort2) s.

Proof.
exact (compSubstSubst_sort8 sigma_sort2 tau_sort2 _ (fun n => eq_refl)
                s).

Qed.
