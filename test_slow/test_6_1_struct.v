Require Import core fintype.

Inductive sort0 (n_sort0 : nat) : Type :=
  | var_sort0 : fin n_sort0 -> sort0 n_sort0
  | cmix0 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 -> sort4 n_sort0 -> sort5 n_sort0 -> sort0 n_sort0
with sort1 (n_sort0 : nat) : Type :=
  | cmix1 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 -> sort4 n_sort0 -> sort5 n_sort0 -> sort1 n_sort0
  | clam6 : sort2 (S n_sort0) -> sort1 n_sort0
with sort2 (n_sort0 : nat) : Type :=
    cmix2 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 -> sort4 n_sort0 -> sort5 n_sort0 -> sort2 n_sort0
with sort3 (n_sort0 : nat) : Type :=
    cmix3 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 -> sort4 n_sort0 -> sort5 n_sort0 -> sort3 n_sort0
with sort4 (n_sort0 : nat) : Type :=
    cmix4 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 -> sort4 n_sort0 -> sort5 n_sort0 -> sort4 n_sort0
with sort5 (n_sort0 : nat) : Type :=
    cmix5 :
      sort0 n_sort0 ->
      sort1 n_sort0 ->
      sort2 n_sort0 ->
      sort3 n_sort0 -> sort4 n_sort0 -> sort5 n_sort0 -> sort5 n_sort0.

Lemma congr_cmix0 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {t0 : sort0 m_sort0} {t1 : sort1 m_sort0}
  {t2 : sort2 m_sort0} {t3 : sort3 m_sort0} {t4 : sort4 m_sort0}
  {t5 : sort5 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix0 m_sort0 s0 s1 s2 s3 s4 s5 = cmix0 m_sort0 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix0 m_sort0 x s1 s2 s3 s4 s5)
                                  H0))
                            (ap (fun x => cmix0 m_sort0 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix0 m_sort0 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix0 m_sort0 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix0 m_sort0 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix0 m_sort0 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix1 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {t0 : sort0 m_sort0} {t1 : sort1 m_sort0}
  {t2 : sort2 m_sort0} {t3 : sort3 m_sort0} {t4 : sort4 m_sort0}
  {t5 : sort5 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix1 m_sort0 s0 s1 s2 s3 s4 s5 = cmix1 m_sort0 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix1 m_sort0 x s1 s2 s3 s4 s5)
                                  H0))
                            (ap (fun x => cmix1 m_sort0 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix1 m_sort0 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix1 m_sort0 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix1 m_sort0 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix1 m_sort0 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_clam6 {m_sort0 : nat} {s0 : sort2 (S m_sort0)}
  {t0 : sort2 (S m_sort0)} (H0 : s0 = t0) :
  clam6 m_sort0 s0 = clam6 m_sort0 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam6 m_sort0 x) H0)).

Qed.

Lemma congr_cmix2 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {t0 : sort0 m_sort0} {t1 : sort1 m_sort0}
  {t2 : sort2 m_sort0} {t3 : sort3 m_sort0} {t4 : sort4 m_sort0}
  {t5 : sort5 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix2 m_sort0 s0 s1 s2 s3 s4 s5 = cmix2 m_sort0 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix2 m_sort0 x s1 s2 s3 s4 s5)
                                  H0))
                            (ap (fun x => cmix2 m_sort0 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix2 m_sort0 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix2 m_sort0 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix2 m_sort0 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix2 m_sort0 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix3 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {t0 : sort0 m_sort0} {t1 : sort1 m_sort0}
  {t2 : sort2 m_sort0} {t3 : sort3 m_sort0} {t4 : sort4 m_sort0}
  {t5 : sort5 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix3 m_sort0 s0 s1 s2 s3 s4 s5 = cmix3 m_sort0 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix3 m_sort0 x s1 s2 s3 s4 s5)
                                  H0))
                            (ap (fun x => cmix3 m_sort0 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix3 m_sort0 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix3 m_sort0 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix3 m_sort0 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix3 m_sort0 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix4 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {t0 : sort0 m_sort0} {t1 : sort1 m_sort0}
  {t2 : sort2 m_sort0} {t3 : sort3 m_sort0} {t4 : sort4 m_sort0}
  {t5 : sort5 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix4 m_sort0 s0 s1 s2 s3 s4 s5 = cmix4 m_sort0 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix4 m_sort0 x s1 s2 s3 s4 s5)
                                  H0))
                            (ap (fun x => cmix4 m_sort0 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix4 m_sort0 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix4 m_sort0 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix4 m_sort0 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix4 m_sort0 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix5 {m_sort0 : nat} {s0 : sort0 m_sort0} {s1 : sort1 m_sort0}
  {s2 : sort2 m_sort0} {s3 : sort3 m_sort0} {s4 : sort4 m_sort0}
  {s5 : sort5 m_sort0} {t0 : sort0 m_sort0} {t1 : sort1 m_sort0}
  {t2 : sort2 m_sort0} {t3 : sort3 m_sort0} {t4 : sort4 m_sort0}
  {t5 : sort5 m_sort0} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix5 m_sort0 s0 s1 s2 s3 s4 s5 = cmix5 m_sort0 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix5 m_sort0 x s1 s2 s3 s4 s5)
                                  H0))
                            (ap (fun x => cmix5 m_sort0 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix5 m_sort0 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix5 m_sort0 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix5 m_sort0 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix5 m_sort0 t0 t1 t2 t3 t4 x) H5)).

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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      cmix0 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
  end
with ren_sort1 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort1 m_sort0) {struct s} :
sort1 n_sort0 :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      cmix1 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
  | clam6 _ s0 => clam6 n_sort0 (ren_sort2 (upRen_sort0_sort0 xi_sort0) s0)
  end
with ren_sort2 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort2 m_sort0) {struct s} :
sort2 n_sort0 :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      cmix2 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
  end
with ren_sort3 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort3 m_sort0) {struct s} :
sort3 n_sort0 :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      cmix3 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
  end
with ren_sort4 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort4 m_sort0) {struct s} :
sort4 n_sort0 :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      cmix4 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
  end
with ren_sort5 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0) (s : sort5 m_sort0) {struct s} :
sort5 n_sort0 :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      cmix5 n_sort0 (ren_sort0 xi_sort0 s0) (ren_sort1 xi_sort0 s1)
        (ren_sort2 xi_sort0 s2) (ren_sort3 xi_sort0 s3)
        (ren_sort4 xi_sort0 s4) (ren_sort5 xi_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      cmix0 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
  end
with subst_sort1 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort1 m_sort0) {struct s} :
sort1 n_sort0 :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      cmix1 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
  | clam6 _ s0 => clam6 n_sort0 (subst_sort2 (up_sort0_sort0 sigma_sort0) s0)
  end
with subst_sort2 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort2 m_sort0) {struct s} :
sort2 n_sort0 :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      cmix2 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
  end
with subst_sort3 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort3 m_sort0) {struct s} :
sort3 n_sort0 :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      cmix3 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
  end
with subst_sort4 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort4 m_sort0) {struct s} :
sort4 n_sort0 :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      cmix4 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
  end
with subst_sort5 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0) (s : sort5 m_sort0) {struct s} :
sort5 n_sort0 :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      cmix5 n_sort0 (subst_sort0 sigma_sort0 s0) (subst_sort1 sigma_sort0 s1)
        (subst_sort2 sigma_sort0 s2) (subst_sort3 sigma_sort0 s3)
        (subst_sort4 sigma_sort0 s4) (subst_sort5 sigma_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
  end
with idSubst_sort1 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort1 m_sort0) {struct s} : subst_sort1 sigma_sort0 s = s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (idSubst_sort2 (up_sort0_sort0 sigma_sort0)
           (upId_sort0_sort0 _ Eq_sort0) s0)
  end
with idSubst_sort2 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort2 m_sort0) {struct s} : subst_sort2 sigma_sort0 s = s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
  end
with idSubst_sort3 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort3 m_sort0) {struct s} : subst_sort3 sigma_sort0 s = s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
  end
with idSubst_sort4 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort4 m_sort0) {struct s} : subst_sort4 sigma_sort0 s = s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
  end
with idSubst_sort5 {m_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 m_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = var_sort0 m_sort0 x)
(s : sort5 m_sort0) {struct s} : subst_sort5 sigma_sort0 s = s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (idSubst_sort0 sigma_sort0 Eq_sort0 s0)
        (idSubst_sort1 sigma_sort0 Eq_sort0 s1)
        (idSubst_sort2 sigma_sort0 Eq_sort0 s2)
        (idSubst_sort3 sigma_sort0 Eq_sort0 s3)
        (idSubst_sort4 sigma_sort0 Eq_sort0 s4)
        (idSubst_sort5 sigma_sort0 Eq_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
  end
with extRen_sort1 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort1 m_sort0) {struct
 s} : ren_sort1 xi_sort0 s = ren_sort1 zeta_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (extRen_sort2 (upRen_sort0_sort0 xi_sort0)
           (upRen_sort0_sort0 zeta_sort0) (upExtRen_sort0_sort0 _ _ Eq_sort0)
           s0)
  end
with extRen_sort2 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort2 m_sort0) {struct
 s} : ren_sort2 xi_sort0 s = ren_sort2 zeta_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
  end
with extRen_sort3 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort3 m_sort0) {struct
 s} : ren_sort3 xi_sort0 s = ren_sort3 zeta_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
  end
with extRen_sort4 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort4 m_sort0) {struct
 s} : ren_sort4 xi_sort0 s = ren_sort4 zeta_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
  end
with extRen_sort5 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(zeta_sort0 : fin m_sort0 -> fin n_sort0)
(Eq_sort0 : forall x, xi_sort0 x = zeta_sort0 x) (s : sort5 m_sort0) {struct
 s} : ren_sort5 xi_sort0 s = ren_sort5 zeta_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (extRen_sort0 xi_sort0 zeta_sort0 Eq_sort0 s0)
        (extRen_sort1 xi_sort0 zeta_sort0 Eq_sort0 s1)
        (extRen_sort2 xi_sort0 zeta_sort0 Eq_sort0 s2)
        (extRen_sort3 xi_sort0 zeta_sort0 Eq_sort0 s3)
        (extRen_sort4 xi_sort0 zeta_sort0 Eq_sort0 s4)
        (extRen_sort5 xi_sort0 zeta_sort0 Eq_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
  end
with ext_sort1 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort1 m_sort0)
{struct s} : subst_sort1 sigma_sort0 s = subst_sort1 tau_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (ext_sort2 (up_sort0_sort0 sigma_sort0) (up_sort0_sort0 tau_sort0)
           (upExt_sort0_sort0 _ _ Eq_sort0) s0)
  end
with ext_sort2 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort2 m_sort0)
{struct s} : subst_sort2 sigma_sort0 s = subst_sort2 tau_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
  end
with ext_sort3 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort3 m_sort0)
{struct s} : subst_sort3 sigma_sort0 s = subst_sort3 tau_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
  end
with ext_sort4 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort4 m_sort0)
{struct s} : subst_sort4 sigma_sort0 s = subst_sort4 tau_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
  end
with ext_sort5 {m_sort0 : nat} {n_sort0 : nat}
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(tau_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, sigma_sort0 x = tau_sort0 x) (s : sort5 m_sort0)
{struct s} : subst_sort5 sigma_sort0 s = subst_sort5 tau_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (ext_sort0 sigma_sort0 tau_sort0 Eq_sort0 s0)
        (ext_sort1 sigma_sort0 tau_sort0 Eq_sort0 s1)
        (ext_sort2 sigma_sort0 tau_sort0 Eq_sort0 s2)
        (ext_sort3 sigma_sort0 tau_sort0 Eq_sort0 s3)
        (ext_sort4 sigma_sort0 tau_sort0 Eq_sort0 s4)
        (ext_sort5 sigma_sort0 tau_sort0 Eq_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
  end
with compRenRen_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort1 m_sort0) {struct s} :
ren_sort1 zeta_sort0 (ren_sort1 xi_sort0 s) = ren_sort1 rho_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (compRenRen_sort2 (upRen_sort0_sort0 xi_sort0)
           (upRen_sort0_sort0 zeta_sort0) (upRen_sort0_sort0 rho_sort0)
           (up_ren_ren _ _ _ Eq_sort0) s0)
  end
with compRenRen_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort2 m_sort0) {struct s} :
ren_sort2 zeta_sort0 (ren_sort2 xi_sort0 s) = ren_sort2 rho_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
  end
with compRenRen_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort3 m_sort0) {struct s} :
ren_sort3 zeta_sort0 (ren_sort3 xi_sort0 s) = ren_sort3 rho_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
  end
with compRenRen_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort4 m_sort0) {struct s} :
ren_sort4 zeta_sort0 (ren_sort4 xi_sort0 s) = ren_sort4 rho_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
  end
with compRenRen_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(zeta_sort0 : fin k_sort0 -> fin l_sort0)
(rho_sort0 : fin m_sort0 -> fin l_sort0)
(Eq_sort0 : forall x, funcomp zeta_sort0 xi_sort0 x = rho_sort0 x)
(s : sort5 m_sort0) {struct s} :
ren_sort5 zeta_sort0 (ren_sort5 xi_sort0 s) = ren_sort5 rho_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compRenRen_sort0 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s0)
        (compRenRen_sort1 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s1)
        (compRenRen_sort2 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s2)
        (compRenRen_sort3 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s3)
        (compRenRen_sort4 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s4)
        (compRenRen_sort5 xi_sort0 zeta_sort0 rho_sort0 Eq_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
  end
with compRenSubst_sort1 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort1 m_sort0) {struct s} :
subst_sort1 tau_sort0 (ren_sort1 xi_sort0 s) = subst_sort1 theta_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (compRenSubst_sort2 (upRen_sort0_sort0 xi_sort0)
           (up_sort0_sort0 tau_sort0) (up_sort0_sort0 theta_sort0)
           (up_ren_subst_sort0_sort0 _ _ _ Eq_sort0) s0)
  end
with compRenSubst_sort2 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort2 m_sort0) {struct s} :
subst_sort2 tau_sort0 (ren_sort2 xi_sort0 s) = subst_sort2 theta_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
  end
with compRenSubst_sort3 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort3 m_sort0) {struct s} :
subst_sort3 tau_sort0 (ren_sort3 xi_sort0 s) = subst_sort3 theta_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
  end
with compRenSubst_sort4 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort4 m_sort0) {struct s} :
subst_sort4 tau_sort0 (ren_sort4 xi_sort0 s) = subst_sort4 theta_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
  end
with compRenSubst_sort5 {k_sort0 : nat} {l_sort0 : nat} {m_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin k_sort0)
(tau_sort0 : fin k_sort0 -> sort0 l_sort0)
(theta_sort0 : fin m_sort0 -> sort0 l_sort0)
(Eq_sort0 : forall x, funcomp tau_sort0 xi_sort0 x = theta_sort0 x)
(s : sort5 m_sort0) {struct s} :
subst_sort5 tau_sort0 (ren_sort5 xi_sort0 s) = subst_sort5 theta_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compRenSubst_sort0 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compRenSubst_sort1 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compRenSubst_sort2 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compRenSubst_sort3 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compRenSubst_sort4 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compRenSubst_sort5 xi_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (compSubstRen_sort2 (up_sort0_sort0 sigma_sort0)
           (upRen_sort0_sort0 zeta_sort0) (up_sort0_sort0 theta_sort0)
           (up_subst_ren_sort0_sort0 _ _ _ Eq_sort0) s0)
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
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compSubstRen_sort0 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstRen_sort1 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstRen_sort2 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstRen_sort3 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstRen_sort4 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstRen_sort5 sigma_sort0 zeta_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (compSubstSubst_sort2 (up_sort0_sort0 sigma_sort0)
           (up_sort0_sort0 tau_sort0) (up_sort0_sort0 theta_sort0)
           (up_subst_subst_sort0_sort0 _ _ _ Eq_sort0) s0)
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
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compSubstSubst_sort0 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s0)
        (compSubstSubst_sort1 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s1)
        (compSubstSubst_sort2 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s2)
        (compSubstSubst_sort3 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s3)
        (compSubstSubst_sort4 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s4)
        (compSubstSubst_sort5 sigma_sort0 tau_sort0 theta_sort0 Eq_sort0 s5)
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
  | cmix0 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
  end
with rinst_inst_sort1 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort1 m_sort0) {struct s} :
ren_sort1 xi_sort0 s = subst_sort1 sigma_sort0 s :=
  match s with
  | cmix1 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
  | clam6 _ s0 =>
      congr_clam6
        (rinst_inst_sort2 (upRen_sort0_sort0 xi_sort0)
           (up_sort0_sort0 sigma_sort0)
           (rinstInst_up_sort0_sort0 _ _ Eq_sort0) s0)
  end
with rinst_inst_sort2 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort2 m_sort0) {struct s} :
ren_sort2 xi_sort0 s = subst_sort2 sigma_sort0 s :=
  match s with
  | cmix2 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
  end
with rinst_inst_sort3 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort3 m_sort0) {struct s} :
ren_sort3 xi_sort0 s = subst_sort3 sigma_sort0 s :=
  match s with
  | cmix3 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
  end
with rinst_inst_sort4 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort4 m_sort0) {struct s} :
ren_sort4 xi_sort0 s = subst_sort4 sigma_sort0 s :=
  match s with
  | cmix4 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
  end
with rinst_inst_sort5 {m_sort0 : nat} {n_sort0 : nat}
(xi_sort0 : fin m_sort0 -> fin n_sort0)
(sigma_sort0 : fin m_sort0 -> sort0 n_sort0)
(Eq_sort0 : forall x, funcomp (var_sort0 n_sort0) xi_sort0 x = sigma_sort0 x)
(s : sort5 m_sort0) {struct s} :
ren_sort5 xi_sort0 s = subst_sort5 sigma_sort0 s :=
  match s with
  | cmix5 _ s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (rinst_inst_sort0 xi_sort0 sigma_sort0 Eq_sort0 s0)
        (rinst_inst_sort1 xi_sort0 sigma_sort0 Eq_sort0 s1)
        (rinst_inst_sort2 xi_sort0 sigma_sort0 Eq_sort0 s2)
        (rinst_inst_sort3 xi_sort0 sigma_sort0 Eq_sort0 s3)
        (rinst_inst_sort4 xi_sort0 sigma_sort0 Eq_sort0 s4)
        (rinst_inst_sort5 xi_sort0 sigma_sort0 Eq_sort0 s5)
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
