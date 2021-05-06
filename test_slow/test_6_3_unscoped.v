Require Import core unscoped.

Inductive sort0 : Type :=
    cmix0 : sort0 -> sort1 -> sort2 -> sort3 -> sort4 -> sort5 -> sort0
with sort1 : Type :=
    cmix1 : sort0 -> sort1 -> sort2 -> sort3 -> sort4 -> sort5 -> sort1
with sort2 : Type :=
    cmix2 : sort0 -> sort1 -> sort2 -> sort3 -> sort4 -> sort5 -> sort2
with sort3 : Type :=
  | cmix3 : sort0 -> sort1 -> sort2 -> sort3 -> sort4 -> sort5 -> sort3
  | clam6 : sort3 -> sort3
with sort4 : Type :=
    cmix4 : sort0 -> sort1 -> sort2 -> sort3 -> sort4 -> sort5 -> sort4
with sort5 : Type :=
  | var_sort5 : nat -> sort5
  | cmix5 : sort0 -> sort1 -> sort2 -> sort3 -> sort4 -> sort5 -> sort5.

Lemma congr_cmix0 {s0 : sort0} {s1 : sort1} {s2 : sort2} {s3 : sort3}
  {s4 : sort4} {s5 : sort5} {t0 : sort0} {t1 : sort1} {t2 : sort2}
  {t3 : sort3} {t4 : sort4} {t5 : sort5} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix0 s0 s1 s2 s3 s4 s5 = cmix0 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix0 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix0 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix0 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix0 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix0 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix0 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix1 {s0 : sort0} {s1 : sort1} {s2 : sort2} {s3 : sort3}
  {s4 : sort4} {s5 : sort5} {t0 : sort0} {t1 : sort1} {t2 : sort2}
  {t3 : sort3} {t4 : sort4} {t5 : sort5} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix1 s0 s1 s2 s3 s4 s5 = cmix1 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix1 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix1 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix1 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix1 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix1 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix1 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix2 {s0 : sort0} {s1 : sort1} {s2 : sort2} {s3 : sort3}
  {s4 : sort4} {s5 : sort5} {t0 : sort0} {t1 : sort1} {t2 : sort2}
  {t3 : sort3} {t4 : sort4} {t5 : sort5} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix2 s0 s1 s2 s3 s4 s5 = cmix2 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix2 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix2 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix2 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix2 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix2 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix2 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix3 {s0 : sort0} {s1 : sort1} {s2 : sort2} {s3 : sort3}
  {s4 : sort4} {s5 : sort5} {t0 : sort0} {t1 : sort1} {t2 : sort2}
  {t3 : sort3} {t4 : sort4} {t5 : sort5} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix3 s0 s1 s2 s3 s4 s5 = cmix3 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix3 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix3 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix3 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix3 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix3 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix3 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_clam6 {s0 : sort3} {t0 : sort3} (H0 : s0 = t0) :
  clam6 s0 = clam6 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam6 x) H0)).

Qed.

Lemma congr_cmix4 {s0 : sort0} {s1 : sort1} {s2 : sort2} {s3 : sort3}
  {s4 : sort4} {s5 : sort5} {t0 : sort0} {t1 : sort1} {t2 : sort2}
  {t3 : sort3} {t4 : sort4} {t5 : sort5} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix4 s0 s1 s2 s3 s4 s5 = cmix4 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix4 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix4 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix4 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix4 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix4 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix4 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix5 {s0 : sort0} {s1 : sort1} {s2 : sort2} {s3 : sort3}
  {s4 : sort4} {s5 : sort5} {t0 : sort0} {t1 : sort1} {t2 : sort2}
  {t3 : sort3} {t4 : sort4} {t5 : sort5} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix5 s0 s1 s2 s3 s4 s5 = cmix5 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix5 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix5 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix5 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix5 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix5 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix5 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma upRen_sort5_sort5 (xi : nat -> nat) : nat -> nat.

Proof.
exact (up_ren xi).

Defined.

Fixpoint ren_sort0 (xi_sort5 : nat -> nat) (s : sort0)  : sort0 :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      cmix0 (ren_sort0 xi_sort5 s0) (ren_sort1 xi_sort5 s1)
        (ren_sort2 xi_sort5 s2) (ren_sort3 xi_sort5 s3)
        (ren_sort4 xi_sort5 s4) (ren_sort5 xi_sort5 s5)
  end
with ren_sort1 (xi_sort5 : nat -> nat) (s : sort1)  : sort1 :=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      cmix1 (ren_sort0 xi_sort5 s0) (ren_sort1 xi_sort5 s1)
        (ren_sort2 xi_sort5 s2) (ren_sort3 xi_sort5 s3)
        (ren_sort4 xi_sort5 s4) (ren_sort5 xi_sort5 s5)
  end
with ren_sort2 (xi_sort5 : nat -> nat) (s : sort2)  : sort2 :=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      cmix2 (ren_sort0 xi_sort5 s0) (ren_sort1 xi_sort5 s1)
        (ren_sort2 xi_sort5 s2) (ren_sort3 xi_sort5 s3)
        (ren_sort4 xi_sort5 s4) (ren_sort5 xi_sort5 s5)
  end
with ren_sort3 (xi_sort5 : nat -> nat) (s : sort3)  : sort3 :=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      cmix3 (ren_sort0 xi_sort5 s0) (ren_sort1 xi_sort5 s1)
        (ren_sort2 xi_sort5 s2) (ren_sort3 xi_sort5 s3)
        (ren_sort4 xi_sort5 s4) (ren_sort5 xi_sort5 s5)
  | clam6 s0 => clam6 (ren_sort3 (upRen_sort5_sort5 xi_sort5) s0)
  end
with ren_sort4 (xi_sort5 : nat -> nat) (s : sort4)  : sort4 :=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      cmix4 (ren_sort0 xi_sort5 s0) (ren_sort1 xi_sort5 s1)
        (ren_sort2 xi_sort5 s2) (ren_sort3 xi_sort5 s3)
        (ren_sort4 xi_sort5 s4) (ren_sort5 xi_sort5 s5)
  end
with ren_sort5 (xi_sort5 : nat -> nat) (s : sort5)  : sort5 :=
  match s with
  | var_sort5 s0 => var_sort5 (xi_sort5 s0)
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      cmix5 (ren_sort0 xi_sort5 s0) (ren_sort1 xi_sort5 s1)
        (ren_sort2 xi_sort5 s2) (ren_sort3 xi_sort5 s3)
        (ren_sort4 xi_sort5 s4) (ren_sort5 xi_sort5 s5)
  end.

Lemma up_sort5_sort5 (sigma : nat -> sort5) : nat -> sort5.

Proof.
exact (scons (var_sort5 var_zero) (funcomp (ren_sort5 shift) sigma)).

Defined.

Fixpoint subst_sort0 (sigma_sort5 : nat -> sort5) (s : sort0)  :
sort0 :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      cmix0 (subst_sort0 sigma_sort5 s0) (subst_sort1 sigma_sort5 s1)
        (subst_sort2 sigma_sort5 s2) (subst_sort3 sigma_sort5 s3)
        (subst_sort4 sigma_sort5 s4) (subst_sort5 sigma_sort5 s5)
  end
with subst_sort1 (sigma_sort5 : nat -> sort5) (s : sort1)  : sort1
:=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      cmix1 (subst_sort0 sigma_sort5 s0) (subst_sort1 sigma_sort5 s1)
        (subst_sort2 sigma_sort5 s2) (subst_sort3 sigma_sort5 s3)
        (subst_sort4 sigma_sort5 s4) (subst_sort5 sigma_sort5 s5)
  end
with subst_sort2 (sigma_sort5 : nat -> sort5) (s : sort2)  : sort2
:=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      cmix2 (subst_sort0 sigma_sort5 s0) (subst_sort1 sigma_sort5 s1)
        (subst_sort2 sigma_sort5 s2) (subst_sort3 sigma_sort5 s3)
        (subst_sort4 sigma_sort5 s4) (subst_sort5 sigma_sort5 s5)
  end
with subst_sort3 (sigma_sort5 : nat -> sort5) (s : sort3)  : sort3
:=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      cmix3 (subst_sort0 sigma_sort5 s0) (subst_sort1 sigma_sort5 s1)
        (subst_sort2 sigma_sort5 s2) (subst_sort3 sigma_sort5 s3)
        (subst_sort4 sigma_sort5 s4) (subst_sort5 sigma_sort5 s5)
  | clam6 s0 => clam6 (subst_sort3 (up_sort5_sort5 sigma_sort5) s0)
  end
with subst_sort4 (sigma_sort5 : nat -> sort5) (s : sort4)  : sort4
:=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      cmix4 (subst_sort0 sigma_sort5 s0) (subst_sort1 sigma_sort5 s1)
        (subst_sort2 sigma_sort5 s2) (subst_sort3 sigma_sort5 s3)
        (subst_sort4 sigma_sort5 s4) (subst_sort5 sigma_sort5 s5)
  end
with subst_sort5 (sigma_sort5 : nat -> sort5) (s : sort5)  : sort5
:=
  match s with
  | var_sort5 s0 => sigma_sort5 s0
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      cmix5 (subst_sort0 sigma_sort5 s0) (subst_sort1 sigma_sort5 s1)
        (subst_sort2 sigma_sort5 s2) (subst_sort3 sigma_sort5 s3)
        (subst_sort4 sigma_sort5 s4) (subst_sort5 sigma_sort5 s5)
  end.

Lemma upId_sort5_sort5 (sigma : nat -> sort5)
  (Eq : forall x, sigma x = var_sort5 x) :
  forall x, up_sort5_sort5 sigma x = var_sort5 x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort5 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint idSubst_sort0 (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = var_sort5 x) (s : sort0)  :
subst_sort0 sigma_sort5 s = s :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (idSubst_sort0 sigma_sort5 Eq_sort5 s0)
        (idSubst_sort1 sigma_sort5 Eq_sort5 s1)
        (idSubst_sort2 sigma_sort5 Eq_sort5 s2)
        (idSubst_sort3 sigma_sort5 Eq_sort5 s3)
        (idSubst_sort4 sigma_sort5 Eq_sort5 s4)
        (idSubst_sort5 sigma_sort5 Eq_sort5 s5)
  end
with idSubst_sort1 (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = var_sort5 x) (s : sort1)  :
subst_sort1 sigma_sort5 s = s :=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (idSubst_sort0 sigma_sort5 Eq_sort5 s0)
        (idSubst_sort1 sigma_sort5 Eq_sort5 s1)
        (idSubst_sort2 sigma_sort5 Eq_sort5 s2)
        (idSubst_sort3 sigma_sort5 Eq_sort5 s3)
        (idSubst_sort4 sigma_sort5 Eq_sort5 s4)
        (idSubst_sort5 sigma_sort5 Eq_sort5 s5)
  end
with idSubst_sort2 (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = var_sort5 x) (s : sort2)  :
subst_sort2 sigma_sort5 s = s :=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (idSubst_sort0 sigma_sort5 Eq_sort5 s0)
        (idSubst_sort1 sigma_sort5 Eq_sort5 s1)
        (idSubst_sort2 sigma_sort5 Eq_sort5 s2)
        (idSubst_sort3 sigma_sort5 Eq_sort5 s3)
        (idSubst_sort4 sigma_sort5 Eq_sort5 s4)
        (idSubst_sort5 sigma_sort5 Eq_sort5 s5)
  end
with idSubst_sort3 (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = var_sort5 x) (s : sort3)  :
subst_sort3 sigma_sort5 s = s :=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (idSubst_sort0 sigma_sort5 Eq_sort5 s0)
        (idSubst_sort1 sigma_sort5 Eq_sort5 s1)
        (idSubst_sort2 sigma_sort5 Eq_sort5 s2)
        (idSubst_sort3 sigma_sort5 Eq_sort5 s3)
        (idSubst_sort4 sigma_sort5 Eq_sort5 s4)
        (idSubst_sort5 sigma_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (idSubst_sort3 (up_sort5_sort5 sigma_sort5)
           (upId_sort5_sort5 _ Eq_sort5) s0)
  end
with idSubst_sort4 (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = var_sort5 x) (s : sort4)  :
subst_sort4 sigma_sort5 s = s :=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (idSubst_sort0 sigma_sort5 Eq_sort5 s0)
        (idSubst_sort1 sigma_sort5 Eq_sort5 s1)
        (idSubst_sort2 sigma_sort5 Eq_sort5 s2)
        (idSubst_sort3 sigma_sort5 Eq_sort5 s3)
        (idSubst_sort4 sigma_sort5 Eq_sort5 s4)
        (idSubst_sort5 sigma_sort5 Eq_sort5 s5)
  end
with idSubst_sort5 (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = var_sort5 x) (s : sort5)  :
subst_sort5 sigma_sort5 s = s :=
  match s with
  | var_sort5 s0 => Eq_sort5 s0
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (idSubst_sort0 sigma_sort5 Eq_sort5 s0)
        (idSubst_sort1 sigma_sort5 Eq_sort5 s1)
        (idSubst_sort2 sigma_sort5 Eq_sort5 s2)
        (idSubst_sort3 sigma_sort5 Eq_sort5 s3)
        (idSubst_sort4 sigma_sort5 Eq_sort5 s4)
        (idSubst_sort5 sigma_sort5 Eq_sort5 s5)
  end.

Lemma upExtRen_sort5_sort5 (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_sort5_sort5 xi x = upRen_sort5_sort5 zeta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap shift (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint extRen_sort0 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(Eq_sort5 : forall x, xi_sort5 x = zeta_sort5 x) (s : sort0)  :
ren_sort0 xi_sort5 s = ren_sort0 zeta_sort5 s :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (extRen_sort0 xi_sort5 zeta_sort5 Eq_sort5 s0)
        (extRen_sort1 xi_sort5 zeta_sort5 Eq_sort5 s1)
        (extRen_sort2 xi_sort5 zeta_sort5 Eq_sort5 s2)
        (extRen_sort3 xi_sort5 zeta_sort5 Eq_sort5 s3)
        (extRen_sort4 xi_sort5 zeta_sort5 Eq_sort5 s4)
        (extRen_sort5 xi_sort5 zeta_sort5 Eq_sort5 s5)
  end
with extRen_sort1 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(Eq_sort5 : forall x, xi_sort5 x = zeta_sort5 x) (s : sort1)  :
ren_sort1 xi_sort5 s = ren_sort1 zeta_sort5 s :=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (extRen_sort0 xi_sort5 zeta_sort5 Eq_sort5 s0)
        (extRen_sort1 xi_sort5 zeta_sort5 Eq_sort5 s1)
        (extRen_sort2 xi_sort5 zeta_sort5 Eq_sort5 s2)
        (extRen_sort3 xi_sort5 zeta_sort5 Eq_sort5 s3)
        (extRen_sort4 xi_sort5 zeta_sort5 Eq_sort5 s4)
        (extRen_sort5 xi_sort5 zeta_sort5 Eq_sort5 s5)
  end
with extRen_sort2 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(Eq_sort5 : forall x, xi_sort5 x = zeta_sort5 x) (s : sort2)  :
ren_sort2 xi_sort5 s = ren_sort2 zeta_sort5 s :=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (extRen_sort0 xi_sort5 zeta_sort5 Eq_sort5 s0)
        (extRen_sort1 xi_sort5 zeta_sort5 Eq_sort5 s1)
        (extRen_sort2 xi_sort5 zeta_sort5 Eq_sort5 s2)
        (extRen_sort3 xi_sort5 zeta_sort5 Eq_sort5 s3)
        (extRen_sort4 xi_sort5 zeta_sort5 Eq_sort5 s4)
        (extRen_sort5 xi_sort5 zeta_sort5 Eq_sort5 s5)
  end
with extRen_sort3 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(Eq_sort5 : forall x, xi_sort5 x = zeta_sort5 x) (s : sort3)  :
ren_sort3 xi_sort5 s = ren_sort3 zeta_sort5 s :=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (extRen_sort0 xi_sort5 zeta_sort5 Eq_sort5 s0)
        (extRen_sort1 xi_sort5 zeta_sort5 Eq_sort5 s1)
        (extRen_sort2 xi_sort5 zeta_sort5 Eq_sort5 s2)
        (extRen_sort3 xi_sort5 zeta_sort5 Eq_sort5 s3)
        (extRen_sort4 xi_sort5 zeta_sort5 Eq_sort5 s4)
        (extRen_sort5 xi_sort5 zeta_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (extRen_sort3 (upRen_sort5_sort5 xi_sort5)
           (upRen_sort5_sort5 zeta_sort5) (upExtRen_sort5_sort5 _ _ Eq_sort5)
           s0)
  end
with extRen_sort4 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(Eq_sort5 : forall x, xi_sort5 x = zeta_sort5 x) (s : sort4)  :
ren_sort4 xi_sort5 s = ren_sort4 zeta_sort5 s :=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (extRen_sort0 xi_sort5 zeta_sort5 Eq_sort5 s0)
        (extRen_sort1 xi_sort5 zeta_sort5 Eq_sort5 s1)
        (extRen_sort2 xi_sort5 zeta_sort5 Eq_sort5 s2)
        (extRen_sort3 xi_sort5 zeta_sort5 Eq_sort5 s3)
        (extRen_sort4 xi_sort5 zeta_sort5 Eq_sort5 s4)
        (extRen_sort5 xi_sort5 zeta_sort5 Eq_sort5 s5)
  end
with extRen_sort5 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(Eq_sort5 : forall x, xi_sort5 x = zeta_sort5 x) (s : sort5)  :
ren_sort5 xi_sort5 s = ren_sort5 zeta_sort5 s :=
  match s with
  | var_sort5 s0 => ap var_sort5 (Eq_sort5 s0)
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (extRen_sort0 xi_sort5 zeta_sort5 Eq_sort5 s0)
        (extRen_sort1 xi_sort5 zeta_sort5 Eq_sort5 s1)
        (extRen_sort2 xi_sort5 zeta_sort5 Eq_sort5 s2)
        (extRen_sort3 xi_sort5 zeta_sort5 Eq_sort5 s3)
        (extRen_sort4 xi_sort5 zeta_sort5 Eq_sort5 s4)
        (extRen_sort5 xi_sort5 zeta_sort5 Eq_sort5 s5)
  end.

Lemma upExt_sort5_sort5 (sigma : nat -> sort5) (tau : nat -> sort5)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_sort5_sort5 sigma x = up_sort5_sort5 tau x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort5 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint ext_sort0 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = tau_sort5 x) (s : sort0)  :
subst_sort0 sigma_sort5 s = subst_sort0 tau_sort5 s :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (ext_sort0 sigma_sort5 tau_sort5 Eq_sort5 s0)
        (ext_sort1 sigma_sort5 tau_sort5 Eq_sort5 s1)
        (ext_sort2 sigma_sort5 tau_sort5 Eq_sort5 s2)
        (ext_sort3 sigma_sort5 tau_sort5 Eq_sort5 s3)
        (ext_sort4 sigma_sort5 tau_sort5 Eq_sort5 s4)
        (ext_sort5 sigma_sort5 tau_sort5 Eq_sort5 s5)
  end
with ext_sort1 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = tau_sort5 x) (s : sort1)  :
subst_sort1 sigma_sort5 s = subst_sort1 tau_sort5 s :=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (ext_sort0 sigma_sort5 tau_sort5 Eq_sort5 s0)
        (ext_sort1 sigma_sort5 tau_sort5 Eq_sort5 s1)
        (ext_sort2 sigma_sort5 tau_sort5 Eq_sort5 s2)
        (ext_sort3 sigma_sort5 tau_sort5 Eq_sort5 s3)
        (ext_sort4 sigma_sort5 tau_sort5 Eq_sort5 s4)
        (ext_sort5 sigma_sort5 tau_sort5 Eq_sort5 s5)
  end
with ext_sort2 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = tau_sort5 x) (s : sort2)  :
subst_sort2 sigma_sort5 s = subst_sort2 tau_sort5 s :=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (ext_sort0 sigma_sort5 tau_sort5 Eq_sort5 s0)
        (ext_sort1 sigma_sort5 tau_sort5 Eq_sort5 s1)
        (ext_sort2 sigma_sort5 tau_sort5 Eq_sort5 s2)
        (ext_sort3 sigma_sort5 tau_sort5 Eq_sort5 s3)
        (ext_sort4 sigma_sort5 tau_sort5 Eq_sort5 s4)
        (ext_sort5 sigma_sort5 tau_sort5 Eq_sort5 s5)
  end
with ext_sort3 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = tau_sort5 x) (s : sort3)  :
subst_sort3 sigma_sort5 s = subst_sort3 tau_sort5 s :=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (ext_sort0 sigma_sort5 tau_sort5 Eq_sort5 s0)
        (ext_sort1 sigma_sort5 tau_sort5 Eq_sort5 s1)
        (ext_sort2 sigma_sort5 tau_sort5 Eq_sort5 s2)
        (ext_sort3 sigma_sort5 tau_sort5 Eq_sort5 s3)
        (ext_sort4 sigma_sort5 tau_sort5 Eq_sort5 s4)
        (ext_sort5 sigma_sort5 tau_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (ext_sort3 (up_sort5_sort5 sigma_sort5) (up_sort5_sort5 tau_sort5)
           (upExt_sort5_sort5 _ _ Eq_sort5) s0)
  end
with ext_sort4 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = tau_sort5 x) (s : sort4)  :
subst_sort4 sigma_sort5 s = subst_sort4 tau_sort5 s :=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (ext_sort0 sigma_sort5 tau_sort5 Eq_sort5 s0)
        (ext_sort1 sigma_sort5 tau_sort5 Eq_sort5 s1)
        (ext_sort2 sigma_sort5 tau_sort5 Eq_sort5 s2)
        (ext_sort3 sigma_sort5 tau_sort5 Eq_sort5 s3)
        (ext_sort4 sigma_sort5 tau_sort5 Eq_sort5 s4)
        (ext_sort5 sigma_sort5 tau_sort5 Eq_sort5 s5)
  end
with ext_sort5 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
(Eq_sort5 : forall x, sigma_sort5 x = tau_sort5 x) (s : sort5)  :
subst_sort5 sigma_sort5 s = subst_sort5 tau_sort5 s :=
  match s with
  | var_sort5 s0 => Eq_sort5 s0
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (ext_sort0 sigma_sort5 tau_sort5 Eq_sort5 s0)
        (ext_sort1 sigma_sort5 tau_sort5 Eq_sort5 s1)
        (ext_sort2 sigma_sort5 tau_sort5 Eq_sort5 s2)
        (ext_sort3 sigma_sort5 tau_sort5 Eq_sort5 s3)
        (ext_sort4 sigma_sort5 tau_sort5 Eq_sort5 s4)
        (ext_sort5 sigma_sort5 tau_sort5 Eq_sort5 s5)
  end.

Lemma up_ren_ren_sort5_sort5 (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_sort5_sort5 zeta) (upRen_sort5_sort5 xi) x =
  upRen_sort5_sort5 rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Time Fixpoint compRenRen_sort0 {k l m ij ji kl : nat} (H: k = l /\ m = ij /\ ji = kl) (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(rho_sort5 : nat -> nat)
(Eq_sort5 : forall x, funcomp zeta_sort5 xi_sort5 x = rho_sort5 x)
(s : sort0)  :
ren_sort0 zeta_sort5 (ren_sort0 xi_sort5 s) = ren_sort0 rho_sort5 s :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compRenRen_sort0 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s0)
        (compRenRen_sort1 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s1)
        (compRenRen_sort2 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s2)
        (compRenRen_sort3 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s3)
        (compRenRen_sort4 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s4)
        (compRenRen_sort5 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s5)
  end
with compRenRen_sort1 {k l m ij ji kl: nat} (H: k = l /\ m = ij /\ ji = kl) (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(rho_sort5 : nat -> nat)
(Eq_sort5 : forall x, funcomp zeta_sort5 xi_sort5 x = rho_sort5 x)
(s : sort1)  :
ren_sort1 zeta_sort5 (ren_sort1 xi_sort5 s) = ren_sort1 rho_sort5 s :=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compRenRen_sort0 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s0)
        (compRenRen_sort1 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s1)
        (compRenRen_sort2 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s2)
        (compRenRen_sort3 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s3)
        (compRenRen_sort4 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s4)
        (compRenRen_sort5 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s5)
  end
with compRenRen_sort2 {k l m ij ji kl: nat} (H: k = l /\ m = ij /\ ji = kl) (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(rho_sort5 : nat -> nat)
(Eq_sort5 : forall x, funcomp zeta_sort5 xi_sort5 x = rho_sort5 x)
(s : sort2)  :
ren_sort2 zeta_sort5 (ren_sort2 xi_sort5 s) = ren_sort2 rho_sort5 s :=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compRenRen_sort0 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s0)
        (compRenRen_sort1 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s1)
        (compRenRen_sort2 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s2)
        (compRenRen_sort3 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s3)
        (compRenRen_sort4 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s4)
        (compRenRen_sort5 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s5)
  end
with compRenRen_sort3 {k l m ij ji kl: nat} (H: k = l /\ m = ij /\ ji = kl) (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(rho_sort5 : nat -> nat)
(Eq_sort5 : forall x, funcomp zeta_sort5 xi_sort5 x = rho_sort5 x)
(s : sort3)  :
ren_sort3 zeta_sort5 (ren_sort3 xi_sort5 s) = ren_sort3 rho_sort5 s :=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compRenRen_sort0 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s0)
        (compRenRen_sort1 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s1)
        (compRenRen_sort2 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s2)
        (compRenRen_sort3 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s3)
        (compRenRen_sort4 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s4)
        (compRenRen_sort5 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (compRenRen_sort3 H (upRen_sort5_sort5 xi_sort5)
           (upRen_sort5_sort5 zeta_sort5) (upRen_sort5_sort5 rho_sort5)
           (up_ren_ren _ _ _ Eq_sort5) s0)
  end
with compRenRen_sort4 {k l m ij ji kl: nat} (H: k = l /\ m = ij /\ ji = kl) (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(rho_sort5 : nat -> nat)
(Eq_sort5 : forall x, funcomp zeta_sort5 xi_sort5 x = rho_sort5 x)
(s : sort4)  :
ren_sort4 zeta_sort5 (ren_sort4 xi_sort5 s) = ren_sort4 rho_sort5 s :=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compRenRen_sort0 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s0)
        (compRenRen_sort1 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s1)
        (compRenRen_sort2 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s2)
        (compRenRen_sort3 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s3)
        (compRenRen_sort4 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s4)
        (compRenRen_sort5 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s5)
  end
with compRenRen_sort5 {k l m ij ji kl: nat} (H: k = l /\ m = ij /\ ji = kl) (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
(rho_sort5 : nat -> nat)
(Eq_sort5 : forall x, funcomp zeta_sort5 xi_sort5 x = rho_sort5 x)
(s : sort5)  :
ren_sort5 zeta_sort5 (ren_sort5 xi_sort5 s) = ren_sort5 rho_sort5 s :=
  match s with
  | var_sort5 s0 => ap var_sort5 (Eq_sort5 s0)
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compRenRen_sort0 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s0)
        (compRenRen_sort1 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s1)
        (compRenRen_sort2 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s2)
        (compRenRen_sort3 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s3)
        (compRenRen_sort4 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s4)
        (compRenRen_sort5 H xi_sort5 zeta_sort5 rho_sort5 Eq_sort5 s5)
  end.

Lemma up_ren_subst_sort5_sort5 (xi : nat -> nat) (tau : nat -> sort5)
  (theta : nat -> sort5) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_sort5_sort5 tau) (upRen_sort5_sort5 xi) x =
  up_sort5_sort5 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort5 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint compRenSubst_sort0 (xi_sort5 : nat -> nat)
(tau_sort5 : nat -> sort5) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp tau_sort5 xi_sort5 x = theta_sort5 x)
(s : sort0)  :
subst_sort0 tau_sort5 (ren_sort0 xi_sort5 s) = subst_sort0 theta_sort5 s :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compRenSubst_sort0 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compRenSubst_sort1 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compRenSubst_sort2 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compRenSubst_sort3 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compRenSubst_sort4 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compRenSubst_sort5 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compRenSubst_sort1 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
(theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp tau_sort5 xi_sort5 x = theta_sort5 x)
(s : sort1)  :
subst_sort1 tau_sort5 (ren_sort1 xi_sort5 s) = subst_sort1 theta_sort5 s :=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compRenSubst_sort0 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compRenSubst_sort1 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compRenSubst_sort2 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compRenSubst_sort3 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compRenSubst_sort4 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compRenSubst_sort5 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compRenSubst_sort2 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
(theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp tau_sort5 xi_sort5 x = theta_sort5 x)
(s : sort2)  :
subst_sort2 tau_sort5 (ren_sort2 xi_sort5 s) = subst_sort2 theta_sort5 s :=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compRenSubst_sort0 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compRenSubst_sort1 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compRenSubst_sort2 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compRenSubst_sort3 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compRenSubst_sort4 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compRenSubst_sort5 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compRenSubst_sort3 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
(theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp tau_sort5 xi_sort5 x = theta_sort5 x)
(s : sort3)  :
subst_sort3 tau_sort5 (ren_sort3 xi_sort5 s) = subst_sort3 theta_sort5 s :=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compRenSubst_sort0 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compRenSubst_sort1 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compRenSubst_sort2 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compRenSubst_sort3 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compRenSubst_sort4 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compRenSubst_sort5 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (compRenSubst_sort3 (upRen_sort5_sort5 xi_sort5)
           (up_sort5_sort5 tau_sort5) (up_sort5_sort5 theta_sort5)
           (up_ren_subst_sort5_sort5 _ _ _ Eq_sort5) s0)
  end
with compRenSubst_sort4 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
(theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp tau_sort5 xi_sort5 x = theta_sort5 x)
(s : sort4)  :
subst_sort4 tau_sort5 (ren_sort4 xi_sort5 s) = subst_sort4 theta_sort5 s :=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compRenSubst_sort0 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compRenSubst_sort1 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compRenSubst_sort2 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compRenSubst_sort3 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compRenSubst_sort4 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compRenSubst_sort5 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compRenSubst_sort5 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
(theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp tau_sort5 xi_sort5 x = theta_sort5 x)
(s : sort5)  :
subst_sort5 tau_sort5 (ren_sort5 xi_sort5 s) = subst_sort5 theta_sort5 s :=
  match s with
  | var_sort5 s0 => Eq_sort5 s0
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compRenSubst_sort0 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compRenSubst_sort1 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compRenSubst_sort2 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compRenSubst_sort3 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compRenSubst_sort4 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compRenSubst_sort5 xi_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end.

Lemma up_subst_ren_sort5_sort5 (sigma : nat -> sort5)
  (zeta_sort5 : nat -> nat) (theta : nat -> sort5)
  (Eq : forall x, funcomp (ren_sort5 zeta_sort5) sigma x = theta x) :
  forall x,
  funcomp (ren_sort5 (upRen_sort5_sort5 zeta_sort5)) (up_sort5_sort5 sigma) x =
  up_sort5_sort5 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenRen_sort5 shift (upRen_sort5_sort5 zeta_sort5)
                       (funcomp shift zeta_sort5) (fun x => eq_refl)
                       (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compRenRen_sort5 zeta_sort5 shift
                             (funcomp shift zeta_sort5) (fun x => eq_refl)
                             (sigma n'))) (ap (ren_sort5 shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstRen_sort0 (sigma_sort5 : nat -> sort5)
(zeta_sort5 : nat -> nat) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (ren_sort5 zeta_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort0)  :
ren_sort0 zeta_sort5 (subst_sort0 sigma_sort5 s) = subst_sort0 theta_sort5 s
:=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compSubstRen_sort0 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstRen_sort1 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstRen_sort2 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstRen_sort3 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstRen_sort4 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstRen_sort5 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstRen_sort1 (sigma_sort5 : nat -> sort5)
(zeta_sort5 : nat -> nat) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (ren_sort5 zeta_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort1)  :
ren_sort1 zeta_sort5 (subst_sort1 sigma_sort5 s) = subst_sort1 theta_sort5 s
:=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compSubstRen_sort0 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstRen_sort1 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstRen_sort2 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstRen_sort3 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstRen_sort4 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstRen_sort5 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstRen_sort2 (sigma_sort5 : nat -> sort5)
(zeta_sort5 : nat -> nat) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (ren_sort5 zeta_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort2)  :
ren_sort2 zeta_sort5 (subst_sort2 sigma_sort5 s) = subst_sort2 theta_sort5 s
:=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compSubstRen_sort0 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstRen_sort1 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstRen_sort2 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstRen_sort3 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstRen_sort4 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstRen_sort5 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstRen_sort3 (sigma_sort5 : nat -> sort5)
(zeta_sort5 : nat -> nat) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (ren_sort5 zeta_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort3)  :
ren_sort3 zeta_sort5 (subst_sort3 sigma_sort5 s) = subst_sort3 theta_sort5 s
:=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compSubstRen_sort0 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstRen_sort1 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstRen_sort2 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstRen_sort3 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstRen_sort4 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstRen_sort5 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (compSubstRen_sort3 (up_sort5_sort5 sigma_sort5)
           (upRen_sort5_sort5 zeta_sort5) (up_sort5_sort5 theta_sort5)
           (up_subst_ren_sort5_sort5 _ _ _ Eq_sort5) s0)
  end
with compSubstRen_sort4 (sigma_sort5 : nat -> sort5)
(zeta_sort5 : nat -> nat) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (ren_sort5 zeta_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort4)  :
ren_sort4 zeta_sort5 (subst_sort4 sigma_sort5 s) = subst_sort4 theta_sort5 s
:=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compSubstRen_sort0 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstRen_sort1 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstRen_sort2 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstRen_sort3 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstRen_sort4 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstRen_sort5 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstRen_sort5 (sigma_sort5 : nat -> sort5)
(zeta_sort5 : nat -> nat) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (ren_sort5 zeta_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort5)  :
ren_sort5 zeta_sort5 (subst_sort5 sigma_sort5 s) = subst_sort5 theta_sort5 s
:=
  match s with
  | var_sort5 s0 => Eq_sort5 s0
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compSubstRen_sort0 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstRen_sort1 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstRen_sort2 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstRen_sort3 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstRen_sort4 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstRen_sort5 sigma_sort5 zeta_sort5 theta_sort5 Eq_sort5 s5)
  end.

Lemma up_subst_subst_sort5_sort5 (sigma : nat -> sort5)
  (tau_sort5 : nat -> sort5) (theta : nat -> sort5)
  (Eq : forall x, funcomp (subst_sort5 tau_sort5) sigma x = theta x) :
  forall x,
  funcomp (subst_sort5 (up_sort5_sort5 tau_sort5)) (up_sort5_sort5 sigma) x =
  up_sort5_sort5 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenSubst_sort5 shift (up_sort5_sort5 tau_sort5)
                       (funcomp (up_sort5_sort5 tau_sort5) shift)
                       (fun x => eq_refl) (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_sort5 tau_sort5 shift
                             (funcomp (ren_sort5 shift) tau_sort5)
                             (fun x => eq_refl) (sigma n')))
                       (ap (ren_sort5 shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstSubst_sort0 (sigma_sort5 : nat -> sort5)
(tau_sort5 : nat -> sort5) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (subst_sort5 tau_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort0)  :
subst_sort0 tau_sort5 (subst_sort0 sigma_sort5 s) = subst_sort0 theta_sort5 s
:=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0
        (compSubstSubst_sort0 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstSubst_sort1 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstSubst_sort2 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstSubst_sort3 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstSubst_sort4 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstSubst_sort5 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstSubst_sort1 (sigma_sort5 : nat -> sort5)
(tau_sort5 : nat -> sort5) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (subst_sort5 tau_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort1)  :
subst_sort1 tau_sort5 (subst_sort1 sigma_sort5 s) = subst_sort1 theta_sort5 s
:=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1
        (compSubstSubst_sort0 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstSubst_sort1 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstSubst_sort2 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstSubst_sort3 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstSubst_sort4 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstSubst_sort5 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstSubst_sort2 (sigma_sort5 : nat -> sort5)
(tau_sort5 : nat -> sort5) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (subst_sort5 tau_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort2)  :
subst_sort2 tau_sort5 (subst_sort2 sigma_sort5 s) = subst_sort2 theta_sort5 s
:=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2
        (compSubstSubst_sort0 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstSubst_sort1 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstSubst_sort2 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstSubst_sort3 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstSubst_sort4 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstSubst_sort5 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstSubst_sort3 (sigma_sort5 : nat -> sort5)
(tau_sort5 : nat -> sort5) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (subst_sort5 tau_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort3)  :
subst_sort3 tau_sort5 (subst_sort3 sigma_sort5 s) = subst_sort3 theta_sort5 s
:=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3
        (compSubstSubst_sort0 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstSubst_sort1 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstSubst_sort2 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstSubst_sort3 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstSubst_sort4 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstSubst_sort5 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (compSubstSubst_sort3 (up_sort5_sort5 sigma_sort5)
           (up_sort5_sort5 tau_sort5) (up_sort5_sort5 theta_sort5)
           (up_subst_subst_sort5_sort5 _ _ _ Eq_sort5) s0)
  end
with compSubstSubst_sort4 (sigma_sort5 : nat -> sort5)
(tau_sort5 : nat -> sort5) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (subst_sort5 tau_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort4)  :
subst_sort4 tau_sort5 (subst_sort4 sigma_sort5 s) = subst_sort4 theta_sort5 s
:=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4
        (compSubstSubst_sort0 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstSubst_sort1 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstSubst_sort2 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstSubst_sort3 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstSubst_sort4 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstSubst_sort5 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end
with compSubstSubst_sort5 (sigma_sort5 : nat -> sort5)
(tau_sort5 : nat -> sort5) (theta_sort5 : nat -> sort5)
(Eq_sort5 : forall x,
            funcomp (subst_sort5 tau_sort5) sigma_sort5 x = theta_sort5 x)
(s : sort5)  :
subst_sort5 tau_sort5 (subst_sort5 sigma_sort5 s) = subst_sort5 theta_sort5 s
:=
  match s with
  | var_sort5 s0 => Eq_sort5 s0
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5
        (compSubstSubst_sort0 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s0)
        (compSubstSubst_sort1 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s1)
        (compSubstSubst_sort2 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s2)
        (compSubstSubst_sort3 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s3)
        (compSubstSubst_sort4 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s4)
        (compSubstSubst_sort5 sigma_sort5 tau_sort5 theta_sort5 Eq_sort5 s5)
  end.

Lemma rinstInst_up_sort5_sort5 (xi : nat -> nat) (sigma : nat -> sort5)
  (Eq : forall x, funcomp var_sort5 xi x = sigma x) :
  forall x,
  funcomp var_sort5 (upRen_sort5_sort5 xi) x = up_sort5_sort5 sigma x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort5 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint rinst_inst_sort0 (xi_sort5 : nat -> nat)
(sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp var_sort5 xi_sort5 x = sigma_sort5 x)
(s : sort0)  : ren_sort0 xi_sort5 s = subst_sort0 sigma_sort5 s :=
  match s with
  | cmix0 s0 s1 s2 s3 s4 s5 =>
      congr_cmix0 (rinst_inst_sort0 xi_sort5 sigma_sort5 Eq_sort5 s0)
        (rinst_inst_sort1 xi_sort5 sigma_sort5 Eq_sort5 s1)
        (rinst_inst_sort2 xi_sort5 sigma_sort5 Eq_sort5 s2)
        (rinst_inst_sort3 xi_sort5 sigma_sort5 Eq_sort5 s3)
        (rinst_inst_sort4 xi_sort5 sigma_sort5 Eq_sort5 s4)
        (rinst_inst_sort5 xi_sort5 sigma_sort5 Eq_sort5 s5)
  end
with rinst_inst_sort1 (xi_sort5 : nat -> nat) (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp var_sort5 xi_sort5 x = sigma_sort5 x)
(s : sort1)  : ren_sort1 xi_sort5 s = subst_sort1 sigma_sort5 s :=
  match s with
  | cmix1 s0 s1 s2 s3 s4 s5 =>
      congr_cmix1 (rinst_inst_sort0 xi_sort5 sigma_sort5 Eq_sort5 s0)
        (rinst_inst_sort1 xi_sort5 sigma_sort5 Eq_sort5 s1)
        (rinst_inst_sort2 xi_sort5 sigma_sort5 Eq_sort5 s2)
        (rinst_inst_sort3 xi_sort5 sigma_sort5 Eq_sort5 s3)
        (rinst_inst_sort4 xi_sort5 sigma_sort5 Eq_sort5 s4)
        (rinst_inst_sort5 xi_sort5 sigma_sort5 Eq_sort5 s5)
  end
with rinst_inst_sort2 (xi_sort5 : nat -> nat) (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp var_sort5 xi_sort5 x = sigma_sort5 x)
(s : sort2)  : ren_sort2 xi_sort5 s = subst_sort2 sigma_sort5 s :=
  match s with
  | cmix2 s0 s1 s2 s3 s4 s5 =>
      congr_cmix2 (rinst_inst_sort0 xi_sort5 sigma_sort5 Eq_sort5 s0)
        (rinst_inst_sort1 xi_sort5 sigma_sort5 Eq_sort5 s1)
        (rinst_inst_sort2 xi_sort5 sigma_sort5 Eq_sort5 s2)
        (rinst_inst_sort3 xi_sort5 sigma_sort5 Eq_sort5 s3)
        (rinst_inst_sort4 xi_sort5 sigma_sort5 Eq_sort5 s4)
        (rinst_inst_sort5 xi_sort5 sigma_sort5 Eq_sort5 s5)
  end
with rinst_inst_sort3 (xi_sort5 : nat -> nat) (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp var_sort5 xi_sort5 x = sigma_sort5 x)
(s : sort3)  : ren_sort3 xi_sort5 s = subst_sort3 sigma_sort5 s :=
  match s with
  | cmix3 s0 s1 s2 s3 s4 s5 =>
      congr_cmix3 (rinst_inst_sort0 xi_sort5 sigma_sort5 Eq_sort5 s0)
        (rinst_inst_sort1 xi_sort5 sigma_sort5 Eq_sort5 s1)
        (rinst_inst_sort2 xi_sort5 sigma_sort5 Eq_sort5 s2)
        (rinst_inst_sort3 xi_sort5 sigma_sort5 Eq_sort5 s3)
        (rinst_inst_sort4 xi_sort5 sigma_sort5 Eq_sort5 s4)
        (rinst_inst_sort5 xi_sort5 sigma_sort5 Eq_sort5 s5)
  | clam6 s0 =>
      congr_clam6
        (rinst_inst_sort3 (upRen_sort5_sort5 xi_sort5)
           (up_sort5_sort5 sigma_sort5)
           (rinstInst_up_sort5_sort5 _ _ Eq_sort5) s0)
  end
with rinst_inst_sort4 (xi_sort5 : nat -> nat) (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp var_sort5 xi_sort5 x = sigma_sort5 x)
(s : sort4)  : ren_sort4 xi_sort5 s = subst_sort4 sigma_sort5 s :=
  match s with
  | cmix4 s0 s1 s2 s3 s4 s5 =>
      congr_cmix4 (rinst_inst_sort0 xi_sort5 sigma_sort5 Eq_sort5 s0)
        (rinst_inst_sort1 xi_sort5 sigma_sort5 Eq_sort5 s1)
        (rinst_inst_sort2 xi_sort5 sigma_sort5 Eq_sort5 s2)
        (rinst_inst_sort3 xi_sort5 sigma_sort5 Eq_sort5 s3)
        (rinst_inst_sort4 xi_sort5 sigma_sort5 Eq_sort5 s4)
        (rinst_inst_sort5 xi_sort5 sigma_sort5 Eq_sort5 s5)
  end
with rinst_inst_sort5 (xi_sort5 : nat -> nat) (sigma_sort5 : nat -> sort5)
(Eq_sort5 : forall x, funcomp var_sort5 xi_sort5 x = sigma_sort5 x)
(s : sort5)  : ren_sort5 xi_sort5 s = subst_sort5 sigma_sort5 s :=
  match s with
  | var_sort5 s0 => Eq_sort5 s0
  | cmix5 s0 s1 s2 s3 s4 s5 =>
      congr_cmix5 (rinst_inst_sort0 xi_sort5 sigma_sort5 Eq_sort5 s0)
        (rinst_inst_sort1 xi_sort5 sigma_sort5 Eq_sort5 s1)
        (rinst_inst_sort2 xi_sort5 sigma_sort5 Eq_sort5 s2)
        (rinst_inst_sort3 xi_sort5 sigma_sort5 Eq_sort5 s3)
        (rinst_inst_sort4 xi_sort5 sigma_sort5 Eq_sort5 s4)
        (rinst_inst_sort5 xi_sort5 sigma_sort5 Eq_sort5 s5)
  end.

Lemma renRen_sort0 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
  (s : sort0) :
  ren_sort0 zeta_sort5 (ren_sort0 xi_sort5 s) =
  ren_sort0 (funcomp zeta_sort5 xi_sort5) s.

Proof.
exact (compRenRen_sort0 xi_sort5 zeta_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort1 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
  (s : sort1) :
  ren_sort1 zeta_sort5 (ren_sort1 xi_sort5 s) =
  ren_sort1 (funcomp zeta_sort5 xi_sort5) s.

Proof.
exact (compRenRen_sort1 xi_sort5 zeta_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort2 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
  (s : sort2) :
  ren_sort2 zeta_sort5 (ren_sort2 xi_sort5 s) =
  ren_sort2 (funcomp zeta_sort5 xi_sort5) s.

Proof.
exact (compRenRen_sort2 xi_sort5 zeta_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort3 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
  (s : sort3) :
  ren_sort3 zeta_sort5 (ren_sort3 xi_sort5 s) =
  ren_sort3 (funcomp zeta_sort5 xi_sort5) s.

Proof.
exact (compRenRen_sort3 xi_sort5 zeta_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort4 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
  (s : sort4) :
  ren_sort4 zeta_sort5 (ren_sort4 xi_sort5 s) =
  ren_sort4 (funcomp zeta_sort5 xi_sort5) s.

Proof.
exact (compRenRen_sort4 xi_sort5 zeta_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort5 (xi_sort5 : nat -> nat) (zeta_sort5 : nat -> nat)
  (s : sort5) :
  ren_sort5 zeta_sort5 (ren_sort5 xi_sort5 s) =
  ren_sort5 (funcomp zeta_sort5 xi_sort5) s.

Proof.
exact (compRenRen_sort5 xi_sort5 zeta_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma compRen_sort0 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat)
  (s : sort0) :
  ren_sort0 zeta_sort5 (subst_sort0 sigma_sort5 s) =
  subst_sort0 (funcomp (ren_sort5 zeta_sort5) sigma_sort5) s.

Proof.
exact (compSubstRen_sort0 sigma_sort5 zeta_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort1 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat)
  (s : sort1) :
  ren_sort1 zeta_sort5 (subst_sort1 sigma_sort5 s) =
  subst_sort1 (funcomp (ren_sort5 zeta_sort5) sigma_sort5) s.

Proof.
exact (compSubstRen_sort1 sigma_sort5 zeta_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort2 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat)
  (s : sort2) :
  ren_sort2 zeta_sort5 (subst_sort2 sigma_sort5 s) =
  subst_sort2 (funcomp (ren_sort5 zeta_sort5) sigma_sort5) s.

Proof.
exact (compSubstRen_sort2 sigma_sort5 zeta_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort3 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat)
  (s : sort3) :
  ren_sort3 zeta_sort5 (subst_sort3 sigma_sort5 s) =
  subst_sort3 (funcomp (ren_sort5 zeta_sort5) sigma_sort5) s.

Proof.
exact (compSubstRen_sort3 sigma_sort5 zeta_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort4 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat)
  (s : sort4) :
  ren_sort4 zeta_sort5 (subst_sort4 sigma_sort5 s) =
  subst_sort4 (funcomp (ren_sort5 zeta_sort5) sigma_sort5) s.

Proof.
exact (compSubstRen_sort4 sigma_sort5 zeta_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compRen_sort5 (sigma_sort5 : nat -> sort5) (zeta_sort5 : nat -> nat)
  (s : sort5) :
  ren_sort5 zeta_sort5 (subst_sort5 sigma_sort5 s) =
  subst_sort5 (funcomp (ren_sort5 zeta_sort5) sigma_sort5) s.

Proof.
exact (compSubstRen_sort5 sigma_sort5 zeta_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma renComp_sort0 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
  (s : sort0) :
  subst_sort0 tau_sort5 (ren_sort0 xi_sort5 s) =
  subst_sort0 (funcomp tau_sort5 xi_sort5) s.

Proof.
exact (compRenSubst_sort0 xi_sort5 tau_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort1 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
  (s : sort1) :
  subst_sort1 tau_sort5 (ren_sort1 xi_sort5 s) =
  subst_sort1 (funcomp tau_sort5 xi_sort5) s.

Proof.
exact (compRenSubst_sort1 xi_sort5 tau_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort2 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
  (s : sort2) :
  subst_sort2 tau_sort5 (ren_sort2 xi_sort5 s) =
  subst_sort2 (funcomp tau_sort5 xi_sort5) s.

Proof.
exact (compRenSubst_sort2 xi_sort5 tau_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort3 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
  (s : sort3) :
  subst_sort3 tau_sort5 (ren_sort3 xi_sort5 s) =
  subst_sort3 (funcomp tau_sort5 xi_sort5) s.

Proof.
exact (compRenSubst_sort3 xi_sort5 tau_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort4 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
  (s : sort4) :
  subst_sort4 tau_sort5 (ren_sort4 xi_sort5 s) =
  subst_sort4 (funcomp tau_sort5 xi_sort5) s.

Proof.
exact (compRenSubst_sort4 xi_sort5 tau_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort5 (xi_sort5 : nat -> nat) (tau_sort5 : nat -> sort5)
  (s : sort5) :
  subst_sort5 tau_sort5 (ren_sort5 xi_sort5 s) =
  subst_sort5 (funcomp tau_sort5 xi_sort5) s.

Proof.
exact (compRenSubst_sort5 xi_sort5 tau_sort5 _ (fun n => eq_refl) s).

Qed.

Lemma compComp_sort0 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  (s : sort0) :
  subst_sort0 tau_sort5 (subst_sort0 sigma_sort5 s) =
  subst_sort0 (funcomp (subst_sort5 tau_sort5) sigma_sort5) s.

Proof.
exact (compSubstSubst_sort0 sigma_sort5 tau_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort1 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  (s : sort1) :
  subst_sort1 tau_sort5 (subst_sort1 sigma_sort5 s) =
  subst_sort1 (funcomp (subst_sort5 tau_sort5) sigma_sort5) s.

Proof.
exact (compSubstSubst_sort1 sigma_sort5 tau_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort2 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  (s : sort2) :
  subst_sort2 tau_sort5 (subst_sort2 sigma_sort5 s) =
  subst_sort2 (funcomp (subst_sort5 tau_sort5) sigma_sort5) s.

Proof.
exact (compSubstSubst_sort2 sigma_sort5 tau_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort3 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  (s : sort3) :
  subst_sort3 tau_sort5 (subst_sort3 sigma_sort5 s) =
  subst_sort3 (funcomp (subst_sort5 tau_sort5) sigma_sort5) s.

Proof.
exact (compSubstSubst_sort3 sigma_sort5 tau_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort4 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  (s : sort4) :
  subst_sort4 tau_sort5 (subst_sort4 sigma_sort5 s) =
  subst_sort4 (funcomp (subst_sort5 tau_sort5) sigma_sort5) s.

Proof.
exact (compSubstSubst_sort4 sigma_sort5 tau_sort5 _ (fun n => eq_refl)
                s).

Qed.

Lemma compComp_sort5 (sigma_sort5 : nat -> sort5) (tau_sort5 : nat -> sort5)
  (s : sort5) :
  subst_sort5 tau_sort5 (subst_sort5 sigma_sort5 s) =
  subst_sort5 (funcomp (subst_sort5 tau_sort5) sigma_sort5) s.

Proof.
exact (compSubstSubst_sort5 sigma_sort5 tau_sort5 _ (fun n => eq_refl)
                s).

Qed.

Inductive sort6 : Type :=
  | cmix6 : sort6 -> sort7 -> sort8 -> sort9 -> sort10 -> sort11 -> sort6
  | clam12 : sort6 -> sort6
with sort7 : Type :=
    cmix7 : sort6 -> sort7 -> sort8 -> sort9 -> sort10 -> sort11 -> sort7
with sort8 : Type :=
    cmix8 : sort6 -> sort7 -> sort8 -> sort9 -> sort10 -> sort11 -> sort8
with sort9 : Type :=
    cmix9 : sort6 -> sort7 -> sort8 -> sort9 -> sort10 -> sort11 -> sort9
with sort10 : Type :=
    cmix10 : sort6 -> sort7 -> sort8 -> sort9 -> sort10 -> sort11 -> sort10
with sort11 : Type :=
  | var_sort11 : nat -> sort11
  | cmix11 : sort6 -> sort7 -> sort8 -> sort9 -> sort10 -> sort11 -> sort11.

Lemma congr_cmix6 {s0 : sort6} {s1 : sort7} {s2 : sort8} {s3 : sort9}
  {s4 : sort10} {s5 : sort11} {t0 : sort6} {t1 : sort7} {t2 : sort8}
  {t3 : sort9} {t4 : sort10} {t5 : sort11} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix6 s0 s1 s2 s3 s4 s5 = cmix6 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix6 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix6 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix6 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix6 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix6 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix6 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_clam12 {s0 : sort6} {t0 : sort6} (H0 : s0 = t0) :
  clam12 s0 = clam12 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam12 x) H0)).

Qed.

Lemma congr_cmix7 {s0 : sort6} {s1 : sort7} {s2 : sort8} {s3 : sort9}
  {s4 : sort10} {s5 : sort11} {t0 : sort6} {t1 : sort7} {t2 : sort8}
  {t3 : sort9} {t4 : sort10} {t5 : sort11} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix7 s0 s1 s2 s3 s4 s5 = cmix7 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix7 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix7 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix7 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix7 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix7 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix7 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix8 {s0 : sort6} {s1 : sort7} {s2 : sort8} {s3 : sort9}
  {s4 : sort10} {s5 : sort11} {t0 : sort6} {t1 : sort7} {t2 : sort8}
  {t3 : sort9} {t4 : sort10} {t5 : sort11} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix8 s0 s1 s2 s3 s4 s5 = cmix8 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix8 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix8 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix8 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix8 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix8 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix8 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix9 {s0 : sort6} {s1 : sort7} {s2 : sort8} {s3 : sort9}
  {s4 : sort10} {s5 : sort11} {t0 : sort6} {t1 : sort7} {t2 : sort8}
  {t3 : sort9} {t4 : sort10} {t5 : sort11} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix9 s0 s1 s2 s3 s4 s5 = cmix9 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix9 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix9 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix9 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix9 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix9 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix9 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix10 {s0 : sort6} {s1 : sort7} {s2 : sort8} {s3 : sort9}
  {s4 : sort10} {s5 : sort11} {t0 : sort6} {t1 : sort7} {t2 : sort8}
  {t3 : sort9} {t4 : sort10} {t5 : sort11} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix10 s0 s1 s2 s3 s4 s5 = cmix10 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix10 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix10 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix10 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix10 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix10 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix10 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix11 {s0 : sort6} {s1 : sort7} {s2 : sort8} {s3 : sort9}
  {s4 : sort10} {s5 : sort11} {t0 : sort6} {t1 : sort7} {t2 : sort8}
  {t3 : sort9} {t4 : sort10} {t5 : sort11} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix11 s0 s1 s2 s3 s4 s5 = cmix11 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix11 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix11 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix11 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix11 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix11 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix11 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma upRen_sort11_sort11 (xi : nat -> nat) : nat -> nat.

Proof.
exact (up_ren xi).

Defined.

Fixpoint ren_sort6 (xi_sort11 : nat -> nat) (s : sort6)  : sort6 :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      cmix6 (ren_sort6 xi_sort11 s0) (ren_sort7 xi_sort11 s1)
        (ren_sort8 xi_sort11 s2) (ren_sort9 xi_sort11 s3)
        (ren_sort10 xi_sort11 s4) (ren_sort11 xi_sort11 s5)
  | clam12 s0 => clam12 (ren_sort6 (upRen_sort11_sort11 xi_sort11) s0)
  end
with ren_sort7 (xi_sort11 : nat -> nat) (s : sort7)  : sort7 :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      cmix7 (ren_sort6 xi_sort11 s0) (ren_sort7 xi_sort11 s1)
        (ren_sort8 xi_sort11 s2) (ren_sort9 xi_sort11 s3)
        (ren_sort10 xi_sort11 s4) (ren_sort11 xi_sort11 s5)
  end
with ren_sort8 (xi_sort11 : nat -> nat) (s : sort8)  : sort8 :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      cmix8 (ren_sort6 xi_sort11 s0) (ren_sort7 xi_sort11 s1)
        (ren_sort8 xi_sort11 s2) (ren_sort9 xi_sort11 s3)
        (ren_sort10 xi_sort11 s4) (ren_sort11 xi_sort11 s5)
  end
with ren_sort9 (xi_sort11 : nat -> nat) (s : sort9)  : sort9 :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      cmix9 (ren_sort6 xi_sort11 s0) (ren_sort7 xi_sort11 s1)
        (ren_sort8 xi_sort11 s2) (ren_sort9 xi_sort11 s3)
        (ren_sort10 xi_sort11 s4) (ren_sort11 xi_sort11 s5)
  end
with ren_sort10 (xi_sort11 : nat -> nat) (s : sort10)  : sort10 :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      cmix10 (ren_sort6 xi_sort11 s0) (ren_sort7 xi_sort11 s1)
        (ren_sort8 xi_sort11 s2) (ren_sort9 xi_sort11 s3)
        (ren_sort10 xi_sort11 s4) (ren_sort11 xi_sort11 s5)
  end
with ren_sort11 (xi_sort11 : nat -> nat) (s : sort11)  : sort11 :=
  match s with
  | var_sort11 s0 => var_sort11 (xi_sort11 s0)
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      cmix11 (ren_sort6 xi_sort11 s0) (ren_sort7 xi_sort11 s1)
        (ren_sort8 xi_sort11 s2) (ren_sort9 xi_sort11 s3)
        (ren_sort10 xi_sort11 s4) (ren_sort11 xi_sort11 s5)
  end.

Lemma up_sort11_sort11 (sigma : nat -> sort11) : nat -> sort11.

Proof.
exact (scons (var_sort11 var_zero) (funcomp (ren_sort11 shift) sigma)).

Defined.

Fixpoint subst_sort6 (sigma_sort11 : nat -> sort11) (s : sort6)  :
sort6 :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      cmix6 (subst_sort6 sigma_sort11 s0) (subst_sort7 sigma_sort11 s1)
        (subst_sort8 sigma_sort11 s2) (subst_sort9 sigma_sort11 s3)
        (subst_sort10 sigma_sort11 s4) (subst_sort11 sigma_sort11 s5)
  | clam12 s0 => clam12 (subst_sort6 (up_sort11_sort11 sigma_sort11) s0)
  end
with subst_sort7 (sigma_sort11 : nat -> sort11) (s : sort7)  :
sort7 :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      cmix7 (subst_sort6 sigma_sort11 s0) (subst_sort7 sigma_sort11 s1)
        (subst_sort8 sigma_sort11 s2) (subst_sort9 sigma_sort11 s3)
        (subst_sort10 sigma_sort11 s4) (subst_sort11 sigma_sort11 s5)
  end
with subst_sort8 (sigma_sort11 : nat -> sort11) (s : sort8)  :
sort8 :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      cmix8 (subst_sort6 sigma_sort11 s0) (subst_sort7 sigma_sort11 s1)
        (subst_sort8 sigma_sort11 s2) (subst_sort9 sigma_sort11 s3)
        (subst_sort10 sigma_sort11 s4) (subst_sort11 sigma_sort11 s5)
  end
with subst_sort9 (sigma_sort11 : nat -> sort11) (s : sort9)  :
sort9 :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      cmix9 (subst_sort6 sigma_sort11 s0) (subst_sort7 sigma_sort11 s1)
        (subst_sort8 sigma_sort11 s2) (subst_sort9 sigma_sort11 s3)
        (subst_sort10 sigma_sort11 s4) (subst_sort11 sigma_sort11 s5)
  end
with subst_sort10 (sigma_sort11 : nat -> sort11) (s : sort10)  :
sort10 :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      cmix10 (subst_sort6 sigma_sort11 s0) (subst_sort7 sigma_sort11 s1)
        (subst_sort8 sigma_sort11 s2) (subst_sort9 sigma_sort11 s3)
        (subst_sort10 sigma_sort11 s4) (subst_sort11 sigma_sort11 s5)
  end
with subst_sort11 (sigma_sort11 : nat -> sort11) (s : sort11)  :
sort11 :=
  match s with
  | var_sort11 s0 => sigma_sort11 s0
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      cmix11 (subst_sort6 sigma_sort11 s0) (subst_sort7 sigma_sort11 s1)
        (subst_sort8 sigma_sort11 s2) (subst_sort9 sigma_sort11 s3)
        (subst_sort10 sigma_sort11 s4) (subst_sort11 sigma_sort11 s5)
  end.

Lemma upId_sort11_sort11 (sigma : nat -> sort11)
  (Eq : forall x, sigma x = var_sort11 x) :
  forall x, up_sort11_sort11 sigma x = var_sort11 x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort11 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint idSubst_sort6 (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 x) (s : sort6) 
   : subst_sort6 sigma_sort11 s = s :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6 (idSubst_sort6 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort7 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort8 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s5)
  | clam12 s0 =>
      congr_clam12
        (idSubst_sort6 (up_sort11_sort11 sigma_sort11)
           (upId_sort11_sort11 _ Eq_sort11) s0)
  end
with idSubst_sort7 (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 x) (s : sort7) 
   : subst_sort7 sigma_sort11 s = s :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7 (idSubst_sort6 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort7 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort8 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s5)
  end
with idSubst_sort8 (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 x) (s : sort8) 
   : subst_sort8 sigma_sort11 s = s :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8 (idSubst_sort6 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort7 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort8 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s5)
  end
with idSubst_sort9 (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 x) (s : sort9) 
   : subst_sort9 sigma_sort11 s = s :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9 (idSubst_sort6 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort7 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort8 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s5)
  end
with idSubst_sort10 (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 x) (s : sort10) 
   : subst_sort10 sigma_sort11 s = s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10 (idSubst_sort6 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort7 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort8 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s5)
  end
with idSubst_sort11 (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = var_sort11 x) (s : sort11) 
   : subst_sort11 sigma_sort11 s = s :=
  match s with
  | var_sort11 s0 => Eq_sort11 s0
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11 (idSubst_sort6 sigma_sort11 Eq_sort11 s0)
        (idSubst_sort7 sigma_sort11 Eq_sort11 s1)
        (idSubst_sort8 sigma_sort11 Eq_sort11 s2)
        (idSubst_sort9 sigma_sort11 Eq_sort11 s3)
        (idSubst_sort10 sigma_sort11 Eq_sort11 s4)
        (idSubst_sort11 sigma_sort11 Eq_sort11 s5)
  end.

Lemma upExtRen_sort11_sort11 (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_sort11_sort11 xi x = upRen_sort11_sort11 zeta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap shift (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint extRen_sort6 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort6)  :
ren_sort6 xi_sort11 s = ren_sort6 zeta_sort11 s :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6 (extRen_sort6 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort7 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s5)
  | clam12 s0 =>
      congr_clam12
        (extRen_sort6 (upRen_sort11_sort11 xi_sort11)
           (upRen_sort11_sort11 zeta_sort11)
           (upExtRen_sort11_sort11 _ _ Eq_sort11) s0)
  end
with extRen_sort7 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort7)  :
ren_sort7 xi_sort11 s = ren_sort7 zeta_sort11 s :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7 (extRen_sort6 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort7 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s5)
  end
with extRen_sort8 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort8)  :
ren_sort8 xi_sort11 s = ren_sort8 zeta_sort11 s :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8 (extRen_sort6 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort7 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s5)
  end
with extRen_sort9 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort9)  :
ren_sort9 xi_sort11 s = ren_sort9 zeta_sort11 s :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9 (extRen_sort6 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort7 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s5)
  end
with extRen_sort10 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort10)  :
ren_sort10 xi_sort11 s = ren_sort10 zeta_sort11 s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10 (extRen_sort6 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort7 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s5)
  end
with extRen_sort11 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(Eq_sort11 : forall x, xi_sort11 x = zeta_sort11 x) (s : sort11)  :
ren_sort11 xi_sort11 s = ren_sort11 zeta_sort11 s :=
  match s with
  | var_sort11 s0 => ap var_sort11 (Eq_sort11 s0)
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11 (extRen_sort6 xi_sort11 zeta_sort11 Eq_sort11 s0)
        (extRen_sort7 xi_sort11 zeta_sort11 Eq_sort11 s1)
        (extRen_sort8 xi_sort11 zeta_sort11 Eq_sort11 s2)
        (extRen_sort9 xi_sort11 zeta_sort11 Eq_sort11 s3)
        (extRen_sort10 xi_sort11 zeta_sort11 Eq_sort11 s4)
        (extRen_sort11 xi_sort11 zeta_sort11 Eq_sort11 s5)
  end.

Lemma upExt_sort11_sort11 (sigma : nat -> sort11) (tau : nat -> sort11)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_sort11_sort11 sigma x = up_sort11_sort11 tau x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort11 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint ext_sort6 (sigma_sort11 : nat -> sort11)
(tau_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort6) 
   : subst_sort6 sigma_sort11 s = subst_sort6 tau_sort11 s :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6 (ext_sort6 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort7 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s5)
  | clam12 s0 =>
      congr_clam12
        (ext_sort6 (up_sort11_sort11 sigma_sort11)
           (up_sort11_sort11 tau_sort11) (upExt_sort11_sort11 _ _ Eq_sort11)
           s0)
  end
with ext_sort7 (sigma_sort11 : nat -> sort11) (tau_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort7) 
   : subst_sort7 sigma_sort11 s = subst_sort7 tau_sort11 s :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7 (ext_sort6 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort7 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s5)
  end
with ext_sort8 (sigma_sort11 : nat -> sort11) (tau_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort8) 
   : subst_sort8 sigma_sort11 s = subst_sort8 tau_sort11 s :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8 (ext_sort6 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort7 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s5)
  end
with ext_sort9 (sigma_sort11 : nat -> sort11) (tau_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort9) 
   : subst_sort9 sigma_sort11 s = subst_sort9 tau_sort11 s :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9 (ext_sort6 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort7 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s5)
  end
with ext_sort10 (sigma_sort11 : nat -> sort11) (tau_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort10) 
   : subst_sort10 sigma_sort11 s = subst_sort10 tau_sort11 s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10 (ext_sort6 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort7 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s5)
  end
with ext_sort11 (sigma_sort11 : nat -> sort11) (tau_sort11 : nat -> sort11)
(Eq_sort11 : forall x, sigma_sort11 x = tau_sort11 x) (s : sort11) 
   : subst_sort11 sigma_sort11 s = subst_sort11 tau_sort11 s :=
  match s with
  | var_sort11 s0 => Eq_sort11 s0
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11 (ext_sort6 sigma_sort11 tau_sort11 Eq_sort11 s0)
        (ext_sort7 sigma_sort11 tau_sort11 Eq_sort11 s1)
        (ext_sort8 sigma_sort11 tau_sort11 Eq_sort11 s2)
        (ext_sort9 sigma_sort11 tau_sort11 Eq_sort11 s3)
        (ext_sort10 sigma_sort11 tau_sort11 Eq_sort11 s4)
        (ext_sort11 sigma_sort11 tau_sort11 Eq_sort11 s5)
  end.

Lemma up_ren_ren_sort11_sort11 (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_sort11_sort11 zeta) (upRen_sort11_sort11 xi) x =
  upRen_sort11_sort11 rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Fixpoint compRenRen_sort6 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(rho_sort11 : nat -> nat)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort6)  :
ren_sort6 zeta_sort11 (ren_sort6 xi_sort11 s) = ren_sort6 rho_sort11 s :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6
        (compRenRen_sort6 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort7 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
  | clam12 s0 =>
      congr_clam12
        (compRenRen_sort6 (upRen_sort11_sort11 xi_sort11)
           (upRen_sort11_sort11 zeta_sort11) (upRen_sort11_sort11 rho_sort11)
           (up_ren_ren _ _ _ Eq_sort11) s0)
  end
with compRenRen_sort7 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(rho_sort11 : nat -> nat)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort7)  :
ren_sort7 zeta_sort11 (ren_sort7 xi_sort11 s) = ren_sort7 rho_sort11 s :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7
        (compRenRen_sort6 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort7 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
  end
with compRenRen_sort8 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(rho_sort11 : nat -> nat)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort8)  :
ren_sort8 zeta_sort11 (ren_sort8 xi_sort11 s) = ren_sort8 rho_sort11 s :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8
        (compRenRen_sort6 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort7 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
  end
with compRenRen_sort9 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(rho_sort11 : nat -> nat)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort9)  :
ren_sort9 zeta_sort11 (ren_sort9 xi_sort11 s) = ren_sort9 rho_sort11 s :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9
        (compRenRen_sort6 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort7 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
  end
with compRenRen_sort10 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(rho_sort11 : nat -> nat)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort10)  :
ren_sort10 zeta_sort11 (ren_sort10 xi_sort11 s) = ren_sort10 rho_sort11 s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10
        (compRenRen_sort6 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort7 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
  end
with compRenRen_sort11 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
(rho_sort11 : nat -> nat)
(Eq_sort11 : forall x, funcomp zeta_sort11 xi_sort11 x = rho_sort11 x)
(s : sort11)  :
ren_sort11 zeta_sort11 (ren_sort11 xi_sort11 s) = ren_sort11 rho_sort11 s :=
  match s with
  | var_sort11 s0 => ap var_sort11 (Eq_sort11 s0)
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11
        (compRenRen_sort6 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s0)
        (compRenRen_sort7 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s1)
        (compRenRen_sort8 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s2)
        (compRenRen_sort9 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s3)
        (compRenRen_sort10 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s4)
        (compRenRen_sort11 xi_sort11 zeta_sort11 rho_sort11 Eq_sort11 s5)
  end.

Lemma up_ren_subst_sort11_sort11 (xi : nat -> nat) (tau : nat -> sort11)
  (theta : nat -> sort11) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_sort11_sort11 tau) (upRen_sort11_sort11 xi) x =
  up_sort11_sort11 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort11 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint compRenSubst_sort6 (xi_sort11 : nat -> nat)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort6)  :
subst_sort6 tau_sort11 (ren_sort6 xi_sort11 s) = subst_sort6 theta_sort11 s
:=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6
        (compRenSubst_sort6 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort7 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
  | clam12 s0 =>
      congr_clam12
        (compRenSubst_sort6 (upRen_sort11_sort11 xi_sort11)
           (up_sort11_sort11 tau_sort11) (up_sort11_sort11 theta_sort11)
           (up_ren_subst_sort11_sort11 _ _ _ Eq_sort11) s0)
  end
with compRenSubst_sort7 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
(theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort7)  :
subst_sort7 tau_sort11 (ren_sort7 xi_sort11 s) = subst_sort7 theta_sort11 s
:=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7
        (compRenSubst_sort6 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort7 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
  end
with compRenSubst_sort8 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
(theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort8)  :
subst_sort8 tau_sort11 (ren_sort8 xi_sort11 s) = subst_sort8 theta_sort11 s
:=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8
        (compRenSubst_sort6 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort7 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
  end
with compRenSubst_sort9 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
(theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort9)  :
subst_sort9 tau_sort11 (ren_sort9 xi_sort11 s) = subst_sort9 theta_sort11 s
:=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9
        (compRenSubst_sort6 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort7 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
  end
with compRenSubst_sort10 (xi_sort11 : nat -> nat)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort10)  :
subst_sort10 tau_sort11 (ren_sort10 xi_sort11 s) =
subst_sort10 theta_sort11 s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10
        (compRenSubst_sort6 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort7 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
  end
with compRenSubst_sort11 (xi_sort11 : nat -> nat)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp tau_sort11 xi_sort11 x = theta_sort11 x)
(s : sort11)  :
subst_sort11 tau_sort11 (ren_sort11 xi_sort11 s) =
subst_sort11 theta_sort11 s :=
  match s with
  | var_sort11 s0 => Eq_sort11 s0
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11
        (compRenSubst_sort6 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s0)
        (compRenSubst_sort7 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s1)
        (compRenSubst_sort8 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s2)
        (compRenSubst_sort9 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s3)
        (compRenSubst_sort10 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s4)
        (compRenSubst_sort11 xi_sort11 tau_sort11 theta_sort11 Eq_sort11 s5)
  end.

Lemma up_subst_ren_sort11_sort11 (sigma : nat -> sort11)
  (zeta_sort11 : nat -> nat) (theta : nat -> sort11)
  (Eq : forall x, funcomp (ren_sort11 zeta_sort11) sigma x = theta x) :
  forall x,
  funcomp (ren_sort11 (upRen_sort11_sort11 zeta_sort11))
    (up_sort11_sort11 sigma) x = up_sort11_sort11 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenRen_sort11 shift
                       (upRen_sort11_sort11 zeta_sort11)
                       (funcomp shift zeta_sort11) (fun x => eq_refl)
                       (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compRenRen_sort11 zeta_sort11 shift
                             (funcomp shift zeta_sort11) (fun x => eq_refl)
                             (sigma n'))) (ap (ren_sort11 shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstRen_sort6 (sigma_sort11 : nat -> sort11)
(zeta_sort11 : nat -> nat) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort6)  :
ren_sort6 zeta_sort11 (subst_sort6 sigma_sort11 s) =
subst_sort6 theta_sort11 s :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6
        (compSubstRen_sort6 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort7 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
  | clam12 s0 =>
      congr_clam12
        (compSubstRen_sort6 (up_sort11_sort11 sigma_sort11)
           (upRen_sort11_sort11 zeta_sort11) (up_sort11_sort11 theta_sort11)
           (up_subst_ren_sort11_sort11 _ _ _ Eq_sort11) s0)
  end
with compSubstRen_sort7 (sigma_sort11 : nat -> sort11)
(zeta_sort11 : nat -> nat) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort7)  :
ren_sort7 zeta_sort11 (subst_sort7 sigma_sort11 s) =
subst_sort7 theta_sort11 s :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7
        (compSubstRen_sort6 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort7 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstRen_sort8 (sigma_sort11 : nat -> sort11)
(zeta_sort11 : nat -> nat) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort8)  :
ren_sort8 zeta_sort11 (subst_sort8 sigma_sort11 s) =
subst_sort8 theta_sort11 s :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8
        (compSubstRen_sort6 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort7 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstRen_sort9 (sigma_sort11 : nat -> sort11)
(zeta_sort11 : nat -> nat) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort9)  :
ren_sort9 zeta_sort11 (subst_sort9 sigma_sort11 s) =
subst_sort9 theta_sort11 s :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9
        (compSubstRen_sort6 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort7 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstRen_sort10 (sigma_sort11 : nat -> sort11)
(zeta_sort11 : nat -> nat) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort10)  :
ren_sort10 zeta_sort11 (subst_sort10 sigma_sort11 s) =
subst_sort10 theta_sort11 s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10
        (compSubstRen_sort6 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort7 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstRen_sort11 (sigma_sort11 : nat -> sort11)
(zeta_sort11 : nat -> nat) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (ren_sort11 zeta_sort11) sigma_sort11 x = theta_sort11 x)
(s : sort11)  :
ren_sort11 zeta_sort11 (subst_sort11 sigma_sort11 s) =
subst_sort11 theta_sort11 s :=
  match s with
  | var_sort11 s0 => Eq_sort11 s0
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11
        (compSubstRen_sort6 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstRen_sort7 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstRen_sort8 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstRen_sort9 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstRen_sort10 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstRen_sort11 sigma_sort11 zeta_sort11 theta_sort11 Eq_sort11
           s5)
  end.

Lemma up_subst_subst_sort11_sort11 (sigma : nat -> sort11)
  (tau_sort11 : nat -> sort11) (theta : nat -> sort11)
  (Eq : forall x, funcomp (subst_sort11 tau_sort11) sigma x = theta x) :
  forall x,
  funcomp (subst_sort11 (up_sort11_sort11 tau_sort11))
    (up_sort11_sort11 sigma) x = up_sort11_sort11 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenSubst_sort11 shift (up_sort11_sort11 tau_sort11)
                       (funcomp (up_sort11_sort11 tau_sort11) shift)
                       (fun x => eq_refl) (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_sort11 tau_sort11 shift
                             (funcomp (ren_sort11 shift) tau_sort11)
                             (fun x => eq_refl) (sigma n')))
                       (ap (ren_sort11 shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstSubst_sort6 (sigma_sort11 : nat -> sort11)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort6)  :
subst_sort6 tau_sort11 (subst_sort6 sigma_sort11 s) =
subst_sort6 theta_sort11 s :=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6
        (compSubstSubst_sort6 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort7 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
  | clam12 s0 =>
      congr_clam12
        (compSubstSubst_sort6 (up_sort11_sort11 sigma_sort11)
           (up_sort11_sort11 tau_sort11) (up_sort11_sort11 theta_sort11)
           (up_subst_subst_sort11_sort11 _ _ _ Eq_sort11) s0)
  end
with compSubstSubst_sort7 (sigma_sort11 : nat -> sort11)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort7)  :
subst_sort7 tau_sort11 (subst_sort7 sigma_sort11 s) =
subst_sort7 theta_sort11 s :=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7
        (compSubstSubst_sort6 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort7 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstSubst_sort8 (sigma_sort11 : nat -> sort11)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort8)  :
subst_sort8 tau_sort11 (subst_sort8 sigma_sort11 s) =
subst_sort8 theta_sort11 s :=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8
        (compSubstSubst_sort6 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort7 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstSubst_sort9 (sigma_sort11 : nat -> sort11)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort9)  :
subst_sort9 tau_sort11 (subst_sort9 sigma_sort11 s) =
subst_sort9 theta_sort11 s :=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9
        (compSubstSubst_sort6 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort7 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstSubst_sort10 (sigma_sort11 : nat -> sort11)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort10)  :
subst_sort10 tau_sort11 (subst_sort10 sigma_sort11 s) =
subst_sort10 theta_sort11 s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10
        (compSubstSubst_sort6 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort7 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
  end
with compSubstSubst_sort11 (sigma_sort11 : nat -> sort11)
(tau_sort11 : nat -> sort11) (theta_sort11 : nat -> sort11)
(Eq_sort11 : forall x,
             funcomp (subst_sort11 tau_sort11) sigma_sort11 x =
             theta_sort11 x) (s : sort11)  :
subst_sort11 tau_sort11 (subst_sort11 sigma_sort11 s) =
subst_sort11 theta_sort11 s :=
  match s with
  | var_sort11 s0 => Eq_sort11 s0
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11
        (compSubstSubst_sort6 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s0)
        (compSubstSubst_sort7 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s1)
        (compSubstSubst_sort8 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s2)
        (compSubstSubst_sort9 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s3)
        (compSubstSubst_sort10 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s4)
        (compSubstSubst_sort11 sigma_sort11 tau_sort11 theta_sort11 Eq_sort11
           s5)
  end.

Lemma rinstInst_up_sort11_sort11 (xi : nat -> nat) (sigma : nat -> sort11)
  (Eq : forall x, funcomp var_sort11 xi x = sigma x) :
  forall x,
  funcomp var_sort11 (upRen_sort11_sort11 xi) x = up_sort11_sort11 sigma x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort11 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint rinst_inst_sort6 (xi_sort11 : nat -> nat)
(sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp var_sort11 xi_sort11 x = sigma_sort11 x)
(s : sort6)  : ren_sort6 xi_sort11 s = subst_sort6 sigma_sort11 s
:=
  match s with
  | cmix6 s0 s1 s2 s3 s4 s5 =>
      congr_cmix6 (rinst_inst_sort6 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort7 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s5)
  | clam12 s0 =>
      congr_clam12
        (rinst_inst_sort6 (upRen_sort11_sort11 xi_sort11)
           (up_sort11_sort11 sigma_sort11)
           (rinstInst_up_sort11_sort11 _ _ Eq_sort11) s0)
  end
with rinst_inst_sort7 (xi_sort11 : nat -> nat) (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp var_sort11 xi_sort11 x = sigma_sort11 x)
(s : sort7)  : ren_sort7 xi_sort11 s = subst_sort7 sigma_sort11 s
:=
  match s with
  | cmix7 s0 s1 s2 s3 s4 s5 =>
      congr_cmix7 (rinst_inst_sort6 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort7 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s5)
  end
with rinst_inst_sort8 (xi_sort11 : nat -> nat) (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp var_sort11 xi_sort11 x = sigma_sort11 x)
(s : sort8)  : ren_sort8 xi_sort11 s = subst_sort8 sigma_sort11 s
:=
  match s with
  | cmix8 s0 s1 s2 s3 s4 s5 =>
      congr_cmix8 (rinst_inst_sort6 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort7 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s5)
  end
with rinst_inst_sort9 (xi_sort11 : nat -> nat) (sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp var_sort11 xi_sort11 x = sigma_sort11 x)
(s : sort9)  : ren_sort9 xi_sort11 s = subst_sort9 sigma_sort11 s
:=
  match s with
  | cmix9 s0 s1 s2 s3 s4 s5 =>
      congr_cmix9 (rinst_inst_sort6 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort7 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s5)
  end
with rinst_inst_sort10 (xi_sort11 : nat -> nat)
(sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp var_sort11 xi_sort11 x = sigma_sort11 x)
(s : sort10)  :
ren_sort10 xi_sort11 s = subst_sort10 sigma_sort11 s :=
  match s with
  | cmix10 s0 s1 s2 s3 s4 s5 =>
      congr_cmix10 (rinst_inst_sort6 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort7 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s5)
  end
with rinst_inst_sort11 (xi_sort11 : nat -> nat)
(sigma_sort11 : nat -> sort11)
(Eq_sort11 : forall x, funcomp var_sort11 xi_sort11 x = sigma_sort11 x)
(s : sort11)  :
ren_sort11 xi_sort11 s = subst_sort11 sigma_sort11 s :=
  match s with
  | var_sort11 s0 => Eq_sort11 s0
  | cmix11 s0 s1 s2 s3 s4 s5 =>
      congr_cmix11 (rinst_inst_sort6 xi_sort11 sigma_sort11 Eq_sort11 s0)
        (rinst_inst_sort7 xi_sort11 sigma_sort11 Eq_sort11 s1)
        (rinst_inst_sort8 xi_sort11 sigma_sort11 Eq_sort11 s2)
        (rinst_inst_sort9 xi_sort11 sigma_sort11 Eq_sort11 s3)
        (rinst_inst_sort10 xi_sort11 sigma_sort11 Eq_sort11 s4)
        (rinst_inst_sort11 xi_sort11 sigma_sort11 Eq_sort11 s5)
  end.

Lemma renRen_sort6 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
  (s : sort6) :
  ren_sort6 zeta_sort11 (ren_sort6 xi_sort11 s) =
  ren_sort6 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort6 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort7 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
  (s : sort7) :
  ren_sort7 zeta_sort11 (ren_sort7 xi_sort11 s) =
  ren_sort7 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort7 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort8 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
  (s : sort8) :
  ren_sort8 zeta_sort11 (ren_sort8 xi_sort11 s) =
  ren_sort8 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort8 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort9 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
  (s : sort9) :
  ren_sort9 zeta_sort11 (ren_sort9 xi_sort11 s) =
  ren_sort9 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort9 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort10 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
  (s : sort10) :
  ren_sort10 zeta_sort11 (ren_sort10 xi_sort11 s) =
  ren_sort10 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort10 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort11 (xi_sort11 : nat -> nat) (zeta_sort11 : nat -> nat)
  (s : sort11) :
  ren_sort11 zeta_sort11 (ren_sort11 xi_sort11 s) =
  ren_sort11 (funcomp zeta_sort11 xi_sort11) s.

Proof.
exact (compRenRen_sort11 xi_sort11 zeta_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma compRen_sort6 (sigma_sort11 : nat -> sort11) (zeta_sort11 : nat -> nat)
  (s : sort6) :
  ren_sort6 zeta_sort11 (subst_sort6 sigma_sort11 s) =
  subst_sort6 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort6 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort7 (sigma_sort11 : nat -> sort11) (zeta_sort11 : nat -> nat)
  (s : sort7) :
  ren_sort7 zeta_sort11 (subst_sort7 sigma_sort11 s) =
  subst_sort7 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort7 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort8 (sigma_sort11 : nat -> sort11) (zeta_sort11 : nat -> nat)
  (s : sort8) :
  ren_sort8 zeta_sort11 (subst_sort8 sigma_sort11 s) =
  subst_sort8 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort8 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort9 (sigma_sort11 : nat -> sort11) (zeta_sort11 : nat -> nat)
  (s : sort9) :
  ren_sort9 zeta_sort11 (subst_sort9 sigma_sort11 s) =
  subst_sort9 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort9 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort10 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) (s : sort10) :
  ren_sort10 zeta_sort11 (subst_sort10 sigma_sort11 s) =
  subst_sort10 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort10 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort11 (sigma_sort11 : nat -> sort11)
  (zeta_sort11 : nat -> nat) (s : sort11) :
  ren_sort11 zeta_sort11 (subst_sort11 sigma_sort11 s) =
  subst_sort11 (funcomp (ren_sort11 zeta_sort11) sigma_sort11) s.

Proof.
exact (compSubstRen_sort11 sigma_sort11 zeta_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma renComp_sort6 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
  (s : sort6) :
  subst_sort6 tau_sort11 (ren_sort6 xi_sort11 s) =
  subst_sort6 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort6 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort7 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
  (s : sort7) :
  subst_sort7 tau_sort11 (ren_sort7 xi_sort11 s) =
  subst_sort7 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort7 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort8 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
  (s : sort8) :
  subst_sort8 tau_sort11 (ren_sort8 xi_sort11 s) =
  subst_sort8 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort8 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort9 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
  (s : sort9) :
  subst_sort9 tau_sort11 (ren_sort9 xi_sort11 s) =
  subst_sort9 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort9 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort10 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
  (s : sort10) :
  subst_sort10 tau_sort11 (ren_sort10 xi_sort11 s) =
  subst_sort10 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort10 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort11 (xi_sort11 : nat -> nat) (tau_sort11 : nat -> sort11)
  (s : sort11) :
  subst_sort11 tau_sort11 (ren_sort11 xi_sort11 s) =
  subst_sort11 (funcomp tau_sort11 xi_sort11) s.

Proof.
exact (compRenSubst_sort11 xi_sort11 tau_sort11 _ (fun n => eq_refl) s).

Qed.

Lemma compComp_sort6 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) (s : sort6) :
  subst_sort6 tau_sort11 (subst_sort6 sigma_sort11 s) =
  subst_sort6 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort6 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort7 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) (s : sort7) :
  subst_sort7 tau_sort11 (subst_sort7 sigma_sort11 s) =
  subst_sort7 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort7 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort8 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) (s : sort8) :
  subst_sort8 tau_sort11 (subst_sort8 sigma_sort11 s) =
  subst_sort8 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort8 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort9 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) (s : sort9) :
  subst_sort9 tau_sort11 (subst_sort9 sigma_sort11 s) =
  subst_sort9 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort9 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort10 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) (s : sort10) :
  subst_sort10 tau_sort11 (subst_sort10 sigma_sort11 s) =
  subst_sort10 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort10 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort11 (sigma_sort11 : nat -> sort11)
  (tau_sort11 : nat -> sort11) (s : sort11) :
  subst_sort11 tau_sort11 (subst_sort11 sigma_sort11 s) =
  subst_sort11 (funcomp (subst_sort11 tau_sort11) sigma_sort11) s.

Proof.
exact (compSubstSubst_sort11 sigma_sort11 tau_sort11 _
                (fun n => eq_refl) s).

Qed.

Inductive sort12 : Type :=
  | var_sort12 : nat -> sort12
  | cmix12 :
      sort12 -> sort13 -> sort14 -> sort15 -> sort16 -> sort17 -> sort12
with sort13 : Type :=
    cmix13 :
      sort12 -> sort13 -> sort14 -> sort15 -> sort16 -> sort17 -> sort13
with sort14 : Type :=
    cmix14 :
      sort12 -> sort13 -> sort14 -> sort15 -> sort16 -> sort17 -> sort14
with sort15 : Type :=
    cmix15 :
      sort12 -> sort13 -> sort14 -> sort15 -> sort16 -> sort17 -> sort15
with sort16 : Type :=
  | cmix16 :
      sort12 -> sort13 -> sort14 -> sort15 -> sort16 -> sort17 -> sort16
  | clam18 : sort12 -> sort16
with sort17 : Type :=
    cmix17 :
      sort12 -> sort13 -> sort14 -> sort15 -> sort16 -> sort17 -> sort17.

Lemma congr_cmix12 {s0 : sort12} {s1 : sort13} {s2 : sort14} {s3 : sort15}
  {s4 : sort16} {s5 : sort17} {t0 : sort12} {t1 : sort13} {t2 : sort14}
  {t3 : sort15} {t4 : sort16} {t5 : sort17} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix12 s0 s1 s2 s3 s4 s5 = cmix12 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix12 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix12 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix12 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix12 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix12 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix12 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix13 {s0 : sort12} {s1 : sort13} {s2 : sort14} {s3 : sort15}
  {s4 : sort16} {s5 : sort17} {t0 : sort12} {t1 : sort13} {t2 : sort14}
  {t3 : sort15} {t4 : sort16} {t5 : sort17} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix13 s0 s1 s2 s3 s4 s5 = cmix13 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix13 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix13 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix13 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix13 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix13 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix13 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix14 {s0 : sort12} {s1 : sort13} {s2 : sort14} {s3 : sort15}
  {s4 : sort16} {s5 : sort17} {t0 : sort12} {t1 : sort13} {t2 : sort14}
  {t3 : sort15} {t4 : sort16} {t5 : sort17} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix14 s0 s1 s2 s3 s4 s5 = cmix14 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix14 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix14 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix14 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix14 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix14 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix14 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix15 {s0 : sort12} {s1 : sort13} {s2 : sort14} {s3 : sort15}
  {s4 : sort16} {s5 : sort17} {t0 : sort12} {t1 : sort13} {t2 : sort14}
  {t3 : sort15} {t4 : sort16} {t5 : sort17} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix15 s0 s1 s2 s3 s4 s5 = cmix15 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix15 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix15 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix15 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix15 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix15 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix15 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_cmix16 {s0 : sort12} {s1 : sort13} {s2 : sort14} {s3 : sort15}
  {s4 : sort16} {s5 : sort17} {t0 : sort12} {t1 : sort13} {t2 : sort14}
  {t3 : sort15} {t4 : sort16} {t5 : sort17} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix16 s0 s1 s2 s3 s4 s5 = cmix16 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix16 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix16 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix16 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix16 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix16 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix16 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma congr_clam18 {s0 : sort12} {t0 : sort12} (H0 : s0 = t0) :
  clam18 s0 = clam18 t0.

Proof.
exact (eq_trans eq_refl (ap (fun x => clam18 x) H0)).

Qed.

Lemma congr_cmix17 {s0 : sort12} {s1 : sort13} {s2 : sort14} {s3 : sort15}
  {s4 : sort16} {s5 : sort17} {t0 : sort12} {t1 : sort13} {t2 : sort14}
  {t3 : sort15} {t4 : sort16} {t5 : sort17} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4) (H5 : s5 = t5) :
  cmix17 s0 s1 s2 s3 s4 s5 = cmix17 t0 t1 t2 t3 t4 t5.

Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans
                      (eq_trans
                         (eq_trans
                            (eq_trans eq_refl
                               (ap (fun x => cmix17 x s1 s2 s3 s4 s5) H0))
                            (ap (fun x => cmix17 t0 x s2 s3 s4 s5) H1))
                         (ap (fun x => cmix17 t0 t1 x s3 s4 s5) H2))
                      (ap (fun x => cmix17 t0 t1 t2 x s4 s5) H3))
                   (ap (fun x => cmix17 t0 t1 t2 t3 x s5) H4))
                (ap (fun x => cmix17 t0 t1 t2 t3 t4 x) H5)).

Qed.

Lemma upRen_sort12_sort12 (xi : nat -> nat) : nat -> nat.

Proof.
exact (up_ren xi).

Defined.

Fixpoint ren_sort12 (xi_sort12 : nat -> nat) (s : sort12)  : sort12
:=
  match s with
  | var_sort12 s0 => var_sort12 (xi_sort12 s0)
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      cmix12 (ren_sort12 xi_sort12 s0) (ren_sort13 xi_sort12 s1)
        (ren_sort14 xi_sort12 s2) (ren_sort15 xi_sort12 s3)
        (ren_sort16 xi_sort12 s4) (ren_sort17 xi_sort12 s5)
  end
with ren_sort13 (xi_sort12 : nat -> nat) (s : sort13)  : sort13 :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      cmix13 (ren_sort12 xi_sort12 s0) (ren_sort13 xi_sort12 s1)
        (ren_sort14 xi_sort12 s2) (ren_sort15 xi_sort12 s3)
        (ren_sort16 xi_sort12 s4) (ren_sort17 xi_sort12 s5)
  end
with ren_sort14 (xi_sort12 : nat -> nat) (s : sort14)  : sort14 :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      cmix14 (ren_sort12 xi_sort12 s0) (ren_sort13 xi_sort12 s1)
        (ren_sort14 xi_sort12 s2) (ren_sort15 xi_sort12 s3)
        (ren_sort16 xi_sort12 s4) (ren_sort17 xi_sort12 s5)
  end
with ren_sort15 (xi_sort12 : nat -> nat) (s : sort15)  : sort15 :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      cmix15 (ren_sort12 xi_sort12 s0) (ren_sort13 xi_sort12 s1)
        (ren_sort14 xi_sort12 s2) (ren_sort15 xi_sort12 s3)
        (ren_sort16 xi_sort12 s4) (ren_sort17 xi_sort12 s5)
  end
with ren_sort16 (xi_sort12 : nat -> nat) (s : sort16)  : sort16 :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      cmix16 (ren_sort12 xi_sort12 s0) (ren_sort13 xi_sort12 s1)
        (ren_sort14 xi_sort12 s2) (ren_sort15 xi_sort12 s3)
        (ren_sort16 xi_sort12 s4) (ren_sort17 xi_sort12 s5)
  | clam18 s0 => clam18 (ren_sort12 (upRen_sort12_sort12 xi_sort12) s0)
  end
with ren_sort17 (xi_sort12 : nat -> nat) (s : sort17)  : sort17 :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      cmix17 (ren_sort12 xi_sort12 s0) (ren_sort13 xi_sort12 s1)
        (ren_sort14 xi_sort12 s2) (ren_sort15 xi_sort12 s3)
        (ren_sort16 xi_sort12 s4) (ren_sort17 xi_sort12 s5)
  end.

Lemma up_sort12_sort12 (sigma : nat -> sort12) : nat -> sort12.

Proof.
exact (scons (var_sort12 var_zero) (funcomp (ren_sort12 shift) sigma)).

Defined.

Fixpoint subst_sort12 (sigma_sort12 : nat -> sort12) (s : sort12) 
   : sort12 :=
  match s with
  | var_sort12 s0 => sigma_sort12 s0
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      cmix12 (subst_sort12 sigma_sort12 s0) (subst_sort13 sigma_sort12 s1)
        (subst_sort14 sigma_sort12 s2) (subst_sort15 sigma_sort12 s3)
        (subst_sort16 sigma_sort12 s4) (subst_sort17 sigma_sort12 s5)
  end
with subst_sort13 (sigma_sort12 : nat -> sort12) (s : sort13)  :
sort13 :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      cmix13 (subst_sort12 sigma_sort12 s0) (subst_sort13 sigma_sort12 s1)
        (subst_sort14 sigma_sort12 s2) (subst_sort15 sigma_sort12 s3)
        (subst_sort16 sigma_sort12 s4) (subst_sort17 sigma_sort12 s5)
  end
with subst_sort14 (sigma_sort12 : nat -> sort12) (s : sort14)  :
sort14 :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      cmix14 (subst_sort12 sigma_sort12 s0) (subst_sort13 sigma_sort12 s1)
        (subst_sort14 sigma_sort12 s2) (subst_sort15 sigma_sort12 s3)
        (subst_sort16 sigma_sort12 s4) (subst_sort17 sigma_sort12 s5)
  end
with subst_sort15 (sigma_sort12 : nat -> sort12) (s : sort15)  :
sort15 :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      cmix15 (subst_sort12 sigma_sort12 s0) (subst_sort13 sigma_sort12 s1)
        (subst_sort14 sigma_sort12 s2) (subst_sort15 sigma_sort12 s3)
        (subst_sort16 sigma_sort12 s4) (subst_sort17 sigma_sort12 s5)
  end
with subst_sort16 (sigma_sort12 : nat -> sort12) (s : sort16)  :
sort16 :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      cmix16 (subst_sort12 sigma_sort12 s0) (subst_sort13 sigma_sort12 s1)
        (subst_sort14 sigma_sort12 s2) (subst_sort15 sigma_sort12 s3)
        (subst_sort16 sigma_sort12 s4) (subst_sort17 sigma_sort12 s5)
  | clam18 s0 => clam18 (subst_sort12 (up_sort12_sort12 sigma_sort12) s0)
  end
with subst_sort17 (sigma_sort12 : nat -> sort12) (s : sort17)  :
sort17 :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      cmix17 (subst_sort12 sigma_sort12 s0) (subst_sort13 sigma_sort12 s1)
        (subst_sort14 sigma_sort12 s2) (subst_sort15 sigma_sort12 s3)
        (subst_sort16 sigma_sort12 s4) (subst_sort17 sigma_sort12 s5)
  end.

Lemma upId_sort12_sort12 (sigma : nat -> sort12)
  (Eq : forall x, sigma x = var_sort12 x) :
  forall x, up_sort12_sort12 sigma x = var_sort12 x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort12 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint idSubst_sort12 (sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = var_sort12 x) (s : sort12) 
   : subst_sort12 sigma_sort12 s = s :=
  match s with
  | var_sort12 s0 => Eq_sort12 s0
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12 (idSubst_sort12 sigma_sort12 Eq_sort12 s0)
        (idSubst_sort13 sigma_sort12 Eq_sort12 s1)
        (idSubst_sort14 sigma_sort12 Eq_sort12 s2)
        (idSubst_sort15 sigma_sort12 Eq_sort12 s3)
        (idSubst_sort16 sigma_sort12 Eq_sort12 s4)
        (idSubst_sort17 sigma_sort12 Eq_sort12 s5)
  end
with idSubst_sort13 (sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = var_sort12 x) (s : sort13) 
   : subst_sort13 sigma_sort12 s = s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13 (idSubst_sort12 sigma_sort12 Eq_sort12 s0)
        (idSubst_sort13 sigma_sort12 Eq_sort12 s1)
        (idSubst_sort14 sigma_sort12 Eq_sort12 s2)
        (idSubst_sort15 sigma_sort12 Eq_sort12 s3)
        (idSubst_sort16 sigma_sort12 Eq_sort12 s4)
        (idSubst_sort17 sigma_sort12 Eq_sort12 s5)
  end
with idSubst_sort14 (sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = var_sort12 x) (s : sort14) 
   : subst_sort14 sigma_sort12 s = s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14 (idSubst_sort12 sigma_sort12 Eq_sort12 s0)
        (idSubst_sort13 sigma_sort12 Eq_sort12 s1)
        (idSubst_sort14 sigma_sort12 Eq_sort12 s2)
        (idSubst_sort15 sigma_sort12 Eq_sort12 s3)
        (idSubst_sort16 sigma_sort12 Eq_sort12 s4)
        (idSubst_sort17 sigma_sort12 Eq_sort12 s5)
  end
with idSubst_sort15 (sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = var_sort12 x) (s : sort15) 
   : subst_sort15 sigma_sort12 s = s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15 (idSubst_sort12 sigma_sort12 Eq_sort12 s0)
        (idSubst_sort13 sigma_sort12 Eq_sort12 s1)
        (idSubst_sort14 sigma_sort12 Eq_sort12 s2)
        (idSubst_sort15 sigma_sort12 Eq_sort12 s3)
        (idSubst_sort16 sigma_sort12 Eq_sort12 s4)
        (idSubst_sort17 sigma_sort12 Eq_sort12 s5)
  end
with idSubst_sort16 (sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = var_sort12 x) (s : sort16) 
   : subst_sort16 sigma_sort12 s = s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16 (idSubst_sort12 sigma_sort12 Eq_sort12 s0)
        (idSubst_sort13 sigma_sort12 Eq_sort12 s1)
        (idSubst_sort14 sigma_sort12 Eq_sort12 s2)
        (idSubst_sort15 sigma_sort12 Eq_sort12 s3)
        (idSubst_sort16 sigma_sort12 Eq_sort12 s4)
        (idSubst_sort17 sigma_sort12 Eq_sort12 s5)
  | clam18 s0 =>
      congr_clam18
        (idSubst_sort12 (up_sort12_sort12 sigma_sort12)
           (upId_sort12_sort12 _ Eq_sort12) s0)
  end
with idSubst_sort17 (sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = var_sort12 x) (s : sort17) 
   : subst_sort17 sigma_sort12 s = s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17 (idSubst_sort12 sigma_sort12 Eq_sort12 s0)
        (idSubst_sort13 sigma_sort12 Eq_sort12 s1)
        (idSubst_sort14 sigma_sort12 Eq_sort12 s2)
        (idSubst_sort15 sigma_sort12 Eq_sort12 s3)
        (idSubst_sort16 sigma_sort12 Eq_sort12 s4)
        (idSubst_sort17 sigma_sort12 Eq_sort12 s5)
  end.

Lemma upExtRen_sort12_sort12 (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_sort12_sort12 xi x = upRen_sort12_sort12 zeta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap shift (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint extRen_sort12 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(Eq_sort12 : forall x, xi_sort12 x = zeta_sort12 x) (s : sort12)  :
ren_sort12 xi_sort12 s = ren_sort12 zeta_sort12 s :=
  match s with
  | var_sort12 s0 => ap var_sort12 (Eq_sort12 s0)
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12 (extRen_sort12 xi_sort12 zeta_sort12 Eq_sort12 s0)
        (extRen_sort13 xi_sort12 zeta_sort12 Eq_sort12 s1)
        (extRen_sort14 xi_sort12 zeta_sort12 Eq_sort12 s2)
        (extRen_sort15 xi_sort12 zeta_sort12 Eq_sort12 s3)
        (extRen_sort16 xi_sort12 zeta_sort12 Eq_sort12 s4)
        (extRen_sort17 xi_sort12 zeta_sort12 Eq_sort12 s5)
  end
with extRen_sort13 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(Eq_sort12 : forall x, xi_sort12 x = zeta_sort12 x) (s : sort13)  :
ren_sort13 xi_sort12 s = ren_sort13 zeta_sort12 s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13 (extRen_sort12 xi_sort12 zeta_sort12 Eq_sort12 s0)
        (extRen_sort13 xi_sort12 zeta_sort12 Eq_sort12 s1)
        (extRen_sort14 xi_sort12 zeta_sort12 Eq_sort12 s2)
        (extRen_sort15 xi_sort12 zeta_sort12 Eq_sort12 s3)
        (extRen_sort16 xi_sort12 zeta_sort12 Eq_sort12 s4)
        (extRen_sort17 xi_sort12 zeta_sort12 Eq_sort12 s5)
  end
with extRen_sort14 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(Eq_sort12 : forall x, xi_sort12 x = zeta_sort12 x) (s : sort14)  :
ren_sort14 xi_sort12 s = ren_sort14 zeta_sort12 s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14 (extRen_sort12 xi_sort12 zeta_sort12 Eq_sort12 s0)
        (extRen_sort13 xi_sort12 zeta_sort12 Eq_sort12 s1)
        (extRen_sort14 xi_sort12 zeta_sort12 Eq_sort12 s2)
        (extRen_sort15 xi_sort12 zeta_sort12 Eq_sort12 s3)
        (extRen_sort16 xi_sort12 zeta_sort12 Eq_sort12 s4)
        (extRen_sort17 xi_sort12 zeta_sort12 Eq_sort12 s5)
  end
with extRen_sort15 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(Eq_sort12 : forall x, xi_sort12 x = zeta_sort12 x) (s : sort15)  :
ren_sort15 xi_sort12 s = ren_sort15 zeta_sort12 s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15 (extRen_sort12 xi_sort12 zeta_sort12 Eq_sort12 s0)
        (extRen_sort13 xi_sort12 zeta_sort12 Eq_sort12 s1)
        (extRen_sort14 xi_sort12 zeta_sort12 Eq_sort12 s2)
        (extRen_sort15 xi_sort12 zeta_sort12 Eq_sort12 s3)
        (extRen_sort16 xi_sort12 zeta_sort12 Eq_sort12 s4)
        (extRen_sort17 xi_sort12 zeta_sort12 Eq_sort12 s5)
  end
with extRen_sort16 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(Eq_sort12 : forall x, xi_sort12 x = zeta_sort12 x) (s : sort16)  :
ren_sort16 xi_sort12 s = ren_sort16 zeta_sort12 s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16 (extRen_sort12 xi_sort12 zeta_sort12 Eq_sort12 s0)
        (extRen_sort13 xi_sort12 zeta_sort12 Eq_sort12 s1)
        (extRen_sort14 xi_sort12 zeta_sort12 Eq_sort12 s2)
        (extRen_sort15 xi_sort12 zeta_sort12 Eq_sort12 s3)
        (extRen_sort16 xi_sort12 zeta_sort12 Eq_sort12 s4)
        (extRen_sort17 xi_sort12 zeta_sort12 Eq_sort12 s5)
  | clam18 s0 =>
      congr_clam18
        (extRen_sort12 (upRen_sort12_sort12 xi_sort12)
           (upRen_sort12_sort12 zeta_sort12)
           (upExtRen_sort12_sort12 _ _ Eq_sort12) s0)
  end
with extRen_sort17 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(Eq_sort12 : forall x, xi_sort12 x = zeta_sort12 x) (s : sort17)  :
ren_sort17 xi_sort12 s = ren_sort17 zeta_sort12 s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17 (extRen_sort12 xi_sort12 zeta_sort12 Eq_sort12 s0)
        (extRen_sort13 xi_sort12 zeta_sort12 Eq_sort12 s1)
        (extRen_sort14 xi_sort12 zeta_sort12 Eq_sort12 s2)
        (extRen_sort15 xi_sort12 zeta_sort12 Eq_sort12 s3)
        (extRen_sort16 xi_sort12 zeta_sort12 Eq_sort12 s4)
        (extRen_sort17 xi_sort12 zeta_sort12 Eq_sort12 s5)
  end.

Lemma upExt_sort12_sort12 (sigma : nat -> sort12) (tau : nat -> sort12)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_sort12_sort12 sigma x = up_sort12_sort12 tau x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort12 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint ext_sort12 (sigma_sort12 : nat -> sort12)
(tau_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = tau_sort12 x) (s : sort12) 
   : subst_sort12 sigma_sort12 s = subst_sort12 tau_sort12 s :=
  match s with
  | var_sort12 s0 => Eq_sort12 s0
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12 (ext_sort12 sigma_sort12 tau_sort12 Eq_sort12 s0)
        (ext_sort13 sigma_sort12 tau_sort12 Eq_sort12 s1)
        (ext_sort14 sigma_sort12 tau_sort12 Eq_sort12 s2)
        (ext_sort15 sigma_sort12 tau_sort12 Eq_sort12 s3)
        (ext_sort16 sigma_sort12 tau_sort12 Eq_sort12 s4)
        (ext_sort17 sigma_sort12 tau_sort12 Eq_sort12 s5)
  end
with ext_sort13 (sigma_sort12 : nat -> sort12) (tau_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = tau_sort12 x) (s : sort13) 
   : subst_sort13 sigma_sort12 s = subst_sort13 tau_sort12 s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13 (ext_sort12 sigma_sort12 tau_sort12 Eq_sort12 s0)
        (ext_sort13 sigma_sort12 tau_sort12 Eq_sort12 s1)
        (ext_sort14 sigma_sort12 tau_sort12 Eq_sort12 s2)
        (ext_sort15 sigma_sort12 tau_sort12 Eq_sort12 s3)
        (ext_sort16 sigma_sort12 tau_sort12 Eq_sort12 s4)
        (ext_sort17 sigma_sort12 tau_sort12 Eq_sort12 s5)
  end
with ext_sort14 (sigma_sort12 : nat -> sort12) (tau_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = tau_sort12 x) (s : sort14) 
   : subst_sort14 sigma_sort12 s = subst_sort14 tau_sort12 s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14 (ext_sort12 sigma_sort12 tau_sort12 Eq_sort12 s0)
        (ext_sort13 sigma_sort12 tau_sort12 Eq_sort12 s1)
        (ext_sort14 sigma_sort12 tau_sort12 Eq_sort12 s2)
        (ext_sort15 sigma_sort12 tau_sort12 Eq_sort12 s3)
        (ext_sort16 sigma_sort12 tau_sort12 Eq_sort12 s4)
        (ext_sort17 sigma_sort12 tau_sort12 Eq_sort12 s5)
  end
with ext_sort15 (sigma_sort12 : nat -> sort12) (tau_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = tau_sort12 x) (s : sort15) 
   : subst_sort15 sigma_sort12 s = subst_sort15 tau_sort12 s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15 (ext_sort12 sigma_sort12 tau_sort12 Eq_sort12 s0)
        (ext_sort13 sigma_sort12 tau_sort12 Eq_sort12 s1)
        (ext_sort14 sigma_sort12 tau_sort12 Eq_sort12 s2)
        (ext_sort15 sigma_sort12 tau_sort12 Eq_sort12 s3)
        (ext_sort16 sigma_sort12 tau_sort12 Eq_sort12 s4)
        (ext_sort17 sigma_sort12 tau_sort12 Eq_sort12 s5)
  end
with ext_sort16 (sigma_sort12 : nat -> sort12) (tau_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = tau_sort12 x) (s : sort16) 
   : subst_sort16 sigma_sort12 s = subst_sort16 tau_sort12 s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16 (ext_sort12 sigma_sort12 tau_sort12 Eq_sort12 s0)
        (ext_sort13 sigma_sort12 tau_sort12 Eq_sort12 s1)
        (ext_sort14 sigma_sort12 tau_sort12 Eq_sort12 s2)
        (ext_sort15 sigma_sort12 tau_sort12 Eq_sort12 s3)
        (ext_sort16 sigma_sort12 tau_sort12 Eq_sort12 s4)
        (ext_sort17 sigma_sort12 tau_sort12 Eq_sort12 s5)
  | clam18 s0 =>
      congr_clam18
        (ext_sort12 (up_sort12_sort12 sigma_sort12)
           (up_sort12_sort12 tau_sort12) (upExt_sort12_sort12 _ _ Eq_sort12)
           s0)
  end
with ext_sort17 (sigma_sort12 : nat -> sort12) (tau_sort12 : nat -> sort12)
(Eq_sort12 : forall x, sigma_sort12 x = tau_sort12 x) (s : sort17) 
   : subst_sort17 sigma_sort12 s = subst_sort17 tau_sort12 s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17 (ext_sort12 sigma_sort12 tau_sort12 Eq_sort12 s0)
        (ext_sort13 sigma_sort12 tau_sort12 Eq_sort12 s1)
        (ext_sort14 sigma_sort12 tau_sort12 Eq_sort12 s2)
        (ext_sort15 sigma_sort12 tau_sort12 Eq_sort12 s3)
        (ext_sort16 sigma_sort12 tau_sort12 Eq_sort12 s4)
        (ext_sort17 sigma_sort12 tau_sort12 Eq_sort12 s5)
  end.

Lemma up_ren_ren_sort12_sort12 (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_sort12_sort12 zeta) (upRen_sort12_sort12 xi) x =
  upRen_sort12_sort12 rho x.

Proof.
exact (up_ren_ren xi zeta rho Eq).

Qed.

Fixpoint compRenRen_sort12 (xi_sort12 : nat -> nat)
(zeta_sort12 : nat -> nat) (rho_sort12 : nat -> nat)
(Eq_sort12 : forall x, funcomp zeta_sort12 xi_sort12 x = rho_sort12 x)
(s : sort12)  :
ren_sort12 zeta_sort12 (ren_sort12 xi_sort12 s) = ren_sort12 rho_sort12 s :=
  match s with
  | var_sort12 s0 => ap var_sort12 (Eq_sort12 s0)
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12
        (compRenRen_sort12 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s0)
        (compRenRen_sort13 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s1)
        (compRenRen_sort14 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s2)
        (compRenRen_sort15 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s3)
        (compRenRen_sort16 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s4)
        (compRenRen_sort17 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s5)
  end
with compRenRen_sort13 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(rho_sort12 : nat -> nat)
(Eq_sort12 : forall x, funcomp zeta_sort12 xi_sort12 x = rho_sort12 x)
(s : sort13)  :
ren_sort13 zeta_sort12 (ren_sort13 xi_sort12 s) = ren_sort13 rho_sort12 s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13
        (compRenRen_sort12 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s0)
        (compRenRen_sort13 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s1)
        (compRenRen_sort14 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s2)
        (compRenRen_sort15 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s3)
        (compRenRen_sort16 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s4)
        (compRenRen_sort17 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s5)
  end
with compRenRen_sort14 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(rho_sort12 : nat -> nat)
(Eq_sort12 : forall x, funcomp zeta_sort12 xi_sort12 x = rho_sort12 x)
(s : sort14)  :
ren_sort14 zeta_sort12 (ren_sort14 xi_sort12 s) = ren_sort14 rho_sort12 s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14
        (compRenRen_sort12 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s0)
        (compRenRen_sort13 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s1)
        (compRenRen_sort14 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s2)
        (compRenRen_sort15 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s3)
        (compRenRen_sort16 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s4)
        (compRenRen_sort17 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s5)
  end
with compRenRen_sort15 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(rho_sort12 : nat -> nat)
(Eq_sort12 : forall x, funcomp zeta_sort12 xi_sort12 x = rho_sort12 x)
(s : sort15)  :
ren_sort15 zeta_sort12 (ren_sort15 xi_sort12 s) = ren_sort15 rho_sort12 s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15
        (compRenRen_sort12 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s0)
        (compRenRen_sort13 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s1)
        (compRenRen_sort14 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s2)
        (compRenRen_sort15 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s3)
        (compRenRen_sort16 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s4)
        (compRenRen_sort17 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s5)
  end
with compRenRen_sort16 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(rho_sort12 : nat -> nat)
(Eq_sort12 : forall x, funcomp zeta_sort12 xi_sort12 x = rho_sort12 x)
(s : sort16)  :
ren_sort16 zeta_sort12 (ren_sort16 xi_sort12 s) = ren_sort16 rho_sort12 s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16
        (compRenRen_sort12 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s0)
        (compRenRen_sort13 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s1)
        (compRenRen_sort14 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s2)
        (compRenRen_sort15 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s3)
        (compRenRen_sort16 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s4)
        (compRenRen_sort17 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s5)
  | clam18 s0 =>
      congr_clam18
        (compRenRen_sort12 (upRen_sort12_sort12 xi_sort12)
           (upRen_sort12_sort12 zeta_sort12) (upRen_sort12_sort12 rho_sort12)
           (up_ren_ren _ _ _ Eq_sort12) s0)
  end
with compRenRen_sort17 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
(rho_sort12 : nat -> nat)
(Eq_sort12 : forall x, funcomp zeta_sort12 xi_sort12 x = rho_sort12 x)
(s : sort17)  :
ren_sort17 zeta_sort12 (ren_sort17 xi_sort12 s) = ren_sort17 rho_sort12 s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17
        (compRenRen_sort12 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s0)
        (compRenRen_sort13 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s1)
        (compRenRen_sort14 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s2)
        (compRenRen_sort15 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s3)
        (compRenRen_sort16 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s4)
        (compRenRen_sort17 xi_sort12 zeta_sort12 rho_sort12 Eq_sort12 s5)
  end.

Lemma up_ren_subst_sort12_sort12 (xi : nat -> nat) (tau : nat -> sort12)
  (theta : nat -> sort12) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_sort12_sort12 tau) (upRen_sort12_sort12 xi) x =
  up_sort12_sort12 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort12 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint compRenSubst_sort12 (xi_sort12 : nat -> nat)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp tau_sort12 xi_sort12 x = theta_sort12 x)
(s : sort12)  :
subst_sort12 tau_sort12 (ren_sort12 xi_sort12 s) =
subst_sort12 theta_sort12 s :=
  match s with
  | var_sort12 s0 => Eq_sort12 s0
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12
        (compRenSubst_sort12 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s0)
        (compRenSubst_sort13 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s1)
        (compRenSubst_sort14 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s2)
        (compRenSubst_sort15 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s3)
        (compRenSubst_sort16 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s4)
        (compRenSubst_sort17 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s5)
  end
with compRenSubst_sort13 (xi_sort12 : nat -> nat)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp tau_sort12 xi_sort12 x = theta_sort12 x)
(s : sort13)  :
subst_sort13 tau_sort12 (ren_sort13 xi_sort12 s) =
subst_sort13 theta_sort12 s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13
        (compRenSubst_sort12 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s0)
        (compRenSubst_sort13 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s1)
        (compRenSubst_sort14 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s2)
        (compRenSubst_sort15 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s3)
        (compRenSubst_sort16 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s4)
        (compRenSubst_sort17 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s5)
  end
with compRenSubst_sort14 (xi_sort12 : nat -> nat)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp tau_sort12 xi_sort12 x = theta_sort12 x)
(s : sort14)  :
subst_sort14 tau_sort12 (ren_sort14 xi_sort12 s) =
subst_sort14 theta_sort12 s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14
        (compRenSubst_sort12 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s0)
        (compRenSubst_sort13 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s1)
        (compRenSubst_sort14 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s2)
        (compRenSubst_sort15 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s3)
        (compRenSubst_sort16 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s4)
        (compRenSubst_sort17 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s5)
  end
with compRenSubst_sort15 (xi_sort12 : nat -> nat)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp tau_sort12 xi_sort12 x = theta_sort12 x)
(s : sort15)  :
subst_sort15 tau_sort12 (ren_sort15 xi_sort12 s) =
subst_sort15 theta_sort12 s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15
        (compRenSubst_sort12 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s0)
        (compRenSubst_sort13 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s1)
        (compRenSubst_sort14 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s2)
        (compRenSubst_sort15 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s3)
        (compRenSubst_sort16 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s4)
        (compRenSubst_sort17 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s5)
  end
with compRenSubst_sort16 (xi_sort12 : nat -> nat)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp tau_sort12 xi_sort12 x = theta_sort12 x)
(s : sort16)  :
subst_sort16 tau_sort12 (ren_sort16 xi_sort12 s) =
subst_sort16 theta_sort12 s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16
        (compRenSubst_sort12 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s0)
        (compRenSubst_sort13 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s1)
        (compRenSubst_sort14 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s2)
        (compRenSubst_sort15 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s3)
        (compRenSubst_sort16 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s4)
        (compRenSubst_sort17 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s5)
  | clam18 s0 =>
      congr_clam18
        (compRenSubst_sort12 (upRen_sort12_sort12 xi_sort12)
           (up_sort12_sort12 tau_sort12) (up_sort12_sort12 theta_sort12)
           (up_ren_subst_sort12_sort12 _ _ _ Eq_sort12) s0)
  end
with compRenSubst_sort17 (xi_sort12 : nat -> nat)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp tau_sort12 xi_sort12 x = theta_sort12 x)
(s : sort17)  :
subst_sort17 tau_sort12 (ren_sort17 xi_sort12 s) =
subst_sort17 theta_sort12 s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17
        (compRenSubst_sort12 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s0)
        (compRenSubst_sort13 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s1)
        (compRenSubst_sort14 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s2)
        (compRenSubst_sort15 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s3)
        (compRenSubst_sort16 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s4)
        (compRenSubst_sort17 xi_sort12 tau_sort12 theta_sort12 Eq_sort12 s5)
  end.

Lemma up_subst_ren_sort12_sort12 (sigma : nat -> sort12)
  (zeta_sort12 : nat -> nat) (theta : nat -> sort12)
  (Eq : forall x, funcomp (ren_sort12 zeta_sort12) sigma x = theta x) :
  forall x,
  funcomp (ren_sort12 (upRen_sort12_sort12 zeta_sort12))
    (up_sort12_sort12 sigma) x = up_sort12_sort12 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenRen_sort12 shift
                       (upRen_sort12_sort12 zeta_sort12)
                       (funcomp shift zeta_sort12) (fun x => eq_refl)
                       (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compRenRen_sort12 zeta_sort12 shift
                             (funcomp shift zeta_sort12) (fun x => eq_refl)
                             (sigma n'))) (ap (ren_sort12 shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstRen_sort12 (sigma_sort12 : nat -> sort12)
(zeta_sort12 : nat -> nat) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (ren_sort12 zeta_sort12) sigma_sort12 x = theta_sort12 x)
(s : sort12)  :
ren_sort12 zeta_sort12 (subst_sort12 sigma_sort12 s) =
subst_sort12 theta_sort12 s :=
  match s with
  | var_sort12 s0 => Eq_sort12 s0
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12
        (compSubstRen_sort12 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstRen_sort13 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstRen_sort14 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstRen_sort15 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstRen_sort16 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstRen_sort17 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstRen_sort13 (sigma_sort12 : nat -> sort12)
(zeta_sort12 : nat -> nat) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (ren_sort12 zeta_sort12) sigma_sort12 x = theta_sort12 x)
(s : sort13)  :
ren_sort13 zeta_sort12 (subst_sort13 sigma_sort12 s) =
subst_sort13 theta_sort12 s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13
        (compSubstRen_sort12 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstRen_sort13 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstRen_sort14 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstRen_sort15 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstRen_sort16 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstRen_sort17 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstRen_sort14 (sigma_sort12 : nat -> sort12)
(zeta_sort12 : nat -> nat) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (ren_sort12 zeta_sort12) sigma_sort12 x = theta_sort12 x)
(s : sort14)  :
ren_sort14 zeta_sort12 (subst_sort14 sigma_sort12 s) =
subst_sort14 theta_sort12 s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14
        (compSubstRen_sort12 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstRen_sort13 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstRen_sort14 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstRen_sort15 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstRen_sort16 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstRen_sort17 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstRen_sort15 (sigma_sort12 : nat -> sort12)
(zeta_sort12 : nat -> nat) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (ren_sort12 zeta_sort12) sigma_sort12 x = theta_sort12 x)
(s : sort15)  :
ren_sort15 zeta_sort12 (subst_sort15 sigma_sort12 s) =
subst_sort15 theta_sort12 s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15
        (compSubstRen_sort12 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstRen_sort13 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstRen_sort14 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstRen_sort15 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstRen_sort16 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstRen_sort17 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstRen_sort16 (sigma_sort12 : nat -> sort12)
(zeta_sort12 : nat -> nat) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (ren_sort12 zeta_sort12) sigma_sort12 x = theta_sort12 x)
(s : sort16)  :
ren_sort16 zeta_sort12 (subst_sort16 sigma_sort12 s) =
subst_sort16 theta_sort12 s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16
        (compSubstRen_sort12 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstRen_sort13 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstRen_sort14 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstRen_sort15 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstRen_sort16 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstRen_sort17 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s5)
  | clam18 s0 =>
      congr_clam18
        (compSubstRen_sort12 (up_sort12_sort12 sigma_sort12)
           (upRen_sort12_sort12 zeta_sort12) (up_sort12_sort12 theta_sort12)
           (up_subst_ren_sort12_sort12 _ _ _ Eq_sort12) s0)
  end
with compSubstRen_sort17 (sigma_sort12 : nat -> sort12)
(zeta_sort12 : nat -> nat) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (ren_sort12 zeta_sort12) sigma_sort12 x = theta_sort12 x)
(s : sort17)  :
ren_sort17 zeta_sort12 (subst_sort17 sigma_sort12 s) =
subst_sort17 theta_sort12 s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17
        (compSubstRen_sort12 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstRen_sort13 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstRen_sort14 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstRen_sort15 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstRen_sort16 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstRen_sort17 sigma_sort12 zeta_sort12 theta_sort12 Eq_sort12
           s5)
  end.

Lemma up_subst_subst_sort12_sort12 (sigma : nat -> sort12)
  (tau_sort12 : nat -> sort12) (theta : nat -> sort12)
  (Eq : forall x, funcomp (subst_sort12 tau_sort12) sigma x = theta x) :
  forall x,
  funcomp (subst_sort12 (up_sort12_sort12 tau_sort12))
    (up_sort12_sort12 sigma) x = up_sort12_sort12 theta x.

Proof.
exact (fun n =>
              match n with
              | S n' =>
                  eq_trans
                    (compRenSubst_sort12 shift (up_sort12_sort12 tau_sort12)
                       (funcomp (up_sort12_sort12 tau_sort12) shift)
                       (fun x => eq_refl) (sigma n'))
                    (eq_trans
                       (eq_sym
                          (compSubstRen_sort12 tau_sort12 shift
                             (funcomp (ren_sort12 shift) tau_sort12)
                             (fun x => eq_refl) (sigma n')))
                       (ap (ren_sort12 shift) (Eq n')))
              | O => eq_refl
              end).

Qed.

Fixpoint compSubstSubst_sort12 (sigma_sort12 : nat -> sort12)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (subst_sort12 tau_sort12) sigma_sort12 x =
             theta_sort12 x) (s : sort12)  :
subst_sort12 tau_sort12 (subst_sort12 sigma_sort12 s) =
subst_sort12 theta_sort12 s :=
  match s with
  | var_sort12 s0 => Eq_sort12 s0
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12
        (compSubstSubst_sort12 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstSubst_sort13 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstSubst_sort14 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstSubst_sort15 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstSubst_sort16 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstSubst_sort17 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstSubst_sort13 (sigma_sort12 : nat -> sort12)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (subst_sort12 tau_sort12) sigma_sort12 x =
             theta_sort12 x) (s : sort13)  :
subst_sort13 tau_sort12 (subst_sort13 sigma_sort12 s) =
subst_sort13 theta_sort12 s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13
        (compSubstSubst_sort12 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstSubst_sort13 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstSubst_sort14 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstSubst_sort15 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstSubst_sort16 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstSubst_sort17 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstSubst_sort14 (sigma_sort12 : nat -> sort12)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (subst_sort12 tau_sort12) sigma_sort12 x =
             theta_sort12 x) (s : sort14)  :
subst_sort14 tau_sort12 (subst_sort14 sigma_sort12 s) =
subst_sort14 theta_sort12 s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14
        (compSubstSubst_sort12 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstSubst_sort13 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstSubst_sort14 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstSubst_sort15 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstSubst_sort16 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstSubst_sort17 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstSubst_sort15 (sigma_sort12 : nat -> sort12)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (subst_sort12 tau_sort12) sigma_sort12 x =
             theta_sort12 x) (s : sort15)  :
subst_sort15 tau_sort12 (subst_sort15 sigma_sort12 s) =
subst_sort15 theta_sort12 s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15
        (compSubstSubst_sort12 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstSubst_sort13 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstSubst_sort14 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstSubst_sort15 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstSubst_sort16 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstSubst_sort17 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s5)
  end
with compSubstSubst_sort16 (sigma_sort12 : nat -> sort12)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (subst_sort12 tau_sort12) sigma_sort12 x =
             theta_sort12 x) (s : sort16)  :
subst_sort16 tau_sort12 (subst_sort16 sigma_sort12 s) =
subst_sort16 theta_sort12 s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16
        (compSubstSubst_sort12 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstSubst_sort13 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstSubst_sort14 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstSubst_sort15 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstSubst_sort16 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstSubst_sort17 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s5)
  | clam18 s0 =>
      congr_clam18
        (compSubstSubst_sort12 (up_sort12_sort12 sigma_sort12)
           (up_sort12_sort12 tau_sort12) (up_sort12_sort12 theta_sort12)
           (up_subst_subst_sort12_sort12 _ _ _ Eq_sort12) s0)
  end
with compSubstSubst_sort17 (sigma_sort12 : nat -> sort12)
(tau_sort12 : nat -> sort12) (theta_sort12 : nat -> sort12)
(Eq_sort12 : forall x,
             funcomp (subst_sort12 tau_sort12) sigma_sort12 x =
             theta_sort12 x) (s : sort17)  :
subst_sort17 tau_sort12 (subst_sort17 sigma_sort12 s) =
subst_sort17 theta_sort12 s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17
        (compSubstSubst_sort12 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s0)
        (compSubstSubst_sort13 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s1)
        (compSubstSubst_sort14 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s2)
        (compSubstSubst_sort15 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s3)
        (compSubstSubst_sort16 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s4)
        (compSubstSubst_sort17 sigma_sort12 tau_sort12 theta_sort12 Eq_sort12
           s5)
  end.

Lemma rinstInst_up_sort12_sort12 (xi : nat -> nat) (sigma : nat -> sort12)
  (Eq : forall x, funcomp var_sort12 xi x = sigma x) :
  forall x,
  funcomp var_sort12 (upRen_sort12_sort12 xi) x = up_sort12_sort12 sigma x.

Proof.
exact (fun n =>
              match n with
              | S n' => ap (ren_sort12 shift) (Eq n')
              | O => eq_refl
              end).

Qed.

Fixpoint rinst_inst_sort12 (xi_sort12 : nat -> nat)
(sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp var_sort12 xi_sort12 x = sigma_sort12 x)
(s : sort12)  :
ren_sort12 xi_sort12 s = subst_sort12 sigma_sort12 s :=
  match s with
  | var_sort12 s0 => Eq_sort12 s0
  | cmix12 s0 s1 s2 s3 s4 s5 =>
      congr_cmix12 (rinst_inst_sort12 xi_sort12 sigma_sort12 Eq_sort12 s0)
        (rinst_inst_sort13 xi_sort12 sigma_sort12 Eq_sort12 s1)
        (rinst_inst_sort14 xi_sort12 sigma_sort12 Eq_sort12 s2)
        (rinst_inst_sort15 xi_sort12 sigma_sort12 Eq_sort12 s3)
        (rinst_inst_sort16 xi_sort12 sigma_sort12 Eq_sort12 s4)
        (rinst_inst_sort17 xi_sort12 sigma_sort12 Eq_sort12 s5)
  end
with rinst_inst_sort13 (xi_sort12 : nat -> nat)
(sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp var_sort12 xi_sort12 x = sigma_sort12 x)
(s : sort13)  :
ren_sort13 xi_sort12 s = subst_sort13 sigma_sort12 s :=
  match s with
  | cmix13 s0 s1 s2 s3 s4 s5 =>
      congr_cmix13 (rinst_inst_sort12 xi_sort12 sigma_sort12 Eq_sort12 s0)
        (rinst_inst_sort13 xi_sort12 sigma_sort12 Eq_sort12 s1)
        (rinst_inst_sort14 xi_sort12 sigma_sort12 Eq_sort12 s2)
        (rinst_inst_sort15 xi_sort12 sigma_sort12 Eq_sort12 s3)
        (rinst_inst_sort16 xi_sort12 sigma_sort12 Eq_sort12 s4)
        (rinst_inst_sort17 xi_sort12 sigma_sort12 Eq_sort12 s5)
  end
with rinst_inst_sort14 (xi_sort12 : nat -> nat)
(sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp var_sort12 xi_sort12 x = sigma_sort12 x)
(s : sort14)  :
ren_sort14 xi_sort12 s = subst_sort14 sigma_sort12 s :=
  match s with
  | cmix14 s0 s1 s2 s3 s4 s5 =>
      congr_cmix14 (rinst_inst_sort12 xi_sort12 sigma_sort12 Eq_sort12 s0)
        (rinst_inst_sort13 xi_sort12 sigma_sort12 Eq_sort12 s1)
        (rinst_inst_sort14 xi_sort12 sigma_sort12 Eq_sort12 s2)
        (rinst_inst_sort15 xi_sort12 sigma_sort12 Eq_sort12 s3)
        (rinst_inst_sort16 xi_sort12 sigma_sort12 Eq_sort12 s4)
        (rinst_inst_sort17 xi_sort12 sigma_sort12 Eq_sort12 s5)
  end
with rinst_inst_sort15 (xi_sort12 : nat -> nat)
(sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp var_sort12 xi_sort12 x = sigma_sort12 x)
(s : sort15)  :
ren_sort15 xi_sort12 s = subst_sort15 sigma_sort12 s :=
  match s with
  | cmix15 s0 s1 s2 s3 s4 s5 =>
      congr_cmix15 (rinst_inst_sort12 xi_sort12 sigma_sort12 Eq_sort12 s0)
        (rinst_inst_sort13 xi_sort12 sigma_sort12 Eq_sort12 s1)
        (rinst_inst_sort14 xi_sort12 sigma_sort12 Eq_sort12 s2)
        (rinst_inst_sort15 xi_sort12 sigma_sort12 Eq_sort12 s3)
        (rinst_inst_sort16 xi_sort12 sigma_sort12 Eq_sort12 s4)
        (rinst_inst_sort17 xi_sort12 sigma_sort12 Eq_sort12 s5)
  end
with rinst_inst_sort16 (xi_sort12 : nat -> nat)
(sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp var_sort12 xi_sort12 x = sigma_sort12 x)
(s : sort16)  :
ren_sort16 xi_sort12 s = subst_sort16 sigma_sort12 s :=
  match s with
  | cmix16 s0 s1 s2 s3 s4 s5 =>
      congr_cmix16 (rinst_inst_sort12 xi_sort12 sigma_sort12 Eq_sort12 s0)
        (rinst_inst_sort13 xi_sort12 sigma_sort12 Eq_sort12 s1)
        (rinst_inst_sort14 xi_sort12 sigma_sort12 Eq_sort12 s2)
        (rinst_inst_sort15 xi_sort12 sigma_sort12 Eq_sort12 s3)
        (rinst_inst_sort16 xi_sort12 sigma_sort12 Eq_sort12 s4)
        (rinst_inst_sort17 xi_sort12 sigma_sort12 Eq_sort12 s5)
  | clam18 s0 =>
      congr_clam18
        (rinst_inst_sort12 (upRen_sort12_sort12 xi_sort12)
           (up_sort12_sort12 sigma_sort12)
           (rinstInst_up_sort12_sort12 _ _ Eq_sort12) s0)
  end
with rinst_inst_sort17 (xi_sort12 : nat -> nat)
(sigma_sort12 : nat -> sort12)
(Eq_sort12 : forall x, funcomp var_sort12 xi_sort12 x = sigma_sort12 x)
(s : sort17)  :
ren_sort17 xi_sort12 s = subst_sort17 sigma_sort12 s :=
  match s with
  | cmix17 s0 s1 s2 s3 s4 s5 =>
      congr_cmix17 (rinst_inst_sort12 xi_sort12 sigma_sort12 Eq_sort12 s0)
        (rinst_inst_sort13 xi_sort12 sigma_sort12 Eq_sort12 s1)
        (rinst_inst_sort14 xi_sort12 sigma_sort12 Eq_sort12 s2)
        (rinst_inst_sort15 xi_sort12 sigma_sort12 Eq_sort12 s3)
        (rinst_inst_sort16 xi_sort12 sigma_sort12 Eq_sort12 s4)
        (rinst_inst_sort17 xi_sort12 sigma_sort12 Eq_sort12 s5)
  end.

Lemma renRen_sort12 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
  (s : sort12) :
  ren_sort12 zeta_sort12 (ren_sort12 xi_sort12 s) =
  ren_sort12 (funcomp zeta_sort12 xi_sort12) s.

Proof.
exact (compRenRen_sort12 xi_sort12 zeta_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort13 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
  (s : sort13) :
  ren_sort13 zeta_sort12 (ren_sort13 xi_sort12 s) =
  ren_sort13 (funcomp zeta_sort12 xi_sort12) s.

Proof.
exact (compRenRen_sort13 xi_sort12 zeta_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort14 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
  (s : sort14) :
  ren_sort14 zeta_sort12 (ren_sort14 xi_sort12 s) =
  ren_sort14 (funcomp zeta_sort12 xi_sort12) s.

Proof.
exact (compRenRen_sort14 xi_sort12 zeta_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort15 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
  (s : sort15) :
  ren_sort15 zeta_sort12 (ren_sort15 xi_sort12 s) =
  ren_sort15 (funcomp zeta_sort12 xi_sort12) s.

Proof.
exact (compRenRen_sort15 xi_sort12 zeta_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort16 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
  (s : sort16) :
  ren_sort16 zeta_sort12 (ren_sort16 xi_sort12 s) =
  ren_sort16 (funcomp zeta_sort12 xi_sort12) s.

Proof.
exact (compRenRen_sort16 xi_sort12 zeta_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renRen_sort17 (xi_sort12 : nat -> nat) (zeta_sort12 : nat -> nat)
  (s : sort17) :
  ren_sort17 zeta_sort12 (ren_sort17 xi_sort12 s) =
  ren_sort17 (funcomp zeta_sort12 xi_sort12) s.

Proof.
exact (compRenRen_sort17 xi_sort12 zeta_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma compRen_sort12 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) (s : sort12) :
  ren_sort12 zeta_sort12 (subst_sort12 sigma_sort12 s) =
  subst_sort12 (funcomp (ren_sort12 zeta_sort12) sigma_sort12) s.

Proof.
exact (compSubstRen_sort12 sigma_sort12 zeta_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort13 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) (s : sort13) :
  ren_sort13 zeta_sort12 (subst_sort13 sigma_sort12 s) =
  subst_sort13 (funcomp (ren_sort12 zeta_sort12) sigma_sort12) s.

Proof.
exact (compSubstRen_sort13 sigma_sort12 zeta_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort14 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) (s : sort14) :
  ren_sort14 zeta_sort12 (subst_sort14 sigma_sort12 s) =
  subst_sort14 (funcomp (ren_sort12 zeta_sort12) sigma_sort12) s.

Proof.
exact (compSubstRen_sort14 sigma_sort12 zeta_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort15 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) (s : sort15) :
  ren_sort15 zeta_sort12 (subst_sort15 sigma_sort12 s) =
  subst_sort15 (funcomp (ren_sort12 zeta_sort12) sigma_sort12) s.

Proof.
exact (compSubstRen_sort15 sigma_sort12 zeta_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort16 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) (s : sort16) :
  ren_sort16 zeta_sort12 (subst_sort16 sigma_sort12 s) =
  subst_sort16 (funcomp (ren_sort12 zeta_sort12) sigma_sort12) s.

Proof.
exact (compSubstRen_sort16 sigma_sort12 zeta_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compRen_sort17 (sigma_sort12 : nat -> sort12)
  (zeta_sort12 : nat -> nat) (s : sort17) :
  ren_sort17 zeta_sort12 (subst_sort17 sigma_sort12 s) =
  subst_sort17 (funcomp (ren_sort12 zeta_sort12) sigma_sort12) s.

Proof.
exact (compSubstRen_sort17 sigma_sort12 zeta_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma renComp_sort12 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12)
  (s : sort12) :
  subst_sort12 tau_sort12 (ren_sort12 xi_sort12 s) =
  subst_sort12 (funcomp tau_sort12 xi_sort12) s.

Proof.
exact (compRenSubst_sort12 xi_sort12 tau_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort13 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12)
  (s : sort13) :
  subst_sort13 tau_sort12 (ren_sort13 xi_sort12 s) =
  subst_sort13 (funcomp tau_sort12 xi_sort12) s.

Proof.
exact (compRenSubst_sort13 xi_sort12 tau_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort14 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12)
  (s : sort14) :
  subst_sort14 tau_sort12 (ren_sort14 xi_sort12 s) =
  subst_sort14 (funcomp tau_sort12 xi_sort12) s.

Proof.
exact (compRenSubst_sort14 xi_sort12 tau_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort15 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12)
  (s : sort15) :
  subst_sort15 tau_sort12 (ren_sort15 xi_sort12 s) =
  subst_sort15 (funcomp tau_sort12 xi_sort12) s.

Proof.
exact (compRenSubst_sort15 xi_sort12 tau_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort16 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12)
  (s : sort16) :
  subst_sort16 tau_sort12 (ren_sort16 xi_sort12 s) =
  subst_sort16 (funcomp tau_sort12 xi_sort12) s.

Proof.
exact (compRenSubst_sort16 xi_sort12 tau_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma renComp_sort17 (xi_sort12 : nat -> nat) (tau_sort12 : nat -> sort12)
  (s : sort17) :
  subst_sort17 tau_sort12 (ren_sort17 xi_sort12 s) =
  subst_sort17 (funcomp tau_sort12 xi_sort12) s.

Proof.
exact (compRenSubst_sort17 xi_sort12 tau_sort12 _ (fun n => eq_refl) s).

Qed.

Lemma compComp_sort12 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) (s : sort12) :
  subst_sort12 tau_sort12 (subst_sort12 sigma_sort12 s) =
  subst_sort12 (funcomp (subst_sort12 tau_sort12) sigma_sort12) s.

Proof.
exact (compSubstSubst_sort12 sigma_sort12 tau_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort13 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) (s : sort13) :
  subst_sort13 tau_sort12 (subst_sort13 sigma_sort12 s) =
  subst_sort13 (funcomp (subst_sort12 tau_sort12) sigma_sort12) s.

Proof.
exact (compSubstSubst_sort13 sigma_sort12 tau_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort14 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) (s : sort14) :
  subst_sort14 tau_sort12 (subst_sort14 sigma_sort12 s) =
  subst_sort14 (funcomp (subst_sort12 tau_sort12) sigma_sort12) s.

Proof.
exact (compSubstSubst_sort14 sigma_sort12 tau_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort15 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) (s : sort15) :
  subst_sort15 tau_sort12 (subst_sort15 sigma_sort12 s) =
  subst_sort15 (funcomp (subst_sort12 tau_sort12) sigma_sort12) s.

Proof.
exact (compSubstSubst_sort15 sigma_sort12 tau_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort16 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) (s : sort16) :
  subst_sort16 tau_sort12 (subst_sort16 sigma_sort12 s) =
  subst_sort16 (funcomp (subst_sort12 tau_sort12) sigma_sort12) s.

Proof.
exact (compSubstSubst_sort16 sigma_sort12 tau_sort12 _
                (fun n => eq_refl) s).

Qed.

Lemma compComp_sort17 (sigma_sort12 : nat -> sort12)
  (tau_sort12 : nat -> sort12) (s : sort17) :
  subst_sort17 tau_sort12 (subst_sort17 sigma_sort12 s) =
  subst_sort17 (funcomp (subst_sort12 tau_sort12) sigma_sort12) s.

Proof.
exact (compSubstSubst_sort17 sigma_sort12 tau_sort12 _
                (fun n => eq_refl) s).

Qed.
