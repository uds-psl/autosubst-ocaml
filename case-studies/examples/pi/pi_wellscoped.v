Require Import axioms fintype header_extensible.
Inductive chan (n_chan : nat) : Type :=
    var_chan : forall _ : fin n_chan, chan n_chan.
Definition subst_chan {m_chan : nat} {n_chan : nat}
  (sigma_chan : forall _ : fin m_chan, chan n_chan) (s : chan m_chan) :
  chan n_chan := match s with
                 | var_chan _ s0 => sigma_chan s0
                 end.
Definition up_chan_chan {m : nat} {n_chan : nat}
  (sigma : forall _ : fin m, chan n_chan) :
  forall _ : fin (S m), chan (S n_chan) :=
  scons (var_chan (S n_chan) var_zero)
    (funcomp (subst_chan (funcomp (var_chan _) shift)) sigma).
Definition up_list_chan_chan (p : nat) {m : nat} {n_chan : nat}
  (sigma : forall _ : fin m, chan n_chan) :
  forall _ : fin (plus p m), chan (plus p n_chan) :=
  scons_p p (funcomp (var_chan (plus p n_chan)) (zero_p p))
    (funcomp (subst_chan (funcomp (var_chan _) (shift_p p))) sigma).
Definition upId_chan_chan {m_chan : nat}
  (sigma : forall _ : fin m_chan, chan m_chan)
  (Eq : forall x, eq (sigma x) (var_chan m_chan x)) :
  forall x, eq (up_chan_chan sigma x) (var_chan (S m_chan) x) :=
  fun n =>
  match n with
  | Some fin_n => ap (subst_chan (funcomp (var_chan _) shift)) (Eq fin_n)
  | None => eq_refl
  end.
Definition upId_list_chan_chan {p : nat} {m_chan : nat}
  (sigma : forall _ : fin m_chan, chan m_chan)
  (Eq : forall x, eq (sigma x) (var_chan m_chan x)) :
  forall x, eq (up_list_chan_chan p sigma x) (var_chan (plus p m_chan) x) :=
  fun n =>
  scons_p_eta (var_chan (plus p m_chan))
    (fun n => ap (subst_chan (funcomp (var_chan _) (shift_p p))) (Eq n))
    (fun n => eq_refl).
Definition idSubst_chan {m_chan : nat}
  (sigma_chan : forall _ : fin m_chan, chan m_chan)
  (Eq_chan : forall x, eq (sigma_chan x) (var_chan m_chan x))
  (s : chan m_chan) : eq (subst_chan sigma_chan s) s :=
  match s with
  | var_chan _ s0 => Eq_chan s0
  end.
Definition upExt_chan_chan {m : nat} {n_chan : nat}
  (sigma : forall _ : fin m, chan n_chan)
  (tau : forall _ : fin m, chan n_chan) (Eq : forall x, eq (sigma x) (tau x))
  : forall x, eq (up_chan_chan sigma x) (up_chan_chan tau x) :=
  fun n =>
  match n with
  | Some fin_n => ap (subst_chan (funcomp (var_chan _) shift)) (Eq fin_n)
  | None => eq_refl
  end.
Definition upExt_list_chan_chan {p : nat} {m : nat} {n_chan : nat}
  (sigma : forall _ : fin m, chan n_chan)
  (tau : forall _ : fin m, chan n_chan) (Eq : forall x, eq (sigma x) (tau x))
  : forall x, eq (up_list_chan_chan p sigma x) (up_list_chan_chan p tau x) :=
  fun n =>
  scons_p_congr (fun n => eq_refl)
    (fun n => ap (subst_chan (funcomp (var_chan _) (shift_p p))) (Eq n)).
Definition ext_chan {m_chan : nat} {n_chan : nat}
  (sigma_chan : forall _ : fin m_chan, chan n_chan)
  (tau_chan : forall _ : fin m_chan, chan n_chan)
  (Eq_chan : forall x, eq (sigma_chan x) (tau_chan x)) (s : chan m_chan) :
  eq (subst_chan sigma_chan s) (subst_chan tau_chan s) :=
  match s with
  | var_chan _ s0 => Eq_chan s0
  end.
Definition compSubstSubst_chan {k_chan : nat} {l_chan : nat} {m_chan : nat}
  (sigma_chan : forall _ : fin m_chan, chan k_chan)
  (tau_chan : forall _ : fin k_chan, chan l_chan)
  (theta_chan : forall _ : fin m_chan, chan l_chan)
  (Eq_chan : forall x,
             eq (funcomp (subst_chan tau_chan) sigma_chan x) (theta_chan x))
  (s : chan m_chan) :
  eq (subst_chan tau_chan (subst_chan sigma_chan s))
    (subst_chan theta_chan s) :=
  match s with
  | var_chan _ s0 => Eq_chan s0
  end.
Definition up_subst_subst_chan_chan {k : nat} {l_chan : nat} {m_chan : nat}
  (sigma : forall _ : fin k, chan l_chan)
  (tau_chan : forall _ : fin l_chan, chan m_chan)
  (theta : forall _ : fin k, chan m_chan)
  (Eq : forall x, eq (funcomp (subst_chan tau_chan) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_chan (up_chan_chan tau_chan)) (up_chan_chan sigma) x)
    (up_chan_chan theta x) :=
  fun n =>
  match n with
  | Some fin_n =>
      eq_trans
        (compSubstSubst_chan (funcomp (var_chan _) shift)
           (up_chan_chan tau_chan) (funcomp (up_chan_chan tau_chan) shift)
           (fun x => eq_refl) (sigma fin_n))
        (eq_trans
           (eq_sym
              (compSubstSubst_chan tau_chan (funcomp (var_chan _) shift)
                 (funcomp (subst_chan (funcomp (var_chan _) shift)) tau_chan)
                 (fun x => eq_refl) (sigma fin_n)))
           (ap (subst_chan (funcomp (var_chan _) shift)) (Eq fin_n)))
  | None => eq_refl
  end.
Definition up_subst_subst_list_chan_chan {p : nat} {k : nat} {l_chan : nat}
  {m_chan : nat} (sigma : forall _ : fin k, chan l_chan)
  (tau_chan : forall _ : fin l_chan, chan m_chan)
  (theta : forall _ : fin k, chan m_chan)
  (Eq : forall x, eq (funcomp (subst_chan tau_chan) sigma x) (theta x)) :
  forall x,
  eq
    (funcomp (subst_chan (up_list_chan_chan p tau_chan))
       (up_list_chan_chan p sigma) x) (up_list_chan_chan p theta x) :=
  fun n =>
  eq_trans
    (scons_p_comp' (funcomp (var_chan (plus p l_chan)) (zero_p p)) _ _ n)
    (scons_p_congr
       (fun x =>
        scons_p_head' _
          (fun z => subst_chan (funcomp (var_chan _) (shift_p p)) _) x)
       (fun n =>
        eq_trans
          (compSubstSubst_chan (funcomp (var_chan _) (shift_p p))
             (up_list_chan_chan p tau_chan)
             (funcomp (up_list_chan_chan p tau_chan) (shift_p p))
             (fun x => eq_refl) (sigma n))
          (eq_trans
             (eq_sym
                (compSubstSubst_chan tau_chan
                   (funcomp (var_chan _) (shift_p p)) _
                   (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
             (ap (subst_chan (funcomp (var_chan _) (shift_p p))) (Eq n))))).
Lemma instId_chan {m_chan : nat} : eq (subst_chan (var_chan m_chan)) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_chan (var_chan m_chan) (fun n => eq_refl) (id x))).
Qed.
Lemma varL_chan {m_chan : nat} {n_chan : nat}
  (sigma_chan : forall _ : fin m_chan, chan n_chan) :
  eq (funcomp (subst_chan sigma_chan) (var_chan m_chan)) sigma_chan.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Inductive proc (n_chan : nat) : Type :=
  | Nil : proc n_chan
  | Bang : forall _ : proc n_chan, proc n_chan
  | Res : forall _ : proc (S n_chan), proc n_chan
  | Par : forall _ : proc n_chan, forall _ : proc n_chan, proc n_chan
  | In : forall _ : chan n_chan, forall _ : proc (S n_chan), proc n_chan
  | Out :
      forall _ : chan n_chan,
      forall _ : chan n_chan, forall _ : proc n_chan, proc n_chan.
Lemma congr_Nil {m_chan : nat} : eq (Nil m_chan) (Nil m_chan).
Proof.
exact (eq_refl).
Qed.
Lemma congr_Bang {m_chan : nat} {s0 : proc m_chan} {t0 : proc m_chan}
  (H0 : eq s0 t0) : eq (Bang m_chan s0) (Bang m_chan t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Bang m_chan x) H0)).
Qed.
Lemma congr_Res {m_chan : nat} {s0 : proc (S m_chan)} {t0 : proc (S m_chan)}
  (H0 : eq s0 t0) : eq (Res m_chan s0) (Res m_chan t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => Res m_chan x) H0)).
Qed.
Lemma congr_Par {m_chan : nat} {s0 : proc m_chan} {s1 : proc m_chan}
  {t0 : proc m_chan} {t1 : proc m_chan} (H0 : eq s0 t0) (H1 : eq s1 t1) :
  eq (Par m_chan s0 s1) (Par m_chan t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Par m_chan x s1) H0))
                (ap (fun x => Par m_chan t0 x) H1)).
Qed.
Lemma congr_In {m_chan : nat} {s0 : chan m_chan} {s1 : proc (S m_chan)}
  {t0 : chan m_chan} {t1 : proc (S m_chan)} (H0 : eq s0 t0) (H1 : eq s1 t1) :
  eq (In m_chan s0 s1) (In m_chan t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => In m_chan x s1) H0))
                (ap (fun x => In m_chan t0 x) H1)).
Qed.
Lemma congr_Out {m_chan : nat} {s0 : chan m_chan} {s1 : chan m_chan}
  {s2 : proc m_chan} {t0 : chan m_chan} {t1 : chan m_chan} {t2 : proc m_chan}
  (H0 : eq s0 t0) (H1 : eq s1 t1) (H2 : eq s2 t2) :
  eq (Out m_chan s0 s1 s2) (Out m_chan t0 t1 t2).
Proof.
exact (eq_trans
                (eq_trans
                   (eq_trans eq_refl (ap (fun x => Out m_chan x s1 s2) H0))
                   (ap (fun x => Out m_chan t0 x s2) H1))
                (ap (fun x => Out m_chan t0 t1 x) H2)).
Qed.
Fixpoint subst_proc {m_chan : nat} {n_chan : nat}
(sigma_chan : forall _ : fin m_chan, chan n_chan) (s : proc m_chan) :
proc n_chan :=
  match s with
  | Nil _ => Nil n_chan
  | Bang _ s0 => Bang n_chan (subst_proc sigma_chan s0)
  | Res _ s0 => Res n_chan (subst_proc (up_chan_chan sigma_chan) s0)
  | Par _ s0 s1 =>
      Par n_chan (subst_proc sigma_chan s0) (subst_proc sigma_chan s1)
  | In _ s0 s1 =>
      In n_chan (subst_chan sigma_chan s0)
        (subst_proc (up_chan_chan sigma_chan) s1)
  | Out _ s0 s1 s2 =>
      Out n_chan (subst_chan sigma_chan s0) (subst_chan sigma_chan s1)
        (subst_proc sigma_chan s2)
  end.
Fixpoint idSubst_proc {m_chan : nat}
(sigma_chan : forall _ : fin m_chan, chan m_chan)
(Eq_chan : forall x, eq (sigma_chan x) (var_chan m_chan x)) (s : proc m_chan)
   : eq (subst_proc sigma_chan s) s :=
  match s with
  | Nil _ => congr_Nil
  | Bang _ s0 => congr_Bang (idSubst_proc sigma_chan Eq_chan s0)
  | Res _ s0 =>
      congr_Res
        (idSubst_proc (up_chan_chan sigma_chan) (upId_chan_chan _ Eq_chan) s0)
  | Par _ s0 s1 =>
      congr_Par (idSubst_proc sigma_chan Eq_chan s0)
        (idSubst_proc sigma_chan Eq_chan s1)
  | In _ s0 s1 =>
      congr_In (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_proc (up_chan_chan sigma_chan) (upId_chan_chan _ Eq_chan) s1)
  | Out _ s0 s1 s2 =>
      congr_Out (idSubst_chan sigma_chan Eq_chan s0)
        (idSubst_chan sigma_chan Eq_chan s1)
        (idSubst_proc sigma_chan Eq_chan s2)
  end.
Fixpoint ext_proc {m_chan : nat} {n_chan : nat}
(sigma_chan : forall _ : fin m_chan, chan n_chan)
(tau_chan : forall _ : fin m_chan, chan n_chan)
(Eq_chan : forall x, eq (sigma_chan x) (tau_chan x)) (s : proc m_chan) :
eq (subst_proc sigma_chan s) (subst_proc tau_chan s) :=
  match s with
  | Nil _ => congr_Nil
  | Bang _ s0 => congr_Bang (ext_proc sigma_chan tau_chan Eq_chan s0)
  | Res _ s0 =>
      congr_Res
        (ext_proc (up_chan_chan sigma_chan) (up_chan_chan tau_chan)
           (upExt_chan_chan _ _ Eq_chan) s0)
  | Par _ s0 s1 =>
      congr_Par (ext_proc sigma_chan tau_chan Eq_chan s0)
        (ext_proc sigma_chan tau_chan Eq_chan s1)
  | In _ s0 s1 =>
      congr_In (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_proc (up_chan_chan sigma_chan) (up_chan_chan tau_chan)
           (upExt_chan_chan _ _ Eq_chan) s1)
  | Out _ s0 s1 s2 =>
      congr_Out (ext_chan sigma_chan tau_chan Eq_chan s0)
        (ext_chan sigma_chan tau_chan Eq_chan s1)
        (ext_proc sigma_chan tau_chan Eq_chan s2)
  end.
Fixpoint compSubstSubst_proc {k_chan : nat} {l_chan : nat} {m_chan : nat}
(sigma_chan : forall _ : fin m_chan, chan k_chan)
(tau_chan : forall _ : fin k_chan, chan l_chan)
(theta_chan : forall _ : fin m_chan, chan l_chan)
(Eq_chan : forall x,
           eq (funcomp (subst_chan tau_chan) sigma_chan x) (theta_chan x))
(s : proc m_chan) :
eq (subst_proc tau_chan (subst_proc sigma_chan s)) (subst_proc theta_chan s)
:=
  match s with
  | Nil _ => congr_Nil
  | Bang _ s0 =>
      congr_Bang
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s0)
  | Res _ s0 =>
      congr_Res
        (compSubstSubst_proc (up_chan_chan sigma_chan)
           (up_chan_chan tau_chan) (up_chan_chan theta_chan)
           (up_subst_subst_chan_chan _ _ _ Eq_chan) s0)
  | Par _ s0 s1 =>
      congr_Par
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s1)
  | In _ s0 s1 =>
      congr_In
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_proc (up_chan_chan sigma_chan)
           (up_chan_chan tau_chan) (up_chan_chan theta_chan)
           (up_subst_subst_chan_chan _ _ _ Eq_chan) s1)
  | Out _ s0 s1 s2 =>
      congr_Out
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s0)
        (compSubstSubst_chan sigma_chan tau_chan theta_chan Eq_chan s1)
        (compSubstSubst_proc sigma_chan tau_chan theta_chan Eq_chan s2)
  end.
Lemma instId_proc {m_chan : nat} : eq (subst_proc (var_chan m_chan)) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x =>
                 idSubst_proc (var_chan m_chan) (fun n => eq_refl) (id x))).
Qed.
