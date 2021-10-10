Require Import List Arith.
Import ListNotations.
Require Import core.


Notation eqdec := eq_nat_dec.

Require Import Lia.

Module renSubst.


Notation upT vs := (0 :: vs).

(* Inductive fin : list nat -> Type := *)
(*   | finO : fin [0] *)
(*   | finS : forall l, fin l -> fin (List.map S l) *)
(*   | finU : forall l, fin l -> fin (upT l). *)

(* Arguments finS {l}. *)
(* Arguments finU {l}. *)

(* should be able to represent any number in an ordered list *)
(* wait that does not really work *)
(* Check finO. *)
(* Check finS finO : fin [1]. *)
(* Check finU (finS finO) : fin [0;2]. *)


Inductive fin : list nat -> Type :=
  | finH : forall n l, fin (n::l) (* the position in the list *)
  | finT : forall n l, fin l -> fin (n::l). (* how big the jump is to the next number *)

Arguments finH _ {l}.
Arguments finT _ {l}.

Fixpoint denote {l: list nat} (x: fin l) : nat :=
  match x with
  | finH n => n
  | finT n x' => n + S (denote x')
  end.

(* flatten [0;1;2] -> [0;0;0]
 * flatten [0;2;3] -> [0;1;0]
 * flatten [1;2;3] -> [1;0;0]
 * flatten [0;3;5] -> [0;2;1] *)
Fixpoint flatten (l: list nat) (acc: nat) : list nat :=
  match l with
  | [] => []
  | x :: l =>
    let x' := x - acc in
    x' :: flatten l (S x)
  end.
Definition fl (l: list nat) : list nat := flatten l 0.

Compute (fl [0]).
Compute (fl [0;1;2]).
Compute (fl [0;2;3]).
Compute (fl [1;2;3]).
Compute (fl [0;3;5]).

Definition f0 : fin (fl [0]) := finH 0.
Definition f1 : fin (fl [0;2;3]) := finH 0. (* denotes 0 *)
Definition f2 : fin (fl [0;2;3]) := finT 0 (finH 1). (* denotes 2 *)
Definition f3 : fin (fl [0;2;3]) := finT 0 (finT 1 (finH 0)). (* denotes 3 *)

Compute (denote f0).
Compute (denote f1).
Compute (denote f2).
Compute (denote f3).


Inductive tm (vs : list nat) : Type :=
  | var_tm : fin vs -> tm vs
  | app : tm vs -> tm vs -> tm vs
  | lam : tm (upT vs) -> tm vs.
Arguments var_tm {vs}.
Arguments app {vs}.
Arguments lam {vs}.

Lemma congr_app {vs : list nat} {s0 : tm vs} {s1 : tm vs} {t0 : tm vs}
  {t1 : tm vs} (H0 : s0 = t0) (H1 : s1 = t1) :
  app s0 s1 = app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
         (ap (fun x => app t0 x) H1)).
Qed.

Lemma congr_lam {vs : list nat} {s0 : tm (upT vs)} {t0 : tm (upT vs)}
  (H0 : s0 = t0) : lam s0 = lam t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam x) H0)).
Qed.


(* Inductive finList3 : list nat -> Type := *)
(*     list0 : forall l, finList3 (0::l) *)
(*   | listC : forall (v w:nat) (vs: list nat), finList3 (v::vs) -> finList3 (S v :: List.map S vs) *)
(*   | listT : forall v vs, finList3 vs -> finList3 (v::vs). *)

Open Scope type.

Definition scons {X : Type} {vs : list nat} (x : X) (f : fin vs -> X) (m : fin (upT vs)) : X.
Proof.
  revert m.
  enough (H: forall vs' (Heq: vs' = upT vs), fin vs' -> X).
  - intros m. exact (H (upT vs) eq_refl m).
  - intros vs' Heq m.
    destruct m.
    + exact x.
    + injection Heq.
      intros -> _.
      exact (f m).
Defined.

Compute (@scons nat (fl [1;2]) 1 (fun _ => 6) f1).
Compute (@scons nat (fl [1;2]) 1 (fun _ => 6) f2).
Compute (@scons nat (fl [1;2]) 1 (fun _ => 6) f3).

Definition var_zero {vs: list nat} : fin (upT vs) := finH 0.

Definition shift {vs: list nat} : fin vs -> fin (upT vs) := finT 0.

Definition up_ren_traced {vs0 vs1 : list nat} (xi: fin vs0 -> fin vs1) : fin (upT vs0) -> fin (upT vs1) :=
  scons var_zero (funcomp shift xi).

Fixpoint ren_tm {vs0 vs1: list nat} (xi_tm : fin vs0 -> fin vs1) (s: tm vs0) {struct s} : tm vs1.
Proof.
  refine (match s with
          | var_tm x => _
          | app s0 s1 => _
          | lam s0 => _
          end).
  - exact (var_tm (xi_tm x)).
  - exact (app (ren_tm _ _ xi_tm s0) (ren_tm _ _ xi_tm s1)).
  - exact (lam (ren_tm _ _ (up_ren_traced xi_tm) s0)).
Defined.

Print Assumptions ren_tm.

Lemma up_tm_tm {vs0 : list nat} {vs1 : list nat} (sigma : fin vs0 -> tm vs1) :
  fin (upT vs0) -> tm (upT vs1).
Proof.
  exact (scons (@var_tm (upT vs1) var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm {vs0 : list nat} {vs1 : list nat} (sigma_tm : fin vs0 -> tm vs1) (s : tm vs0) {struct s}
  : tm vs1.
Proof.
  refine (match s with
          | var_tm x => _
          | app s0 s1 => _
          | lam s0 => _
          end).
  - exact (sigma_tm x).
  - exact (app (subst_tm _ _ sigma_tm s0) (subst_tm _ _ sigma_tm s1)).
  - exact (lam (subst_tm _ _ (up_tm_tm sigma_tm) s0)).
Defined.

Print Assumptions subst_tm.

(* lambda x y . x w (lambda z . w z y) *)
(* lambda . lambda . 1 2 (lambda . 3 0 1) *)
Definition testtm : tm [1].
Proof.
  refine (lam (lam (app (app (* x w *) _ _)
                        (lam (app (app (* w z *) _ _) (* y *) _))))).
  - (* x *)
    cbv.
    (* apparently here Coq's unification is too weak *)
    refine (@var_tm [0;0;1] var_zero).
  - (* outer w *)
    refine (@var_tm [0;0;1] (shift var_zero)).
  - (* inner w *)
    refine (@var_tm [0;0;0;1] (shift (shift var_zero))).
  - (* z *)
    exact (@var_tm (fl [0;1;2;4]) var_zero).
  - (* y *)
    refine (@var_tm (fl [0;1;2;4]) (shift (shift var_zero))).
Defined.

Print Assumptions testtm.
Print testtm.
Compute (ren_tm shift testtm).
Compute (subst_tm var_tm testtm).

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

(* Lemma In_0 : forall vs (H: InN 0 (upT vs)), H = InNCons. *)

(* Lemma in_map_if_nat2 : forall (f: nat -> nat) (l: list nat) (x: nat), *)
(*   in_map_nat *)
Lemma upId_tm_tm {vs : list nat} (sigma : fin vs -> tm vs)
  (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = @var_tm (upT vs) x.
Proof.
  unfold up_tm_tm.
  refine (fun x =>
          match x with
          | finH n => _
          | finT n x' => _
          end).
  - 
  - exact (ap (ren_tm shift) (Eq))
  - (* v = 0 *)
    cbv.
  intros v H.
  (* H: v is either 0 or some number in vs + 1 *)
  inversion H.
  - (* v = 0 *)
    subst v.
    rewrite <- (InN_Cons 0 (List.map S vs) H).
    cbv.
    reflexivity.
  - (* v is some number in vs + 1 *)
    rewrite <- (InN_Carry2 v (List.map S vs) 0 H3 H H2).
    cbn [scons].
    cbv [eq_rect_r eq_rect eq_sym].
    destruct v.
    + exfalso. apply (lt_irrefl _ H3).
    + simpl. unfold funcomp.
      rewrite Eq.
      simpl.
      f_equal.
      apply InN_uniq.
Qed.
    

Fixpoint idSubst_tm {vs : list nat} (sigma_tm : finList2 vs -> tm vs)
(Eq_tm : forall x H, sigma_tm (liftFinList x H) = var_tm H) (s : tm vs) {struct s} :
subst_tm sigma_tm s = s :=
  match s as s0 return subst_tm sigma_tm s0 = s0
  with
  | var_tm s0 => Eq_tm _ s0
  | app s0 s1 => congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | lam s0 => congr_lam (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm sigma_tm Eq_tm) s0)
  end.

Fail Check 1.
(* Lemma upRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n) : *)
(*   fin (S m) -> fin (S n). *)
(* Proof. *)
(* exact (up_ren xi). *)
(* Defined. *)

(* Fixpoint ren_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) *)
(* (s : tm m_tm) {struct s} : tm n_tm := *)
(*   match s with *)
(*   | var_tm _ s0 => var_tm n_tm (xi_tm s0) *)
(*   | app _ s0 s1 => app n_tm (ren_tm xi_tm s0) (ren_tm xi_tm s1) *)
(*   | lam _ s0 => lam n_tm (ren_tm (upRen_tm_tm xi_tm) s0) *)
(*   end. *)

Lemma up_tm_tm {m : nat} {n_tm : nat} (sigma : fin m -> tm n_tm) :
  fin (S m) -> tm (S n_tm).
Proof.
exact (scons (var_tm (S n_tm) var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Lemma up_list_tm_tm (p : nat) {m : nat} {n_tm : nat}
  (sigma : fin m -> tm n_tm) : fin (plus p m) -> tm (plus p n_tm).
Proof.
exact (scons_p p (funcomp (var_tm (plus p n_tm)) (zero_p p))
         (funcomp (ren_tm (shift_p p)) sigma)).
Defined.

Fixpoint subst_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
(s : tm m_tm) {struct s} : tm n_tm :=
  match s with
  | var_tm _ s0 => sigma_tm s0
  | app _ s0 s1 => app n_tm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | lam _ s0 => lam n_tm (subst_tm (up_tm_tm sigma_tm) s0)
  end.

Lemma upId_tm_tm {m_tm : nat} (sigma : fin m_tm -> tm m_tm)
  (Eq : forall x, sigma x = var_tm m_tm x) :
  forall x, up_tm_tm sigma x = var_tm (S m_tm) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_tm_tm {p : nat} {m_tm : nat} (sigma : fin m_tm -> tm m_tm)
  (Eq : forall x, sigma x = var_tm m_tm x) :
  forall x, up_list_tm_tm p sigma x = var_tm (plus p m_tm) x.
Proof.
exact (fun n =>
       scons_p_eta (var_tm (plus p m_tm))
         (fun n => ap (ren_tm (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_tm {m_tm : nat} (sigma_tm : fin m_tm -> tm m_tm)
(Eq_tm : forall x, sigma_tm x = var_tm m_tm x) (s : tm m_tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
  end.

Lemma upExtRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_tm_tm {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_tm p xi x = upRen_list_tm_tm p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
(zeta_tm : fin m_tm -> fin n_tm) (Eq_tm : forall x, xi_tm x = zeta_tm x)
(s : tm m_tm) {struct s} : ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm _ s0 => ap (var_tm n_tm) (Eq_tm s0)
  | app _ s0 s1 =>
      congr_app (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
  end.

Lemma upExt_tm_tm {m : nat} {n_tm : nat} (sigma : fin m -> tm n_tm)
  (tau : fin m -> tm n_tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_tm_tm {p : nat} {m : nat} {n_tm : nat}
  (sigma : fin m -> tm n_tm) (tau : fin m -> tm n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_tm p sigma x = up_list_tm_tm p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_tm (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
(tau_tm : fin m_tm -> tm n_tm) (Eq_tm : forall x, sigma_tm x = tau_tm x)
(s : tm m_tm) {struct s} : subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
  end.

Lemma up_ren_ren_tm_tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_tm_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_tm p zeta) (upRen_list_tm_tm p xi) x =
  upRen_list_tm_tm p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
(rho_tm : fin m_tm -> fin l_tm)
(Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x) (s : tm m_tm) {struct
 s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm _ s0 => ap (var_tm l_tm) (Eq_tm s0)
  | app _ s0 s1 =>
      congr_app (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
  end.

Lemma up_ren_subst_tm_tm {k : nat} {l : nat} {m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_tm) (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_tm_tm {p : nat} {k : nat} {l : nat} {m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_tm) (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_tm_tm p tau) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_tm (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm m_tm) {struct
 s} : subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_ren_tm_tm {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_tm_tm {p : nat} {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_list_tm_tm p zeta_tm)) (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_tm (plus p m_tm)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_tm (shift_p p) (upRen_list_tm_tm p zeta_tm)
                  (funcomp (shift_p p) zeta_tm)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_tm zeta_tm (shift_p p)
                        (funcomp (shift_p p) zeta_tm) (fun x => eq_refl)
                        (sigma n))) (ap (ren_tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x)
(s : tm m_tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma up_subst_subst_tm_tm {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (tau_tm : fin l_tm -> tm m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma fin_n))) (ap (ren_tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_tm_tm {p : nat} {k : nat} {l_tm : nat} {m_tm : nat}
  (sigma : fin k -> tm l_tm) (tau_tm : fin l_tm -> tm m_tm)
  (theta : fin k -> tm m_tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_tm_tm p tau_tm)) (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_tm (plus p l_tm)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_tm (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_tm (shift_p p) (up_list_tm_tm p tau_tm)
                  (funcomp (up_list_tm_tm p tau_tm) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_tm tau_tm (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
(sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
(theta_tm : fin m_tm -> tm l_tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm m_tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
  end.

Lemma rinstInst_up_tm_tm {m : nat} {n_tm : nat} (xi : fin m -> fin n_tm)
  (sigma : fin m -> tm n_tm)
  (Eq : forall x, funcomp (var_tm n_tm) xi x = sigma x) :
  forall x, funcomp (var_tm (S n_tm)) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_tm_tm {p : nat} {m : nat} {n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_tm)
  (Eq : forall x, funcomp (var_tm n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (plus p n_tm)) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_tm (plus p n_tm)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_tm (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_tm {m_tm : nat} {n_tm : nat}
(xi_tm : fin m_tm -> fin n_tm) (sigma_tm : fin m_tm -> tm n_tm)
(Eq_tm : forall x, funcomp (var_tm n_tm) xi_tm x = sigma_tm x) (s : tm m_tm)
{struct s} : ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm _ s0 => Eq_tm s0
  | app _ s0 s1 =>
      congr_app (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | lam _ s0 =>
      congr_lam
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
  end.

Lemma renRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) (s : tm m_tm)
  : subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm)
  (s : tm m_tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
  (s : tm m_tm) : ren_tm xi_tm s = subst_tm (funcomp (var_tm n_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise {m_tm : nat} {n_tm : nat}
  (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq (ren_tm xi_tm)
    (subst_tm (funcomp (var_tm n_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm {m_tm : nat} (s : tm m_tm) : subst_tm (var_tm m_tm) s = s.
Proof.
exact (idSubst_tm (var_tm m_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise {m_tm : nat} :
  pointwise_relation _ eq (subst_tm (var_tm m_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm m_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm {m_tm : nat} (s : tm m_tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise {m_tm : nat} :
  pointwise_relation _ eq (@ren_tm m_tm m_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm)
  (x : fin m_tm) : subst_tm sigma_tm (var_tm m_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise {m_tm : nat} {n_tm : nat}
  (sigma_tm : fin m_tm -> tm n_tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm m_tm))
    sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm)
  (x : fin m_tm) : ren_tm xi_tm (var_tm m_tm x) = var_tm n_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise {m_tm : nat} {n_tm : nat}
  (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm m_tm))
    (funcomp (var_tm n_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

Instance Subst_tm  {m_tm n_tm : nat}: (Subst1 _ _ _) := (@subst_tm m_tm n_tm).

Instance Up_tm_tm  {m n_tm : nat}: (Up_tm _ _) := (@up_tm_tm m n_tm).

Instance Ren_tm  {m_tm n_tm : nat}: (Ren1 _ _ _) := (@ren_tm m_tm n_tm).

Instance VarInstance_tm  {n_tm : nat}: (Var _ _) := (@var_tm n_tm).

Notation "[ sigma_tm ]" := (subst_tm sigma_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "↑__tm" := up_tm (only printing) : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing) : subst_scope.

Notation "⟨ xi_tm ⟩" := (ren_tm xi_tm)
  ( at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
  ( at level 7, left associativity, only printing) : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing) : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
  ( at level 5, format "x __tm", only printing) : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm") :
  subst_scope.

Instance subst_tm_morphism  {m_tm : nat} {n_tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm m_tm n_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

Instance ren_tm_morphism  {m_tm : nat} {n_tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_tm m_tm n_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress
                    unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm,
                     upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm.

End renSubst.

Module fext.

Import
renSubst.

Lemma rinstInst_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) :
  ren_tm xi_tm = subst_tm (funcomp (var_tm n_tm) xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_tm xi_tm _ (fun n => eq_refl) x)).
Qed.

Lemma instId_tm {m_tm : nat} : subst_tm (var_tm m_tm) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_tm (var_tm m_tm) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_tm {m_tm : nat} : @ren_tm m_tm m_tm id = id.
Proof.
exact (eq_trans (rinstInst_tm (id _)) instId_tm).
Qed.

Lemma varL_tm {m_tm : nat} {n_tm : nat} (sigma_tm : fin m_tm -> tm n_tm) :
  funcomp (subst_tm sigma_tm) (var_tm m_tm) = sigma_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_tm {m_tm : nat} {n_tm : nat} (xi_tm : fin m_tm -> fin n_tm) :
  funcomp (ren_tm xi_tm) (var_tm m_tm) = funcomp (var_tm n_tm) xi_tm.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (ren_tm xi_tm) = ren_tm (funcomp zeta_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_tm xi_tm zeta_tm n)).
Qed.

Lemma substRen'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (zeta_tm : fin k_tm -> fin l_tm) :
  funcomp (ren_tm zeta_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_tm sigma_tm zeta_tm n)).
Qed.

Lemma renSubst'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (xi_tm : fin m_tm -> fin k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  funcomp (subst_tm tau_tm) (ren_tm xi_tm) = subst_tm (funcomp tau_tm xi_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_tm xi_tm tau_tm n)).
Qed.

Lemma substSubst'_tm {k_tm : nat} {l_tm : nat} {m_tm : nat}
  (sigma_tm : fin m_tm -> tm k_tm) (tau_tm : fin k_tm -> tm l_tm) :
  funcomp (subst_tm tau_tm) (subst_tm sigma_tm) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_tm sigma_tm tau_tm n)).
Qed.

Ltac asimpl_fext' := repeat (first
                      [ progress setoid_rewrite substSubst_tm_pointwise
                      | progress setoid_rewrite substSubst_tm
                      | progress setoid_rewrite renSubst_tm_pointwise
                      | progress setoid_rewrite renSubst_tm
                      | progress setoid_rewrite substRen_tm_pointwise
                      | progress setoid_rewrite substRen_tm
                      | progress setoid_rewrite renRen'_tm_pointwise
                      | progress setoid_rewrite renRen_tm
                      | progress setoid_rewrite substSubst'_tm
                      | progress setoid_rewrite renSubst'_tm
                      | progress setoid_rewrite substRen'_tm
                      | progress setoid_rewrite renRen'_tm
                      | progress setoid_rewrite varLRen_tm
                      | progress setoid_rewrite varL_tm
                      | progress setoid_rewrite rinstId_tm
                      | progress setoid_rewrite instId_tm
                      | progress
                         unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm,
                          upRen_tm_tm, up_ren
                      | progress cbn[subst_tm ren_tm]
                      | fsimpl_fext ]).

Ltac asimpl_fext := check_no_evars; repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                       Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 
                       in *; asimpl_fext'; repeat try unfold_funcomp.

Tactic Notation "asimpl_fext" "in" hyp(J) := revert J; asimpl_fext; intros J.

Ltac substify_fext := auto_unfold; try repeat erewrite ?rinstInst_tm.

Ltac renamify_fext := auto_unfold; try repeat erewrite <- ?rinstInst_tm.

End fext.

Module interface.

Export renSubst.

Export
fext.

Arguments var_tm {n_tm}.

Arguments lam {n_tm}.

Arguments app {n_tm}.

Hint Opaque subst_tm: rewrite.

Hint Opaque ren_tm: rewrite.

End interface.

Export interface.

