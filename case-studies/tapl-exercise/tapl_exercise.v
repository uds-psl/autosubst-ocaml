
(** 
  We were able to mechanize the first three steps of Exercise 23.6.3 of Types and Programming Languages (page 356)
  Autosubst was a great help because it lowers the burden of starting to work on an exercise.
  If I didn't have Autosubst available, I would not have attempted to mechanize the exercise 
    because the substitution boilerplate is so tedious.

  Andrej told me that the rest of the steps (3-7) are probably very hard to prove in Coq 
  because they are always talking about "forms" which is hard to control in Coq.
    
  I tried around a little bit, defining more well-formed predicates.
  It went nowehere, though, because writing proofs with them is hard.  
  But this is not a failing of Autosubst.
  *)
Require Import Arith.
Require Import sysf.
Require Import core unscoped.
Require List.
Import List.ListNotations.
Open Scope list.

(* we define an erasure of system F into the lambda calculus *)
Inductive utlc :=
| var_utlc : nat -> utlc
| app_utlc : utlc -> utlc -> utlc
| lam_utlc : utlc -> utlc.

Scheme Equality for utlc.
Scheme Equality for ty.
Scheme Equality for tm.

(*** Evaluation ***)
Inductive isval : tm -> Prop :=
| isval_lam : forall T s, isval (lam T s)
| isval_tlam : forall s, isval (tlam s).

Inductive eval : tm -> tm -> Prop :=
| eval_app1 : forall s s' t, eval s s' -> eval (app s t) (app s' t)
| eval_app2 : forall v t t', isval v -> eval t t' -> eval (app v t) (app v t')
| eval_app_lam : forall T s v, isval v -> eval (app (lam T s) v) (subst_tm var_ty (scons v var_tm) s)
| eval_tapp : forall T s s', eval s s' -> eval (tapp s T) (tapp s' T)
| eval_tapp_tlam : forall T s, eval (tapp (tlam s) T) (subst_tm (scons T var_ty) var_tm s).


(*** Typing ***)

Inductive has_type (Gamma: list ty): tm -> ty -> Prop :=
| has_type_var :
    forall x T,
      List.nth_error Gamma x = Some T ->
      has_type Gamma (var_tm x) T
| has_type_lam :
    forall T1 T2 s,
      has_type (T1 :: Gamma) s T2 ->
      has_type Gamma (lam T1 s) (arr T1 T2)
| has_type_app :
    forall T1 T2 s t,
      has_type Gamma s (arr T1 T2) ->
      has_type Gamma t T1 ->
      has_type Gamma (app s t) T2
| has_type_tlam :
    forall s T,
      (* increment all the indices in the environment. because we go under a binder, if we access a type in the environment in `s` we need to jump over one more tlam *)
      has_type (List.map (ren_ty S) Gamma) s T ->
      has_type Gamma (tlam s) (all T)
| has_type_tapp :
    forall s T1 T2,
      has_type Gamma s (all T1) ->
      has_type Gamma (tapp s T2) (subst_ty (scons T2 var_ty) T1).

Definition foo := tlam (lam (var_ty 0) (var_tm 0)).
Definition fooT := all (arr (var_ty 0) (var_ty 0)).

Goal has_type [] foo fooT.
Proof.
  unfold foo, fooT.
  apply has_type_tlam. apply has_type_lam.
  cbn. apply has_type_var. cbn. reflexivity.
Qed.

(*** Util ***)

Lemma nth_error_map {X Y:Type} : forall (l:list X) (f: X -> Y) y n,
    List.nth_error (List.map f l) n = Some y ->
    exists x, List.nth_error l n = Some x /\ y = f x.
Proof.
  intros * H. 
  destruct (List.nth_error l n) as [x'|] eqn:E.
  - exists x'. split. reflexivity. 
    specialize (List.map_nth_error f  _ _ E) as H'.
    rewrite H' in H. injection H. intros ->. reflexivity.
  - exfalso.
    (* we know that it cannot be None since map does not change the length *)
    rewrite List.nth_error_None in E.
    apply (Lt.le_not_lt _ _ E).
    rewrite <- (List.map_length f).
    apply List.nth_error_Some. 
    intros H'. rewrite H' in H. discriminate H.
Qed.

(*** Progress ***)
Lemma canonical_form_arr :
  forall t T1 T2,
    has_type [] t (arr T1 T2) ->
    isval t ->
    exists u, t = (lam T1 u).
Proof.
  intros * Htype Hval.
  inversion Hval; subst.
  - inversion Htype; subst. exists s. reflexivity.
  - inversion Htype.
Qed.

Lemma canonical_form_all :
  forall t T,
    has_type [] t (all T) ->
    isval t ->
    exists u, t = (tlam u).
Proof.
  intros * Htype Hval.
  inversion Hval; subst.
  - inversion Htype.
  - exists s. reflexivity.
Qed.

(* turns out I don't even need the progress lemma *)
Lemma sysf_progress :
  forall s T, has_type [] s T -> isval s \/ exists s', eval s s'.
Proof.
  intros * Htype.
  remember [] as Gamma.
  induction Htype; subst Gamma.
  - exfalso. destruct x; discriminate H.
  - left. constructor.
  - right. destruct (IHHtype1 eq_refl) as [H|(s' & Hs')].
    + destruct (IHHtype2 eq_refl) as [H'|(t' & Ht')].
      * (* canonical form lemma *)
        specialize (canonical_form_arr s T1 T2 Htype1 H) as (u & Hu).
        subst s. exists (subst_tm var_ty (scons t var_tm) u).
        constructor; assumption.
      * exists (app s t'). constructor; assumption.
    + exists (app s' t). constructor. assumption.
  - left. constructor.
  - right. destruct (IHHtype eq_refl) as [H|(s' & Hs')].
    + (* canonical form lemma *)
      specialize (canonical_form_all s T1 Htype H) as (u & Hu).
      subst s. exists (subst_tm (scons T2 var_ty) var_tm u).
      constructor.
    + exists (tapp s' T2). constructor. assumption.
Qed.

(*** Preservation ***)

Lemma context_renaming_lemma :
  forall Gamma Gamma' s T xi zeta ,
    (forall x T, List.nth_error Gamma x = Some T ->
            List.nth_error Gamma' (zeta x) = Some (ren_ty xi T)) ->
  has_type Gamma s T -> has_type Gamma' (ren_tm xi zeta s) (ren_ty xi T).
Proof.
  intros * H Htype.
  induction Htype in Gamma', H, xi, zeta |- *.
  - constructor. apply H, H0.
  - cbn. constructor.
    apply IHHtype.
    intros [|x] T Hx.
    + cbn. injection Hx. intros ->. reflexivity.
    + cbn. apply H. apply Hx.
  - cbn. econstructor.
    + apply IHHtype1.
      intros x T Hx.
      apply H, Hx.
    + fold ren_ty.
      apply IHHtype2.
      intros x T Hx.
      apply H, Hx.
  - cbn. constructor.
    apply IHHtype.
    intros x Tx Hx.
    unfold upRen_ty_tm.
    unfold upRen_ty_ty. unfold up_ren.
    specialize (nth_error_map _ _ _ _ Hx) as (Tx' & HTx0 & HTx1).
    specialize (H _ _ HTx0).
    specialize (List.map_nth_error (ren_ty S) _ _ H).
    (* now autoubst should be enough to form Hren into the goal *)
    rewrite HTx1.
    now asimpl.
    (* instead of asimpl, we can use the below script. *)
    (* rewrite renRen_ty. intros Hren.
    subst Tx.
    rewrite renRen_ty.
    rewrite (extRen_ty _ (funcomp S xi)).
    exact Hren.
    intros [|n].
    + cbn. reflexivity.
    + cbn. reflexivity. *)
  - cbn.
    (* this should be the substitution lemma we want to prove *)
    assert (ren_ty xi (subst_ty (scons T2 var_ty) T1) = subst_ty (scons (ren_ty xi T2) var_ty) (ren_ty (upRen_ty_ty xi) T1)) as ->.
    {
      asimpl.
      apply ext_ty.
      intros [|x].
      - cbn. reflexivity.
      - cbn. reflexivity.
      (* instead of asimpl we can use the below script *)
      (* rewrite compRen_ty.
      rewrite renComp_ty.
      apply ext_ty.
      intros [|x].
      - cbn. reflexivity.
      - cbn. reflexivity. *)
    }
    constructor.
    apply IHHtype.
    intros x T Hx.
    apply H, Hx.
Qed.
    
Lemma context_morphism_lemma :
  forall Gamma Gamma' s T sigma tau,
  (forall x T, List.nth_error Gamma x = Some T -> has_type Gamma' (tau x) (subst_ty sigma T)) ->
  has_type Gamma s T -> has_type Gamma' (subst_tm sigma tau s) (subst_ty sigma T).
Proof.
  intros * H Htype.
  induction Htype in Gamma', sigma, tau, H |- *.
  - cbn. apply H, H0.
  - cbn. constructor.
    rewrite (ext_tm _ _ sigma (up_tm_tm tau)).
    2: {
      now asimpl.
    }
    2: intros x; reflexivity.
    apply IHHtype.
    unfold up_tm_tm.
    intros [|x] T Hx.
    + cbn. constructor. cbn.
      injection Hx. intros ->. reflexivity.
    + cbn. 
      rewrite <- rinstId'_ty.
      eapply context_renaming_lemma.
      2: apply H, Hx.
      intros [|n] Tn Hn.
      * cbn. destruct Gamma'. discriminate Hn. cbn in Hn.
        injection Hn. intros ->. now asimpl.
      * cbn. destruct Gamma'. discriminate Hn. cbn in Hn.
        rewrite Hn. now asimpl.
  - cbn. econstructor.
    + apply IHHtype1.
      intros x T Hx. apply H, Hx.
    + apply IHHtype2.
      intros x T Hx. apply H, Hx.
  - cbn. constructor.
    apply IHHtype.
    intros x Tx Hx.
    specialize (nth_error_map _ _ _ _ Hx) as (Tx' & HTx0 & HTx1).
    specialize (H _ _ HTx0).
    unfold up_ty_tm, up_ty_ty, funcomp.
    rewrite HTx1.
    asimpl.
    (* rewrite renComp_ty. unfold funcomp. cbn.
    change (fun x0 => ren_ty shift (sigma x0)) with (funcomp (ren_ty shift) sigma). *)
    rewrite <- substRen_ty.
    eapply context_renaming_lemma.
    2: exact H.
    intros [|n] Tn Hn.
    + cbn. destruct Gamma'. discriminate Hn.
      cbn. cbn in Hn. injection Hn as ->. reflexivity.
    + cbn. destruct Gamma'. discriminate Hn.
      cbn. cbn in Hn.
      apply List.map_nth_error. apply Hn.
  - cbn.
    assert (subst_ty sigma (subst_ty (scons T2 var_ty) T1) = subst_ty (scons (subst_ty sigma T2) var_ty) (subst_ty (up_ty_ty sigma) T1)) as ->.
    {
      now asimpl.
      (* instead of asimpl the below script also works *)
      (* rewrite compComp_ty.
      rewrite compComp_ty.
      apply ext_ty.
      intros [|x].
      - cbn. reflexivity.
      - cbn. (* should be true. when we shift (sigma x) the next substitution will just decrement all indices again *)
        unfold funcomp.
        rewrite renComp_ty.
        rewrite (ext_ty _ var_ty).
        rewrite idSubst_ty. reflexivity.
        intros n; reflexivity.
        intros [|n].
        cbn. reflexivity.
        cbn. reflexivity. *)
    }
    constructor.
    apply IHHtype.
    intros x T Hx.
    apply H, Hx.
Qed.

(* it was pleasantly simple to prove preservation which I can then use to prove some part of the TAPL exercise.
   It is a bit strange that I have to sometime `rewrite <- idSubst` to be able to 
      apply the context_renaming_lemma/context_morphism_lemma *)
Lemma sysf_preservation :
  forall Gamma s s' T, has_type Gamma s T -> eval s s' -> has_type Gamma s' T.
Proof.
  intros * Htype Heval.
  induction Heval in Htype, T |- *; inversion Htype; subst.
  - econstructor. 2: exact H3.
    apply IHHeval, H1.
  - econstructor. 1: exact H2.
    apply IHHeval, H4.
  - inversion H2; subst.
    rewrite <- idSubst_ty with (sigma_ty := var_ty).
    2: intros x; trivial.
    apply context_morphism_lemma with (Gamma:=T1 :: Gamma).
    2: exact H1.
    intros x Tx.
    rewrite idSubst_ty. 2: intros n; trivial.
    destruct x as [|x].
    + cbn. intros [=].
      subst.  exact H4.
    + cbn. intros Hnth.
      constructor. exact Hnth.
  - econstructor. apply IHHeval, H2.
  - inversion H2; subst.
    apply context_morphism_lemma with (Gamma:=List.map (ren_ty S) Gamma).
    2: exact H1.
    intros x Tx H.
    (* I think I proved this goal before somewhere.
     Intuitively holds because of H, T1 does not contain a 0, so the substitution does not do anything *)
    specialize (@nth_error_map ty _ _ _ _ _ H) as (T1' & HT1 & HT1').
    rewrite HT1'.
    (* from here the lemmas from autosubst should suffice *)
    asimpl.
    constructor. apply HT1.
Qed.

(* characterization of exposed terms *)
Inductive exposed : tm -> Prop :=
| ex_var : forall n, exposed (var_tm n)
| ex_lam : forall T s, exposed (lam T s)
| ex_app : forall s t, exposed (app s t).

(* A predicate on terms that should model the "sequences" from TAPL.
  The first nat represents the nested type applications
  The second nat represents the nested type abstractions
*)
Inductive wf : tm -> nat -> nat -> Prop :=
| wf_empty : forall u, exposed u -> wf u 0 0
| wf_tapp : forall s T l, wf s 0 l -> wf (tapp s T) 0 (S l)
| wf_tlam : forall s n l, wf s n l -> wf (tlam s) (S n) l.

(* definition of erasure into utlc *)
Fixpoint erase (s: tm) : utlc :=
  match s with
  | var_tm n => var_utlc n
  | lam T t => lam_utlc (erase t)
  | app s t => app_utlc (erase s) (erase t)
  | tlam t => erase t
  | tapp t _ => erase t
  end.

(* This should be a correct formalization of exercise 23.6.3 1) *)
Lemma lemma_23_6_3_1:
  forall Gamma t T m, has_type Gamma t T -> erase t = m ->
                 exists Gamma' s T', has_type Gamma' s T' /\ erase s = m. 
Proof.
  (* intros Gamma t. revert Gamma. *)
  intros * Htype Herase. 
  induction t in Gamma, T, Htype, Herase |- *.
  - exists Gamma, (var_tm n), T. now split.
  - exists Gamma, (app t1 t2), T. now split.
  - inversion Htype. subst.
    apply (IHt Gamma (all T1) H2 eq_refl).
  - exists Gamma, (lam t t0), T. now split.
  - inversion Htype. subst.
    apply (IHt _ T0 H0 eq_refl).
Qed.

Print Assumptions lemma_23_6_3_1.

Import UnscopedNotations.


Lemma erase_subst: forall s m sigma_ty,
    erase s = m -> erase (subst_tm sigma_ty var_tm s) = m.
Proof.
  intros * Herase.
  induction s in sigma_ty, Herase, m |- *.
  - assumption.
  - cbn. cbn in Herase.
    rewrite (IHs1 _ sigma_ty eq_refl), (IHs2 _ sigma_ty eq_refl).
    assumption.
  - cbn. apply (IHs _ sigma_ty Herase).
  - cbn.
    (* I think need a morphism for ersae to apply my asimpl but I don't really care about functional extensionality *)
    asimpl_fext.
    specialize (IHs (erase s) (up_tm_ty sigma_ty) eq_refl).
    asimpl in IHs.
    rewrite IHs. assumption.
  - cbn.
    asimpl_fext.
    rewrite (IHs (erase s) _ eq_refl). assumption.
Qed.

Print Assumptions erase_subst.
    
Lemma wf_subst: forall s n l sigma_ty,
    wf s n l -> wf (subst_tm sigma_ty var_tm s) n l.
Proof.
  intros * Hwf.
  induction s in sigma_ty, n, l, Hwf |- *.
  - cbn. exact Hwf.
  - cbn.
    inversion Hwf. subst.
    constructor. constructor.
  - inversion Hwf. inversion H.
    subst. cbn. constructor.
    apply IHs, H3.
  - inversion Hwf. constructor. constructor.
  - inversion Hwf. inversion H.
    subst. cbn. constructor.
    apply (IHs n0 l), H0.
Qed.


(* This should be a correct formalization of exercise 23.6.3 2) *)
Lemma lemma_23_6_3_2:
  forall Gamma t T m, has_type Gamma t T -> erase t = m ->
                 exists s n l, has_type Gamma s T /\ erase s = m /\ wf s n l.
Proof.
  intros Gamma t. revert Gamma.
  induction t; intros * Htype Herase.
  - exists (var_tm n), 0, 0. repeat split.
    1, 2: assumption. constructor. constructor.
  - exists (app t1 t2), 0, 0. repeat split.
    1, 2: assumption. constructor. constructor.
  - inversion Htype. subst T s T2.   
    specialize (IHt Gamma (all T1) m H2 Herase) as (s & n & l & IH0 & IH1 & IH2).
    destruct n as [|n'].
    + exists (tapp s t0), 0, (S l). repeat split.
      constructor. assumption.
      apply IH1.
      constructor. assumption.
    + inversion IH2; subst.
      exists (subst_tm (t0 .: var_ty) var_tm s0), n', l. repeat split.
      * (* this statement follows from preservation if I can prove that (tapp (tlam s0) t0) has the correct type *)
        enough (has_type Gamma (tapp (tlam s0) t0) (subst_ty (t0 .: var_ty) T1)).
        apply (sysf_preservation _ _ _ _ H). constructor.
        constructor. apply IH0.
        (* At first I thought the substitutivity of erasure and wf does not hold.
           It does not seem to hold in general but we only need a special case *)
      * (* substitutivity of erasure, subtituting does no change structure so this should be easy case analysis on s0 *)
        apply erase_subst. exact IH1.
      * (* substitutivity of well-formedness, same as erasure it does not change the structure of s0 so it should be easy *)
        apply wf_subst. apply H1.
  - exists (lam t t0), 0, 0. repeat split.
    1, 2: assumption. constructor. constructor.
  - inversion Htype. subst T s. 
    specialize (IHt (List.map (ren_ty S) Gamma) T0 m H0 Herase) as (s & n & l & IH0 & IH1 & IH2).
    exists (tlam s), (S n), l. repeat split.
    + constructor. assumption.
    + apply IH1.
    + constructor. assumption.
Qed.

Print Assumptions lemma_23_6_3_2.

Require Import Lia.
Lemma bin_size_ind (f : nat -> nat -> nat) (P : nat -> nat -> Type) :
  (forall x y, (forall x' y', f x' y' < f x y -> P x' y') -> P x y) -> forall x y, P x y.
Proof.
  intros H x y. apply H.
  induction (f x y).
  - intros x' y'. lia.
  - intros x' y' H'. apply H.
    intros x'' y'' H''. apply (IHn x'' y''). lia.
Qed.

Inductive wf' : tm -> tm -> nat -> nat -> Prop :=
| wf'_empty : forall u, wf' u u 0 0
| wf'_tapp : forall s u T l, wf' s u 0 l -> wf' (tapp s T) u 0 (S l)
| wf'_tlam : forall s u n l, wf' s u n l -> wf' (tlam s) u (S n) l.

Inductive wf'' : tm -> tm -> nat -> nat -> Prop :=
| wf''_empty : forall u, exposed u -> wf'' u u 0 0
| wf''_tapp : forall s u T n l, wf'' s u n l -> wf'' (tapp s T) u n (S l)
| wf''_tlam : forall s u n l, wf'' s u n l -> wf'' (tlam s) u (S n) l.

Lemma wf''_exposed : forall t u n l, wf'' t u n l -> exposed u.
Proof.
  intros t u n l. revert t u. revert n l.
  refine (bin_size_ind (fun x y => x + y) _ _).
  intros n l IH t u Hwf.
  destruct (n + l) as [|nl] eqn:E.
  - apply plus_is_O in E as [En El]. subst n l.
    inversion Hwf. exact H.
  - inversion Hwf; subst.
    + exact H.
    + eapply IH. 2: exact H.
      lia.
    + eapply IH. 2: exact H.
      lia.
Qed.

Lemma wf''_complete : forall t, exists r n l, wf'' t r n l.
Proof.
  induction t.
  - exists (var_tm n), 0, 0. constructor. constructor.
  - exists (app t1 t2), 0, 0. constructor. constructor.
  - destruct IHt as (r & n & l & IH).
    exists r, n, (S l).
    constructor. exact IH.
  - exists (lam t t0), 0, 0. constructor. constructor.
  - destruct IHt as (r & n & l & IH).
    exists r, (S n), l.
    constructor. exact IH.
Qed.


Lemma lemma_23_6_3_3 :
  forall Gamma t m n T, exposed t -> has_type Gamma t T -> erase t = app_utlc m n ->
    exists s u U, has_type Gamma s (arr U T) /\ erase s = m /\ 
                  has_type Gamma u U /\ erase u = n /\ 
                  t = app s u.
Proof.  
  intros Gamma t. revert Gamma.
  destruct t; intros * Hext HTt Hert; 
    try discriminate Hert. (* takes care of cases where erase does not change the constructor. *)
  - inversion HTt; subst.
    inversion Hert; subst. 
    exists t1, t2, T1; repeat split; assumption.
  - inversion Hext. (* tapp is thrown away by erase but cannot be exposed. *)
  - inversion Hext. (* tlam is thrown away by erase but cannot be exposed. *)
Qed.
