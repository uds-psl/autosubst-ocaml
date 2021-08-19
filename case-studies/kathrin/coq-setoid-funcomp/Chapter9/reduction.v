(** ** Reduction and Values *)

Require Export ARS Coq.Program.Equality.
Require Import core fintype.
Import ScopedNotations.
From Chapter9 Require Export stlc.
Set Implicit Arguments.
Unset Strict Implicit.

Ltac inv H := dependent destruction H.
Hint Constructors star.

(** *** Single-step reduction *)
Inductive step {n} : tm n -> tm n -> Prop :=
| step_beta A b t : step (app (lam A b) t) (b[t..])
| step_abs A b1 b2 : @step (S n) b1 b2 -> step (lam A b1) (lam A b2)
| step_appL s1 s2 t : step s1 s2 -> step (app s1 t) (app s2 t)
| step_appR s t1 t2 : step t1 t2 -> step (app s t1) (app s t2).

Hint Constructors step.

Lemma step_beta' n A b (t t': tm n):
  t' = b[t..] -> step (app (lam A b) t) t'.
Proof. intros ->. now constructor. Qed.

(** *** Multi-step reduction *)

Lemma mstep_lam n A (s t : tm (S n)) :
  star step s t -> star step (lam A s) (lam A t).
Proof. induction 1; eauto. Qed.

Lemma mstep_app n (s1 s2 : tm n) (t1 t2 : tm n) :
  star step s1 s2 -> star step t1 t2 -> star step (app s1 t1) (app s2 t2).
Proof with eauto.
  intros ms. induction 1. induction ms... auto...
Qed.

(** *** Substitutivity *)

(* Ltac fsimpl2 := *)
(*   repeat match goal with *)
(*          | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *); idtac "id comp" *)
(*          | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *); idtac "comp id" *)
(*          | [|- context [id ?s]] => change (id s) with s; idtac "ideval" *)
(*          | [|- context[(?f >> ?g) >> ?h]] => change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *); idtac "funcomp assoc" *)
(*          (* | [|- zero_p >> scons_p ?f ?g] => rewrite scons_p_head *) *)
(*          | [|- context[(?s .: ?sigma) var_zero]] => change ((s.:sigma) var_zero) with s; idtac "scons head" *)
(*          | [|- context[(?s .: ?sigma) (shift ?m)]] => change ((s.:sigma) (shift m)) with (sigma m); idtac "scons tail" *)
(*          | [|- context[idren >> ?f]] => change (idren >> f) with f; idtac "idren comp" *)
(*          | [|- context[?f >> idren]] => change (f >> idren) with f; idtac "comp idren" *)
(*          | [|- context[?f >> (?x .: ?g)]] => change (f >> (x .: g)) with g (* f should evaluate to shift *); idtac "shift scons" *)
(*          | [|- context[?x2 .: (funcomp ?f shift)]] => change (scons x2 (funcomp f shift)) with (scons (f var_zero) (funcomp f shift)); setoid_rewrite (@scons_eta' _ _ f); eta_reduce; idtac "scons eta 1" *)
(*          | [|- context[?f var_zero .: ?g]] => change (scons (f var_zero) g) with (scons (f var_zero) (funcomp f shift)); setoid_rewrite scons_eta'; eta_reduce; idtac "scons eta 2" *)
(*          |[|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s); idtac "funcomp 1" *)
(*          |[|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s); idtac "funcomp 2" *)
(*          | [|- context[funcomp _ (scons _ _)]] => setoid_rewrite scons_comp'; eta_reduce; idtac "scons comp" *)
(*          | [|- context[funcomp _ (scons_p _ _ _)]] => setoid_rewrite scons_p_comp'; eta_reduce; idtac "scons_p comp" *)
(*          | [|- context[scons (@var_zero ?n) shift]] => setoid_rewrite scons_eta_id'; eta_reduce; idtac "eta_id" *)
(*          (* | _ => progress autorewrite with FunctorInstances *) *)
(*          | [|- context[funcomp (zero_p _) (scons_p _ _ _)]] => setoid_rewrite scons_p_head'; idtac "head" *)
(*          | [|- context[funcomp (shift_p _) (scons_p _ _ _)]] => setoid_rewrite scons_p_tail'; idtac "tail" *)
(*          end. *)

(* Ltac asimpl2' := repeat (first *)
(*                  [ progress setoid_rewrite substSubst_tm; idtac "substSubst" *)
(*                  | progress setoid_rewrite renSubst_tm; idtac "renSubst" *)
(*                  | progress setoid_rewrite substRen_tm; idtac "substRen" *)
(*                  | progress setoid_rewrite renRen_tm; idtac "renRent" *)
(*                  | progress setoid_rewrite varLRen'_tm; idtac "varLRen" *)
(*                  | progress setoid_rewrite varL'_tm; idtac "varL" *)
(*                  | progress setoid_rewrite rinstId'_tm; idtac "rinstId" *)
(*                  | progress setoid_rewrite instId'_tm; idtac "instId" *)
(*                  | progress *)
(*                     unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, *)
(*                      upRen_tm_tm, up_ren; idtac "unfold" *)
(*                  | progress cbn[subst_tm ren_tm]; idtac "cbn" *)
(*                  | idtac "presimpl"; progress fsimpl2; idtac "fsimpl" ]). *)

(* Ltac asimpl2 := check_no_evars; repeat try unfold_funcomp; *)
(*                 repeat *)
(*                  unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1, *)
(*                   Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *; *)
(*                 asimpl2'; minimize. *)

Lemma step_inst {m n} (f : fin m -> tm n) (s t : tm m) :
  step s t -> step (subst_tm f s) (subst_tm f t).
Proof.
   intros st. revert n f.  induction st as  [m b s t |m A b1 b2 _ ih|m s1 s2 t _ ih|m s t1 t2 _ ih]; intros n f; cbn.
   - apply step_beta'.
     (* TODO declare those as opaue. otherwise setoid rewrite does spurious rewrites -> infinite loop
      * any var_tm can be expanded to (ren_tm id var_tm) and then varLRen triggers *)
     Hint Opaque ren_tm : rewrite.
     Hint Opaque subst_tm : rewrite.
     now asimpl.
     (* check_no_evars; repeat try unfold_funcomp; *)
     (*   repeat *)
     (*     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1, *)
     (*   Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *. *)
     (* (first *)
     (*             [ progress setoid_rewrite substSubst_tm; idtac "substSubst" *)
     (*             | progress setoid_rewrite renSubst_tm; idtac "renSubst" *)
     (*             | progress setoid_rewrite substRen_tm; idtac "substRen" *)
     (*             | progress setoid_rewrite renRen_tm; idtac "renRent" *)
     (*             | progress setoid_rewrite varLRen'_tm; idtac "varLRen" *)
     (*             | progress setoid_rewrite varL'_tm; idtac "varL" *)
     (*             | progress setoid_rewrite rinstId'_tm; idtac "rinstId" *)
     (*             | progress setoid_rewrite instId'_tm; idtac "instId" *)
     (*             | progress *)
     (*                unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, *)
     (*                 upRen_tm_tm, up_ren; idtac "unfold" *)
     (*             | progress cbn[subst_tm ren_tm]; idtac "cbn" *)
     (*             | idtac "presimpl"; progress fsimpl2; idtac "fsimpl" ]). *)
     (* Unset Printing Notations. *)
     (* unfold up_tm_tm. *)
     (* (* rewrite_strat innermost varLRen'_tm. *) *)
     (* (* rewrite_strat innermost varLRen'_tm. *) *)
     (* (* setoid_rewrite -> varLRen'_tm. *) *)
     (* fsimpl2. *)
  - apply step_abs. eapply ih.
  - apply step_appL, ih.
  - apply step_appR, ih.
Qed.

Lemma mstep_inst m n (f : fin m -> tm n) (s t : tm m) :
  star step s t -> star step (s[f]) (t[f]).
Proof. induction 1; eauto using step_inst. Qed.

Lemma mstep_subst m n (f g : fin m -> tm n) (s t : tm m) :
  star step s t -> (forall i, star step (f i) (g i)) ->
  star step (s[f]) (t[g]).
Proof with eauto.
  intros st fg.
  apply star_trans with (y := t[f]); [eauto using mstep_inst|].
  clear s st. revert n f g fg.
  induction t; eauto using mstep_app; intros; simpl.
  - cbn. apply mstep_lam. apply IHt. intros [i|]; [|constructor].
    + asimpl.  cbn. unfold funcomp. substify. now apply mstep_inst.
Qed.

Lemma mstep_beta n (s1 s2 : tm (S n)) (t1 t2 : tm n) :
  star step s1 s2 -> star step t1 t2 ->
  star step (s1 [t1..]) (s2 [t2..]).
Proof.
  intros st1 st2. apply mstep_subst; [assumption|].
  now intros [|].
Qed.

Lemma step_naturality m n (M: tm m) (rho: fin m -> fin n) M' :
  step (M ⟨rho⟩) M' -> exists M'', step M M'' /\ M' = (M'' ⟨rho⟩).
Proof.
  intros H.
  dependent induction H.
  - destruct M; try inversion x. subst.
    destruct M1; try inversion H0. subst.
    exists (M1[M2..]). split. eauto.
    asimpl. reflexivity.
  - destruct M; inversion x. subst.
    edestruct (IHstep _ M) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - destruct M; inversion x. subst.
    edestruct (IHstep _ M1) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
  - destruct M; inversion x. subst.
    edestruct (IHstep _ M2) as (?&?&?); [reflexivity|].
    subst. eexists; eauto.
Qed.

Definition value {m} (e : tm m) : Prop :=
  match e with
  | lam  _ _ => True
  | _ => False
  end.

Lemma value_anti {m n} (xi : fin m -> fin n) (s : tm m) :
  value (s⟨xi⟩) -> value s.
Proof.
  destruct s; eauto.
Qed.
