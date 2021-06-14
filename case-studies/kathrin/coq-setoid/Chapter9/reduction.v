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

Lemma step_inst {m n} (f : fin m -> tm n) (s t : tm m) :
  step s t -> step s[f] t[f].
Proof.
   intros st. revert n f.  induction st as  [m b s t |m A b1 b2 _ ih|m s1 s2 t _ ih|m s t1 t2 _ ih]; intros n f; cbn.
   - apply step_beta'.
     now asimpl.
     (* TODO except for the weirdness with the two lambdas the setoid rewriting works in H *)
     (* assert (H: s[t..][f] = s[t..][f]) by reflexivity. *)
     (* auto_unfold in *. *)
     (* setoid_rewrite compComp_tm in H. *)
     (* unfold funcomp in H. *)
     (* setoid_rewrite scons_comp' in H. *)
     (* (* unfold funcomp in H. *) *)
     (* setoid_rewrite varL_tm' in H. *)

(* TODO check why setoid_rewrite fails with two lambdas and how does asimpl not fail? *)
     (* asimpl. *)
(*      auto_unfold. *)
(*      setoid_rewrite compComp_tm. *)
(*      unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, upRen_tm_tm, up_ren. *)
(*      unfold funcomp. *)
(*      fsimpl. *)


     
(* simple refine ?Goal2;setoid_rewrite true *)
(* compComp_tm;(* compComp *)unfold up_list_tm_tm, up_tm_tm, *)
(*                            upRen_list_tm_tm, upRen_tm_tm, up_ren;(*  *)
(* unfold *)unfold funcomp;(* funcomp *)fsimpl ;(*  *)
(* fsimpl *)setoid_rewrite true varL_tm';(* varL *)fsimpl *)
(* ;(* fsimpl *)unfold funcomp;(* funcomp *)setoid_rewrite true *)
(* renComp_tm;(* renComp *)setoid_rewrite true *)
(* varL_tm';(* varL *)setoid_rewrite true instId_tm';(*  *)
(* instId *)<change> *)
(*      auto_unfold. *)
(*      setoid_rewrite compComp_tm. *)
(*      unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, upRen_tm_tm, up_ren. *)
(*      unfold funcomp. *)
(*      setoid_rewrite scons_comp'. *)
(*      (* If I don't do this eta_reduction the rewrite for renComp and the second varL_tm' fails *) *)
(*      (* eta_reduce. *) *)
(*      (* Info 2 fsimpl. *) *)
(*      setoid_rewrite varL_tm'. *)
(*      fsimpl. *)
(*      unfold funcomp. *)
(*      (* minimize. *) *)
(*      setoid_rewrite renComp_tm. *)
(*      setoid_rewrite varL_tm'. *)
(*      setoid_rewrite instId_tm'. *)
(*      minimize. *)
(* compComp *)
(* unfold *)
(* funcomp *)
(* scons_comp *)
(* fsimpl *)
(* varL *)
(* fsimpl *)
(* funcomp *)
(* renComp *)
(* varL *)
(* instId *)
(* funcomp *)
     
(*      normalize (s[t..][f]). *)
(*      (*   Set Typeclasses Debug. *) *)
(*      (* TODO here the rewrite with scons_comp fails b/c setoid rewrite behaves differently when there is an evar *) *)
(*        assert ((subst_tm f (subst_tm (scons t var_tm) s)) = _) *)
(*          by (auto_unfold; setoid_rewrite compComp_tm; unfold funcomp; setoid_rewrite scons_comp'; reflexivity). *)
     (* { *)
     (*   revert H. *)
     (*   unfold funcomp. *)
     (*   setoid_rewrite scons_comp'. *)
     (*   unfold funcomp. *)
     (*   (* minimize. *) *)
     (*   (* unfold funcomp. *) *)
     (*   Set Typeclasses Debug. *)
     (*   try setoid_rewrite varL_tm'. *)
     (*   minimize. *)
     (* } *)
     (* this does not work well with setoid rewriting because apparently it behaves differently but below is a tactic script which should be produced by the non-setoid version of asimpl. *)
(*      assert (s[t..][f] = _) by *)
(*      ( auto_unfold; *)
(*        rewrite compComp_tm; *)
(*        erewrite ext_tm; [reflexivity|]; *)
(*        intros x; *)
(*        rewrite scons_comp''; *)
(*        apply scons_morphism; *)
(*        intros y; *)
(*        rewrite varL_tm''; *)
(*        change (f >> id) with f; *)
(*        eta_reduce; *)
(*        reflexivity *)
(*      ). *)
(* now asimpl. *)
(*      auto_unfold. *)
(*      setoid_rewrite compComp_tm. *)
(*      unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, *)
(*      upRen_tm_tm, up_ren. *)
(*      fsimpl. *)
(*      eta_expand_varL; setoid_rewrite varL_tm''. *)
(*      eta_expand_ren_comp. *)
(*      Set Typeclasses Debug. *)
(*      try setoid_rewrite renComp_tm. *)
(*      simple apply subst_morphism; [|reflexivity]. *)
(*      simple apply scons_morphism. *)
(*      change (fun x => (f >> id) x) with (f >> id). *)

(*      simple apply funcomp_morphism1. *)

(* compComp *)
(* unfold *)
(* scons_comp *)
(* scons_comp *)
(* fsimpl *)
(* varL *)
(* fsimpl *)
(* cbn *)
(* fsimpl *)
     
(*      (* unfold funcomp. *) *)
(*      (* setoid_rewrite renComp_tm. *) *)
(*      eta_expand_ren_comp. *)
(*      (* Set Typeclasses Debug. *) *)
(*      (* Unset Printing Notations. *) *)
(*      (* Set Printing Implicit. *) *)
(*      (* try setoid_rewrite renComp_tm. *) *)
(*      simple apply subst_morphism; [|reflexivity]. *)
(*      simple apply scons_morphism. *)
(*      simple apply funcomp_morphism. *)
     (* now asimpl. *)
     (* auto_unfold. *)
     (* setoid_rewrite compComp_tm. *)
     (* unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, *)
     (* upRen_tm_tm, up_ren. *)
     (* repeat match goal with *)
     (*        | [|- context[funcomp ?tau (scons ?t ?f)]] => *)
     (*          change (funcomp tau (scons t f)) with (fun x => tau (scons t f x)) *)
     (*        end. *)
     (* setoid_rewrite scons_comp'. *)
     (* (* eta_reduce. *) *)
     (* cbn [subst_tm ren_tm]. *)
     (* fsimpl. *)
     (* unfold funcomp. *)
     (* (* TODO minimal working example where the rewrite does not work *) *)
     (* setoid_rewrite renComp_tm. *)
(*      (* simple apply subst_morphism; [|reflexivity]. *) *)
(*      (* simple apply scons_morphism. *) *)
     
(*      Set Typeclasses Debug. *)
     
(*      setoid_rewrite renComp_tm. *)
(*      Unset Printing Notations. *)
(*      change (fun x : fin (S m) => *)
(*         scons (subst_tm f t) *)
(*           (fun x0 : fin m => *)
(*            subst_tm (scons (subst_tm f t) var_tm) (ren_tm shift (f x0))) *)
(*           x) with *)
(*          (scons (subst_tm f t) *)
(*           (fun x0 : fin m => *)
(*            subst_tm (scons (subst_tm f t) var_tm) (ren_tm shift (f x0)))). *)
(*      Set Printing Notations. *)
(*      setoid_rewrite renComp_tm. *)
     
(* compComp *)
(* unfold *)
(* funcomp *)
(* scons_comp *)
(* cbn *)
(* fsimpl *)
(* funcomp *)
(* cbn *)
(* funcomp *)
(*      (* eta_reduce. *) *)
(*      setoid_rewrite renComp_tm. *)
(*      reflexivity. *)
(*      auto_unfold. *)
(*      setoid_rewrite compComp_tm. *)
(*      unfold funcomp. *)
(*      eta_expand_subst; setoid_rewrite scons_comp'; eta_reduce *)
(* compComp *)
(* scons_comp *)
(* cbn *)
(* fsimpl *)
(* funcomp *)
(* renComp *)
(* instId *)
(* cbn *)
(* funcomp *)
(*      auto_unfold. *)
(*      setoid_rewrite compComp_tm. *)
(*      unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, *)
(*      upRen_tm_tm, up_ren. *)
(*      (* Unset Printing Notations. *) *)
(*      (* TODO in order to rewrite with scons_comp' I need a syntactic match already in the goal. Unfortunately it's not enough that the subst_morophism would create a syntactic match. *)
(*       Therefore I need to eta expand here *)
(*       1. either change subst_tm so that it always uses an eta expanded function *)
(*       2. or find some heruistic when to eta expand (I think I would only have to eta expand a function immediately in a subst_tm. But how to check that it is not already eta expanded?) *)

(*       2. works but makes it even slower. Have to test if it works for everything*) *)
(*      setoid_rewrite scons_comp'. *)
(*      fsimpl. *)
(*      (* Set Typeclasses Debug. *) *)
(*      unfold funcomp. *)
(*      cbn.  *)

(*      (* Set Typeclasses Debug. *) *)
(*      (* Unset Printing Notations. *) *)
(*      (* fsimpl. *) *)
(*      try setoid_rewrite renComp_tm. *)
(*      apply subst_morphism; [|reflexivity]. *)
(*      apply scons_morphism. *)
(*      unfold funcomp. *)
(*      intros x. rewrite renComp_tm. *)
(*      intros x. *)
(*      rewrite ?scons_comp'. *)
(*      fsimpl. *)
(*      cbn. *)
(* compComp *)
(* unfold *)
(* funcomp *)
(* fsimpl *)
(* unfold *)
(* funcomp *)
(* funcomp *)

(*      (* TODO scons_comp' setoid rewrite does not work yet :( *) *)
(*      rewrite scons_comp. *)
(*      asimpl. *)

     
  - apply step_abs. eapply ih.
  - apply step_appL, ih.
  - apply step_appR, ih.
Qed.
Print Assumptions step_inst.

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
    (* myasimpl. *)
    (* reflexivity. *)
    (* auto_unfold. *)
    (* rewrite renComp_tm. *)
    (* rewrite compRen_tm. *)
    (* unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, upRen_tm_tm, up_ren. *)
    (* fsimpl. *)
    
    (* rewrite varLRen_tm'. *)
(*     fsimpl. *)
(*     reflexivity. *)
(* renComp *)
(* compRen *)
(* unfold *)
(* fsimpl *)
(* varLRen *)
(* fsimpl *)
   (*  auto_unfold. *)
   (* rewrite renComp_tm. *)
   (* rewrite compRen_tm. *)
   (* simple apply subst_morphism'; intros ?. *)
   (* unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, upRen_tm_tm, up_ren. *)
   (* fsimpl. *)
   (* simple apply scons_morphism'; intros ?. *)
   (* unfold_funcomp. *)
   (* cbn [subst_tm ren_tm]. *)
   (* fsimpl. *)
   (* rewrite varLRen_tm''. *)
   (* unfold_funcomp. *)
   (* fsimpl. *)
   
(* renComp *)
(* compRen *)
(* subst_morph *)
(* unfold *)
(* fsimpl *)
(* scons_morph *)
(* funcomp *)
(* cbn *)
(* fsimpl *)
(* funcomp *)
(* fsimpl *)
(* funcomp *)
(* fsimpl *)
(* funcomp *)
(* fsimpl *)
(* funcomp *)
(* fsimpl *)
(* funcomp *)
(* fsimpl *)
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
