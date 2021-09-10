
Require Import core fintype.
Import ScopedNotations.
(* From Chapter9 Require Export stlc. *)
Load stlc.
Set Implicit Arguments.
Unset Strict Implicit.
Require Import Setoid Morphisms.

(*** Rewriting laws that have to hold ***)
(* one of the rewriting laws of lambda-sigma *)
Goal forall m (s: tm (S m)), (ren_tm (var_zero .: shift) s) = s.
Proof.
  (* can be proved by asimpl both in the original form and reformulated as a substitution *)
  intros m s.
  asimpl.
  reflexivity.
  Restart.
  intros m s.
  substify.
  asimpl.
  reflexivity.
Qed.

(*** Iea for normalization ***)
(* I want to be able to say assert (H: s[sigma] = _) by (now asimpl)
 * so that it fills in the normal form in the evar.
 * With normal setoid rewriting this is not directly possible because setoid rewriting seems to behave differently on goals of the form
 * `s[sigma] = t[tau]` where it normalizes both sides.
than on goals of the form
 * `s[sigma] = ?E` where it fails to normalize the left side.
 *
 * A hack around this is the following tactic that asserts the trivial equality, then normalizes both sides and then builds another equality where we already know the normal form on the right hand side and proves it again with asimpl.
 * Of course it's slow since it uses asimpl twice.
 * Plus `asimpl in H` is naive and reverts H so asimpl is also applied to the rest of the goal which is not desirable and often defeeats the purpose of the tactic. But we might be able to write a more performant `asimpl in H` tactic.
 *) 
Ltac normalize t :=
  let H := fresh "H" in
  assert (H: t = t) by (reflexivity);
  asimpl in H;
  match goal with
  | [ H: ?t2 = ?t2 |- _ ] =>
    clear H;
    let H := fresh "H" in
    assert (H: t = t2) by (now asimpl)
  end.

(*** Testing out asimpl. ***)
(* Ltac apply_subst_morphism := *)
(*   match goal with *)
(*     | [|- eq (subst_tm ?sigma ?s) (subst_tm ?tau ?t)] => *)
(*       apply subst_morphism; intros ? *)
(*     | [|- context[(subst_tm ?sigma ?s)]] => *)
(*       erewrite subst_morphism *)
(*   end. *)

Inductive Foo {n} : tm n -> Type :=
  FooC : forall s:tm n, Foo s.

Goal forall {m n} (f : fin m -> tm n) (s : tm (S m)) (t : tm m),
    Foo (s[t[f] .: f]) -> Foo (s[t..][f]).
Proof.
  intros * H.
  (* unfortunately it's not practicable to use the normalize tactic because apply is too simple (would have to use rewrite with the morphisms but that has its own set of problems with normalize).
   Idea: use the setoid rewriting version (or the funext version) to find out the normal form and then use the fast tactic to prove it
   If using the setoid rewrite tactic I would need some way of caching it otherwise it's useless
*)
  assert (s[t..][f] = s[t[f] .: f]) as -> by (now asimpl).
  assumption.
(*   normalize (s[t..][f]). *)
(*   asimpl. *)
(*   apply_subst_morphism. *)
(*   2: { *)
(*     intros ?. *)
(*     (* If we just have ?g x on the right hand side of the equality, we can always rewrite with rinstId_tm' (or instId_tm' but the other comes first) *) *)
(* (*      which would then constrain the evar to be ?g = ?s <id> *) *)
(* (*      That's the reason why I always got these <id> terms when I tried to normalize something with this tactic. *) *)
(*     rewrite rinstId_tm'. *)
(*     asimpl. *)
(*   } *)
Abort.


(* this subsitution equation that appears for example in step_inst is pretty nice to test since it uses a lot of the lemmas.
  
 Experience shows that if asimpl works here it works for a lot of other lemmas of Chapter9 *)
Lemma default_subst_lemma {m n} (f : fin m -> tm n) (s : tm (S m)) (t : tm m) :
  s[t..][f] = s[up_tm_tm f][(t[f])..].
Proof.
  (* assert (s[t..][f] = _) by (asimpl; reflexivity). *)
  now asimpl.
Qed.

Lemma default_subst_lemma2 {m n} (f : fin m -> tm n) (s : tm (S m)) (t : tm m) :
  (var_tm var_zero)[t..][f] = subst_tm (@scons (tm n) (S n) t[f] (@scons (tm n) n t[f] var_tm)) (var_tm (shift var_zero)).
Proof.
  now asimpl.
  Restart.
  auto_unfold.
  rewrite substSubst_tm.
  cbn [subst_tm ren_tm].
  fsimpl.
  reflexivity.
Qed.

Definition const {n} (a: fin (S n)) := @var_zero n.

Lemma default_subst_lemma3 {n} (x: fin (S n)):
  @subst_tm (S n) (S n) (@const n >> @var_tm (S n)) (var_tm x) = @subst_tm (S (S n)) (S n) (var_tm x .: @const n >> var_tm) (var_tm (shift x)).
Proof.
  asimpl.
  unfold const.
  reflexivity.
Qed.
