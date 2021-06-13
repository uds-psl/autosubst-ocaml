
Require Import core core_axioms fintype fintype_axioms.
Import ScopedNotations.
From Chapter9 Require Export stlc.
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
  | [ H2: ?t2 = ?t2 |- _ ] =>
    clear H;
    let H := fresh "H" in
    assert (H: t = t2) by (now asimpl)
  end.

(* this normalization tactic is a bit better since it does not apply asimpl to the original goal (like asimpl in H does)
 It uses the evar tactic to carry out information out of the second goal of the `enough`
 Could also be done by assert instead of enough and matching on the context but this seems safer. *)
Ltac normalize_evar t T :=
  let x := fresh "x" in
  let H := fresh "H" in
  evar (x : T);
  enough (H : t = t);
  [| asimpl;
     match goal with
     | [|- ?t2 = ?t2] =>
       instantiate (x := t2);
       reflexivity
     end ];
  clear H;
  assert (H : t = x) by (subst x; now asimpl);
  subst x.

(*** Testing out asimpl. ***)
(* this subsitution equation that appears for example in step_inst is pretty nice to test since it uses a lot of the lemmas.
 Experience shows that if asimpl works here it works for a lot of other lemmas of Chapter9 *)
Lemma default_subst_lemma {m n} (f : fin m -> tm n) (s : tm (S m)) (t : tm m) :
  s[t..][f] = s[up_tm_tm f][(t[f])..].
Proof.
  now asimpl.
  Restart.
  (* use normalization tactic *)
  normalize_evar (s[t..][f]) (tm n).
  (* manually apply the tactics based on the trace by asimpl
compComp
unfold
funcomp
scons_comp
fsimpl
renComp
varL
instId
fsimpl
funcomp
   *)
  auto_unfold.
  setoid_rewrite compComp_tm.
  unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, upRen_tm_tm, up_ren.
  unfold funcomp.
  (* the scons_comp happens inside fsimpl *)
  fsimpl.
  setoid_rewrite renComp_tm.
  setoid_rewrite varL_tm'.
  (* with this superfluous fsimpl we can see that the [shift >> (t[f] .: n__tm)] on the right evaluates to just n__tm *)
  (* fsimpl. *)
  setoid_rewrite instId_tm'.
  fsimpl.
  minimize.
  reflexivity.
  Restart.
  (* manually apply the tactics again but now we don't eta reduce after scons_comp which affects varL_tm and renComp. Both of these rewrites then fail *)
  auto_unfold.
  setoid_rewrite compComp_tm.
  unfold up_list_tm_tm, up_tm_tm, upRen_list_tm_tm, upRen_tm_tm, up_ren.
  unfold funcomp.
  setoid_rewrite scons_comp'.
  (* eta_reduce. *)
  (* the next rewrites all fail
   TODO make a MWE for this. It appears to fail because it's inside two lambdas (one of which can be removed by eta reduction) *)
  (* setoid_rewrite renComp_tm. *)
  (* setoid_rewrite varL_tm'. *)
  (* setoid_rewrite instId_tm'. *)
  (* fsimpl. *)
  (* minimize. *)
  (* reflexivity. *)
  (* Restart. *)
Abort.

Module MWE.
  (* As I thought the problem appears to be the eta expansion together with another operation (just fold without cons does not work) *)
  Parameter X : Type.
  Parameter op1 : (X -> X) -> X.
  Parameter op2 : X -> (X -> X) -> (X -> X).

  Instance op1_morphism:
    Proper (pointwise_relation _ eq ==> eq) op1.
  Proof.
  Admitted.

  Instance op2_morphism :
    Proper (eq ==> pointwise_relation _ eq ==> pointwise_relation _ eq) op2.
  Proof.
  Admitted.

  Lemma mwe (b:X) (f g h: X -> X) (H: forall x, f (g x) = h x) :
      op1 (op2 b (funcomp f g)) = op1 (op2 b h).
  Proof.
    unfold funcomp.
    setoid_rewrite H. reflexivity.
    Restart.
    unfold funcomp.
    change (op2 b (fun x => f (g x))) with (fun y => (op2 b (fun x => f (g x))) y).
    Set Typeclasses Debug.
    try setoid_rewrite H.
    (* needs eta reduction first *)
    eta_reduce.
    setoid_rewrite H.
    reflexivity.
  Abort.

  Lemma mwe2 (f g h: X -> X) (H: forall x, f (g x) = h x) :
    op1 (funcomp f g) = op1 h.
  Proof.
    unfold funcomp.
    setoid_rewrite H. reflexivity.
    Restart.
    unfold funcomp.
    change (fun x => f (g x)) with (fun y => (fun x => f (g x)) y).
    (* without op2 it works fine *)
    setoid_rewrite H.
    reflexivity.
  Qed.

  Definition const (a b:X) := a.

  (* rewriting the part of the body of a function that does not depend on the argument seems possible *)
  Lemma rewrite_under_eta (a b:X) (H: a = b) :
    (fun x => const a x) = (fun x => const b x).
  Proof.
    rewrite H. reflexivity.
  Qed.

End MWE.

