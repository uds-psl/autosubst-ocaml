From Chapter10 Require Import sysf.
Require Import core fintype.
Import ScopedNotations.

Check scons_comp'.
Check scons_p_comp'.


(* TODO this is a substitution lemma not solved by asimpl. *)
Goal forall m n k l (s: tm l n) (sigma: fin m -> tm l n) (f: fin n -> tm l k) (x: fin (S m)),
    subst_tm var_ty f ((s .: sigma) x) = (subst_tm var_ty f s .: sigma >> subst_tm var_ty f) x.
Proof.
  intros *.
  (* asimpl_fext can solve it immediately. *)
  (* now asimpl_fext. *)
  (* I have to manually fold the function composition. Then asimpl can solve the goal.
     This is a disadvantage of the setoid asimpl 
     It relies too much on a syntactic funcomp. *)
  change (subst_tm var_ty f ((s .: sigma) x)) with ((funcomp (subst_tm var_ty f) (s .: sigma)) x).
  revert x. apply pointwise_forall.
  now asimpl. 
  (* TODO here I get the same problem as with scons_p
   * so the problem seems to be that we don't need any morphism.
   * the top is eq and scons follows directly after.
   * In other situations where the rewrite would first have to use a morphisms to traverse e.g a subst_tm, it works correctly.
   * So could we introduce a bogus morphism? *)
Qed.

Require Setoid Morphisms.
Inductive AsimplWrapper {A} := AW : A -> AsimplWrapper.


Goal forall m n k l (s: tm l n) (sigma: fin m -> tm l n) (f: fin n -> tm l k) (x: fin (S m)),
    AW (subst_tm var_ty f ((s .: sigma) x)) = AW ((subst_tm var_ty f s .: sigma >> subst_tm var_ty f) x).
Proof.
  intros *.
  (* yeah that works but it's ugly *)
  rewrite scons_comp'.
  reflexivity.
Qed.


Goal forall m n k l (s: tm l n) (sigma: fin m -> tm l n) (f: fin n -> tm l k) (x: fin (S m)),
    id (subst_tm var_ty f ((s .: sigma) x)) = id ((subst_tm var_ty f s .: sigma >> subst_tm var_ty f) x).
Proof.
  intros *.
  (* yeah that works but it's ugly *)
  rewrite scons_comp'.
  reflexivity.
Qed.

Ltac wrap_id := match goal with
                | [ |- ?x = ?y ] => change (x = y) with (id x = id y)
                | [ |- ?x ] => change x with (id x)
                end.

Goal forall m n k l (s: tm l n) (sigma: fin m -> tm l n) (f: fin n -> tm l k) (x: fin (S m)),
    (subst_tm var_ty f ((s .: sigma) x)) = ((subst_tm var_ty f s .: sigma >> subst_tm var_ty f) x).
Proof.
  intros *.
  (* yeah that works but it's ugly *)
  wrap_id.
  rewrite scons_comp'.
  reflexivity.
Qed.

Goal forall m n k k' l (f: fin m -> tm l k) (g: fin n -> tm l k) (h: fin k -> tm l k') (x: fin (m + n)),
    (subst_tm var_ty h (scons_p m f g x)) = scons_p m (f >> subst_tm var_ty h) (g >> subst_tm var_ty h) x.
Proof.
  intros *.
  rewrite scons_p_comp'.
  Restart.
  intros *.
  wrap_id.
  rewrite scons_p_comp'.
  reflexivity.
Qed.
