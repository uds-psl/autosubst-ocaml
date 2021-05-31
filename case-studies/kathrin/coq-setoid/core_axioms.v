(** * General Header Autosubst - Assumptions and Definitions *)

(** ** Axiomatic Assumptions
    For our development, during rewriting of the reduction rules,  we have to extend Coq with two well known axiomatic assumptions, namely _functional extensionality_ and _propositional extensionality_. The latter entails _proof irrelevance_.
*)

(** *** Functional Extensionality
    We import the axiom from the Coq Standard Library and derive a utility tactic to make the assumption practically usable.
*)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.Tactics.
Require Import core.

Tactic Notation "autosubst_nointr" tactic(t) :=
  let m := fresh "marker" in
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := autosubst_nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (refine (@functional_extensionality_dep _ _ _ _ _) ||
     refine (@forall_extensionality _ _ _ _) ||
     refine (@forall_extensionalityP _ _ _ _) ||
     refine (@forall_extensionalityS _ _ _ _)); intro
  end).

(** *** Function Instance *)

Definition cod X A:  Type :=  X -> A.

Definition cod_map {X} {A B} (f : A -> B) (p : X -> A) :
  X -> B.
Proof.
  intros x. exact (f (p x)).
Defined.

(** Note that this requires functional extensionality. *)
Definition cod_id {X} {A} {f : A -> A} :
  (forall x, f x = x) -> forall (p: X -> A), cod_map f p = p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_ext {X} {A B} {f f' : A -> B} :
  (forall x, f x = f' x) -> forall (p: X -> A), cod_map f p = cod_map f' p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_comp {X} {A B C} {f : A -> B} {g : B -> C} {h} :
  (forall x, (funcomp g f) x =  h x) -> forall (p: X -> _), cod_map g (cod_map f p) = cod_map h p.
Proof. intros H p. unfold cod_map. fext. intros x. apply H. Defined.
