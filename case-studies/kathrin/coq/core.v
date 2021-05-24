(* Function composition *)

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Lemma funcomp_assoc {W X Y Z} (g: Y -> Z) (f: X -> Y) (h: W -> X) :
  funcomp g (funcomp f h) = (funcomp (funcomp g f) h).
Proof.
  reflexivity.
Qed.


(** ** Functor Instances

Exemplary functor instances needed to make Autosubst's generation possible for functors.
Two things are important:
1. The names are fixed.
2. For Coq to check termination, also the proofs have to be closed with Defined.
 *)

(** *** List Instance *)
Require Import List.

Definition list_ext {A B} {f g : A -> B} :
  (forall x, f x = g x) -> forall xs, map f xs = map g xs.
  intros H. induction xs. reflexivity.
  cbn. f_equal. apply H. apply IHxs.
Defined.

Definition list_id {A}  { f : A -> A} :
  (forall x, f x = x) -> forall xs, map f xs = xs.
Proof.
  intros H. induction xs. reflexivity.
  cbn. rewrite H. rewrite IHxs; eauto.
Defined.

Definition list_comp {A B C} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp  g f) x = h x) -> forall xs, map g (map f xs) = map h xs.
Proof.
  induction xs. reflexivity.
  cbn. rewrite <- H. f_equal. apply IHxs.
Defined.

(** *** Prod Instance *)

Definition prod_map {A B C D} (f : A -> C) (g : B -> D) (p : A * B) :
  C * D.
Proof.
  destruct p as [a b]. split.
  exact (f a). exact (g b).
Defined.

Definition prod_id {A B} {f : A -> A} {g : B -> B} :
  (forall x, f x = x) -> (forall x, g x = x) -> forall p, prod_map f g p = p.
Proof.
  intros H0 H1. destruct p. cbn. f_equal; [ apply H0 | apply H1 ].
Defined.

Definition prod_ext {A B C D} {f f' : A -> C} {g g': B -> D} :
  (forall x, f x = f' x) -> (forall x, g x = g' x) -> forall p, prod_map f g p = prod_map f' g' p.
Proof.
  intros H0 H1. destruct p as [a b]. cbn. f_equal; [ apply H0 | apply H1 ].
Defined.

Definition prod_comp {A B C D E F} {f1 : A -> C} {g1 : C -> E} {h1 : A -> E} {f2: B -> D} {g2: D -> F} {h2 : B -> F}:
  (forall x, (funcomp  g1 f1) x = h1 x) -> (forall x, (funcomp g2 f2) x = h2 x) -> forall p, prod_map g1 g2 (prod_map f1 f2 p) = prod_map h1 h2 p.
Proof.
  intros H0 H1. destruct p as [a b]. cbn. f_equal; [ apply H0 | apply H1 ].
Defined.

(* a.d. TODO hints outside of sections without explicit locality are deprecated. Is this even used in the first place?  *)
Hint Rewrite in_map_iff : FunctorInstances.

(* Declaring the scopes that all our notations will live in *)
(* Declare Scope fscope. *)
(* Declare Scope subst_scope. *)
