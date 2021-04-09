Require Import core core_axioms unscoped.
Import UnscopedNotations.

#[ local ]
 Open Scope subst_scope.

(** Eta laws. *)
Lemma scons_eta_id {n : nat} : var_zero .: shift = id :> (nat -> nat).
Proof. fext. intros [|x]; reflexivity. Qed.

Lemma scons_eta {T} (f : nat -> T) :
  f var_zero .: shift >> f = f.
Proof. fext. intros [|x]; reflexivity. Qed.

Lemma scons_comp (T: Type) U (s: T) (sigma: nat -> T) (tau: T -> U ) :
  (s .: sigma) >> tau = scons (tau s) (sigma >> tau) .
Proof.
  fext. intros [|x]; reflexivity.
Qed.
