Require Import core axioms fintype.
Import ScopedNotations.

Lemma scons_eta {T} {n : nat} (f : fin (S n) -> T) :
  f var_zero .: shift >> f = f.
Proof. fext. intros [x|]; reflexivity.  Qed.


Lemma scons_eta_id {n : nat} : var_zero .: shift = id :> (fin (S n) -> fin (S n)).
Proof. fext. intros [x|]; reflexivity. Qed.

Lemma scons_comp (T: Type) U {m} (s: T) (sigma: fin m -> T) (tau: T -> U ) :
  (s .: sigma) >> tau = (tau s) .: (sigma >> tau) .
Proof.
  fext. intros [x|]. reflexivity. simpl. reflexivity.
Qed.

Lemma scons_p_head X m n (f : fin m -> X) (g : fin n -> X) :
  (zero_p m >> scons_p m f g) = f.
Proof. fext. intros z. unfold funcomp. apply scons_p_head'. Qed.

Lemma scons_p_tail X  m n (f : fin m -> X) (g : fin n -> X) :
  shift_p m  >> scons_p m f g = g.
Proof. fext. intros z. unfold funcomp. apply scons_p_tail'. Qed.

Lemma scons_p_comp {X Y m n} {f : fin m -> X} {g : fin n -> X} {h : X -> Y} :
  (scons_p m f g) >> h = scons_p m (f >> h) (g >> h).
Proof. fext. intros z. unfold funcomp. apply scons_p_comp'. Qed.

Hint Rewrite @scons_p_comp scons_p_head scons_p_tail: FunctorInstances.
