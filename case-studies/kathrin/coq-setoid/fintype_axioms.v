Require Import core core_axioms fintype.
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

(** Generic fsimpl tactic: simplifies the above primitives in a goal. *)
Ltac fsimpl_fext :=
  repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *)
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *)
         | [|- context [id ?s]] => change (id s) with s
         (* | [|- context[comp ?f ?g]] => change (comp f g) with (g >> f) (* AsimplCompIdL *) *)
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *)

         | [|- zero_p >> scons_p ?f ?g] => rewrite scons_p_head

         | [|- context[(?s.:?sigma) var_zero]] => change ((s.:sigma) var_zero) with s
         | [|- context[(?s.:?sigma) (shift ?m)]] => change ((s.:sigma) (shift m)) with (sigma m)

         | [|- context[idren >> ?f]] => change (idren >> f) with f
         | [|- context[?f >> idren]] => change (f >> idren) with f
         | [|- context[?f >> (?x .: ?g)]] => change (f >> (x .: g)) with g
         | [|- context[?x2 .: shift >> ?f]] => change x2 with (f var_zero); rewrite (@scons_eta _ _ f)
         | [|- context[?f var_zero .: ?g]] => change g with (shift >> f); rewrite scons_eta

         |[|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s)
         |[|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s)

         | _ => first [progress (rewrite scons_comp) |  progress (rewrite scons_eta_id) | progress (autorewrite with FunctorInstances)]
         end.

(** Generic fsimpl tactic: simplifies the above primitives in the context *)
Ltac fsimplc_fext :=
  repeat match goal with
         | [H: context[id >> ?f] |- _] => change (id >> f) with f in H(* AsimplCompIdL *)
         | [H: context[?f >> id]|- _] => change (f >> id) with f in H(* AsimplCompIdR *)
         | [H: context [id ?s]|- _] => change (id s) with s in H
         (* | [H: context[comp ?f ?g]|- _] => change (comp f g) with (g >> f) in H (* AsimplCompIdL *) *)
         | [H: context[(?f >> ?g) >> ?h]|- _] =>
           change ((f >> g) >> h) with (f >> (g >> h)) in H (* AsimplComp *)
         | [H: context[(?s.:?sigma) var_zero]|- _] => change ((s.:sigma) var_zero) with s in H
         | [H: context[(?s.:?sigma) var_zero]|- _] => change ((s.:sigma) var_zero) with s in H
         | [H: context[(?s.:?sigma) (shift ?m)]|- _] => change ((s.:sigma) (shift m)) with (sigma m) in H
                                                                                      |[H : context[ _ =  ?h (?f ?s)]|- _] => change (h (f s)) with ((f >> h) s) in H
         |[H: context[?h (?f ?s) = _]|- _] => change (h (f s)) with ((f >> h) s) in H
         | [H: context[idren >> ?f]|- _] => change (idren >> f) with f in H
         | [H: context[?f >> idren]|- _] => change (f >> idren) with f in H
         | [H: context[?f >> (?x .: ?g)]|- _] =>
           change (f >> (x .: g)) with g in H
         | [H: context[?x2 .: shift >> ?f]|- _] =>
           change x2 with (f var_zero) in H; rewrite (@scons_eta _ _ f) in H
         | [H: context[?f var_zero .: ?g]|- _] =>
           change g with (shift >> f) in H; rewrite scons_eta in H
         | _ => first [progress (rewrite scons_comp in *) | progress (rewrite scons_eta_id in *) | progress (autorewrite with FunctorInstances in *)]
         end.

(** Simplification in both the goal and the context *)
Tactic Notation "fsimpl_fext" "in" "*" :=
  fsimpl_fext; fsimplc_fext.

Hint Rewrite @scons_p_comp scons_p_head scons_p_tail : FunctorInstances.
