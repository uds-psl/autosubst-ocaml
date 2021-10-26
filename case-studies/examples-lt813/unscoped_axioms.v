Require Import core core_axioms unscoped.
Import UnscopedNotations.

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

(** Generic fsimpl tactic: simplifies the above primitives in a goal. *)
Ltac fsimpl_fext :=
  unfold up_ren; repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *)
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *)
         | [|- context [id ?s]] => change (id s) with s
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((?f >> ?g) >> ?h) with (f >> (g >> h)) (* AsimplComp *)
         | [|- context[(?s.:?sigma) var_zero]] => change ((s.:sigma)var_zero) with s
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((f >> g) >> h) with (f >> (g >> h))
        | [|- context[?f >> (?x .: ?g)]] =>
           change (f >> (x .: g)) with g
         | [|- context[var_zero]] =>  change var_zero with 0
         | [|- context[?x2 .: shift >> ?f]] =>
           change x2 with (f 0); rewrite (@scons_eta _ _ f)
         | [|- context[(?v .: ?g) 0]] =>
           change ((v .: g) 0) with v
         | [|- context[(?v .: ?g) (S ?n)]] =>
           change ((v .: g) (S n)) with (g n)
         | [|- context[?f 0 .: ?g]] =>
           change g with (shift >> f); rewrite scons_eta
         | _ => first [progress (rewrite ?scons_comp) | progress (rewrite ?scons_eta_id)]
 end.

(** Generic fsimpl tactic: simplifies the above primitives in the context *)
Ltac fsimplc_fext :=
  unfold up_ren; repeat match goal with
         | [H : context[id >> ?f] |- _] => change (id >> f) with f in H(* AsimplCompIdL *)
         | [H: context[?f >> id] |- _] => change (f >> id) with f in H(* AsimplCompIdR *)
         | [H: context [id ?s] |- _]  => change (id s) with s in H
         | [H:  context[(?f >> ?g) >> ?h]  |- _] =>
           change ((?f >> ?g) >> ?h) with (f >> (g >> h)) in H(* AsimplComp *)
         | [H : context[(?s.:?sigma) var_zero]  |- _] => change ((s.:sigma)var_zero) with s in H
         | [H: context[(?f >> ?g) >> ?h]  |- _] =>
           change ((f >> g) >> h) with (f >> (g >> h)) in H
        | [H: context[?f >> (?x .: ?g)]  |- _] =>
           change (f >> (x .: g)) with g in H
         | [H: context[var_zero]  |- _] =>  change var_zero with 0 in H
         | [H: context[?x2 .: shift >> ?f]  |- _] =>
           change x2 with (f 0) in H; rewrite (@scons_eta _ _ f) in H
         | [H: context[(?v .: ?g) 0]  |- _] =>
           change ((v .: g) 0) with v in H
         | [H: context[(?v .: ?g) (S ?n)]  |- _] =>
           change ((v .: g) (S n)) with (g n) in H
         | [H: context[?f 0 .: ?g]  |- _] =>
           change g with (shift >> f); rewrite scons_eta in H
         | _ => first [progress (rewrite ?scons_comp in *)  | progress (rewrite ?scons_eta_id in *) ]
 end.

(** Simplification in both the goal and the context *)
Tactic Notation "fsimpl_fext" "in" "*" :=
  fsimpl_fext; fsimplc_fext.
