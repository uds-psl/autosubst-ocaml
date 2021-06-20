
Check (fun x : nat => 0).

From Coq Require Import ssreflect ssrfun ssrbool.
(* ssreflext completely hides a spurious argument *)
Check (fun x : nat => 0).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Parameter map : (nat -> nat) -> list nat -> list nat.
Parameter sumlist : list nat -> nat.
Axiom eq_map :
  forall F1 F2 : nat -> nat,
  (forall n : nat, F1 n = F2 n) ->
  forall l : list nat, map F1 l = map F2 l.

Require Import Arith.

Lemma example_map l : sumlist (map (fun m => m - m) l) = 0.
Proof.
  under eq_map => m.
  rewrite Nat.sub_diag. over.
