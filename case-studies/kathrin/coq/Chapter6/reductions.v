(** ** Substitutivity proofs of reduction. *)

(** *** Substitutivity for the Lambda Calculus with Pairs *)
Require core fintype.
From Chapter6 Require sysf_cbv.
From Chapter6 Require utlc_pairs.

Module polyadic.
Section polyadic.
  Import core fintype.  
  Export Chapter6.utlc_pairs.
  Import ScopedNotations.

  Inductive step {m} : tm m -> tm m -> Prop :=
  | beta s t t' : t' = (s[t..]) -> step (app (lam s) t) t'
  | beta_match s1 s2 t t' : t' = (t[s1 .: s2..]) -> step (matchpair (pair s1 s2) t) t'.

  Lemma step_substitutive m m' (s: tm m) t (sigma: fin m -> tm m')  :
    step s t -> step (s[sigma]) (t[sigma]).
  Proof.
    induction 1; subst.
    - cbn. constructor. now asimpl.
    - cbn. constructor. now asimpl.
Qed.

End polyadic.
End polyadic.

(** *** Substitutivity for Call-by-Value System F *)

Module sysf_cbv.
Section sysf_cbv.
  Import core fintype.
  Export Chapter6.sysf_cbv.
  Import ScopedNotations.

  Inductive step {m n} : tm m n -> tm m n -> Prop :=
  | beta A s v t : t = (s[ids;v..]) -> step (app (vt (lam A s)) (vt v)) t
  | Beta s A t: t = (s[A..;ids]) ->  step (tapp (vt (tlam s)) A) t.

  Lemma step_substitutive m n m' n' (s: tm m n) t sigma (tau: fin n -> vl m' n'):
    step s t -> step (s[sigma;tau]) (t[sigma;tau]).
  Proof.
    induction 1; subst.
    - cbn. constructor. now asimpl.
    - cbn. constructor. now asimpl.
  Qed.


End sysf_cbv.
End sysf_cbv.
