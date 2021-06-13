
From Chapter9 Require Export stlc.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma default_subst_lemma {m n} (f : fin m -> tm n) (s : tm (S m)) (t : tm m) :
  s[t..][f] = s[up_tm_tm f][(t[f])..].
Proof.
  asimpl.
  reflexivity.
Qed.

Lemma default_subst_lemma2 {m n} (f : fin m -> tm n) (s : tm (S m)) (t : tm m) :
  (var_tm var_zero)[t..][f] = subst_tm (@scons (tm n) (S n) t[f] (@scons (tm n) n t[f] var_tm)) (var_tm (shift var_zero)).
Proof.
  asimpl.
