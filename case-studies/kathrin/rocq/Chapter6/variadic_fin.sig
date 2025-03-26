tm: Type

cod : Functor

app (p: nat): tm -> "cod (fin p)" (tm) -> tm
lam (p: nat) : (bind <p,tm> in tm) -> tm
