tm: Type

list : Functor

app : tm -> "list" (tm) -> tm
lam (p: nat) : (bind <p, tm> in tm) -> tm
