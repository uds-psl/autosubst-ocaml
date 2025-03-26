ty : Type
tm : Type

Base : ty
Fun : ty -> ty -> ty

app : tm -> tm -> tm
lam : ty -> (bind tm in tm) -> tm
