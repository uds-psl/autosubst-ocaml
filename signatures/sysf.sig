ty : Type
tm : Type

arr : ty -> ty -> ty
all : (ty -> ty) -> ty

app : tm -> tm -> tm
tapp : tm -> ty -> tm
lam : ty -> (tm -> tm) -> tm
tlam : (ty -> tm) -> tm
