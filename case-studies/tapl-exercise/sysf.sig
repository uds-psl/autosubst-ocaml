ty : Type
tm : Type

arr : ty -> ty -> ty
all : (bind ty in ty) -> ty

app : tm -> tm -> tm
tapp : tm -> ty -> tm
lam : ty -> (bind tm in tm) -> tm
tlam : (bind ty in tm) -> tm
