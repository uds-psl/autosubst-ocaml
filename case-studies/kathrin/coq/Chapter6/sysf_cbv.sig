ty : Type
tm : Type
vl : Type

arr : ty -> ty -> ty
all : (ty -> ty) -> ty

app  : tm -> tm -> tm
tapp : tm -> ty -> tm
vt   : vl -> tm

lam  : ty -> (vl -> tm) -> vl
tlam : (ty -> tm) -> vl
