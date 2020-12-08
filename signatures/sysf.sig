ty : Type
tm : Type

top : ty
arr : ty -> ty -> ty
all : ty -> (ty -> ty) -> ty

app : tm -> tm -> tm
tapp : tm -> ty -> tm
vt : tm -> tm
abs : ty -> (tm -> tm) -> tm
tabs : ty -> (ty -> tm) -> tm
