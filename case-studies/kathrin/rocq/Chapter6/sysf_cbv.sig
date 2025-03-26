ty : Type
tm : Type
vl : Type

arr : ty -> ty -> ty
all : (bind ty in ty) -> ty

app  : tm -> tm -> tm
tapp : tm -> ty -> tm
vt   : vl -> tm

lam  : ty -> (bind vl in tm) -> vl
tlam : (bind ty in tm) -> vl
