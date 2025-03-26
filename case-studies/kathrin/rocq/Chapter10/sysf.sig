-- Signature for System F

-- the types
ty : Type
tm : Type

-- the constructors for ty
top : ty
arr : ty -> ty -> ty
all : ty -> (bind ty in ty) -> ty

-- the constructors for tm
app  : tm -> tm -> tm
tapp : tm -> ty -> tm
vt   : tm -> tm
abs : ty -> (bind tm in tm) -> tm
tabs : ty -> (bind ty in tm) -> tm
