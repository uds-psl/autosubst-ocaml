-- Signature for System F

-- the types
ty : Type
tm : Type

-- the constructors for ty
top : ty
arr : ty -> ty -> ty
all : ty -> (ty -> ty) -> ty

-- the constructors for tm
app  : tm -> tm -> tm
tapp : tm -> ty -> tm
vt   : tm -> tm
abs : ty -> (tm -> tm) -> tm 
tabs : ty -> (ty -> tm) -> tm 

