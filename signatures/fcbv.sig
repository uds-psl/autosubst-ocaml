-- Signature for System F

-- the types
ty : Type
tm : Type
vl : Type

-- the constructors for ty
arr : ty -> ty -> ty
all : (bind ty in ty) -> ty

-- the constructors for tm
app  : tm -> tm -> tm
tapp : tm -> ty -> tm
vt   : vl -> tm

-- the constructors for vl
lam  : ty -> (bind vl in tm) -> vl
tlam : (bind ty in tm) -> vl
