-- Signature for System F

-- the types
ty : Type
tm : Type
nat : Type
pat : Type

-- the functors 
list : Functor
prod : Functor

-- the constructors for ty
top : ty
arr : ty -> ty -> ty
all : ty -> (bind ty in ty) -> ty
recty : "list" ("prod" (nat, ty)) -> ty

-- the constructors for patterns
patvar : ty -> pat 
patlist : "list" ("prod" (nat, pat)) -> pat

-- the constructors for tm
app  : tm -> tm -> tm
tapp : tm -> ty -> tm
abs : ty -> (bind tm in tm) -> tm
tabs : ty -> (bind ty in tm) -> tm
rectm : "list" ("prod" (nat, tm)) -> tm
proj : tm -> nat -> tm 
letpat (p : nat) : pat -> tm -> (bind <p, tm> in tm) -> tm
