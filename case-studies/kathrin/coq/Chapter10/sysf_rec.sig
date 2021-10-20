-- Signature for System F

-- the types
ty : Type
tm : Type
label : Type

-- the functors 
list : Functor
prod : Functor

-- the constructors for ty
top : ty
arr : ty -> ty -> ty
all : ty -> (bind ty in ty) -> ty
recty : "list ("prod label ty")" -> ty

-- the constructors for tm
app  : tm -> tm -> tm
tapp : tm -> ty -> tm
abs : ty -> (bind tm in tm) -> tm
tabs : ty -> (bind ty in tm) -> tm
rectm : "list ("prod label tm")" -> tm
proj : tm -> label -> tm 
letpat : tm -> "cod ty" -> "cod ("list label")" -> (bind <p, tm> in tm) -> tm
