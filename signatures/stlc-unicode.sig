ty : Type
tm : Type

Base : ty
Fun : ty -> ty -> ty

アップ : tm -> tm -> tm
λ : ty -> (tm -> tm) -> tm

