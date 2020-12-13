tm: Type

app : tm -> tm -> tm
lam : (tm -> tm) -> tm

pair : tm -> tm -> tm 
matchpair : tm -> (tm -> tm -> tm) -> tm
