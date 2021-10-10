tm: Type

app : tm -> tm -> tm
lam : (bind tm in tm) -> tm

pair : tm -> tm -> tm 
matchpair : tm -> (bind tm, tm in tm) -> tm
