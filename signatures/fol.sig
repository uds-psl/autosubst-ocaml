cod : Functor

term  : Type
form  : Type

Func (p : nat) : "cod (fin p)" (term) -> term
Fal : form
Pred (p : nat) : "cod (fin p)" (term) -> form
Impl : form -> form -> form
Conj : form -> form -> form
Disj : form -> form -> form
All  : (bind term in form) -> form
Ex   : (bind term in form) -> form
