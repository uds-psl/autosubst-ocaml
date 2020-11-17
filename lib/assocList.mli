
val assoc : 'a -> ('a * 'b) list -> 'b option

val assoc_default : 'a -> ('a * 'b) list -> default:'b -> 'b

val insert : 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list

val mem_assoc : 'a -> ('a * 'b) list -> bool
