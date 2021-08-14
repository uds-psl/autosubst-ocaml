(** This module implements a Map from 'a to 'b by as association list of pairs 'a * 'b *)

type ('a, 'b) t [@@deriving show]

val empty : ('a, 'b) t

val assoc_exn : 'a -> ('a, 'b) t -> 'b
val assoc : 'a -> ('a, 'b) t -> 'b option

val assoc_default : 'a -> ('a, 'b) t -> default:'b -> 'b

val insert : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t

val mem_assoc : 'a -> ('a, 'b) t -> bool

val update : 'a -> ('b -> 'b) -> ('a, 'b) t -> ('a, 'b) t
val update_exn : 'a -> ('b -> 'b) -> ('a, 'b) t -> ('a, 'b) t

val map : ('a -> 'b -> 'c) -> ('a, 'b) t -> ('a, 'c) t

(** Remove all shadowed elements from the assoc list *)
val flatten : ('a, 'b) t -> ('a, 'b) t

val from_list : ('a * 'b) list -> ('a, 'b) t
val to_list : ('a, 'b) t -> ('a * 'b) list
