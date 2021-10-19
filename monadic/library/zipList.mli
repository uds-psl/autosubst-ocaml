include Monad.ALTERNATIVE with type 'a t = 'a list

val ( <|> ) : 'a t -> 'a t -> 'a t

val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t

val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t

module Syntax : sig
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
end
