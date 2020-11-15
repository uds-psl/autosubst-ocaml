module type MONOID = sig
  type t

  val empty : t

  val append : t -> t -> t
end

module type FUNCTOR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
end

module type APPLICATIVE = sig
  include FUNCTOR

  val apply : ('a -> 'b) t -> 'a t -> 'b t

  val pure : 'a -> 'a t
end

module type ALTERNATIVE = sig
  include APPLICATIVE

  val empty : unit -> 'a t

  val append : 'a t -> 'a t -> 'a t
end

module type MONAD = sig
  include APPLICATIVE

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val join : 'a t t -> 'a t
end

module type MONAD_PLUS = sig
  include MONAD

  include ALTERNATIVE with type 'a t := 'a t
end

module FunctorInfix : functor (F : FUNCTOR) -> sig
  val ( <$> ) : ('a -> 'b) -> 'a F.t -> 'b F.t

  module Syntax : sig
    val ( let+ ) : 'a F.t -> ('a -> 'b) -> 'b F.t
  end
end

module ApplicativeInfix : functor (A : APPLICATIVE) -> sig
  val ( <$> ) : ('a -> 'b) -> 'a A.t -> 'b A.t

  val ( <*> ) : ('a -> 'b) A.t -> 'a A.t -> 'b A.t

  module Syntax : sig
    val ( let+ ) : 'a A.t -> ('a -> 'b) -> 'b A.t

    val ( and+ ) : 'a A.t -> 'b A.t -> ('a * 'b) A.t
  end
end

module AlternativeInfix : functor (A : ALTERNATIVE) -> sig
  val ( <$> ) : ('a -> 'b) -> 'a A.t -> 'b A.t

  val ( <*> ) : ('a -> 'b) A.t -> 'a A.t -> 'b A.t

  module Syntax : sig
    val ( let+ ) : 'a A.t -> ('a -> 'b) -> 'b A.t

    val ( and+ ) : 'a A.t -> 'b A.t -> ('a * 'b) A.t
  end

  val ( <|> ) : 'a A.t -> 'a A.t -> 'a A.t
end

module MonadInfix : functor (M : MONAD) -> sig
  val ( <$> ) : ('a -> 'b) -> 'a M.t -> 'b M.t

  val ( <*> ) : ('a -> 'b) M.t -> 'a M.t -> 'b M.t

  val ( >>= ) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t

  module Syntax : sig
    val ( let+ ) : 'a M.t -> ('a -> 'b) -> 'b M.t

    val ( and+ ) : 'a M.t -> 'b M.t -> ('a * 'b) M.t

    val ( let* ) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t
  end
end

module MonadPlusInfix : functor (M : MONAD_PLUS) -> sig
  val ( <$> ) : ('a -> 'b) -> 'a M.t -> 'b M.t

  val ( <*> ) : ('a -> 'b) M.t -> 'a M.t -> 'b M.t

  val ( >>= ) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t

  module Syntax : sig
    val ( let+ ) : 'a M.t -> ('a -> 'b) -> 'b M.t

    val ( and+ ) : 'a M.t -> 'b M.t -> ('a * 'b) M.t

    val ( let* ) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t
  end

  val ( <|> ) : 'a M.t -> 'a M.t -> 'a M.t
end

module type MAKE_T = sig
  type 'a wrapped

  type 'a t

  type 'a actual_t

  include MONAD with type 'a t := 'a t

  val elevate : 'a wrapped -> 'a t

  val run : 'a t -> 'a actual_t

  val create : 'a actual_t -> 'a t

  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t

  val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t

  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

  module Syntax : sig
    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

    val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t

    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end
end

module type MAKE_PLUS_T = sig
  include MAKE_T

  val ( <|> ) : 'a t -> 'a t -> 'a t

  val append : 'a t -> 'a t -> 'a t

  val empty : unit -> 'a t
end

module CreateMonadPlus : functor
  (M : MONAD)
  (C : sig
     type 'a t = 'a M.t

     val append : 'a t -> 'a t -> 'a t

     val empty : unit -> 'a t
   end)
  -> sig
  include MONAD_PLUS with type 'a t = 'a M.t

  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t

  val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t

  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

  val ( <|> ) : 'a t -> 'a t -> 'a t

  module Syntax : sig
    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

    val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t

    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end
end

module type COLLECTION = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val init : int -> (int -> 'a) -> 'a t

  val cons : 'a -> 'a t -> 'a t

  val empty : 'a t
end

module SeqCollection : COLLECTION with type 'a t = 'a Stdlib.Seq.t

module ListCollection : COLLECTION with type 'a t = 'a list

module ArrayCollection : COLLECTION with type 'a t = 'a array

module type APPLICATIVE_FUNCTIONS = sig
  type 'a applicative

  type 'a collection

  val ( *> ) : 'a applicative -> 'b applicative -> 'b applicative

  val ( <* ) : 'a applicative -> 'b applicative -> 'a applicative

  val sequence : 'a applicative collection -> 'a collection applicative

  val sequence_ : 'a applicative collection -> 'b collection applicative

  val a_map :
    ('a -> 'b applicative) -> 'a collection -> 'b collection applicative

  val a_map_ :
    ('a -> 'b applicative) -> 'a collection -> 'c collection applicative

  val a_filter :
    ('a -> bool applicative) -> 'a collection -> 'a collection applicative

  val traverse :
    ('a -> 'b applicative) -> 'a collection -> 'b collection applicative

  val a_for :
    'a collection -> ('a -> 'b applicative) -> 'b collection applicative

  val a_for_ : 'a collection -> ('a -> 'b applicative) -> unit applicative

  val lift2 :
    ('a -> 'b -> 'c) applicative ->
    'a applicative ->
    'b applicative ->
    'c applicative

  val lift3 :
    ('a -> 'b -> 'c -> 'd) applicative ->
    'a applicative ->
    'b applicative ->
    'c applicative ->
    'd applicative

  val lift4 :
    ('a -> 'b -> 'c -> 'd -> 'e) applicative ->
    'a applicative ->
    'b applicative ->
    'c applicative ->
    'd applicative ->
    'e applicative

  val a_when : bool -> unit applicative -> unit applicative

  val a_unless : bool -> unit applicative -> unit applicative

  val a_replicate : int -> 'a applicative -> 'a collection applicative

  val a_replicate_ : int -> 'a applicative -> unit applicative
end

module type MONAD_FUNCTIONS = sig
  type 'a monad

  type 'a collection

  val m_fold : ('a -> 'b -> 'a monad) -> 'a -> 'b collection -> 'a monad

  val m_fold_ : ('a -> 'b -> 'a monad) -> 'a -> 'b collection -> unit monad

  val ( >=> ) : ('a -> 'b monad) -> ('b -> 'c monad) -> 'a -> 'c monad
end

module ApplicativeFunctionsGeneric : functor
  (C : COLLECTION)
  (A : APPLICATIVE)
  ->
  APPLICATIVE_FUNCTIONS
    with type 'a collection := 'a C.t
    with type 'a applicative := 'a A.t

module ApplicativeFunctions : functor (A : APPLICATIVE) ->
  APPLICATIVE_FUNCTIONS
    with type 'a applicative := 'a A.t
    with type 'a collection := 'a Stdlib.Seq.t

module ApplicativeFunctionsList : functor (A : APPLICATIVE) ->
  APPLICATIVE_FUNCTIONS
    with type 'a applicative := 'a A.t
    with type 'a collection := 'a list

module ApplicativeFunctionsArray : functor (A : APPLICATIVE) ->
  APPLICATIVE_FUNCTIONS
    with type 'a applicative := 'a A.t
    with type 'a collection := 'a array

module MonadFunctionsGeneric : functor (C : COLLECTION) (M : MONAD) ->
  MONAD_FUNCTIONS with type 'a monad := 'a M.t with type 'a collection := 'a C.t

module MonadFunctions : functor (M : MONAD) ->
  MONAD_FUNCTIONS
    with type 'a monad := 'a M.t
    with type 'a collection := 'a Stdlib.Seq.t

module MonadFunctionsList : functor (M : MONAD) ->
  MONAD_FUNCTIONS
    with type 'a monad := 'a M.t
    with type 'a collection := 'a list

module MonadFunctionsArray : functor (M : MONAD) ->
  MONAD_FUNCTIONS
    with type 'a monad := 'a M.t
    with type 'a collection := 'a array

module AlternativeFunctions : functor (A : ALTERNATIVE) -> sig
  val guard : bool -> unit A.t

  val some : 'a A.t -> 'a Stdlib.Seq.t A.t

  val many : 'a A.t -> 'a Stdlib.Seq.t A.t

  val optional : 'a A.t -> 'a option A.t
end
