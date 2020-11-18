(* Common definitions for all monads *)
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

module FunctorInfix (F : FUNCTOR) = struct
  let ( <$> ) f xa = F.map f xa [@@inline]

  module Syntax = struct
    let ( let+ ) x f = F.map f x [@@inline]
  end
end

module ApplicativeInfix (A : APPLICATIVE) = struct
  module InfixF = FunctorInfix (A)
  include InfixF

  let ( <*> ) = A.apply

  module Syntax = struct
    include InfixF.Syntax

    let ( and+ ) xa ya = (fun x y -> (x, y)) <$> xa <*> ya [@@inline]
  end
end

module AlternativeInfix (A : ALTERNATIVE) = struct
  module InfixA = ApplicativeInfix (A)
  include InfixA

  let ( <|> ) = A.append
end

module MonadInfix (M : MONAD) = struct
  module InfixA = ApplicativeInfix (M)
  include InfixA

  let ( >>= ) = M.bind

  module Syntax = struct
    include InfixA.Syntax

    let ( let* ) = M.bind
  end
end

module MonadPlusInfix (M : MONAD_PLUS) = struct
  module InfixM = MonadInfix (M)
  include InfixM

  let ( <|> ) = M.append
end

module type MAKE_T = sig
  type 'a wrapped

  type 'a actual_t

  include MONAD

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

module CreateMonadPlus
    (M : MONAD) (C : sig
      type 'a t = 'a M.t

      val append : 'a t -> 'a t -> 'a t

      val empty : unit -> 'a t
    end) : sig
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
end = struct
  module MonadPlus = struct
    include M
    include C
  end

  module Infix = MonadPlusInfix (MonadPlus)
  include MonadPlus
  include Infix
end

module type COLLECTION = sig
  type 'a t

  include FUNCTOR with type 'a t := 'a t

  val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val init : int -> (int -> 'a) -> 'a t

  val cons : 'a -> 'a t -> 'a t

  val empty : 'a t
end

module SeqCollection = struct
  include Stdlib.Seq

  let rec fold_right f seq init =
    match seq () with
    | Stdlib.Seq.Nil -> init
    | Stdlib.Seq.Cons (y, ys) -> f y (fold_right f ys init)

  let init i0 f =
    let rec k i =
      if i <= 0 then Stdlib.Seq.empty
      else fun () -> Stdlib.Seq.Cons (f (i0 - i), k (i - 1))
    in
    k i0

  let cons x xs () = Stdlib.Seq.Cons (x, xs) [@@inline]

  let empty = Stdlib.Seq.empty
end

module ListCollection = struct
  include Stdlib.List

  let empty = []
end

module ArrayCollection = struct
  include Stdlib.Array

  let empty = [||]

  let cons x xs = Stdlib.Array.append [| x |] xs [@@inline]
end

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

module ApplicativeFunctionsGeneric (C : COLLECTION) (A : APPLICATIVE) = struct
  open A
  module Infix = ApplicativeInfix (A)
  open Infix.Syntax

  let ( *> ) m m' =
    let+ _ = m and+ x' = m' in
    x'

  let ( <* ) m m' =
    let+ x' = m and+ _ = m' in
    x'

  let sequence ms =
    let k m m' =
      let+ x = m and+ xs = m' in
      C.cons x xs
    in
    C.fold_right k ms (pure C.empty)

  let sequence_ ms = C.fold_right ( *> ) ms (pure C.empty)

  let a_map f ms = sequence (C.map f ms) [@@inline]

  let a_map_ f ms = sequence_ (C.map f ms) [@@inline]

  let a_filter f xs =
    let k curr acc =
      let+ flg = f curr and+ ys = acc in
      if flg then C.cons curr ys else ys
    in
    C.fold_right k xs (pure C.empty)

  let traverse f xs = C.map f xs |> sequence [@@inline]

  let a_for xs f = traverse f xs [@@inline]

  let a_for_ xs f = a_for xs f *> pure () [@@inline]

  let lift2 fa aa ba =
    let+ f = fa and+ a = aa and+ b = ba in
    f a b

  let lift3 fa aa ba ca =
    let+ f = fa and+ a = aa and+ b = ba and+ c = ca in
    f a b c

  let lift4 fa aa ba ca da =
    let+ f = fa and+ a = aa and+ b = ba and+ c = ca and+ d = da in
    f a b c d

  let a_when condition action = if condition then action else pure ()

  let a_unless condition = a_when (not condition)

  let a_replicate i m = C.init i (fun _ -> m) |> sequence

  let a_replicate_ i m = a_replicate i m *> pure ()
end

module ApplicativeFunctions = ApplicativeFunctionsGeneric (SeqCollection)
module ApplicativeFunctionsList = ApplicativeFunctionsGeneric (ListCollection)
module ApplicativeFunctionsArray = ApplicativeFunctionsGeneric (ArrayCollection)

module MonadFunctionsGeneric (C : COLLECTION) (M : MONAD) = struct
  open M
  module Infix = MonadInfix (M)
  open Infix.Syntax

  open ApplicativeFunctionsGeneric (C) (M)

  let m_fold f initial ms =
    let c x k z =
      let* m' = f z x in
      k m'
    in
    C.fold_right c ms pure initial

  let m_fold_ f initial ms = m_fold f initial ms *> pure () [@@inline]

  let ( >=> ) f1 f2 s =
    let* s' = f1 s in
    let+ s'' = f2 s' in
    s''
end

module MonadFunctions = MonadFunctionsGeneric (SeqCollection)
module MonadFunctionsList = MonadFunctionsGeneric (ListCollection)
module MonadFunctionsArray = MonadFunctionsGeneric (ArrayCollection)

module AlternativeFunctions (A : ALTERNATIVE) = struct
  let guard c = if c then A.pure () else A.empty ()

  module Infix = AlternativeInfix (A)

  (* some and many are still untested, they are completely based on the Haskell definitions *)
  let some v =
    let open Infix in
    let open Infix.Syntax in
    let rec some_v () =
      let+ v_ = v and+ many_v_ = many_v () in
      fun () -> Stdlib.Seq.Cons (v_, many_v_)
    and many_v () = some_v () <|> A.pure Stdlib.Seq.empty in
    some_v ()

  let many v =
    let open Infix in
    let open Infix.Syntax in
    let rec some_v () =
      let+ v_ = v and+ many_v_ = many_v () in
      fun () -> Stdlib.Seq.Cons (v_, many_v_)
    and many_v () = some_v () <|> A.pure Stdlib.Seq.empty in
    many_v ()

  let optional v =
    let open Infix in
    Stdlib.Option.some <$> v <|> A.pure None
end
