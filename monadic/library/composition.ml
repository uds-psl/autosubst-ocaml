module ComposeFunctor (F1 : Monad.FUNCTOR) (F2 : Monad.FUNCTOR) = struct
  module ComposeFunctor = struct
    type 'a t = 'a F2.t F1.t

    let map f x = F1.map (F2.map f) x [@@inline]
  end

  include ComposeFunctor
  module Infix = Monad.FunctorInfix (ComposeFunctor)
  include Infix
end

module ComposeApplicative (A1 : Monad.APPLICATIVE) (A2 : Monad.APPLICATIVE) =
struct
  module Functor = ComposeFunctor (A1) (A2)

  module ComposeApplicative = struct
    include Functor.ComposeFunctor

    let pure x = A1.pure (A2.pure x) [@@inline]

    let apply fa xa = A1.apply (A1.map A2.apply fa) xa [@@inline]
  end

  let elevate x = A1.map A2.pure x [@@inline]

  include ComposeApplicative
  module Infix = Monad.ApplicativeInfix (ComposeApplicative)
  include Infix
end

module ComposeAlternative (A1 : Monad.ALTERNATIVE) (A2 : Monad.APPLICATIVE) =
struct
  module Applicative = ComposeApplicative (A1) (A2)

  module ComposeAlternative = struct
    include Applicative.ComposeApplicative

    let empty = A1.empty

    let append = A1.append
  end

  let elevate = Applicative.elevate

  include ComposeAlternative
  module Infix = Monad.AlternativeInfix (ComposeAlternative)
  include Infix
end
