
module Error = Monadic.Result.Make (String)
include Error

include Monadic.Monad.ApplicativeFunctionsList (Error)
include Monadic.Monad.MonadFunctionsList (Error)
include Monads.ExtraFunctionsList (Error)
