(** The error monad with strings as error messages. Sometimes used on its own
 ** but mostly inside the ReaderT monad transformer in the REM module. *)

module Error = Monadic.Result.Make (String)
include Error

include Monadic.Monad.ApplicativeFunctionsList (Error)
include Monadic.Monad.MonadFunctionsList (Error)
include Monads.ExtraFunctionsList (Error)
