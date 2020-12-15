
module M = Monads.Std
module E = M.Monad.Result.Error
module RE = M.Monad.Reader.Make(struct type t = int end)(E)
(* module RES = M.Monad.State.Make(struct type t = string end)(RE) *)
