open Monads.Std
open Types

(* after trying around for a while it seems a lot harder than in Haskell to combine these Monads into some kind of transformer stack. The problem seems to be that the output of Make does not include the type "t" which would be needed for the next application of Make.
 * So since I probably cannot compose them well, I should just write my own RWS monad and then in the Make take the Error monad which seems to work
 * In order to write my own module I should [[https://github.com/BinaryAnalysisPlatform/bap/blob/8ec0e7bd9990d7a8fee5cba887d2b1e2ecf23a99/lib/monads/monads_monad.ml][check the implementation of the reader/writer monad]] *)
module MError = Monad.Result.Error
module SigReaderF = Monad.Reader.Make(struct type t = signature end)
module CodeWriterF = Monad.Writer.Make(Monoid.String)
module ScopeStateF = Monad.State.Make(struct type t = int end)

module TestSigReader = SigReaderF(Monad.Ident)
module TestCodeWriter = CodeWriterF(Monad.Ident)
module TestScopeState = ScopeStateF(Monad.Ident)

(* module M1 = Monad.State.Make(struct type t = int end)(Monad.Result.Error) *)
(* module M2 = Monad.Writer.Make(Monoid.String)(struct type 'a t = (('a, int) Monad.State.storage Monad.Result.Error.t, int) Monad.State.state;; include M1 end) *)

(* module RWSE = SigReaderF(CodeWriterF(ScopeStateF(MError))) *)
