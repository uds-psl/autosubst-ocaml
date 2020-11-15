open Monadic

module MakeT
    (Wrapped : Monad.MONAD) (R: sig type t end) (W: Monad.MONOID) (S: sig type t end) =
struct
  type rws_r = R.t
  type rws_w = W.t
  type rws_s = S.t

  (* also import syntax of wrapped monad so that we can use it in functions later *)
  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  (* I'm so happy! using the monadic library it was so easy to compose the monads (^w^) *)
  module M1 = Reader.MakeT(Wrapped)(R)
  module M2 = State.MakeT(M1)(S)
  module M3 = Writer.MakeT(M2)(W)
  (* a.d. TODO if I just add the module here I don't know what kind of monad it is, can I also parameterize RWS by the module signature of Wrapped? *)
  module W = Wrapped

  (* include the top monad so that RWS itself becomes a monad *)
  include M3

  (* should be unnec. since M3 already contains a Syntax module *)
  (* include Monad.MonadInfix (M3) *)

  (* and now we can define liftings for the important functions of this monad *)
  let peek = M3.elevate @@ M2.elevate M1.peek

  let tell = M3.tell

  let put x = M2.put x |> M3.elevate
  let get = M3.elevate M2.get

  let run x ~r ~s =
    let x' = M3.run x in
    let x'' = M2.run x' s in
    let x''' = M1.run x'' r in
    let* ((a_out, w_out), s_out) = x''' in
    Wrapped.pure (a_out, w_out, s_out)

  let elevate x = x |> M1.elevate |> M2.elevate |> M3.elevate

  let create f = M3.create @@ M2.create (fun s -> M1.create (fun r ->
      let* (a_out, w_out, s_out) = f r s in
      Wrapped.pure ((a_out, w_out), s_out)))
end

module Make = MakeT(Identity)
