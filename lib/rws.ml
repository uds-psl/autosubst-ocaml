open Monadic

module type MONAD_RWS = sig
  type 'a t
  type rws_r
  type rws_w
  type rws_s


  include Monads.MONAD_READER
    with type 'a t := 'a t
    with type r := rws_r

  include Monads.MONAD_WRITER
    with type 'a t := 'a t
    with type w := rws_w

  include Monads.MONAD_STATE
    with type 'a t := 'a t
    with type s := rws_s

end


module MakeT
    (Wrapped : Monad.MONAD) (R: sig type t end) (W: Monad.MONOID) (S: sig type t end) :
  MONAD_RWS =
struct
  type rws_r = R.t
  type rws_w = W.t
  type rws_s = S.t

    (* also import syntax of wrapped monad so that we can use it in functions later *)
  module WrappedInfix = Monad.MonadInfix (Wrapped)
  open WrappedInfix.Syntax

  module MON : Monad.MONAD
    with type 'a t = rws_r -> rws_s -> (('a * rws_w) * rws_s) Wrapped.t =
  struct
    type 'a t = rws_r -> rws_s -> (('a * rws_w) * rws_s) Wrapped.t

    let pure v _ s = Wrapped.pure ((v, W.empty), s)

    (* val map :
     *   ('a -> 'b) ->
     *   (r -> s -> (('a * w) * s) Wrapped.t) ->
     *   r -> s -> (('b * w) * w) Wrapped.t *)
    let map f m r s =
      let+ (result, w), s1 = m r s in
      ((f result, w), s1)

    (* val apply :
     *   (r -> s -> ((('a -> 'b) * w) * s) Wrapped.t) ->
     *   (r -> s -> (('a * w) * s) Wrapped.t) ->
     *   r -> s -> (('b * w) * s) Wrapped.t *)
    let apply fa xa r s =
      let* (f, w1), s1 = fa r s in
      let+ (result, w2), s2 = xa r s1 in
      ((f result, W.append w1 w2), s2)

    (* val bind :
     *   (r -> s -> (('a * w) * s) Wrapped.t) ->
     *   ('a -> (r -> s -> (('b * w) * s) Wrapped.t)) ->
     *   r -> s -> (('b * w) * s) Wrapped.t *)
    let bind m k r s =
      let* (result1, w1), s1 = m r s in
      let+ (result2, w2), s2 = k result1 r s1 in
      ((result2, W.append w1 w2), s2)

    let join m = bind m (fun x -> x)
  end

    (* I'm so happy! using the monadic library it was so easy to compose the monads (^w^) *)
    (* module M1 = Reader.MakeT(Wrapped)(R)
     * module M2 = State.MakeT(M1)(S)
     * module M3 = Writer.MakeT(M2)(W) *)
        (* with type 'a t := 'a t *)
    (*
     * 'a M3.t = ('a * w) M2.t
     * 'b M2.t = s -> ('b * s) M1.t
     * 'c M1.t = r -> 'c Wrapped.t
     * ==>
     * 'a M3.t = r -> s -> (('a * w) * s) Wrapped.t
     **)
    (* include M3 *)
    (* a.d. DONE if I just add the module here I don't know what kind of monad it is, can I also parameterize RWS by the module signature of Wrapped? No, you cannot parameterize by module signature. But there are more complicated patterns to do that I think *)
    (* module Wr = Wrapped
     *
     * let pure = M3.pure
     * let map = M3.map
     * let bind = M3.bind
     * let join = M3.join
     * let apply = M3.apply *)

    (* include the top monad so that RWS itself becomes a monad *)
    (* include M3 *)
    (* with type 'a t := 'a t *)

    (* include M3.Syntax *)

    (* should be unnec. since M3 already contains a Syntax module *)
    (* include Monad.MonadInfix (M3) *)
  include MON


    (* and now we can define liftings for the important functions of this monad *)
    let ask = M3.elevate @@ M2.elevate M1.peek
    let asks f = f <$> ask

    let tell = M3.tell

    let put x = M2.put x |> M3.elevate
    let get = M3.elevate M2.get
    let modify f = get >>= (fun s -> put (f s))
    let gets f = f <$> get

    (* it is a bit unfortunate that for run and create I would need the do notation of the Wrapped monad, but for the rest I would rather use the Syntax of M3. So maybe I need to define these in another nested module and then include it here *)
    let run x ~r ~s =
      let open WrappedInfix.Syntax in
      let x' = M3.run x in
      let x'' = M2.run x' s in
      let x''' = M1.run x'' r in
      let* ((a_out, w_out), s_out) = x''' in
      Wrapped.pure (a_out, w_out, s_out)

    let elevate x = x |> M1.elevate |> M2.elevate |> M3.elevate

    let create f = M3.create @@ M2.create (fun s -> M1.create (fun r ->
        let open WrappedInfix.Syntax in
        let* (a_out, w_out, s_out) = f r s in
        Wrapped.pure ((a_out, w_out), s_out)))
  end

  include MON
  (* dont do that in a monad transformer I think. only at the end when I instantiate Rws.MakeT *)
  (* include Monad.ApplicativeFunctionsList(MON)
   * include Monad.MonadFunctionsList(MON) *)
end

module Make = MakeT(Identity)
