module IdentityMonad = struct
  type 'a t = 'a

  let pure v = v [@@inline]

  let map f x = f x [@@inline]

  let apply fa xa = fa xa [@@inline]

  let bind m f = f m [@@inline]

  let join m = bind m (fun x -> x) [@@inline]
end

include IdentityMonad
include Monad.MonadInfix (IdentityMonad)
