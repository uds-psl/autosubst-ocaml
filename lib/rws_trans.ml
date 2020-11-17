
  (* (\* and now we can define liftings for the important functions of this monad *\)
   * let ask = M3.elevate @@ M2.elevate M1.peek
   * let asks f = f <$> ask
   *
   * let tell = M3.tell
   *
   * let put x = M2.put x |> M3.elevate
   * let get = M3.elevate M2.get
   * let modify f = get >>= (fun s -> put (f s))
   * let gets f = f <$> get
   *
   * (\* it is a bit unfortunate that for run and create I would need the do notation of the Wrapped monad, but for the rest I would rather use the Syntax of M3. So maybe I need to define these in another nested module and then include it here *\)
   * let run x ~r ~s =
   *     let open WrappedInfix.Syntax in
   *     let x' = M3.run x in
   *     let x'' = M2.run x' s in
   *     let x''' = M1.run x'' r in
   *     let* ((a_out, w_out), s_out) = x''' in
   *     Wrapped.pure (a_out, w_out, s_out)
   *
   *   let elevate x = x |> M1.elevate |> M2.elevate |> M3.elevate
   *
   *   let create f = M3.create @@ M2.create (fun s -> M1.create (fun r ->
   *       let open WrappedInfix.Syntax in
   *       let* (a_out, w_out, s_out) = f r s in
   *       Wrapped.pure ((a_out, w_out), s_out)))
   * end *)
