open Base

module CS = CoqSyntax
module H = Hsig

let unscopedPreamble = "Require Export unscoped.\nRequire Export header_extensible.\n"
let scopedPreamble = "Require Export fintype.\nRequire Export header_extensible.\n"

let getUps scope_type component =
  let open List in
  let cart = cartesian_product component component in
  let singles = cart >>| (fun (x, y) -> (H.Single x, y)) in
  let blists =  cart >>| (fun (x, y) -> (H.BinderList ("p", x), y)) in
  match scope_type with
  | CS.WellScoped -> List.append singles blists
  | CS.Unscoped -> singles

(* deriving a comparator for a type and packing it in a module
 * from https://stackoverflow.com/a/59266326 *)
module UpsComp = struct
  module T = struct
    type t = H.binder * string [@@deriving compare]
    let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_opaque
  end

  include T
  include Comparable.Make(T)
end

let genCode scope_type components =
  let open REM.Functions in
  let open REM.Syntax in
  let open REM in
  let* code = m_fold (fun sentences component ->
      let* substSorts = substOf (List.hd_exn component) in
      let ups = getUps scope_type substSorts in
      let* code_x = Generator.genCodeT component ups in
      let sentences = sentences @ code_x in
      pure @@ sentences)
      [] components in
  pure code

let genFile scope_type =
  let open REM.Functions in
  let open REM.Syntax in
  let open REM in
  let* components = getComponents in
  let* code = genCode scope_type components in
  let ps = (List.map ~f:Coqgen.pr_vernac_expr code) in
  pure @@ (scopedPreamble
           ^ String.concat (List.map ~f:Pp.string_of_ppcmds ps))

let runGenCode scope_type hsig = REM.run (genFile scope_type) hsig
