open Vernacexpr

type g_assoc = Gramlib.Gramext.g_assoc = NonA | RightA | LeftA

type notation_type = NG_VarConstr of string * string
                   | NG_VarInst of string * string
                   | NG_Var
                   | NG_Up of string
                   | NG_SubstApply of string * string
                   | NG_Subst of string
                   | NG_RenApply of string * string
                   | NG_Ren of string

let subst_scope = "subst_scope"
let fscope = "fscope"

let level_ l = SetLevel l
let assoc_ a = SetAssoc a
let format_ fmt = SetFormat ("text", CAst.make fmt)
let only_print_ = SetOnlyPrinting

let notation_string n =
  let open Printf in
  match n with
  | NG_VarConstr (var, sort)
  | NG_VarInst (var, sort) ->
    sprintf "%s '__%s'" var sort
  | NG_Var ->
    "'var'"
  | NG_Up sort ->
    sprintf "↑__%s" sort
  | NG_SubstApply (var, sigma) ->
    sprintf "%s [ %s ]" var sigma
  | NG_Subst sigma ->
    sprintf "[ %s ]" sigma
  | NG_RenApply (var, sigma) ->
    sprintf "%s ⟨ %s ⟩" var sigma
  | NG_Ren sigma ->
    sprintf "⟨ %s ⟩" sigma

let notation_modifiers n =
  let open Printf in
  match n with
  | NG_VarConstr (var, sort) ->
    let fmt = sprintf "%s __%s" var sort in
    [ level_ 5; format_ fmt ]
  | NG_VarInst (var, sort) ->
    let fmt = sprintf "%s __%s" var sort in
    [ level_ 5; format_ fmt; only_print_ ]
  | NG_Var ->
    [ level_ 1; only_print_ ]
  | NG_Up sort ->
    [ only_print_ ]
  | NG_SubstApply _
  | NG_RenApply _ ->
    [ level_ 7; assoc_ LeftA; only_print_ ]
  | NG_Subst _
  | NG_Ren _ ->
    [ level_ 1; assoc_ LeftA; only_print_ ]

let notation_scope = function
  | NG_VarConstr _ | NG_VarInst _ | NG_Var | NG_Up _
  | NG_SubstApply _ | NG_RenApply _ ->
    subst_scope
  | NG_Subst _ | NG_Ren _ ->
    fscope
