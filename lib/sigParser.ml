(** This module implements a parser for the HOAS files using the parser combinator library Angstrom.
 ** It shoudl be able to parse most reasonable signature that Autosubst 2 can parse.
 ** Differences:
 **   - we disallow constructors to have the same name as any type/functor
 **   - we disallow the extra parentheses around variadic binder specifications "(<p,m>)", so you must write "<p,m>" instead.
 ** The only thing we really have to do differently from Autosubst 2 is that we must actually parse the arguments of functors, not take them as a plain string because in the end we want to construct Coq AST. *)
open Angstrom
open Util

module L = Language
module AL = AssocList
module CG = GallinaGen
module S = Settings


(** what we parse here *)
type parameter = string * string
type constructorAST = L.cId * parameter list * L.position list * string
type specAST = L.tId list * L.fId list * constructorAST list * (L.tId, string) AL.t
type parserSpec = L.tId list * L.fId list * L.spec [@@deriving show]

(** char tests *)
let is_ascii c = (Char.code c) <= 127
let is_space = function
  | ' ' | '\t' -> true | _ -> false
let is_end_of_line = function
  | '\n' -> true | _ -> false


(** lex can be used to separate tokens from each other as it eats all following whitespace *)
let spaces = skip_while is_space
let lex p = p <* spaces

(** parser that aborts parsing by commiting so we can't backtrack and then immediately failing *)
let hard_fail msg = commit *> fail msg


(** * Parsers for all the tokens we encounter. *)

(** When parsing an identifier we just take the longest valid non-empty prefix *)
let check_non_empty_ident = function
  | (s, "") -> fail ("empty identifier: " ^ s)
  | (_, valid_prefix) -> return valid_prefix

(** Parse an identifier using functions from the Coq implementation.
 ** This allows the same unicode identifiers as Coq, e.g. greek letters.
 ** It works by taking bytes from the input stream and successively checking if they
 ** are a valid identifier.
 ** Because utf-8 encoded codepoints may be represented by multiple bytes we have to skip the check for any non-ascii bytes and remember the longest valid prefix so far.
 ** If the byte is ascii we check if the whole string is an identifier and if so we update the longest valid prefix. If not we are done and return this prefix. *)
(* folding over the input bytes is safe because ascii bytes cannot appear in non-ascii utf-8 encodings.
 * e.g. if the identifier is the greek letter lambda it will consist of 2 bytes, CE and BB, and is_ascii will fail for both *)
let raw_ident = lex @@ scan_state ("", "") (fun (s, valid_prefix) c ->
    let s' = s ^ string_of_char c in
    if is_ascii c
    then
      if CLexer.is_ident s'
      then Some (s', s')
      else None
    else Some (s', valid_prefix)
  ) >>= check_non_empty_ident

(** Parse an identifier. *)
let ident = lex raw_ident

let arrow = lex @@ string "->"
let colon = lex @@ char ':'
let ttype = lex @@ string "Type"
let tfunctor = lex @@ string "Functor"
let lparen = lex @@ char '('
let rparen = lex @@ char ')'
let comma = lex @@ char ','
let langle = lex @@ char '<'
let rangle = lex @@ char '>'
let quote = lex @@ char '"'
let comment_begin = lex @@ string "--"
let bbind = lex @@ string "bind"
let bin = lex @@ string "in"

(** combinators which wrap another parser in braces *)
let parens p = lparen *> p <* rparen
let angles p = langle *> p <* rangle

(** All declarations have to be each on one line
 ** A comment begins with "--" and is either terminated by a newline of the end of input
 ** A blank line only contains optional whitespace and an optional comment.
 ** For a line to be finished we need either at least one newline (followed by more blank
 ** lines and maybe the end of input) or the end of input *)
let comment = comment_begin *> skip_while (fun c -> c <> '\n') *> (end_of_line <|> end_of_input)
let blank_line = spaces *> (comment <|> end_of_line)
let end_line = skip_many1 blank_line *> option () (spaces *> end_of_input)
               <|> spaces *> end_of_input
let line (p: 'a t) = spaces *> lex p <* end_line

(** sort and functor declarations just care about the name *)
(** if var_name is not present (i.e. None) it will be filtered out in the end *)
let var_name = parens ident >>| (fun name -> Some name)
let sortDecl = lift4 (fun s name _ _ -> `Sort (s, name)) ident (option None var_name) colon ttype
let functorDecl = lift3 (fun f _ _ -> `Functor f) ident colon tfunctor

(** Binders can be parsed as either a single binder or a variadic binder *)
(** they are comma-separated and enclosed between 'bind' and 'in' *)
let singleBinder = lift (fun i -> L.Single i) ident
let variadicBinder = angles @@ lift3 (fun n _ t -> L.BinderList (n, t)) ident comma ident
let binders = lift3 (fun _ bs _ -> bs) bbind (sep_by1 comma (singleBinder <|> variadicBinder)) bin

(** As an argument for functors I think we allow arbitrary s-expressions that only contain identifiers
 ** e.g. (fin f) in the first-order logic example *)
let sexpr = fix (fun s ->
    (lift (fun i -> CG.ref_ i) raw_ident)
    <|> (lift (function
        | [] -> CG.ref_ "tt"
        | s :: ss -> CG.app_ s ss)
        (parens (many s))))

(** A functor argument is the name of the functor followed by optional arguments *)
let functorArg = lift4 (fun _ n pms _ ->
    (* let cexpr = CG.parse_constr_expr (String.strip pms) in *)
    (n, pms)
  )
    quote ident (* (take_till (fun c -> Char.(c = '"'))) *)
    (* TODO allow multiple static args *)
    (option [] (sexpr >>| (fun x -> [x])))
    quote

(** An argument is either an identifier representing a sort or a functor application
 ** to another argument. Here we have at last a reason to use fix *)
let arghead =
  fix (fun arg ->
      (lift2 (fun (x, y) args -> L.FunApp (x, y, args))
         functorArg (parens (sep_by1 comma arg)))
      <|> (lift (fun i -> L.Atom i) ident))

(** A position is either some binders and a head (all enclosed in parentheses)
 ** or only a head. *)
let pos =
  parens (lift2 (fun binders head -> L.{ binders; head; }) binders arghead)
  <|> lift (fun head -> L.{ binders=[]; head; }) arghead

let parameterDecl = parens @@ lift3 (fun n _ t -> (n, t)) ident colon ident

(** A constructor consists of a name, optionally some parameters, optionally some
 ** positions separated by arrows and a result sort.
 ** This was the first time I needed something above lift4. The let syntax also works okay *)
let constructorDecl : ([> `Constructor of constructorAST ]) t =
  let open Let_syntax in
  let* n = ident in
  let* pms = many parameterDecl in
  let* _ = colon in
  let* ps = many (pos <* arrow) in
  let* rt = ident in
  return (`Constructor (n, pms, ps, rt))

(** For a signature we first ignore any blank lines at the beginning and then parse
 ** an arbitrary number of sort/functor/constructor declarations in any order.
 ** Because they can appear in any order we can just throw them in a polymorphic variant
 ** and filter them out again later *)
let signature : specAST t =
  lift3 (fun _ ds _ ->
      let ss = List.filter_map (function `Sort (s, _) -> Some s | _ -> None) ds in
      let var_name_assoc = AL.from_list (List.filter_map (function `Sort (s, Some var_name) -> Some (s, var_name) | _ -> None) ds) in
      let fs = List.filter_map (function `Functor f -> Some f | _ -> None) ds in
      let cs = List.filter_map (function `Constructor c -> Some c | _ -> None) ds in
      (ss, fs, cs, var_name_assoc))
    (skip_many blank_line)
    (sortDecl <|> functorDecl <|> constructorDecl |> line |> many)
    (commit *>
     end_of_input <|>
     (take_till is_end_of_line >>= fun s -> hard_fail ("Could not parse the following line: "^s)))

(** check is a given string is a reserved constant in Coq
 ** we use a function from the Coq implementation that checks for constants like "Type"
 ** and a heuristic of common predefined constants and keywords taken from Autosubst 2 *)
let reservedIds =
  (* Keywords according to the Coq manual *)
  ["as"; "at"; "cofix"; "else"; "end"; "exists"; "exists2"; "fix";
   "for"; "forall"; "fun"; "if"; "IF"; "in"; "let"; "match"; "mod";
   "Prop"; "return"; "Set"; "then"; "Type"; "using"; "where"; "with";
   (* Additional reserved identifiers *)
   "lazymatch"; "multimatch"; "Definition"; "Fixpoint"; "CoFixpoint";
   "Axiom"; "Inductive"; "CoInductive"; "Theorem"; "Class";
   (* Identifiers used by Autosubst *)
   "fin"; "shift"; "None"; "Some"; "scons"; "var_zero"; "fun_comp"; "ap_ren";
   "ap"; "apc"; "up_ren_ren"; "id"; "scons_eta"; "scons_comp"; "scons_eta_id";
   "up_ren"; "size_ind"; "lift";
   "get_In"; "some_none_explosion"; "Some_inj"
  ]

let check_reserved s =
  let open ErrorM in
  if List.mem s reservedIds || CLexer.is_keyword CLexer.empty_keyword_state s
  then error ("reserved identifier: " ^ s)
  else pure ()

(** check if the spec is well formed.
 ** For that we check that all sort/functor/constructor names are unique
 ** and we go homomorphically through the constructors to check that all mentioned sorts
 ** and functors exist.
 ** Also, unscoped syntax with variadic binders is not supported and we check that here.
 ** The applicative Syntax *> of the error monad is very nice here because it acts as a semicolon. *)
let checkSpec (sorts, functors, ctors, var_name_assoc) =
  let open ErrorM.Syntax in
  let open ErrorM in
  let names = sorts @ functors @ List.map (fun (ctor_name, _, _, _) -> ctor_name) ctors in
  if list_contains_dup String.compare names
  then error "sort/functor/constructor names must all be different"
  else
    let checkTId tid =
      check_reserved tid *>
      if List.mem tid sorts
      then pure ()
      else error ("unknown sort: " ^ tid) in
    let checkFId fid =
      check_reserved fid *>
      if List.mem fid functors
      then pure ()
      else error ("unknown functor: " ^ fid) in
    let checkBinder () = function
      | L.Single x -> checkTId x
      | L.BinderList (_, x) ->
        if S.(equal_scopeType !scope_type Unscoped)
        then error "unscoped syntax + variadic binders are not supported"
        else checkTId x in
    let rec checkHead () = function
      | L.Atom x -> checkTId x
      | L.FunApp (fname, _, args) ->
        checkFId fname *> m_fold_ checkHead () args in
    let checkPosition () L.{ binders; head; } =
      m_fold_ checkBinder () binders
      *> checkHead () head in
    let checkConstructor (cname, cparameters, cpositions, rtype) (spec : L.spec) =
      checkTId rtype
      *> m_fold_ checkPosition () cpositions
      *> pure (AL.update rtype (fun cs -> L.{ cparameters; cname; cpositions; } :: cs) spec)
    in
    let empty_spec = AL.from_list @@ List.map (fun s -> (s, [])) sorts in
    let* ctors = m_fold_right ~f:checkConstructor ~init:empty_spec ctors in
    pure (sorts, functors, AL.flatten ctors, var_name_assoc)

(** parse and check a signature.
 ** We replace windows line endings here because that's the only way I found to handle comments
 ** with windows line endings correctly. *)
let parse_signature s =
  let open ErrorM in
  let posix_s = Str.global_replace (Str.regexp "\r\n") "\n" s in
  match parse_string ~consume:All signature posix_s with
  | Error e -> error ("Error during parsing:\n" ^ e)
  | Ok v -> checkSpec v

(** Some signatures for testing the parser in the repl *)
module [@warning "-32"] Test = struct
  let test_sort = "tm : Type"
  let test_constructor = "arr : tm -> tm -> tm"

  let test_string = {|ty : Type
arr : ty -> ty -> ty
|}
  let test_string2 = {|
tm : Type
app : tm -> tm -> tm|}

  (** From the autosubst2 examples *)
  let test_fol = {|
cod : Functor

term  : Type
form  : Type

Func (f : nat) : "cod (fin f)" (term) -> term
Fal : form
Pred (p : nat) : "cod (fin p)" (term) -> form
Impl : form -> form -> form
Conj : form -> form -> form
Disj : form -> form -> form
All  : (term -> form) -> form
Ex   : (term -> form) -> form
|}

  let test_cbpv = {|
value : Type
comp : Type
nat : Type

cod : Functor

const : nat -> value
thunk: comp -> value

force: value -> comp
letrec (p : nat) : (<p,value>  -> "cod (fin p)" (comp)) -> (<p,value> -> comp) -> comp
prd : value -> comp
seq : comp -> (value -> comp) -> comp
app: comp -> value -> comp
op : value -> value -> value
if0 : value -> comp -> comp -> comp
|}

  let test_comment = {|
-- Do I even want to support this?
tm : Type
app : tm -> tm -> tm
|}

  let parse p s = parse_string ~consume:All p s
end
