open Base
open Angstrom
module H = Hsig
module AL = AssocList

(** what we parse here *)
type parameter = string * string
type constructorAST = H.cId * parameter list * H.position list * string
type specAST = H.tId list * H.fId list * constructorAST list
type parserSpec = H.tId list * H.fId list * H.spec [@@deriving show]

(** char tests *)
let is_first_ident = function
  | 'A' .. 'Z' | 'a' .. 'z' -> true
  | _ -> false
let is_ident = function
  | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' -> true
  | _ -> false
let is_space = function
  | ' ' | '\t' -> true | _ -> false

(** lex can be used to separate tokens from each other as it eats all following whitespace *)
let spaces = skip_while is_space
let lex p = p <* spaces

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
let filterReserved i =
  if List.mem reservedIds i ~equal:String.equal
  then fail @@ "reserved identifier: " ^ i
  else return i

(** parsers for all the tokens we encounter. Identifiers are filtered here so that they are not reserved keywords *)
let ident = lex @@ take_while1 is_ident >>= filterReserved
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

(** combinators which wrap another parser in braces *)
let parens p = lparen *> p <* rparen
let angles p = langle *> p <* rangle

(** All declarations have to be each on one line
 ** A comment begins with "--" and is either terminated by a newline of the end of input
 ** A blank line only contains optional whitespace and an optional comment.
 ** For a line to be finished we need either at least one newline (followed by more blank
 ** lines and maybe the end of input) or the end of input *)
let comment = comment_begin *> skip_while (fun c -> Char.(c <> '\n')) *> (end_of_line <|> end_of_input)
let blank_line = spaces *> (comment <|> end_of_line)
let end_line = skip_many1 blank_line *> option () (spaces *> end_of_input)
               <|> spaces *> end_of_input
let line (p: 'a t) = spaces *> lex p <* end_line

(** sort and functor declarations just care about the name *)
let sortDecl = lift3 (fun s _ _ -> `Sort s) ident colon ttype
let functorDecl = lift3 (fun f _ _ -> `Functor f) ident colon tfunctor

(** Binders can be parsed as either a single binder or a variadic binder *)
let singleBinder = lift (fun i -> H.Single i) ident
let variadicBinder = angles @@ lift3 (fun n _ t -> H.BinderList (n, t)) ident comma ident
let binders = many1 ((singleBinder <|> variadicBinder) <* arrow)

(** Functor parsing is a bit ugly since the parameters is just the whole string after the
 ** functor name (excluding leading whitespace) up to the closing quote
 ** Parsing functor application like this "cod (fin p)" is not really nice anyways but
 ** that's how it was in autosubst *)
let functorArg = lift4 (fun _ n pms _ -> (n, pms))
    quote ident (take_till (fun c -> Char.(c = '"'))) quote

(** An argument is either an identifier representing a sort or a functor application
 ** to another argument. Here we have at last a reason to use fix *)
let arghead =
  fix (fun arg ->
      (lift2 (fun (x, y) args -> H.FunApp (x, y, args))
         functorArg (parens (sep_by1 comma arg)))
      <|> (lift (fun i -> H.Atom i) ident))

(** A position is an optional arbitrary number of binders (need parentheses in that case)
 ** and a head *)
let pos =
  parens (lift2 (fun binders head -> H.{ binders; head; }) binders arghead)
  <|> lift (fun head -> H.{ binders=[]; head; }) arghead

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
let signature : specAST t = lift2 (fun _ ds ->
    let ss = List.filter_map ds ~f:(function `Sort s -> Some s | _ -> None) in
    let fs = List.filter_map ds ~f:(function `Functor f -> Some f | _ -> None) in
    let cs = List.filter_map ds ~f:(function `Constructor c -> Some c | _ -> None) in
    (ss, fs, cs))
    (skip_many blank_line)
    (sortDecl <|> functorDecl <|> constructorDecl |> line |> many)

(** check if the spec is well formed.
 ** For that we check that all sort/functor/constructor names are unique
 ** and we go homomorphically through the constructors to check that all mentioned sorts
 ** and functors exist. For that the applicative Syntax *> of the error monad is very nice
 ** because it acts as a semicolon. *)
let checkSpec (ts, fs, cs) =
  let open ErrorM.Syntax in
  let open ErrorM in
  let names = ts @ fs @ List.map cs ~f:(fun (cn, _, _, _) -> cn) in
  if List.contains_dup names ~compare:String.compare
  then error "sort/functor/constructor names must all be different"
  else
    let checkTId tid =
      if List.mem ts tid ~equal:String.equal
      then pure ()
      else error ("unknown sort: " ^ tid) in
    let checkFId fid =
      if List.mem fs fid ~equal:String.equal
      then pure ()
      else error ("unknown functor: " ^ fid) in
    let checkBinder () = function
      | H.Single x -> checkTId x
      | H.BinderList (_, x) -> checkTId x in
    let rec checkHead () = function
      | H.Atom x -> checkTId x
      | H.FunApp (f, _, args) ->
        checkFId f *> m_fold_ checkHead () args in
    let checkPosition () H.{ binders; head; } =
      m_fold_ checkBinder () binders
      *> checkHead () head in
    let checkConstructor (spec : H.spec) (cname, cparameters, cpositions, rtype) =
      checkTId rtype
      *> m_fold_ checkPosition () cpositions
      *> pure (AL.update rtype (fun cs -> H.{ cparameters; cname; cpositions; } :: cs) spec)
    in
    let empty_spec = AL.from_list @@ List.map ts ~f:(fun t -> (t, [])) in
    (* TODO I reversed the constructors because m_fold is a left fold. Rather implement m_fold_right *)
    let* spec = m_fold checkConstructor empty_spec (List.rev cs) in
    pure (ts, fs, AL.flatten spec)

(** parse and check a signature.
 ** We replace windows line endings here because that's the only way I found to handle comments
 ** with windows line endings correctly. *)
let parse_signature s =
  let open ErrorM in
  let posix_s = Str.global_replace (Str.regexp "\r\n") "\n" s in
  match parse_string ~consume:All signature posix_s with
  | Error e -> error e
  | Ok v -> checkSpec v

(** Some signatures for testing the parser in the repl *)
module Test = struct
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
