module AL = AssocList

let var_name_assoc = ref (AL.empty : (Language.tId, string) AL.t)

type scope = Wellscoped | Unscoped

let equal_scopeType x y = match (x, y) with
  | Wellscoped, Wellscoped -> true
  | Unscoped, Unscoped -> true
  | _, _ -> false

let scope_type = ref Unscoped

let is_wellscoped () =
  match !scope_type with
  | Unscoped -> false
  | Wellscoped -> true

type coq_version = LT810 | GE810

type args = {
  infile : string;
  outfile : string;
  scope : scope;
  gen_allfv : bool;
  gen_fext : bool;
  gen_static_files : bool;
  force_overwrite : bool;
  version : coq_version;
}

type flags = { fl_allfv : bool 
             ; fl_fext : bool
             ; fl_version : coq_version }