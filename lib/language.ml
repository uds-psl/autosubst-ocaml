(** This module implements the types for the HOAS signature that is parsed by autosubst.
 ** Also it contains the variant for which kind of syntax we generate. *)
module AL = AssocList
module CG = GallinaGen

type tId = string [@@deriving show]
type vId = string [@@deriving show]
type fId = string [@@deriving show]
type cId = string [@@deriving show]

type 'a tIdMap = (tId, 'a) AL.t [@@deriving show]

type binder = Single of tId | BinderList of string * tId
[@@deriving show]
type argument_head = Atom of tId | FunApp of fId * (CG.constr_expr option [@opaque]) * (argument_head list)
[@@deriving show]

let get_bound_sort = function
  | Single x -> x
  | BinderList (_, x) -> x
let rec getArgSorts = function
  | Atom x -> [x]
  | FunApp (_, _, xs) -> List.(concat (map getArgSorts xs))

type position =
  { binders : binder list;
    head : argument_head;
  }
[@@deriving show]

type constructor =
  { cparameters : (string * tId) list;
    cname : cId;
    cpositions : position list;
  }
[@@deriving show]

let getArgs { cpositions; _ } =
  List.(concat (map (fun { head; _ } -> getArgSorts head)
                  cpositions))

type spec = (constructor list) tIdMap [@@deriving show]
type tId_list = tId list [@@deriving show]
module SSet = Set.Make (String)
type tId_set = SSet.t
let pp_tId_set f x = pp_tId_list f (SSet.elements x)
let show_tId_set x = show_tId_list (SSet.elements x)

type signature =
  { sigSpec : spec;
    sigSubstOf : (tId list) tIdMap;
    sigComponents : tId list list;
    sigIsOpen : tId_set;
    sigArguments : (tId list) tIdMap;
  }
[@@deriving show]

let sigSpec { sigSpec; _ } = sigSpec
let sigSubstOf { sigSubstOf; _ } = sigSubstOf
let sigComponents { sigComponents; _ } = sigComponents
let sigIsOpen { sigIsOpen; _ } = sigIsOpen
let sigArguments { sigArguments; _ } = sigArguments

type t = signature
[@@deriving show]

(* disable unused warning *)
module [@warning "-32"] Hsig_example = struct

  let mySigSpec : spec = AL.from_list [
    ("tm", [ {
         cparameters = [];
         cname = "app";
         cpositions = [ { binders = []; head = Atom "tm" };
                       { binders = []; head = Atom "tm" } ];
       }; {
           cparameters = [];
           cname = "tapp";
           cpositions = [ { binders = []; head = Atom "tm" };
                         { binders = []; head = Atom "ty" } ];
         }; {
           cparameters = [];
           cname = "vt";
           cpositions = [ { binders = []; head = Atom "vl" } ];
         } ]);
    ("ty", [{
         cparameters = [];
         cname = "arr";
         cpositions = [ { binders = []; head = Atom "ty" };
                       { binders = []; head = Atom "ty" } ];
       }; {
          cparameters = [];
          cname = "all";
          cpositions = [ { binders = [ Single "ty" ]; head = Atom "ty" } ];
        } ]);
    ("vl", [{
         cparameters = [];
         cname = "lam";
         cpositions = [ { binders = []; head = Atom "ty" };
                       { binders = [ Single "vl" ]; head = Atom "tm" } ];
       }; {
          cparameters = [];
          cname = "tlam";
          cpositions = [ { binders = [ Single "ty" ]; head = Atom "tm" } ];
        } ])
  ]

  let mySig = {
    sigSpec = mySigSpec;
    sigSubstOf = AL.from_list [ ("tm", ["ty"; "vl"]); ("ty", ["ty"]); ("vl", ["ty";"vl"]) ];
    sigComponents = [ ["ty"]; ["tm";"vl"] ];
    sigIsOpen = SSet.of_list ["ty"; "vl"];
    sigArguments = AL.from_list [ ("tm", ["tm"; "ty"; "vl"])
                                ; ("ty", ["ty"])
                                ; ("vl", ["ty"; "tm"])];
  }
end

module [@warning "-32"] Hsig_fol = struct
  open CG
  let mySigSpec = AL.from_list [
    ("form", [ {
         cparameters = [];
         cname = "Fal";
         cpositions = []
       }; {
           cparameters = [("p","nat")];
           cname = "Pred";
           cpositions = [ { binders = []; head = FunApp ("cod", Some (app1_ (ref_ "fin") (ref_ "p")), [ Atom "term" ]); }]
         }; {
           cparameters = [];
           cname = "Impl";
           cpositions = [ { binders = []; head = Atom "form"; };
                         { binders = []; head = Atom "form"; } ];
         }; {
           cparameters = [];
           cname = "Conj";
           cpositions = [ { binders = []; head = Atom "form" };
                         { binders = []; head = Atom "form" } ];
         }; {
           cparameters = [];
           cname = "Disj";
           cpositions = [ { binders = []; head = Atom "form" };
                         { binders = []; head = Atom "form" } ];
         }; {
           cparameters = [];
           cname = "All";
           cpositions = [ { binders = [Single "term"];
                           head = Atom "form" } ];
         }; {
           cparameters = [];
           cname = "Ex";
           cpositions = [ { binders = [Single "term"]; head = Atom "form"; } ]
         }
       ]
    ); ("term", [ {
        cparameters = [("f","nat")];
        cname = "Func";
        cpositions = [ {binders = []; head = FunApp ("cod", Some (app1_ (ref_ "fin") (ref_ "f")), [Atom "term"]); } ]
      } ] )
  ]
  let mySig = {
    sigSpec = mySigSpec;
    sigSubstOf = AL.from_list [ ("form",["term"]); ("term",["term"])];
    sigComponents = [["term"];["form"]];
    sigIsOpen = SSet.of_list ["term"];
    sigArguments = AL.from_list [ ("form",["term";"form"])
                                ; ("term",["term"])];
  }
end
