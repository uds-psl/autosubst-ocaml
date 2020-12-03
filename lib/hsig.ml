open Base
(* I'm using association lists until I figure out how to build a map from a list *)
(* strangely even something like tId need a deriving show. So they are not like 'type' in Haskell but rather like newtype? *)

type tId = string [@@deriving show]
type vId = string [@@deriving show]
type fId = string [@@deriving show]
type cId = string [@@deriving show]

type 'a tIdMap = (tId * 'a) list [@@deriving show]

type binder = Single of tId | BinderList of string * tId
[@@deriving show]
type argument_head = Atom of tId | FunApp of fId * fId * (argument_head list)
[@@deriving show]

let getBinders = function
  | Single x -> [x]
  | BinderList (_, x) -> [x]
let rec getIds = function
  | Atom x -> [x]
  | FunApp (_, _, xs) -> List.(xs >>| getIds |> concat)

type position =
  { binders : binder list;
    head : argument_head;
  }
[@@deriving show]

type constructor =
  { cparameters : (string * tId) list;
    cname : cId;
    (* TODO rename to arguments? *)
    cpositions : position list;
  }
[@@deriving show]

type spec = (constructor list) tIdMap [@@deriving show]

type signature =
  { sigSpec : spec;
    sigSubstOf : (tId list) tIdMap;
    (* TODO very often I need just the first sort of a component, so maybe make this into a nonempty list. E.g. I think I need it in Generator.genSubstitutions.
     * TODO is the second part of the pair only used in modular code? *)
    sigComponents : (tId list * tId list) list;
    sigExt : tId tIdMap;
    (* sigIsOpen was a set originally *)
    sigIsOpen : tId list;
    sigArguments : (tId list) tIdMap;
  }
[@@deriving show, fields]

type t = signature
[@@deriving show]

module Hsig_example = struct

  let mySigSpec : spec = [
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
    sigSubstOf = [ ("tm", ["ty"; "vl"]); ("ty", ["ty"]); ("vl", ["ty";"vl"]) ];
    sigComponents = [ (["ty"], []); (["tm";"vl"],[])];
    sigExt = [];
    sigIsOpen = ["ty"; "vl"];
    sigArguments = [("tm", ["tm"; "ty"; "vl"]);
                    ("ty", ["ty"]);
                    ("vl", ["ty"; "tm"])];
  }
end

module Hsig_fol = struct
  let mySigSpec = [
    ("form", [ {
         cparameters = [];
         cname = "Fal";
         cpositions = []
       }; {
           cparameters = [("p","nat")];
           cname = "Pred";
           cpositions = [ { binders = []; head = FunApp ("cod", "(fin p)", [ Atom "term" ]); }]
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
        cpositions = [ {binders = []; head = FunApp ("cod", "(fin f)", [Atom "term"]); } ]
      } ] )
  ]
  let mySig = {
    sigSpec = mySigSpec;
    sigSubstOf = [ ("form",["term"]); ("term",["term"])];
    sigComponents = [(["term"],[]);(["form"],[])];
    sigExt = [];
    sigIsOpen = ["term"];
    sigArguments = [ ("form",["term";"form"]);
                     ("term",["term"])];
  }
end
