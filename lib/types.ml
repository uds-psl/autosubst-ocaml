(* type 'a map  = Map.Make string 'a *)
(* module TIdMap = Map.Make(String) *)
(* I'm using association lists until I figure out how to build a map from a list *)

type tId = string [@@deriving show]
type cId = string [@@deriving show]

type 'a tIdMap = (tId * 'a) list [@@deriving show]

type binder = Single of tId
[@@deriving show]
type argument = Atom of tId
[@@deriving show]

let getBinders (Single x) = [x]
let getIds (Atom x) = [x]

type position =
  { binders : binder list;
    arg : argument;
  }
[@@deriving show]

type constructor =
  { parameters : (string * tId) list;
    name : cId;
    positions : position list;
  }
[@@deriving show]

type spec = (constructor list) tIdMap [@@deriving show]

type signature =
  { sigSpec : spec;
    sigSubstOf : (tId list) tIdMap;
    sigComponents : (tId list * tId list) list;
    sigExt : tId tIdMap;
    (* sigIsOpen was a set originally *)
    sigIsOpen : tId list;
    sigArguments : (tId list) tIdMap;
  }
[@@deriving show]

type point2d = float * float
[@@deriving show]

let mySigSpec : spec = [
  ("tm", [ {
       parameters = [];
       name = "app";
       positions = [ { binders = []; arg = Atom "tm" };
                     { binders = []; arg = Atom "tm" } ];
     }; {
       parameters = [];
       name = "tapp";
       positions = [ { binders = []; arg = Atom "tm" };
                     { binders = []; arg = Atom "ty" } ];
     }; {
       parameters = [];
       name = "vt";
       positions = [ { binders = []; arg = Atom "vl" } ];
     } ]);
  ("ty", [{
       parameters = [];
       name = "arr";
       positions = [ { binders = []; arg = Atom "ty" };
                     { binders = []; arg = Atom "ty" } ];
     }; {
       parameters = [];
       name = "all";
       positions = [ { binders = [ Single "ty" ]; arg = Atom "ty" } ];
     } ]);
  ("vl", [{
       parameters = [];
       name = "lam";
       positions = [ { binders = []; arg = Atom "ty" };
                     { binders = [ Single "vl" ]; arg = Atom "tm" } ];
     }; {
       parameters = [];
       name = "tlam";
       positions = [ { binders = [ Single "ty" ]; arg = Atom "tm" } ];
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
