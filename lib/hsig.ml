open Base
module AL = AssocList

type tId = string [@@deriving show, compare]
type vId = string [@@deriving show]
type fId = string [@@deriving show]
type cId = string [@@deriving show]

type 'a tIdMap = (tId, 'a) AL.t [@@deriving show]

type binder = Single of tId | BinderList of string * tId
[@@deriving show, compare]
type argument_head = Atom of tId | FunApp of fId * fId * (argument_head list)
[@@deriving show]

let getBinders = function
  | Single x -> [x]
  | BinderList (_, x) -> [x]
let rec getArgSorts = function
  | Atom x -> [x]
  | FunApp (_, _, xs) -> List.(xs >>| getArgSorts |> concat)

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
  List.concat_map cpositions ~f:(fun { head; _ } ->
    getArgSorts head)

type spec = (constructor list) tIdMap [@@deriving show]
type tId_list = tId list [@@deriving show]
type tId_set = Set.M (String).t
let pp_tId_set f x = pp_tId_list f (Set.to_list x)
let show_tId_set x = show_tId_list (Set.to_list x)

type signature =
  { sigSpec : spec;
    sigSubstOf : (tId list) tIdMap;
    sigComponents : tId list list;
    sigIsOpen : tId_set;
    sigArguments : (tId list) tIdMap;
  }
[@@deriving show, fields]

type t = signature
[@@deriving show]


module Hsig_example = struct

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
    sigIsOpen = Set.of_list (module String) ["ty"; "vl"];
    sigArguments = AL.from_list [ ("tm", ["tm"; "ty"; "vl"])
                                ; ("ty", ["ty"])
                                ; ("vl", ["ty"; "tm"])];
  }
end

module Hsig_fol = struct
  let mySigSpec = AL.from_list [
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
    sigSubstOf = AL.from_list [ ("form",["term"]); ("term",["term"])];
    sigComponents = [["term"];["form"]];
    sigIsOpen = Set.of_list (module String) ["term"];
    sigArguments = AL.from_list [ ("form",["term";"form"])
                                ; ("term",["term"])];
  }
end
