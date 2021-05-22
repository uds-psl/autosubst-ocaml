(* open Coqgen *)
open VernacGen
open GallinaGen
open AutomationGen
open TacGen
open ClassGen
open NotationGen
open RWEM.Syntax
open RWEM

let gen_auto_unfold () =
  let* auto_unfold_functions = gets auto_unfold_functions in
  let tac = repeat_ (unfold_ auto_unfold_functions) in
  pure @@ TacticLtac ("auto_unfold", tac)

let gen_auto_unfold_star' () =
  let* auto_unfold_functions = gets auto_unfold_functions in
  pure @@ repeat_ (unfold_ ~locus_clause:star_locus_clause auto_unfold_functions)

let gen_auto_unfold_star () =
  let* auf = gen_auto_unfold_star' () in
  pure @@ TacticNotation ([ "\"auto_unfold\""; "\"in\""; "\"*\"" ], auf)

let gen_asimpl' () =
  let* info = get in
  let asimpl_rewrite_lemmas = info.asimpl_rewrite_lemmas in
  let asimpl_cbn_functions = info.asimpl_cbn_functions in
  let asimpl_unfold_functions = info.asimpl_unfold_functions in
  let rewrites = List.map (fun t -> progress_ (rewrite_ t)) asimpl_rewrite_lemmas in
  let tac = repeat_ (first_ (rewrites @
                             [ progress_ (unfold_ asimpl_unfold_functions)
                             ; progress_ (cbn_ asimpl_cbn_functions)
                             ; calltac_ "fsimpl" ])) in
  pure @@ TacticLtac ("asimpl'", tac)

let gen_asimpl_star () =
  let* info = get in
  let asimpl_rewrite_lemmas = info.asimpl_rewrite_lemmas in
  let asimpl_cbn_functions = info.asimpl_cbn_functions in
  let asimpl_unfold_functions = info.asimpl_unfold_functions in
  let* auto_unfold_star = gen_auto_unfold_star' () in
  let rewrites = List.map (fun t -> progress_ (rewrite_ ~locus_clause:star_locus_clause t)) asimpl_rewrite_lemmas in
  let tac = then1_ auto_unfold_star
      (repeat_ (first_ (rewrites @
                        [ progress_ (unfold_ ~locus_clause:star_locus_clause asimpl_unfold_functions)
                        ; progress_ (cbn_ asimpl_cbn_functions)
                        ; calltac_ "fsimpl" ]))) in
  pure @@ TacticNotation ([ "\"asimpl\""; "\"in\""; "\"*\"" ], tac)

let gen_asimpl () =
  let* auto_unfold_star = gen_auto_unfold_star' () in
  let unfold_funcomp = repeat_ (try_ (calltac_ "unfold_funcomp")) in
  let tac = then_ [ unfold_funcomp
                  ; auto_unfold_star
                  ; calltac_ "asimpl'"
                  ; unfold_funcomp ] in
  pure @@ TacticLtac ("asimpl", tac)

let gen_asimpl_hyp () =
  let tac = then_ [ calltacArgs_ "revert" [ "J" ]
                  ; calltac_ "asimpl"
                  ; intros_ [ "J" ] ] in
  pure @@  TacticNotation ([ "\"asimpl\""; "\"in\""; "hyp(J)" ], tac)

let gen_auto_case () =
  let inner_tac = then_ [ calltac_ "asimpl"
                        ; cbn_ []
                        ; calltac_ "eauto" ] in
  let tac = calltacTac_ "auto_case" inner_tac in
  pure @@ TacticNotation ([ "\"auto_case\"" ], tac)

let gen_substify () =
  let* substify_lemmas = gets substify_lemmas in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("substify", tac)

let gen_renamify () =
  let* substify_lemmas = gets substify_lemmas in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true ~to_left:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("renamify", tac)

let gen_arguments () =
  let* arguments = gets arguments in
  pure @@ List.map (fun (name, args) -> impl_arguments_ name args) arguments

let gen_classes () =
  let* classes = gets classes in
  let gen_class (inst_type, sort) =
    let open GallinaGen in
    let binders = [ binder_ [ "X"; "Y" ] ] in
    let ctors = [ constructor_ (class_field sort inst_type)
                    (arr1_ (ref_ "X") (ref_ "Y")) ] in
    class_ (class_name sort inst_type) binders ctors in
  pure @@ List.map gen_class classes

let gen_instances () =
  let* instances = gets instances in
  let register_instance_unfolds (inst_type, sort) =
    let unfolds = instance_unfolds sort inst_type in
    let* info = get in
    put { info with auto_unfold_functions = unfolds @ info.auto_unfold_functions }
  in
  let gen_instance (inst_type, sort) =
    let iname = instance_name sort inst_type in
    let cname = class_name sort inst_type in
    let fname = function_name sort inst_type in
    instance_ iname (app_ref cname (class_args inst_type)) (app_ref ~expl:true fname [])
  in
  let* _ = sequence (List.map register_instance_unfolds instances) in
  let instance_definitions = List.map gen_instance instances in
  let ex_instances = List.map (fun (inst_type, sort) ->
      ex_instance_ (instance_name sort inst_type)) instances in
  pure @@ instance_definitions @ ex_instances

let gen_notations () =
  let* notations = gets notations in
  let gen_notation (ntype, sort) =
    notation_ (notation_string sort ntype) (notation_modifiers sort ntype) ~scope:(notation_scope ntype) (notation_body sort ntype) in
  pure @@ List.map gen_notation notations

let gen_additional () =
  let* arguments = gen_arguments () in
  let* classes = gen_classes () in
  let* instances = gen_instances () in
  let* notations = gen_notations () in
  let tactic_funs = [ gen_auto_unfold
                    ; gen_auto_unfold_star
                    ; gen_asimpl'
                    ; gen_asimpl
                    ; gen_asimpl_hyp
                    ; gen_auto_case
                    ; gen_asimpl_star
                    ; gen_substify
                    ; gen_renamify ] in
  let* tactics = a_map (fun f -> f ()) tactic_funs in
  pure { as_units = arguments @ classes @ instances @ notations; as_fext_units =  tactics }
