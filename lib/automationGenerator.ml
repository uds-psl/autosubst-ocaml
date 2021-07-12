(* open Coqgen *)
open Util
open VernacGen
open GallinaGen
open AutomationGen
open TacGen
open ClassGen
open NotationGen
open Termutil
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

let gen_asimpl_fext' () =
  let* info = get in
  let asimpl_rewrite_fext = info.asimpl_rewrite_fext in
  let asimpl_rewrite_base = info.asimpl_rewrite_base in
  let asimpl_cbn_functions = info.asimpl_cbn_functions in
  let asimpl_unfold_functions = info.asimpl_unfold_functions in
  let rewrites = List.map (fun t -> progress_ (setoid_rewrite_ t)) (asimpl_rewrite_base @ asimpl_rewrite_fext) in
  let tac = repeat_ (first_ (rewrites @
                             [ progress_ (unfold_ asimpl_unfold_functions)
                             ; progress_ (cbn_ asimpl_cbn_functions)
                             ; calltac_ "fsimpl_fext" ])) in
  pure @@ TacticLtac ("asimpl_fext'", tac)

let gen_asimpl' () =
  let* info = get in
  let asimpl_rewrite_no_fext = info.asimpl_rewrite_no_fext in
  let asimpl_rewrite_base = info.asimpl_rewrite_base in
  let asimpl_cbn_functions = info.asimpl_cbn_functions in
  let asimpl_unfold_functions = info.asimpl_unfold_functions in
  let rewrites = List.concat_map (fun t -> [ progress_ (setoid_rewrite_ t); progress_ (rewrite_ t) ]) (asimpl_rewrite_base @ asimpl_rewrite_no_fext) in
  let tac = repeat_ (first_ (rewrites @
                             [ progress_ (unfold_ asimpl_unfold_functions)
                             ; progress_ (cbn_ asimpl_cbn_functions)
                             ; progress_ (calltac_ "fsimpl")
                             ; repeat_ (unfold_ [ "funcomp" ]) ])) in
  pure @@ TacticLtac ("asimpl'", tac)

(*
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
                        ; progress_ (cbn_ ~locus_clause:star_locus_clause asimpl_cbn_functions)
                        ; calltac_ "fsimpl" ]))) in
  pure @@ TacticNotation ([ "\"asimpl\""; "\"in\""; "\"*\"" ], tac)
*)

let gen_asimpl_fext () =
  let* auto_unfold_star = gen_auto_unfold_star' () in
  let unfold_funcomp = repeat_ (try_ (calltac_ "unfold_funcomp")) in
  let tac = then_ [ unfold_funcomp
                  ; auto_unfold_star
                  ; calltac_ "asimpl_fext'"
                  ; unfold_funcomp ] in
  pure @@ TacticLtac ("asimpl_fext", tac)

let gen_asimpl () =
  let* auto_unfold_star = gen_auto_unfold_star' () in
  let unfold_funcomp = repeat_ (try_ (calltac_ "unfold_funcomp")) in
  let tac = then_ [ unfold_funcomp
                  ; auto_unfold_star
                  ; calltac_ "asimpl'"
                  ; calltac_ "minimize" ] in
  pure @@ TacticLtac ("asimpl", tac)

let gen_asimpl_fext_hyp () =
  let tac = then_ [ calltacArgs_ "revert" [ "J" ]
                  ; calltac_ "asimpl_fext"
                  ; intros_ [ "J" ] ] in
  pure @@  TacticNotation ([ "\"asimpl_fext\""; "\"in\""; "hyp(J)" ], tac)

let gen_asimpl_hyp () =
  let tac = then_ [ calltacArgs_ "revert" [ "J" ]
                  ; calltac_ "asimpl"
                  ; intros_ [ "J" ] ] in
  pure @@  TacticNotation ([ "\"asimpl\""; "\"in\""; "hyp(J)" ], tac)

let gen_auto_case_fext () =
  let inner_tac = then_ [ calltac_ "asimpl_fext"
                        ; cbn_ []
                        ; calltac_ "eauto" ] in
  let tac = calltacTac_ "auto_case" inner_tac in
  pure @@ TacticNotation ([ "\"auto_case_fext\"" ], tac)

let gen_auto_case () =
  let inner_tac = then_ [ calltac_ "asimpl"
                        ; cbn_ []
                        ; calltac_ "eauto" ] in
  let tac = calltacTac_ "auto_case" inner_tac in
  pure @@ TacticNotation ([ "\"auto_case\"" ], tac)

let gen_substify_fext () =
  let* substify_lemmas = gets substify_lemmas_fext in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("substify_fext", tac)

let gen_substify () =
  let* substify_lemmas = gets substify_lemmas in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("substify", tac)

let gen_renamify_fext () =
  let* substify_lemmas = gets substify_lemmas_fext in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true ~to_left:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("renamify_fext", tac)

let gen_renamify () =
  let* substify_lemmas = gets substify_lemmas in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true ~to_left:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("renamify", tac)

let gen_arguments_clear () =
  let* arguments = gets arguments in
  if Settings.is_wellscoped () then
    pure @@ List.map (fun (name, _) -> clear_arguments_ name) arguments
  else pure []

let gen_arguments () =
  let* arguments = gets arguments in
  if Settings.is_wellscoped () then
    pure @@ List.filter_map (fun (name, args) ->
        if list_empty args then None
        else Some (impl_arguments_ name args))
      arguments
  else pure []

let gen_classes () =
  let* classes = gets classes in
  let gen_class (inst_type, sort) =
    let open GallinaGen in
    let binders = [ binder_ [ "X"; "Y" ] ] in
    let ctors = [ constructor_ (class_field sort inst_type)
                    (arr1_ (ref_ "X") (ref_ "Y")) ] in
    class_ (class_name sort inst_type) binders ctors in
  pure @@ List.map gen_class classes

let gen_proper_instances () =
  let* proper_instances = gets proper_instances in
  let gen_instance (sort, fun_sort, ext_sort) =
    let* v = Variables.genVariables sort [ `MS; `NS ] in
    let [@warning "-8"] [], [ ms; ns ], [], scopeBinders = v in
    let* substSorts = substOf sort in
    let iname = sep (fun_sort) "morphism" in
    let signature = List.fold_right (fun _ signature ->
        app_ref "respectful" [ app_ref "pointwise_relation" [ underscore_; ref_ "eq" ]
                             ; signature ])
        substSorts (app_ref "respectful" [ ref_ "eq"; ref_ "eq" ]) in
    let itype = app_ref "Proper" [ signature; app_fix ~expl:true (fun_sort) ~sscopes:[ ms; ns ] [] ] in
    (* a.d. TODO right now this is the easiest way to generate all the names. all the other functions liek genRen are too generalized and we can't use the binders they return. So we generate them again fresh *)
    let fs = mk_refs @@ List.map (sep "f") substSorts in
    let gs = mk_refs @@ List.map (sep "g") substSorts in
    let eqs = mk_refs @@ List.map (sep "Eq") substSorts in
    let s = VarState.tfresh "s" in
    let t = VarState.tfresh "t" in
    let eq_st = VarState.tfresh "Eq_st" in
    let proof_binders = binder_ (List.fold_right (fun substSort binders ->
        [ sep "f" substSort; sep "g" substSort; sep "Eq" substSort ] @ binders)
        substSorts [ s; t; eq_st ]) in
    let proof = lambda_ [ proof_binders ]
        (app_ref "eq_ind" [ ref_ s
                          ; abs_ref "t'" (eq_ (app_ref fun_sort (fs @ [ ref_ s])) (app_ref fun_sort (gs @ [ ref_ "t'" ])))
                          ; app_ref ext_sort (fs @ gs @ eqs @ [ ref_ s ])
                          ; ref_ t
                          ; ref_ eq_st ]) in
    pure @@ instance'_ iname scopeBinders itype ~interactive:true proof
  in
  a_map gen_instance proper_instances

let gen_instances () =
  let* instances = gets instances in
  (* the instances created here should also be unfolded *)
  let register_instance_unfolds (inst_type, sort, _) =
    let unfolds = instance_unfolds sort inst_type in
    let* info = get in
    put { info with auto_unfold_functions = unfolds @ info.auto_unfold_functions }
  in
  let gen_instance inst_type sort params =
    let iname = instance_name sort inst_type in
    let cname = class_name sort inst_type in
    let fname = function_name sort inst_type in
    let cbinders = guard (Settings.is_wellscoped ()) [ binder_ ~implicit:true ~btype:(ref_ "nat") params ] in
    let args = guard (Settings.is_wellscoped ()) (List.map ref_ params) in
    instance'_ iname cbinders (app_ref cname (class_args inst_type)) (app_ref ~expl:true fname args)
  in
  (* TODO better way to chain actions? *)
  let* _ = sequence (List.map register_instance_unfolds instances) in
  let instance_definitions = List.concat_map (fun (inst_type, sort, params) -> [ gen_instance inst_type sort params ]) instances in
  pure instance_definitions

let gen_notations () =
  let* notations = gets notations in
  let gen_notation (ntype, sort) =
    notation_ (notation_string sort ntype) (notation_modifiers sort ntype) ~scope:(notation_scope ntype) (notation_body sort ntype) in
  pure @@ List.map gen_notation notations

let gen_automation () =
  let* arguments = gen_arguments () in
  let* classes = gen_classes () in
  let* instances = gen_instances () in
  let* notations = gen_notations () in
  let* proper_instances = gen_proper_instances () in
  let tactic_funs = [ gen_auto_unfold
                    ; gen_auto_unfold_star
                    ; gen_asimpl'
                    ; gen_asimpl
                    ; gen_asimpl_hyp
                    ; gen_auto_case
                    (* ; gen_asimpl_star *)
                    ; gen_substify
                    ; gen_renamify ] in
  let tactic_fext_funs = [ gen_asimpl_fext'
                         ; gen_asimpl_fext
                         ; gen_asimpl_fext_hyp
                         ; gen_substify_fext
                         ; gen_renamify_fext ] in
  let* tactics = a_map (fun f -> f ()) tactic_funs in
  let* tactics_fext = a_map (fun f -> f ()) tactic_fext_funs in
  pure { ren_subst_units = classes @ instances @ notations @ proper_instances @ tactics
       ; allfv_units = []
       ; fext_units = tactics_fext
       ; interface_units = arguments }
