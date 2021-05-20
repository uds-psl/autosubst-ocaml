(* open Coqgen *)
open TacGen
open NotationGen
open ClassGen

let gen_auto_unfold { auto_unfold_functions; _ } =
  let tac = repeat_ (unfold_ auto_unfold_functions) in
  TacticLtac ("auto_unfold", tac)

let gen_auto_unfold_star { auto_unfold_functions; _ } =
  let tac = repeat_ (unfold_ ~locus_clause:star_locus_clause auto_unfold_functions) in
  TacticNotation ([ "\"auto_unfold\""; "\"in\""; "\"*\"" ], tac)

let gen_asimpl' { asimpl_rewrite_lemmas; asimpl_cbn_functions; asimpl_unfold_functions; _ } =
  let rewrites = List.map (fun t -> progress_ (rewrite_ t)) asimpl_rewrite_lemmas in
  let tac = repeat_ (first_ (rewrites @
                             [ progress_ (unfold_ asimpl_unfold_functions)
                             ; progress_ (cbn_ asimpl_cbn_functions)
                             ; calltac_ "fsimpl" ])) in
  TacticLtac ("asimpl'", tac)

let gen_asimpl_star ({ asimpl_rewrite_lemmas; asimpl_cbn_functions; asimpl_unfold_functions; _ } as info) =
  let [@warning "-8"] TacticNotation (_, auto_unfold_star) = gen_auto_unfold_star info in
  let rewrites = List.map (fun t -> progress_ (rewrite_ ~locus_clause:star_locus_clause t)) asimpl_rewrite_lemmas in
  let tac = then1_ auto_unfold_star
      (repeat_ (first_ (rewrites @
                        [ progress_ (unfold_ ~locus_clause:star_locus_clause asimpl_unfold_functions)
                        ; progress_ (cbn_ asimpl_cbn_functions)
                        ; calltac_ "fsimpl" ]))) in
  TacticNotation ([ "\"asimpl\""; "\"in\""; "\"*\"" ], tac)

let gen_asimpl info =
  let [@warning "-8"] TacticNotation (_, auto_unfold_star) = gen_auto_unfold_star info in
  let unfold_funcomp = repeat_ (try_ (calltac_ "unfold_funcomp")) in
  let tac = then_ [ unfold_funcomp
                  ; auto_unfold_star
                  ; calltac_ "asimpl'"
                  ; unfold_funcomp ] in
  TacticLtac ("asimpl", tac)

let gen_asimpl_hyp _ =
  let tac = then_ [ calltacArgs_ "revert" [ "J" ]
                  ; calltac_ "asimpl"
                  ; intros_ [ "J" ] ] in
  TacticNotation ([ "\"asimpl\""; "\"in\""; "hyp(J)" ], tac)

let gen_auto_case _ =
  let inner_tac = then_ [ calltac_ "asimpl"
                        ; cbn_ []
                        ; calltac_ "eauto" ] in
  let tac = calltacTac_ "auto_case" inner_tac in
  TacticNotation ([ "\"auto_case\"" ], tac)

let gen_substify { substify_lemmas; _ } =
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  TacticLtac ("substify", tac)

let gen_renamify { substify_lemmas; _ } =
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true ~to_left:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  TacticLtac ("renamify", tac)

let gen_instances { instance_infos; _ } =
  let gen_instance (inst_type, sort, class_args) =
    let iname = instance_name sort inst_type in
    let cname = class_name inst_type in
    let fname = function_name sort inst_type in
    instance_ iname (app_ref cname class_args) (app_ref ~expl:true fname [])
  in
  List.map gen_instance instance_infos

let gen_additional info =
  let tactic_funs = [ gen_auto_unfold
                    ; gen_auto_unfold_star
                    ; gen_asimpl'
                    ; gen_asimpl
                    ; gen_asimpl_hyp
                    ; gen_auto_case
                    ; gen_asimpl_star
                    ; gen_substify
                    ; gen_renamify ] in
  let tactics = List.map (fun f -> f info) tactic_funs in
  { as_tactics = []; as_fext_tactics = tactics }
