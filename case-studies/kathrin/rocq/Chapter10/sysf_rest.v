
Arguments var_ty {n_ty}.

Arguments top {n_ty}.

Arguments arr {n_ty}.

Arguments all {n_ty}.

Arguments var_tm {n_ty} {n_tm}.

Arguments app {n_ty} {n_tm}.

Arguments tapp {n_ty} {n_tm}.

Arguments vt {n_ty} {n_tm}.

Arguments abs {n_ty} {n_tm}.

Arguments tabs {n_ty} {n_tm}.

#[global] Instance Subst_ty { m_ty : nat } { n_ty : nat } : Subst1 ((fin) (m_ty) -> ty (n_ty)) (ty (m_ty)) (ty (n_ty)) := @subst_ty (m_ty) (n_ty) .

#[global] Instance Subst_tm { m_ty m_tm : nat } { n_ty n_tm : nat } : Subst2 ((fin) (m_ty) -> ty (n_ty)) ((fin) (m_tm) -> tm (n_ty) (n_tm)) (tm (m_ty) (m_tm)) (tm (n_ty) (n_tm)) := @subst_tm (m_ty) (m_tm) (n_ty) (n_tm) .

#[global] Instance Ren_ty { m_ty : nat } { n_ty : nat } : Ren1 ((fin) (m_ty) -> (fin) (n_ty)) (ty (m_ty)) (ty (n_ty)) := @ren_ty (m_ty) (n_ty) .

#[global] Instance Ren_tm { m_ty m_tm : nat } { n_ty n_tm : nat } : Ren2 ((fin) (m_ty) -> (fin) (n_ty)) ((fin) (m_tm) -> (fin) (n_tm)) (tm (m_ty) (m_tm)) (tm (n_ty) (n_tm)) := @ren_tm (m_ty) (m_tm) (n_ty) (n_tm) .

#[global] Instance VarInstance_ty { m_ty : nat } : Var ((fin) (m_ty)) (ty (m_ty)) := @var_ty (m_ty) .

Notation "x '__ty'" := (var_ty x) (at level 5, format "x __ty") : subst_scope.

Notation "x '__ty'" := (@ids (_) (_) VarInstance_ty x) (at level 5, only printing, format "x __ty") : subst_scope.

Notation "'var'" := (var_ty) (only printing, at level 1) : subst_scope.

#[global] Instance VarInstance_tm { m_ty m_tm : nat } : Var ((fin) (m_tm)) (tm (m_ty) (m_tm)) := @var_tm (m_ty) (m_tm) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_ty X Y := up_ty : X -> Y.

Notation "↑__ty" := (up_ty) (only printing) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__ty" := (up_ty_ty) (only printing) : subst_scope.

#[global] Instance Up_ty_ty { m : nat } { n_ty : nat } : Up_ty (_) (_) := @up_ty_ty (m) (n_ty) .

Notation "↑__ty" := (up_ty_tm) (only printing) : subst_scope.

#[global] Instance Up_ty_tm { m : nat } { n_ty n_tm : nat } : Up_tm (_) (_) := @up_ty_tm (m) (n_ty) (n_tm) .

Notation "↑__tm" := (up_tm_ty) (only printing) : subst_scope.

#[global] Instance Up_tm_ty { m : nat } { n_ty : nat } : Up_ty (_) (_) := @up_tm_ty (m) (n_ty) .

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

#[global] Instance Up_tm_tm { m : nat } { n_ty n_tm : nat } : Up_tm (_) (_) := @up_tm_tm (m) (n_ty) (n_tm) .

Notation "s [ sigmaty ]" := (subst_ty sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xity ⟩" := (ren_ty xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ]" := (subst_ty sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xity ⟩" := (ren_ty xity) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ; sigmatm ]" := (subst_tm sigmaty sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "s ⟨ xity ; xitm ⟩" := (ren_tm xity xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ; sigmatm ]" := (subst_tm sigmaty sigmatm) (at level 1, left associativity, only printing) : fscope.

Notation "⟨ xity ; xitm ⟩" := (ren_tm xity xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_ty,  Subst_tm,  Ren_ty,  Ren_tm,  VarInstance_ty,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  ren1,  subst2,  ren2,  Subst1,  Ren1,  Subst2,  Ren2,  ids,  Subst_ty,  Subst_tm,  Ren_ty,  Ren_tm,  VarInstance_ty,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_ty| progress rewrite ?rinstId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?instId_tm| progress rewrite ?rinstId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_ty| progress rewrite ?varLRen_ty| progress rewrite ?varL_tm| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_ty_ty, upRen_list_ty_ty, upRen_ty_tm, upRen_tm_ty, upRen_tm_tm, upRen_list_ty_tm, upRen_list_tm_ty, upRen_list_tm_tm, up_ty_ty, up_list_ty_ty, up_ty_tm, up_tm_ty, up_tm_tm, up_list_ty_tm, up_list_tm_ty, up_list_tm_tm)| progress (cbn [subst_ty subst_tm ren_ty ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_ty in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?instId_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_ty in *| progress rewrite ?varLRen_ty in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_ty_ty, upRen_list_ty_ty, upRen_ty_tm, upRen_tm_ty, upRen_tm_tm, upRen_list_ty_tm, upRen_list_tm_ty, upRen_list_tm_tm, up_ty_ty, up_list_ty_ty, up_ty_tm, up_tm_ty, up_tm_tm, up_list_ty_tm, up_list_tm_ty, up_list_tm_tm in *)| progress (cbn [subst_ty subst_tm ren_ty ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinst_inst_ty; [|now intros]); try repeat (erewrite rinst_inst_tm; [|now intros]).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinst_inst_ty; [|intros; now asimpl]); try repeat (erewrite <- rinst_inst_tm; [|intros; now asimpl]).
