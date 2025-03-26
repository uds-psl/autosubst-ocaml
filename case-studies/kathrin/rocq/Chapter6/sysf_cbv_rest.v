
Arguments var_ty {n_ty}.

Arguments arr {n_ty}.

Arguments all {n_ty}.

Arguments app {n_ty} {n_vl}.

Arguments tapp {n_ty} {n_vl}.

Arguments vt {n_ty} {n_vl}.

Arguments var_vl {n_ty} {n_vl}.

Arguments lam {n_ty} {n_vl}.

Arguments tlam {n_ty} {n_vl}.

Global Instance Subst_ty { m_ty : nat } { n_ty : nat } : Subst1 ((fin) (m_ty) -> ty (n_ty)) (ty (m_ty)) (ty (n_ty)) := @subst_ty (m_ty) (n_ty) .

Global Instance Subst_tm { m_ty m_vl : nat } { n_ty n_vl : nat } : Subst2 ((fin) (m_ty) -> ty (n_ty)) ((fin) (m_vl) -> vl (n_ty) (n_vl)) (tm (m_ty) (m_vl)) (tm (n_ty) (n_vl)) := @subst_tm (m_ty) (m_vl) (n_ty) (n_vl) .

Global Instance Subst_vl { m_ty m_vl : nat } { n_ty n_vl : nat } : Subst2 ((fin) (m_ty) -> ty (n_ty)) ((fin) (m_vl) -> vl (n_ty) (n_vl)) (vl (m_ty) (m_vl)) (vl (n_ty) (n_vl)) := @subst_vl (m_ty) (m_vl) (n_ty) (n_vl) .

Global Instance Ren_ty { m_ty : nat } { n_ty : nat } : Ren1 ((fin) (m_ty) -> (fin) (n_ty)) (ty (m_ty)) (ty (n_ty)) := @ren_ty (m_ty) (n_ty) .

Global Instance Ren_tm { m_ty m_vl : nat } { n_ty n_vl : nat } : Ren2 ((fin) (m_ty) -> (fin) (n_ty)) ((fin) (m_vl) -> (fin) (n_vl)) (tm (m_ty) (m_vl)) (tm (n_ty) (n_vl)) := @ren_tm (m_ty) (m_vl) (n_ty) (n_vl) .

Global Instance Ren_vl { m_ty m_vl : nat } { n_ty n_vl : nat } : Ren2 ((fin) (m_ty) -> (fin) (n_ty)) ((fin) (m_vl) -> (fin) (n_vl)) (vl (m_ty) (m_vl)) (vl (n_ty) (n_vl)) := @ren_vl (m_ty) (m_vl) (n_ty) (n_vl) .

Global Instance VarInstance_ty { m_ty : nat } : Var ((fin) (m_ty)) (ty (m_ty)) := @var_ty (m_ty) .

Notation "x '__ty'" := (var_ty x) (at level 5, format "x __ty") : subst_scope.

Notation "x '__ty'" := (@ids (_) (_) VarInstance_ty x) (at level 5, only printing, format "x __ty") : subst_scope.

Notation "'var'" := (var_ty) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_vl { m_ty m_vl : nat } : Var ((fin) (m_vl)) (vl (m_ty) (m_vl)) := @var_vl (m_ty) (m_vl) .

Notation "x '__vl'" := (var_vl x) (at level 5, format "x __vl") : subst_scope.

Notation "x '__vl'" := (@ids (_) (_) VarInstance_vl x) (at level 5, only printing, format "x __vl") : subst_scope.

Notation "'var'" := (var_vl) (only printing, at level 1) : subst_scope.

Class Up_ty X Y := up_ty : X -> Y.

Notation "↑__ty" := (up_ty) (only printing) : subst_scope.

Class Up_vl X Y := up_vl : X -> Y.

Notation "↑__vl" := (up_vl) (only printing) : subst_scope.

Notation "↑__ty" := (up_ty_ty) (only printing) : subst_scope.

Global Instance Up_ty_ty { m : nat } { n_ty : nat } : Up_ty (_) (_) := @up_ty_ty (m) (n_ty) .

Notation "↑__ty" := (up_ty_vl) (only printing) : subst_scope.

Global Instance Up_ty_vl { m : nat } { n_ty n_vl : nat } : Up_vl (_) (_) := @up_ty_vl (m) (n_ty) (n_vl) .

Notation "↑__vl" := (up_vl_ty) (only printing) : subst_scope.

Global Instance Up_vl_ty { m : nat } { n_ty : nat } : Up_ty (_) (_) := @up_vl_ty (m) (n_ty) .

Notation "↑__vl" := (up_vl_vl) (only printing) : subst_scope.

Global Instance Up_vl_vl { m : nat } { n_ty n_vl : nat } : Up_vl (_) (_) := @up_vl_vl (m) (n_ty) (n_vl) .

Notation "s [ sigmaty ]" := (subst_ty sigmaty s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ]" := (subst_ty sigmaty) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ⟩" := (ren_ty xity s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ⟩" := (ren_ty xity) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ; sigmavl ]" := (subst_tm sigmaty sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ; sigmavl ]" := (subst_tm sigmaty sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ; xivl ⟩" := (ren_tm xity xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ; xivl ⟩" := (ren_tm xity xivl) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaty ; sigmavl ]" := (subst_vl sigmaty sigmavl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaty ; sigmavl ]" := (subst_vl sigmaty sigmavl) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xity ; xivl ⟩" := (ren_vl xity xivl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xity ; xivl ⟩" := (ren_vl xity xivl) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Subst_vl,  Ren_ty,  Ren_tm,  Ren_vl,  VarInstance_ty,  VarInstance_vl.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_ty,  Subst_tm,  Subst_vl,  Ren_ty,  Ren_tm,  Ren_vl,  VarInstance_ty,  VarInstance_vl in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_ty| progress rewrite ?compComp_ty| progress rewrite ?compComp'_ty| progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?instId_vl| progress rewrite ?compComp_vl| progress rewrite ?compComp'_vl| progress rewrite ?rinstId_ty| progress rewrite ?compRen_ty| progress rewrite ?compRen'_ty| progress rewrite ?renComp_ty| progress rewrite ?renComp'_ty| progress rewrite ?renRen_ty| progress rewrite ?renRen'_ty| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?rinstId_vl| progress rewrite ?compRen_vl| progress rewrite ?compRen'_vl| progress rewrite ?renComp_vl| progress rewrite ?renComp'_vl| progress rewrite ?renRen_vl| progress rewrite ?renRen'_vl| progress rewrite ?varL_ty| progress rewrite ?varL_vl| progress rewrite ?varLRen_ty| progress rewrite ?varLRen_vl| progress (unfold up_ren, upRen_ty_ty, upRen_list_ty_ty, upRen_ty_vl, upRen_vl_ty, upRen_vl_vl, upRen_list_ty_vl, upRen_list_vl_ty, upRen_list_vl_vl, up_ty_ty, up_list_ty_ty, up_ty_vl, up_vl_ty, up_vl_vl, up_list_ty_vl, up_list_vl_ty, up_list_vl_vl)| progress (cbn [subst_ty subst_tm subst_vl ren_ty ren_tm ren_vl])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_ty in *| progress rewrite ?compComp_ty in *| progress rewrite ?compComp'_ty in *| progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?instId_vl in *| progress rewrite ?compComp_vl in *| progress rewrite ?compComp'_vl in *| progress rewrite ?rinstId_ty in *| progress rewrite ?compRen_ty in *| progress rewrite ?compRen'_ty in *| progress rewrite ?renComp_ty in *| progress rewrite ?renComp'_ty in *| progress rewrite ?renRen_ty in *| progress rewrite ?renRen'_ty in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?rinstId_vl in *| progress rewrite ?compRen_vl in *| progress rewrite ?compRen'_vl in *| progress rewrite ?renComp_vl in *| progress rewrite ?renComp'_vl in *| progress rewrite ?renRen_vl in *| progress rewrite ?renRen'_vl in *| progress rewrite ?varL_ty in *| progress rewrite ?varL_vl in *| progress rewrite ?varLRen_ty in *| progress rewrite ?varLRen_vl in *| progress (unfold up_ren, upRen_ty_ty, upRen_list_ty_ty, upRen_ty_vl, upRen_vl_ty, upRen_vl_vl, upRen_list_ty_vl, upRen_list_vl_ty, upRen_list_vl_vl, up_ty_ty, up_list_ty_ty, up_ty_vl, up_vl_ty, up_vl_vl, up_list_ty_vl, up_list_vl_ty, up_list_vl_vl in *)| progress (cbn [subst_ty subst_tm subst_vl ren_ty ren_tm ren_vl] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_ty); try repeat (erewrite rinstInst_tm); try repeat (erewrite rinstInst_vl).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_ty); try repeat (erewrite <- rinstInst_tm); try repeat (erewrite <- rinstInst_vl).
