Require Export unscoped.
Require Export header_extensible.

Section ty_lam.
Variable ty : Type.

Inductive ty_lam  : Type :=
  | arr : ( ty   ) -> ( ty   ) -> ty_lam .

Variable retract_ty_lam : retract ty_lam ty.

Definition arr_  (s0 : ty  ) (s1 : ty  ) : _ :=
  inj (arr s0 s1).

Lemma congr_arr_  { s0 : ty   } { s1 : ty   } { t0 : ty   } { t1 : ty   } (H1 : s0 = t0) (H2 : s1 = t1) : arr_ s0 s1 = arr_ t0 t1 .
Proof. congruence. Qed.

End ty_lam.

Section ty_bool.
Variable ty : Type.

Inductive ty_bool  : Type :=
  | boolTy : ty_bool .

Variable retract_ty_bool : retract ty_bool ty.

Definition boolTy_  : _ :=
  inj (boolTy ).

Lemma congr_boolTy_  : boolTy_  = boolTy_  .
Proof. congruence. Qed.

End ty_bool.

Section ty_arith.
Variable ty : Type.

Inductive ty_arith  : Type :=
  | natTy : ty_arith .

Variable retract_ty_arith : retract ty_arith ty.

Definition natTy_  : _ :=
  inj (natTy ).

Lemma congr_natTy_  : natTy_  = natTy_  .
Proof. congruence. Qed.

End ty_arith.

Section ty.
Inductive ty  : Type :=
  | In_ty_lam : ( ty_lam ty  ) -> ty 
  | In_ty_bool : ( ty_bool   ) -> ty 
  | In_ty_arith : ( ty_arith   ) -> ty .

Lemma congr_In_ty_lam  { s0 : ty_lam ty  } { t0 : ty_lam ty  } (H1 : s0 = t0) : In_ty_lam s0 = In_ty_lam t0 .
Proof. congruence. Qed.

Lemma congr_In_ty_bool  { s0 : ty_bool   } { t0 : ty_bool   } (H1 : s0 = t0) : In_ty_bool s0 = In_ty_bool t0 .
Proof. congruence. Qed.

Lemma congr_In_ty_arith  { s0 : ty_arith   } { t0 : ty_arith   } (H1 : s0 = t0) : In_ty_arith s0 = In_ty_arith t0 .
Proof. congruence. Qed.

Global Instance retract_ty_lam_ty  : retract (ty_lam ty) ty := Build_retract In_ty_lam (fun x => match x with
| In_ty_lam s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_ty_lam t' => fun H => congr_In_ty_lam ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_ty_bool_ty  : retract (ty_bool ) ty := Build_retract In_ty_bool (fun x => match x with
| In_ty_bool s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_ty_bool t' => fun H => congr_In_ty_bool ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_ty_arith_ty  : retract (ty_arith ) ty := Build_retract In_ty_arith (fun x => match x with
| In_ty_arith s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_ty_arith t' => fun H => congr_In_ty_arith ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

End ty.

Section exp_lam.
Variable exp : Type.

Variable var_exp : ( nat ) -> exp .

Variable upRen_exp_exp : forall   (xi : ( nat ) -> nat), ( nat ) -> nat.

Variable ren_exp : forall   (xiexp : ( nat ) -> nat) (s : exp ), exp .

Variable up_exp_exp : forall   (sigma : ( nat ) -> exp ), ( nat ) -> exp .

Variable subst_exp : forall   (sigmaexp : ( nat ) -> exp ) (s : exp ), exp .

Variable upId_exp_exp : forall  (sigma : ( nat ) -> exp ) (Eq : forall x, sigma x = (var_exp ) x), forall x, (up_exp_exp sigma) x = (var_exp ) x.

Variable idSubst_exp : forall  (sigmaexp : ( nat ) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp ), subst_exp sigmaexp s = s.

Variable upExtRen_exp_exp : forall   (xi : ( nat ) -> nat) (zeta : ( nat ) -> nat) (Eq : forall x, xi x = zeta x), forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x.

Variable extRen_exp : forall   (xiexp : ( nat ) -> nat) (zetaexp : ( nat ) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp ), ren_exp xiexp s = ren_exp zetaexp s.

Variable upExt_exp_exp : forall   (sigma : ( nat ) -> exp ) (tau : ( nat ) -> exp ) (Eq : forall x, sigma x = tau x), forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x.

Variable ext_exp : forall   (sigmaexp : ( nat ) -> exp ) (tauexp : ( nat ) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp ), subst_exp sigmaexp s = subst_exp tauexp s.

Variable up_ren_ren_exp_exp : forall    (xi : ( nat ) -> nat) (tau : ( nat ) -> nat) (theta : ( nat ) -> nat) (Eq : forall x, ((funcomp) tau xi) x = theta x), forall x, ((funcomp) (upRen_exp_exp tau) (upRen_exp_exp xi)) x = (upRen_exp_exp theta) x.

Variable compRenRen_exp : forall    (xiexp : ( nat ) -> nat) (zetaexp : ( nat ) -> nat) (rhoexp : ( nat ) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp ), ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s.

Variable up_ren_subst_exp_exp : forall    (xi : ( nat ) -> nat) (tau : ( nat ) -> exp ) (theta : ( nat ) -> exp ) (Eq : forall x, ((funcomp) tau xi) x = theta x), forall x, ((funcomp) (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x.

Variable compRenSubst_exp : forall    (xiexp : ( nat ) -> nat) (tauexp : ( nat ) -> exp ) (thetaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp ), subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s.

Variable up_subst_ren_exp_exp : forall    (sigma : ( nat ) -> exp ) (zetaexp : ( nat ) -> nat) (theta : ( nat ) -> exp ) (Eq : forall x, ((funcomp) (ren_exp zetaexp) sigma) x = theta x), forall x, ((funcomp) (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.

Variable compSubstRen_exp : forall    (sigmaexp : ( nat ) -> exp ) (zetaexp : ( nat ) -> nat) (thetaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp ), ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s.

Variable up_subst_subst_exp_exp : forall    (sigma : ( nat ) -> exp ) (tauexp : ( nat ) -> exp ) (theta : ( nat ) -> exp ) (Eq : forall x, ((funcomp) (subst_exp tauexp) sigma) x = theta x), forall x, ((funcomp) (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.

Variable compSubstSubst_exp : forall    (sigmaexp : ( nat ) -> exp ) (tauexp : ( nat ) -> exp ) (thetaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp ), subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s.

Variable rinstInst_up_exp_exp : forall   (xi : ( nat ) -> nat) (sigma : ( nat ) -> exp ) (Eq : forall x, ((funcomp) (var_exp ) xi) x = sigma x), forall x, ((funcomp) (var_exp ) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x.

Variable rinst_inst_exp : forall   (xiexp : ( nat ) -> nat) (sigmaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp ), ren_exp xiexp s = subst_exp sigmaexp s.

Inductive exp_lam  : Type :=
  | ab : ( ty   ) -> ( exp   ) -> exp_lam 
  | app : ( exp   ) -> ( exp   ) -> exp_lam .

Variable retract_exp_lam : retract exp_lam exp.

Definition ab_  (s0 : ty  ) (s1 : exp  ) : _ :=
  inj (ab s0 s1).

Definition app_  (s0 : exp  ) (s1 : exp  ) : _ :=
  inj (app s0 s1).

Lemma congr_ab_  { s0 : ty   } { s1 : exp   } { t0 : ty   } { t1 : exp   } (H1 : s0 = t0) (H2 : s1 = t1) : ab_  s0 s1 = ab_  t0 t1 .
Proof. congruence. Qed.

Lemma congr_app_  { s0 : exp   } { s1 : exp   } { t0 : exp   } { t1 : exp   } (H1 : s0 = t0) (H2 : s1 = t1) : app_  s0 s1 = app_  t0 t1 .
Proof. congruence. Qed.

Definition ren_exp_lam   (xiexp : ( nat ) -> nat) (s : exp_lam ) : exp  :=
    match s return exp  with
    | ab  s0 s1 => ab_  ((fun x => x) s0) ((ren_exp (upRen_exp_exp xiexp)) s1)
    | app  s0 s1 => app_  ((ren_exp xiexp) s0) ((ren_exp xiexp) s1)
    end.

Variable retract_ren_exp : forall   (xiexp : ( nat ) -> nat) s, ren_exp xiexp (inj s) = ren_exp_lam xiexp s.

Definition subst_exp_lam   (sigmaexp : ( nat ) -> exp ) (s : exp_lam ) : exp  :=
    match s return exp  with
    | ab  s0 s1 => ab_  ((fun x => x) s0) ((subst_exp (up_exp_exp sigmaexp)) s1)
    | app  s0 s1 => app_  ((subst_exp sigmaexp) s0) ((subst_exp sigmaexp) s1)
    end.

Variable retract_subst_exp : forall   (sigmaexp : ( nat ) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_lam sigmaexp s.

Definition idSubst_exp_lam  (sigmaexp : ( nat ) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp_lam ) : subst_exp_lam sigmaexp s = inj s :=
    match s return subst_exp_lam sigmaexp s = inj s with
    | ab  s0 s1 => congr_ab_ ((fun x => (eq_refl) x) s0) ((idSubst_exp (up_exp_exp sigmaexp) (upId_exp_exp (_) Eqexp)) s1)
    | app  s0 s1 => congr_app_ ((idSubst_exp sigmaexp Eqexp) s0) ((idSubst_exp sigmaexp Eqexp) s1)
    end.

Definition extRen_exp_lam   (xiexp : ( nat ) -> nat) (zetaexp : ( nat ) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp_lam ) : ren_exp_lam xiexp s = ren_exp_lam zetaexp s :=
    match s return ren_exp_lam xiexp s = ren_exp_lam zetaexp s with
    | ab  s0 s1 => congr_ab_ ((fun x => (eq_refl) x) s0) ((extRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upExtRen_exp_exp (_) (_) Eqexp)) s1)
    | app  s0 s1 => congr_app_ ((extRen_exp xiexp zetaexp Eqexp) s0) ((extRen_exp xiexp zetaexp Eqexp) s1)
    end.

Definition ext_exp_lam   (sigmaexp : ( nat ) -> exp ) (tauexp : ( nat ) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp_lam ) : subst_exp_lam sigmaexp s = subst_exp_lam tauexp s :=
    match s return subst_exp_lam sigmaexp s = subst_exp_lam tauexp s with
    | ab  s0 s1 => congr_ab_ ((fun x => (eq_refl) x) s0) ((ext_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (upExt_exp_exp (_) (_) Eqexp)) s1)
    | app  s0 s1 => congr_app_ ((ext_exp sigmaexp tauexp Eqexp) s0) ((ext_exp sigmaexp tauexp Eqexp) s1)
    end.

Definition compRenRen_exp_lam    (xiexp : ( nat ) -> nat) (zetaexp : ( nat ) -> nat) (rhoexp : ( nat ) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp_lam ) : ren_exp zetaexp (ren_exp_lam xiexp s) = ren_exp_lam rhoexp s :=
    match s return ren_exp zetaexp (ren_exp_lam xiexp s) = ren_exp_lam rhoexp s with
    | ab  s0 s1 => (eq_trans) (retract_ren_exp (_) (ab (_) (_))) (congr_ab_ ((fun x => (eq_refl) x) s0) ((compRenRen_exp (upRen_exp_exp xiexp) (upRen_exp_exp zetaexp) (upRen_exp_exp rhoexp) (up_ren_ren_exp_exp (_) (_) (_) Eqexp)) s1))
    | app  s0 s1 => (eq_trans) (retract_ren_exp (_) (app (_) (_))) (congr_app_ ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s0) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s1))
    end.

Definition compRenSubst_exp_lam    (xiexp : ( nat ) -> nat) (tauexp : ( nat ) -> exp ) (thetaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp_lam ) : subst_exp tauexp (ren_exp_lam xiexp s) = subst_exp_lam thetaexp s :=
    match s return subst_exp tauexp (ren_exp_lam xiexp s) = subst_exp_lam thetaexp s with
    | ab  s0 s1 => (eq_trans) (retract_subst_exp (_) (ab (_) (_))) (congr_ab_ ((fun x => (eq_refl) x) s0) ((compRenSubst_exp (upRen_exp_exp xiexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_ren_subst_exp_exp (_) (_) (_) Eqexp)) s1))
    | app  s0 s1 => (eq_trans) (retract_subst_exp (_) (app (_) (_))) (congr_app_ ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s0) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s1))
    end.

Definition compSubstRen_exp_lam    (sigmaexp : ( nat ) -> exp ) (zetaexp : ( nat ) -> nat) (thetaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp_lam ) : ren_exp zetaexp (subst_exp_lam sigmaexp s) = subst_exp_lam thetaexp s :=
    match s return ren_exp zetaexp (subst_exp_lam sigmaexp s) = subst_exp_lam thetaexp s with
    | ab  s0 s1 => (eq_trans) (retract_ren_exp (_) (ab (_) (_))) (congr_ab_ ((fun x => (eq_refl) x) s0) ((compSubstRen_exp (up_exp_exp sigmaexp) (upRen_exp_exp zetaexp) (up_exp_exp thetaexp) (up_subst_ren_exp_exp (_) (_) (_) Eqexp)) s1))
    | app  s0 s1 => (eq_trans) (retract_ren_exp (_) (app (_) (_))) (congr_app_ ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s0) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s1))
    end.

Definition compSubstSubst_exp_lam    (sigmaexp : ( nat ) -> exp ) (tauexp : ( nat ) -> exp ) (thetaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp_lam ) : subst_exp tauexp (subst_exp_lam sigmaexp s) = subst_exp_lam thetaexp s :=
    match s return subst_exp tauexp (subst_exp_lam sigmaexp s) = subst_exp_lam thetaexp s with
    | ab  s0 s1 => (eq_trans) (retract_subst_exp (_) (ab (_) (_))) (congr_ab_ ((fun x => (eq_refl) x) s0) ((compSubstSubst_exp (up_exp_exp sigmaexp) (up_exp_exp tauexp) (up_exp_exp thetaexp) (up_subst_subst_exp_exp (_) (_) (_) Eqexp)) s1))
    | app  s0 s1 => (eq_trans) (retract_subst_exp (_) (app (_) (_))) (congr_app_ ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s0) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s1))
    end.

Definition rinst_inst_exp_lam   (xiexp : ( nat ) -> nat) (sigmaexp : ( nat ) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp_lam ) : ren_exp_lam xiexp s = subst_exp_lam sigmaexp s :=
    match s return ren_exp_lam xiexp s = subst_exp_lam sigmaexp s with
    | ab  s0 s1 => congr_ab_ ((fun x => (eq_refl) x) s0) ((rinst_inst_exp (upRen_exp_exp xiexp) (up_exp_exp sigmaexp) (rinstInst_up_exp_exp (_) (_) Eqexp)) s1)
    | app  s0 s1 => congr_app_ ((rinst_inst_exp xiexp sigmaexp Eqexp) s0) ((rinst_inst_exp xiexp sigmaexp Eqexp) s1)
    end.

Lemma rinstInst_exp_lam   (xiexp : ( nat ) -> nat) : ren_exp_lam xiexp = subst_exp_lam ((funcomp) (var_exp ) xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_exp_lam xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp_lam  : subst_exp_lam (var_exp ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp_lam (var_exp ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_exp_lam  : @ren_exp_lam   (id) = inj .
Proof. exact ((eq_trans) (rinstInst_exp_lam ((id) (_))) instId_exp_lam). Qed.

Lemma compComp_exp_lam    (sigmaexp : ( nat ) -> exp ) (tauexp : (nat) -> exp ) (s : exp_lam ) : subst_exp tauexp (subst_exp_lam sigmaexp s) = subst_exp_lam ((funcomp) (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp_lam sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp_lam    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (subst_exp_lam sigmaexp) = subst_exp_lam ((funcomp) (subst_exp tauexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp_lam sigmaexp tauexp n)). Qed.

Lemma compRen_exp_lam    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (s : exp_lam ) : ren_exp zetaexp (subst_exp_lam sigmaexp s) = subst_exp_lam ((funcomp) (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen_exp_lam sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp_lam    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (subst_exp_lam sigmaexp) = subst_exp_lam ((funcomp) (ren_exp zetaexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_exp_lam sigmaexp zetaexp n)). Qed.

Lemma renComp_exp_lam    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (s : exp_lam ) : subst_exp tauexp (ren_exp_lam xiexp s) = subst_exp_lam ((funcomp) tauexp xiexp) s .
Proof. exact (compRenSubst_exp_lam xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp_lam    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (ren_exp_lam xiexp) = subst_exp_lam ((funcomp) tauexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_exp_lam xiexp tauexp n)). Qed.

Lemma renRen_exp_lam    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (s : exp_lam ) : ren_exp zetaexp (ren_exp_lam xiexp s) = ren_exp_lam ((funcomp) zetaexp xiexp) s .
Proof. exact (compRenRen_exp_lam xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp_lam    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (ren_exp_lam xiexp) = ren_exp_lam ((funcomp) zetaexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_exp_lam xiexp zetaexp n)). Qed.

Definition isIn_exp_exp_lam (s : exp) (t : exp_lam) : Prop :=
  match t with
  | ab t0 t1 => s = t1
  | app t0 t1 => or (s = t0) (s = t1)
  end.

End exp_lam.

Section exp_arith.
Variable exp : Type.

Variable var_exp : (nat) -> exp .

Variable upRen_exp_exp : forall   (xi : (nat) -> nat), (nat) -> nat.

Variable ren_exp : forall   (xiexp : (nat) -> nat) (s : exp ), exp .

Variable up_exp_exp : forall   (sigma : (nat) -> exp ), (nat) -> exp .

Variable subst_exp : forall   (sigmaexp : (nat) -> exp ) (s : exp ), exp .

Variable upId_exp_exp : forall  (sigma : (nat) -> exp ) (Eq : forall x, sigma x = (var_exp ) x), forall x, (up_exp_exp sigma) x = (var_exp ) x.

Variable idSubst_exp : forall  (sigmaexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp ), subst_exp sigmaexp s = s.

Variable upExtRen_exp_exp : forall   (xi : (nat) -> nat) (zeta : (nat) -> nat) (Eq : forall x, xi x = zeta x), forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x.

Variable extRen_exp : forall   (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp ), ren_exp xiexp s = ren_exp zetaexp s.

Variable upExt_exp_exp : forall   (sigma : (nat) -> exp ) (tau : (nat) -> exp ) (Eq : forall x, sigma x = tau x), forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x.

Variable ext_exp : forall   (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp ), subst_exp sigmaexp s = subst_exp tauexp s.

Variable up_ren_ren_exp_exp : forall    (xi : (nat) -> nat) (tau : (nat) -> nat) (theta : (nat) -> nat) (Eq : forall x, ((funcomp) tau xi) x = theta x), forall x, ((funcomp) (upRen_exp_exp tau) (upRen_exp_exp xi)) x = (upRen_exp_exp theta) x.

Variable compRenRen_exp : forall    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (rhoexp : (nat) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp ), ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s.

Variable up_ren_subst_exp_exp : forall    (xi : (nat) -> nat) (tau : (nat) -> exp ) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) tau xi) x = theta x), forall x, ((funcomp) (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x.

Variable compRenSubst_exp : forall    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp ), subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s.

Variable up_subst_ren_exp_exp : forall    (sigma : (nat) -> exp ) (zetaexp : (nat) -> nat) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) (ren_exp zetaexp) sigma) x = theta x), forall x, ((funcomp) (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.

Variable compSubstRen_exp : forall    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp ), ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s.

Variable up_subst_subst_exp_exp : forall    (sigma : (nat) -> exp ) (tauexp : (nat) -> exp ) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) (subst_exp tauexp) sigma) x = theta x), forall x, ((funcomp) (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.

Variable compSubstSubst_exp : forall    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp ), subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s.

Variable rinstInst_up_exp_exp : forall   (xi : (nat) -> nat) (sigma : (nat) -> exp ) (Eq : forall x, ((funcomp) (var_exp ) xi) x = sigma x), forall x, ((funcomp) (var_exp ) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x.

Variable rinst_inst_exp : forall   (xiexp : (nat) -> nat) (sigmaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp ), ren_exp xiexp s = subst_exp sigmaexp s.

Inductive exp_arith  : Type :=
  | plus : ( exp   ) -> ( exp   ) -> exp_arith 
  | constNat : ( nat   ) -> exp_arith .

Variable retract_exp_arith : retract exp_arith exp.

Definition plus_  (s0 : exp  ) (s1 : exp  ) : _ :=
  inj (plus s0 s1).

Definition constNat_  (s0 : nat  ) : _ :=
  inj (constNat s0).

Lemma congr_plus_  { s0 : exp   } { s1 : exp   } { t0 : exp   } { t1 : exp   } (H1 : s0 = t0) (H2 : s1 = t1) : plus_  s0 s1 = plus_  t0 t1 .
Proof. congruence. Qed.

Lemma congr_constNat_  { s0 : nat   } { t0 : nat   } (H1 : s0 = t0) : constNat_  s0 = constNat_  t0 .
Proof. congruence. Qed.

Definition ren_exp_arith   (xiexp : (nat) -> nat) (s : exp_arith ) : exp  :=
    match s return exp  with
    | plus  s0 s1 => plus_  ((ren_exp xiexp) s0) ((ren_exp xiexp) s1)
    | constNat  s0 => constNat_  ((fun x => x) s0)
    end.

Variable retract_ren_exp : forall   (xiexp : (nat) -> nat) s, ren_exp xiexp (inj s) = ren_exp_arith xiexp s.

Definition subst_exp_arith   (sigmaexp : (nat) -> exp ) (s : exp_arith ) : exp  :=
    match s return exp  with
    | plus  s0 s1 => plus_  ((subst_exp sigmaexp) s0) ((subst_exp sigmaexp) s1)
    | constNat  s0 => constNat_  ((fun x => x) s0)
    end.

Variable retract_subst_exp : forall   (sigmaexp : (nat) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_arith sigmaexp s.

Definition idSubst_exp_arith  (sigmaexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp_arith ) : subst_exp_arith sigmaexp s = inj s :=
    match s return subst_exp_arith sigmaexp s = inj s with
    | plus  s0 s1 => congr_plus_ ((idSubst_exp sigmaexp Eqexp) s0) ((idSubst_exp sigmaexp Eqexp) s1)
    | constNat  s0 => congr_constNat_ ((fun x => (eq_refl) x) s0)
    end.

Definition extRen_exp_arith   (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp_arith ) : ren_exp_arith xiexp s = ren_exp_arith zetaexp s :=
    match s return ren_exp_arith xiexp s = ren_exp_arith zetaexp s with
    | plus  s0 s1 => congr_plus_ ((extRen_exp xiexp zetaexp Eqexp) s0) ((extRen_exp xiexp zetaexp Eqexp) s1)
    | constNat  s0 => congr_constNat_ ((fun x => (eq_refl) x) s0)
    end.

Definition ext_exp_arith   (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp_arith ) : subst_exp_arith sigmaexp s = subst_exp_arith tauexp s :=
    match s return subst_exp_arith sigmaexp s = subst_exp_arith tauexp s with
    | plus  s0 s1 => congr_plus_ ((ext_exp sigmaexp tauexp Eqexp) s0) ((ext_exp sigmaexp tauexp Eqexp) s1)
    | constNat  s0 => congr_constNat_ ((fun x => (eq_refl) x) s0)
    end.

Definition compRenRen_exp_arith    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (rhoexp : (nat) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp_arith ) : ren_exp zetaexp (ren_exp_arith xiexp s) = ren_exp_arith rhoexp s :=
    match s return ren_exp zetaexp (ren_exp_arith xiexp s) = ren_exp_arith rhoexp s with
    | plus  s0 s1 => (eq_trans) (retract_ren_exp (_) (plus (_) (_))) (congr_plus_ ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s0) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s1))
    | constNat  s0 => (eq_trans) (retract_ren_exp (_) (constNat (_))) (congr_constNat_ ((fun x => (eq_refl) x) s0))
    end.

Definition compRenSubst_exp_arith    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp_arith ) : subst_exp tauexp (ren_exp_arith xiexp s) = subst_exp_arith thetaexp s :=
    match s return subst_exp tauexp (ren_exp_arith xiexp s) = subst_exp_arith thetaexp s with
    | plus  s0 s1 => (eq_trans) (retract_subst_exp (_) (plus (_) (_))) (congr_plus_ ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s0) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s1))
    | constNat  s0 => (eq_trans) (retract_subst_exp (_) (constNat (_))) (congr_constNat_ ((fun x => (eq_refl) x) s0))
    end.

Definition compSubstRen_exp_arith    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp_arith ) : ren_exp zetaexp (subst_exp_arith sigmaexp s) = subst_exp_arith thetaexp s :=
    match s return ren_exp zetaexp (subst_exp_arith sigmaexp s) = subst_exp_arith thetaexp s with
    | plus  s0 s1 => (eq_trans) (retract_ren_exp (_) (plus (_) (_))) (congr_plus_ ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s0) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s1))
    | constNat  s0 => (eq_trans) (retract_ren_exp (_) (constNat (_))) (congr_constNat_ ((fun x => (eq_refl) x) s0))
    end.

Definition compSubstSubst_exp_arith    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp_arith ) : subst_exp tauexp (subst_exp_arith sigmaexp s) = subst_exp_arith thetaexp s :=
    match s return subst_exp tauexp (subst_exp_arith sigmaexp s) = subst_exp_arith thetaexp s with
    | plus  s0 s1 => (eq_trans) (retract_subst_exp (_) (plus (_) (_))) (congr_plus_ ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s0) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s1))
    | constNat  s0 => (eq_trans) (retract_subst_exp (_) (constNat (_))) (congr_constNat_ ((fun x => (eq_refl) x) s0))
    end.

Definition rinst_inst_exp_arith   (xiexp : (nat) -> nat) (sigmaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp_arith ) : ren_exp_arith xiexp s = subst_exp_arith sigmaexp s :=
    match s return ren_exp_arith xiexp s = subst_exp_arith sigmaexp s with
    | plus  s0 s1 => congr_plus_ ((rinst_inst_exp xiexp sigmaexp Eqexp) s0) ((rinst_inst_exp xiexp sigmaexp Eqexp) s1)
    | constNat  s0 => congr_constNat_ ((fun x => (eq_refl) x) s0)
    end.

Lemma rinstInst_exp_arith   (xiexp : (nat) -> nat) : ren_exp_arith xiexp = subst_exp_arith ((funcomp) (var_exp ) xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_exp_arith xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp_arith  : subst_exp_arith (var_exp ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp_arith (var_exp ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_exp_arith  : @ren_exp_arith   (id) = inj .
Proof. exact ((eq_trans) (rinstInst_exp_arith ((id) (_))) instId_exp_arith). Qed.

Lemma compComp_exp_arith    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (s : exp_arith ) : subst_exp tauexp (subst_exp_arith sigmaexp s) = subst_exp_arith ((funcomp) (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp_arith sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp_arith    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (subst_exp_arith sigmaexp) = subst_exp_arith ((funcomp) (subst_exp tauexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp_arith sigmaexp tauexp n)). Qed.

Lemma compRen_exp_arith    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (s : exp_arith ) : ren_exp zetaexp (subst_exp_arith sigmaexp s) = subst_exp_arith ((funcomp) (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen_exp_arith sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp_arith    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (subst_exp_arith sigmaexp) = subst_exp_arith ((funcomp) (ren_exp zetaexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_exp_arith sigmaexp zetaexp n)). Qed.

Lemma renComp_exp_arith    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (s : exp_arith ) : subst_exp tauexp (ren_exp_arith xiexp s) = subst_exp_arith ((funcomp) tauexp xiexp) s .
Proof. exact (compRenSubst_exp_arith xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp_arith    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (ren_exp_arith xiexp) = subst_exp_arith ((funcomp) tauexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_exp_arith xiexp tauexp n)). Qed.

Lemma renRen_exp_arith    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (s : exp_arith ) : ren_exp zetaexp (ren_exp_arith xiexp s) = ren_exp_arith ((funcomp) zetaexp xiexp) s .
Proof. exact (compRenRen_exp_arith xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp_arith    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (ren_exp_arith xiexp) = ren_exp_arith ((funcomp) zetaexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_exp_arith xiexp zetaexp n)). Qed.

Definition isIn_exp_exp_arith (s : exp) (t : exp_arith) : Prop :=
  match t with
  | plus t0 t1 => or (s = t0) (s = t1)
  | constNat t0 => False
  end.

End exp_arith.

Section exp_bool.
Variable exp : Type.

Variable var_exp : (nat) -> exp .

Variable upRen_exp_exp : forall   (xi : (nat) -> nat), (nat) -> nat.

Variable ren_exp : forall   (xiexp : (nat) -> nat) (s : exp ), exp .

Variable up_exp_exp : forall   (sigma : (nat) -> exp ), (nat) -> exp .

Variable subst_exp : forall   (sigmaexp : (nat) -> exp ) (s : exp ), exp .

Variable upId_exp_exp : forall  (sigma : (nat) -> exp ) (Eq : forall x, sigma x = (var_exp ) x), forall x, (up_exp_exp sigma) x = (var_exp ) x.

Variable idSubst_exp : forall  (sigmaexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp ), subst_exp sigmaexp s = s.

Variable upExtRen_exp_exp : forall   (xi : (nat) -> nat) (zeta : (nat) -> nat) (Eq : forall x, xi x = zeta x), forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x.

Variable extRen_exp : forall   (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp ), ren_exp xiexp s = ren_exp zetaexp s.

Variable upExt_exp_exp : forall   (sigma : (nat) -> exp ) (tau : (nat) -> exp ) (Eq : forall x, sigma x = tau x), forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x.

Variable ext_exp : forall   (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp ), subst_exp sigmaexp s = subst_exp tauexp s.

Variable up_ren_ren_exp_exp : forall    (xi : (nat) -> nat) (tau : (nat) -> nat) (theta : (nat) -> nat) (Eq : forall x, ((funcomp) tau xi) x = theta x), forall x, ((funcomp) (upRen_exp_exp tau) (upRen_exp_exp xi)) x = (upRen_exp_exp theta) x.

Variable compRenRen_exp : forall    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (rhoexp : (nat) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp ), ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s.

Variable up_ren_subst_exp_exp : forall    (xi : (nat) -> nat) (tau : (nat) -> exp ) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) tau xi) x = theta x), forall x, ((funcomp) (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x.

Variable compRenSubst_exp : forall    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp ), subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s.

Variable up_subst_ren_exp_exp : forall    (sigma : (nat) -> exp ) (zetaexp : (nat) -> nat) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) (ren_exp zetaexp) sigma) x = theta x), forall x, ((funcomp) (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.

Variable compSubstRen_exp : forall    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp ), ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s.

Variable up_subst_subst_exp_exp : forall    (sigma : (nat) -> exp ) (tauexp : (nat) -> exp ) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) (subst_exp tauexp) sigma) x = theta x), forall x, ((funcomp) (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x.

Variable compSubstSubst_exp : forall    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp ), subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s.

Variable rinstInst_up_exp_exp : forall   (xi : (nat) -> nat) (sigma : (nat) -> exp ) (Eq : forall x, ((funcomp) (var_exp ) xi) x = sigma x), forall x, ((funcomp) (var_exp ) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x.

Variable rinst_inst_exp : forall   (xiexp : (nat) -> nat) (sigmaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp ), ren_exp xiexp s = subst_exp sigmaexp s.

Inductive exp_bool  : Type :=
  | constBool : ( bool   ) -> exp_bool 
  | If : ( exp   ) -> ( exp   ) -> ( exp   ) -> exp_bool .

Variable retract_exp_bool : retract exp_bool exp.

Definition constBool_  (s0 : bool  ) : _ :=
  inj (constBool s0).

Definition If_  (s0 : exp  ) (s1 : exp  ) (s2 : exp  ) : _ :=
  inj (If s0 s1 s2).

Lemma congr_constBool_  { s0 : bool   } { t0 : bool   } (H1 : s0 = t0) : constBool_  s0 = constBool_  t0 .
Proof. congruence. Qed.

Lemma congr_If_  { s0 : exp   } { s1 : exp   } { s2 : exp   } { t0 : exp   } { t1 : exp   } { t2 : exp   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : If_  s0 s1 s2 = If_  t0 t1 t2 .
Proof. congruence. Qed.

Definition ren_exp_bool   (xiexp : (nat) -> nat) (s : exp_bool ) : exp  :=
    match s return exp  with
    | constBool  s0 => constBool_  ((fun x => x) s0)
    | If  s0 s1 s2 => If_  ((ren_exp xiexp) s0) ((ren_exp xiexp) s1) ((ren_exp xiexp) s2)
    end.

Variable retract_ren_exp : forall   (xiexp : (nat) -> nat) s, ren_exp xiexp (inj s) = ren_exp_bool xiexp s.

Definition subst_exp_bool   (sigmaexp : (nat) -> exp ) (s : exp_bool ) : exp  :=
    match s return exp  with
    | constBool  s0 => constBool_  ((fun x => x) s0)
    | If  s0 s1 s2 => If_  ((subst_exp sigmaexp) s0) ((subst_exp sigmaexp) s1) ((subst_exp sigmaexp) s2)
    end.

Variable retract_subst_exp : forall   (sigmaexp : (nat) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_bool sigmaexp s.

Definition idSubst_exp_bool  (sigmaexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp_bool ) : subst_exp_bool sigmaexp s = inj s :=
    match s return subst_exp_bool sigmaexp s = inj s with
    | constBool  s0 => congr_constBool_ ((fun x => (eq_refl) x) s0)
    | If  s0 s1 s2 => congr_If_ ((idSubst_exp sigmaexp Eqexp) s0) ((idSubst_exp sigmaexp Eqexp) s1) ((idSubst_exp sigmaexp Eqexp) s2)
    end.

Definition extRen_exp_bool   (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp_bool ) : ren_exp_bool xiexp s = ren_exp_bool zetaexp s :=
    match s return ren_exp_bool xiexp s = ren_exp_bool zetaexp s with
    | constBool  s0 => congr_constBool_ ((fun x => (eq_refl) x) s0)
    | If  s0 s1 s2 => congr_If_ ((extRen_exp xiexp zetaexp Eqexp) s0) ((extRen_exp xiexp zetaexp Eqexp) s1) ((extRen_exp xiexp zetaexp Eqexp) s2)
    end.

Definition ext_exp_bool   (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp_bool ) : subst_exp_bool sigmaexp s = subst_exp_bool tauexp s :=
    match s return subst_exp_bool sigmaexp s = subst_exp_bool tauexp s with
    | constBool  s0 => congr_constBool_ ((fun x => (eq_refl) x) s0)
    | If  s0 s1 s2 => congr_If_ ((ext_exp sigmaexp tauexp Eqexp) s0) ((ext_exp sigmaexp tauexp Eqexp) s1) ((ext_exp sigmaexp tauexp Eqexp) s2)
    end.

Definition compRenRen_exp_bool    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (rhoexp : (nat) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp_bool ) : ren_exp zetaexp (ren_exp_bool xiexp s) = ren_exp_bool rhoexp s :=
    match s return ren_exp zetaexp (ren_exp_bool xiexp s) = ren_exp_bool rhoexp s with
    | constBool  s0 => (eq_trans) (retract_ren_exp (_) (constBool (_))) (congr_constBool_ ((fun x => (eq_refl) x) s0))
    | If  s0 s1 s2 => (eq_trans) (retract_ren_exp (_) (If (_) (_) (_))) (congr_If_ ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s0) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s1) ((compRenRen_exp xiexp zetaexp rhoexp Eqexp) s2))
    end.

Definition compRenSubst_exp_bool    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp_bool ) : subst_exp tauexp (ren_exp_bool xiexp s) = subst_exp_bool thetaexp s :=
    match s return subst_exp tauexp (ren_exp_bool xiexp s) = subst_exp_bool thetaexp s with
    | constBool  s0 => (eq_trans) (retract_subst_exp (_) (constBool (_))) (congr_constBool_ ((fun x => (eq_refl) x) s0))
    | If  s0 s1 s2 => (eq_trans) (retract_subst_exp (_) (If (_) (_) (_))) (congr_If_ ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s0) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s1) ((compRenSubst_exp xiexp tauexp thetaexp Eqexp) s2))
    end.

Definition compSubstRen_exp_bool    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp_bool ) : ren_exp zetaexp (subst_exp_bool sigmaexp s) = subst_exp_bool thetaexp s :=
    match s return ren_exp zetaexp (subst_exp_bool sigmaexp s) = subst_exp_bool thetaexp s with
    | constBool  s0 => (eq_trans) (retract_ren_exp (_) (constBool (_))) (congr_constBool_ ((fun x => (eq_refl) x) s0))
    | If  s0 s1 s2 => (eq_trans) (retract_ren_exp (_) (If (_) (_) (_))) (congr_If_ ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s0) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s1) ((compSubstRen_exp sigmaexp zetaexp thetaexp Eqexp) s2))
    end.

Definition compSubstSubst_exp_bool    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp_bool ) : subst_exp tauexp (subst_exp_bool sigmaexp s) = subst_exp_bool thetaexp s :=
    match s return subst_exp tauexp (subst_exp_bool sigmaexp s) = subst_exp_bool thetaexp s with
    | constBool  s0 => (eq_trans) (retract_subst_exp (_) (constBool (_))) (congr_constBool_ ((fun x => (eq_refl) x) s0))
    | If  s0 s1 s2 => (eq_trans) (retract_subst_exp (_) (If (_) (_) (_))) (congr_If_ ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s0) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s1) ((compSubstSubst_exp sigmaexp tauexp thetaexp Eqexp) s2))
    end.

Definition rinst_inst_exp_bool   (xiexp : (nat) -> nat) (sigmaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp_bool ) : ren_exp_bool xiexp s = subst_exp_bool sigmaexp s :=
    match s return ren_exp_bool xiexp s = subst_exp_bool sigmaexp s with
    | constBool  s0 => congr_constBool_ ((fun x => (eq_refl) x) s0)
    | If  s0 s1 s2 => congr_If_ ((rinst_inst_exp xiexp sigmaexp Eqexp) s0) ((rinst_inst_exp xiexp sigmaexp Eqexp) s1) ((rinst_inst_exp xiexp sigmaexp Eqexp) s2)
    end.

Lemma rinstInst_exp_bool   (xiexp : (nat) -> nat) : ren_exp_bool xiexp = subst_exp_bool ((funcomp) (var_exp ) xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_exp_bool xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp_bool  : subst_exp_bool (var_exp ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp_bool (var_exp ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_exp_bool  : @ren_exp_bool   (id) = inj .
Proof. exact ((eq_trans) (rinstInst_exp_bool ((id) (_))) instId_exp_bool). Qed.

Lemma compComp_exp_bool    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (s : exp_bool ) : subst_exp tauexp (subst_exp_bool sigmaexp s) = subst_exp_bool ((funcomp) (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp_bool sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp_bool    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (subst_exp_bool sigmaexp) = subst_exp_bool ((funcomp) (subst_exp tauexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp_bool sigmaexp tauexp n)). Qed.

Lemma compRen_exp_bool    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (s : exp_bool ) : ren_exp zetaexp (subst_exp_bool sigmaexp s) = subst_exp_bool ((funcomp) (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen_exp_bool sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp_bool    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (subst_exp_bool sigmaexp) = subst_exp_bool ((funcomp) (ren_exp zetaexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_exp_bool sigmaexp zetaexp n)). Qed.

Lemma renComp_exp_bool    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (s : exp_bool ) : subst_exp tauexp (ren_exp_bool xiexp s) = subst_exp_bool ((funcomp) tauexp xiexp) s .
Proof. exact (compRenSubst_exp_bool xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp_bool    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (ren_exp_bool xiexp) = subst_exp_bool ((funcomp) tauexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_exp_bool xiexp tauexp n)). Qed.

Lemma renRen_exp_bool    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (s : exp_bool ) : ren_exp zetaexp (ren_exp_bool xiexp s) = ren_exp_bool ((funcomp) zetaexp xiexp) s .
Proof. exact (compRenRen_exp_bool xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp_bool    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (ren_exp_bool xiexp) = ren_exp_bool ((funcomp) zetaexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_exp_bool xiexp zetaexp n)). Qed.

Definition isIn_exp_exp_bool (s : exp) (t : exp_bool) : Prop :=
  match t with
  | constBool t0 => False
  | If t0 t1 t2 => or (s = t0) (or (s = t1) (s = t2))
  end.

End exp_bool.

Section exp_var.
Variable exp : Type.

Variable ren_exp : forall   (xiexp : (nat) -> nat) (s : exp ), exp .

Variable subst_exp : forall   (sigmaexp : (nat) -> exp ) (s : exp ), exp .

Inductive exp_var  : Type :=
  | var_exp_var : (nat) -> exp_var .

Variable retract_exp_var : retract exp_var exp.

Definition var_exp  x : _ :=
  inj (var_exp_var x).

Definition ren_exp_var   (xiexp : (nat) -> nat) (s : exp_var ) : exp  :=
    match s return exp  with
    | var_exp_var  s => (var_exp ) (xiexp s)
    end.

Variable retract_ren_exp : forall   (xiexp : (nat) -> nat) s, ren_exp xiexp (inj s) = ren_exp_var xiexp s.

Definition subst_exp_var   (sigmaexp : (nat) -> exp ) (s : exp_var ) : exp  :=
    match s return exp  with
    | var_exp_var  s => sigmaexp s
    end.

Variable retract_subst_exp : forall   (sigmaexp : (nat) -> exp ) s, subst_exp sigmaexp (inj s) = subst_exp_var sigmaexp s.

Definition idSubst_exp_var  (sigmaexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp_var ) : subst_exp_var sigmaexp s = inj s :=
    match s return subst_exp_var sigmaexp s = inj s with
    | var_exp_var  s => Eqexp s
    end.

Definition extRen_exp_var   (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp_var ) : ren_exp_var xiexp s = ren_exp_var zetaexp s :=
    match s return ren_exp_var xiexp s = ren_exp_var zetaexp s with
    | var_exp_var  s => (ap) (var_exp ) (Eqexp s)
    end.

Definition ext_exp_var   (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp_var ) : subst_exp_var sigmaexp s = subst_exp_var tauexp s :=
    match s return subst_exp_var sigmaexp s = subst_exp_var tauexp s with
    | var_exp_var  s => Eqexp s
    end.

Definition compRenRen_exp_var    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (rhoexp : (nat) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp_var ) : ren_exp zetaexp (ren_exp_var xiexp s) = ren_exp_var rhoexp s :=
    match s return ren_exp zetaexp (ren_exp_var xiexp s) = ren_exp_var rhoexp s with
    | var_exp_var  s => (eq_trans) (retract_ren_exp (_) (var_exp_var (xiexp s))) ((ap) (var_exp ) (Eqexp s))
    end.

Definition compRenSubst_exp_var    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp_var ) : subst_exp tauexp (ren_exp_var xiexp s) = subst_exp_var thetaexp s :=
    match s return subst_exp tauexp (ren_exp_var xiexp s) = subst_exp_var thetaexp s with
    | var_exp_var  s => (eq_trans) (retract_subst_exp (_) (var_exp_var (xiexp s))) (Eqexp s)
    end.

Definition compSubstRen_exp_var    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp_var ) : ren_exp zetaexp (subst_exp_var sigmaexp s) = subst_exp_var thetaexp s :=
    match s return ren_exp zetaexp (subst_exp_var sigmaexp s) = subst_exp_var thetaexp s with
    | var_exp_var  s => Eqexp s
    end.

Definition compSubstSubst_exp_var    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp_var ) : subst_exp tauexp (subst_exp_var sigmaexp s) = subst_exp_var thetaexp s :=
    match s return subst_exp tauexp (subst_exp_var sigmaexp s) = subst_exp_var thetaexp s with
    | var_exp_var  s => Eqexp s
    end.

Definition rinst_inst_exp_var   (xiexp : (nat) -> nat) (sigmaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp_var ) : ren_exp_var xiexp s = subst_exp_var sigmaexp s :=
    match s return ren_exp_var xiexp s = subst_exp_var sigmaexp s with
    | var_exp_var  s => Eqexp s
    end.

Lemma rinstInst_exp_var   (xiexp : (nat) -> nat) : ren_exp_var xiexp = subst_exp_var ((funcomp) (var_exp ) xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_exp_var xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp_var  : subst_exp_var (var_exp ) = inj .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp_var (var_exp ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_exp_var  : @ren_exp_var   (id) = inj .
Proof. exact ((eq_trans) (rinstInst_exp_var ((id) (_))) instId_exp_var). Qed.

Lemma varL_exp_var   (sigmaexp : (nat) -> exp ) : (funcomp) (subst_exp_var sigmaexp) (var_exp_var ) = sigmaexp .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_exp_var   (xiexp : (nat) -> nat) : (funcomp) (ren_exp_var xiexp) (var_exp_var ) = (funcomp) (var_exp ) xiexp .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_exp_var    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (s : exp_var ) : subst_exp tauexp (subst_exp_var sigmaexp s) = subst_exp_var ((funcomp) (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp_var sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp_var    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (subst_exp_var sigmaexp) = subst_exp_var ((funcomp) (subst_exp tauexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp_var sigmaexp tauexp n)). Qed.

Lemma compRen_exp_var    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (s : exp_var ) : ren_exp zetaexp (subst_exp_var sigmaexp s) = subst_exp_var ((funcomp) (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen_exp_var sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp_var    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (subst_exp_var sigmaexp) = subst_exp_var ((funcomp) (ren_exp zetaexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_exp_var sigmaexp zetaexp n)). Qed.

Lemma renComp_exp_var    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (s : exp_var ) : subst_exp tauexp (ren_exp_var xiexp s) = subst_exp_var ((funcomp) tauexp xiexp) s .
Proof. exact (compRenSubst_exp_var xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp_var    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (ren_exp_var xiexp) = subst_exp_var ((funcomp) tauexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_exp_var xiexp tauexp n)). Qed.

Lemma renRen_exp_var    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (s : exp_var ) : ren_exp zetaexp (ren_exp_var xiexp s) = ren_exp_var ((funcomp) zetaexp xiexp) s .
Proof. exact (compRenRen_exp_var xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp_var    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (ren_exp_var xiexp) = ren_exp_var ((funcomp) zetaexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_exp_var xiexp zetaexp n)). Qed.

Definition isIn_exp_exp_var (s : exp) (t : exp_var) : Prop :=
  match t with
  | _ => False
  end.

End exp_var.

Section exp.
Inductive exp  : Type :=
  | In_exp_var : ( exp_var   ) -> exp 
  | In_exp_lam : ( exp_lam exp  ) -> exp 
  | In_exp_bool : ( exp_bool exp  ) -> exp 
  | In_exp_arith : ( exp_arith exp  ) -> exp .

Lemma congr_In_exp_var  { s0 : exp_var   } { t0 : exp_var   } (H1 : s0 = t0) : In_exp_var  s0 = In_exp_var  t0 .
Proof. congruence. Qed.

Lemma congr_In_exp_lam  { s0 : exp_lam exp  } { t0 : exp_lam exp  } (H1 : s0 = t0) : In_exp_lam  s0 = In_exp_lam  t0 .
Proof. congruence. Qed.

Lemma congr_In_exp_bool  { s0 : exp_bool exp  } { t0 : exp_bool exp  } (H1 : s0 = t0) : In_exp_bool  s0 = In_exp_bool  t0 .
Proof. congruence. Qed.

Lemma congr_In_exp_arith  { s0 : exp_arith exp  } { t0 : exp_arith exp  } (H1 : s0 = t0) : In_exp_arith  s0 = In_exp_arith  t0 .
Proof. congruence. Qed.

Global Instance retract_exp_lam_exp  : retract (exp_lam exp) exp := Build_retract In_exp_lam (fun x => match x with
| In_exp_lam s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_exp_lam t' => fun H => congr_In_exp_lam ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_exp_arith_exp  : retract (exp_arith exp) exp := Build_retract In_exp_arith (fun x => match x with
| In_exp_arith s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_exp_arith t' => fun H => congr_In_exp_arith ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_exp_bool_exp  : retract (exp_bool exp) exp := Build_retract In_exp_bool (fun x => match x with
| In_exp_bool s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_exp_bool t' => fun H => congr_In_exp_bool ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Global Instance retract_exp_var_exp  : retract (exp_var ) exp := Build_retract In_exp_var (fun x => match x with
| In_exp_var s => Datatypes.Some s
| _ => Datatypes.None
end) (fun s => eq_refl) (fun s t => match t with
| In_exp_var t' => fun H => congr_In_exp_var ((eq_sym) (Some_inj H))
| _ => some_none_explosion
end) .

Arguments var_exp {_} {_}.

Arguments var_exp {_} {_}.

Arguments var_exp {_} {_}.

Arguments var_exp {_} {_}.

Definition upRen_exp_exp   (xi : (nat) -> nat) : (nat) ->nat:=
  (up_ren) xi.

Fixpoint ren_exp   (xiexp : (nat) -> nat) (s : exp ) : exp  :=
    match s return exp  with
    | In_exp_var  s0 =>   ((ren_exp_var (_) (_) xiexp) s0)
    | In_exp_lam  s0 =>   ((ren_exp_lam (_) upRen_exp_exp ren_exp (_) xiexp) s0)
    | In_exp_bool  s0 =>   ((ren_exp_bool (_) ren_exp (_) xiexp) s0)
    | In_exp_arith  s0 =>   ((ren_exp_arith (_) ren_exp (_) xiexp) s0)
    end.

Definition up_exp_exp   (sigma : (nat) -> exp ) : (nat) -> exp  :=
  (scons) ((var_exp ) (var_zero)) ((funcomp) (ren_exp (shift)) sigma).

Fixpoint subst_exp   (sigmaexp : (nat) -> exp ) (s : exp ) : exp  :=
    match s return exp  with
    | In_exp_var  s0 =>   ((subst_exp_var (_) sigmaexp) s0)
    | In_exp_lam  s0 =>   ((subst_exp_lam (_) up_exp_exp subst_exp (_) sigmaexp) s0)
    | In_exp_bool  s0 =>   ((subst_exp_bool (_) subst_exp (_) sigmaexp) s0)
    | In_exp_arith  s0 =>   ((subst_exp_arith (_) subst_exp (_) sigmaexp) s0)
    end.

Definition upId_exp_exp  (sigma : (nat) -> exp ) (Eq : forall x, sigma x = (var_exp ) x) : forall x, (up_exp_exp sigma) x = (var_exp ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint idSubst_exp  (sigmaexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = (var_exp ) x) (s : exp ) : subst_exp sigmaexp s = s :=
    match s return subst_exp sigmaexp s = s with
    | In_exp_var  s0 =>  ((idSubst_exp_var (_) (_) sigmaexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((idSubst_exp_lam (_) var_exp up_exp_exp subst_exp upId_exp_exp idSubst_exp (_) sigmaexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((idSubst_exp_bool (_) var_exp subst_exp idSubst_exp (_) sigmaexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((idSubst_exp_arith (_) var_exp subst_exp idSubst_exp (_) sigmaexp Eqexp) s0)
    end.

Definition upExtRen_exp_exp   (xi : (nat) -> nat) (zeta : (nat) -> nat) (Eq : forall x, xi x = zeta x) : forall x, (upRen_exp_exp xi) x = (upRen_exp_exp zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint extRen_exp   (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (Eqexp : forall x, xiexp x = zetaexp x) (s : exp ) : ren_exp xiexp s = ren_exp zetaexp s :=
    match s return ren_exp xiexp s = ren_exp zetaexp s with
    | In_exp_var  s0 =>  ((extRen_exp_var (_) (_) xiexp zetaexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((extRen_exp_lam (_) upRen_exp_exp ren_exp upExtRen_exp_exp extRen_exp (_) xiexp zetaexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((extRen_exp_bool (_) ren_exp extRen_exp (_) xiexp zetaexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((extRen_exp_arith (_) ren_exp extRen_exp (_) xiexp zetaexp Eqexp) s0)
    end.

Definition upExt_exp_exp   (sigma : (nat) -> exp ) (tau : (nat) -> exp ) (Eq : forall x, sigma x = tau x) : forall x, (up_exp_exp sigma) x = (up_exp_exp tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint ext_exp   (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (Eqexp : forall x, sigmaexp x = tauexp x) (s : exp ) : subst_exp sigmaexp s = subst_exp tauexp s :=
    match s return subst_exp sigmaexp s = subst_exp tauexp s with
    | In_exp_var  s0 =>  ((ext_exp_var (_) sigmaexp tauexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((ext_exp_lam (_) up_exp_exp subst_exp upExt_exp_exp ext_exp (_) sigmaexp tauexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((ext_exp_bool (_) subst_exp ext_exp (_) sigmaexp tauexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((ext_exp_arith (_) subst_exp ext_exp (_) sigmaexp tauexp Eqexp) s0)
    end.

Definition up_ren_ren_exp_exp    (xi : (nat) -> nat) (tau : (nat) -> nat) (theta : (nat) -> nat) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_exp_exp tau) (upRen_exp_exp xi)) x = (upRen_exp_exp theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_exp    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (rhoexp : (nat) -> nat) (Eqexp : forall x, ((funcomp) zetaexp xiexp) x = rhoexp x) (s : exp ) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s :=
    match s return ren_exp zetaexp (ren_exp xiexp s) = ren_exp rhoexp s with
    | In_exp_var  s0 =>  ((compRenRen_exp_var (_) (_) (_) (fun x y => eq_refl) xiexp zetaexp rhoexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((compRenRen_exp_lam (_) upRen_exp_exp (_) up_ren_ren_exp_exp compRenRen_exp (_) (fun x y => eq_refl) xiexp zetaexp rhoexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((compRenRen_exp_bool (_) (_) compRenRen_exp (_) (fun x y => eq_refl) xiexp zetaexp rhoexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((compRenRen_exp_arith (_) (_) compRenRen_exp (_) (fun x y => eq_refl) xiexp zetaexp rhoexp Eqexp) s0)
    end.

Definition up_ren_subst_exp_exp    (xi : (nat) -> nat) (tau : (nat) -> exp ) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_exp_exp tau) (upRen_exp_exp xi)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint compRenSubst_exp    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) tauexp xiexp) x = thetaexp x) (s : exp ) : subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s :=
    match s return subst_exp tauexp (ren_exp xiexp s) = subst_exp thetaexp s with
    | In_exp_var  s0 =>  ((compRenSubst_exp_var (_) (_) (_) (fun x y => eq_refl) xiexp tauexp thetaexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((compRenSubst_exp_lam (_) upRen_exp_exp ren_exp up_exp_exp (_) up_ren_subst_exp_exp compRenSubst_exp (_) (fun x y => eq_refl) xiexp tauexp thetaexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((compRenSubst_exp_bool (_) ren_exp (_) compRenSubst_exp (_) (fun x y => eq_refl) xiexp tauexp thetaexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((compRenSubst_exp_arith (_) ren_exp (_) compRenSubst_exp (_) (fun x y => eq_refl) xiexp tauexp thetaexp Eqexp) s0)
    end.

Definition up_subst_ren_exp_exp    (sigma : (nat) -> exp ) (zetaexp : (nat) -> nat) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) (ren_exp zetaexp) sigma) x = theta x) : forall x, ((funcomp) (ren_exp (upRen_exp_exp zetaexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_exp (shift) (upRen_exp_exp zetaexp) ((funcomp) (shift) zetaexp) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_exp zetaexp (shift) ((funcomp) (shift) zetaexp) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_exp (shift)) (Eq fin_n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstRen_exp    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (ren_exp zetaexp) sigmaexp) x = thetaexp x) (s : exp ) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s return ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp thetaexp s with
    | In_exp_var  s0 =>  ((compSubstRen_exp_var (_) (_) sigmaexp zetaexp thetaexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((compSubstRen_exp_lam (_) upRen_exp_exp (_) up_exp_exp subst_exp up_subst_ren_exp_exp compSubstRen_exp (_) (fun x y => eq_refl) sigmaexp zetaexp thetaexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((compSubstRen_exp_bool (_) (_) subst_exp compSubstRen_exp (_) (fun x y => eq_refl) sigmaexp zetaexp thetaexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((compSubstRen_exp_arith (_) (_) subst_exp compSubstRen_exp (_) (fun x y => eq_refl) sigmaexp zetaexp thetaexp Eqexp) s0)
    end.

Definition up_subst_subst_exp_exp    (sigma : (nat) -> exp ) (tauexp : (nat) -> exp ) (theta : (nat) -> exp ) (Eq : forall x, ((funcomp) (subst_exp tauexp) sigma) x = theta x) : forall x, ((funcomp) (subst_exp (up_exp_exp tauexp)) (up_exp_exp sigma)) x = (up_exp_exp theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_exp (shift) (up_exp_exp tauexp) ((funcomp) (up_exp_exp tauexp) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_exp tauexp (shift) ((funcomp) (ren_exp (shift)) tauexp) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_exp (shift)) (Eq fin_n)))
  | 0 => eq_refl
  end.

Fixpoint compSubstSubst_exp    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (thetaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (subst_exp tauexp) sigmaexp) x = thetaexp x) (s : exp ) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s :=
    match s return subst_exp tauexp (subst_exp sigmaexp s) = subst_exp thetaexp s with
    | In_exp_var  s0 =>  ((compSubstSubst_exp_var (_) (_) sigmaexp tauexp thetaexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((compSubstSubst_exp_lam (_) up_exp_exp (_) up_subst_subst_exp_exp compSubstSubst_exp (_) (fun x y => eq_refl) sigmaexp tauexp thetaexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((compSubstSubst_exp_bool (_) (_) compSubstSubst_exp (_) (fun x y => eq_refl) sigmaexp tauexp thetaexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((compSubstSubst_exp_arith (_) (_) compSubstSubst_exp (_) (fun x y => eq_refl) sigmaexp tauexp thetaexp Eqexp) s0)
    end.

Definition rinstInst_up_exp_exp   (xi : (nat) -> nat) (sigma : (nat) -> exp ) (Eq : forall x, ((funcomp) (var_exp ) xi) x = sigma x) : forall x, ((funcomp) (var_exp ) (upRen_exp_exp xi)) x = (up_exp_exp sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_exp (shift)) (Eq fin_n)
  | 0 => eq_refl
  end.

Fixpoint rinst_inst_exp   (xiexp : (nat) -> nat) (sigmaexp : (nat) -> exp ) (Eqexp : forall x, ((funcomp) (var_exp ) xiexp) x = sigmaexp x) (s : exp ) : ren_exp xiexp s = subst_exp sigmaexp s :=
    match s return ren_exp xiexp s = subst_exp sigmaexp s with
    | In_exp_var  s0 =>  ((rinst_inst_exp_var (_) (_) xiexp sigmaexp Eqexp) s0)
    | In_exp_lam  s0 =>  ((rinst_inst_exp_lam (_) var_exp upRen_exp_exp ren_exp up_exp_exp subst_exp rinstInst_up_exp_exp rinst_inst_exp (_) xiexp sigmaexp Eqexp) s0)
    | In_exp_bool  s0 =>  ((rinst_inst_exp_bool (_) var_exp ren_exp subst_exp rinst_inst_exp (_) xiexp sigmaexp Eqexp) s0)
    | In_exp_arith  s0 =>  ((rinst_inst_exp_arith (_) var_exp ren_exp subst_exp rinst_inst_exp (_) xiexp sigmaexp Eqexp) s0)
    end.

Lemma rinstInst_exp   (xiexp : (nat) -> nat) : ren_exp xiexp = subst_exp ((funcomp) (var_exp ) xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_exp xiexp (_) (fun n => eq_refl) x)). Qed.

Lemma instId_exp  : subst_exp (var_exp ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp (var_exp ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_exp  : @ren_exp   (id) = id .
Proof. exact ((eq_trans) (rinstInst_exp ((id) (_))) instId_exp). Qed.

Lemma compComp_exp    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) (s : exp ) : subst_exp tauexp (subst_exp sigmaexp s) = subst_exp ((funcomp) (subst_exp tauexp) sigmaexp) s .
Proof. exact (compSubstSubst_exp sigmaexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp    (sigmaexp : (nat) -> exp ) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (subst_exp sigmaexp) = subst_exp ((funcomp) (subst_exp tauexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp sigmaexp tauexp n)). Qed.

Lemma compRen_exp    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) (s : exp ) : ren_exp zetaexp (subst_exp sigmaexp s) = subst_exp ((funcomp) (ren_exp zetaexp) sigmaexp) s .
Proof. exact (compSubstRen_exp sigmaexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_exp    (sigmaexp : (nat) -> exp ) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (subst_exp sigmaexp) = subst_exp ((funcomp) (ren_exp zetaexp) sigmaexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_exp sigmaexp zetaexp n)). Qed.

Lemma renComp_exp    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) (s : exp ) : subst_exp tauexp (ren_exp xiexp s) = subst_exp ((funcomp) tauexp xiexp) s .
Proof. exact (compRenSubst_exp xiexp tauexp (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_exp    (xiexp : (nat) -> nat) (tauexp : (nat) -> exp ) : (funcomp) (subst_exp tauexp) (ren_exp xiexp) = subst_exp ((funcomp) tauexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_exp xiexp tauexp n)). Qed.

Lemma renRen_exp    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) (s : exp ) : ren_exp zetaexp (ren_exp xiexp s) = ren_exp ((funcomp) zetaexp xiexp) s .
Proof. exact (compRenRen_exp xiexp zetaexp (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_exp    (xiexp : (nat) -> nat) (zetaexp : (nat) -> nat) : (funcomp) (ren_exp zetaexp) (ren_exp xiexp) = ren_exp ((funcomp) zetaexp xiexp) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_exp xiexp zetaexp n)). Qed.

End exp.























Global Instance Subst_exp   : Subst1 ((nat) -> exp ) (exp ) (exp ) := @subst_exp   .

Global Instance Ren_exp   : Ren1 ((nat) -> nat) (exp ) (exp ) := @ren_exp   .

Global Instance VarInstance_exp_var  : Var (nat) (exp_var ) := @var_exp_var  .

Notation "x '__exp_var'" := (var_exp_var x) (at level 5, format "x __exp_var") : subst_scope.

Notation "x '__exp_var'" := (@ids (_) (_) VarInstance_exp_var x) (at level 5, only printing, format "x __exp_var") : subst_scope.

Notation "'var'" := (var_exp_var) (only printing, at level 1) : subst_scope.

Class Up_exp X Y := up_exp : ( X ) -> Y.

Notation "↑__exp" := (up_exp) (only printing) : subst_scope.

Notation "↑__exp" := (up_exp_exp) (only printing) : subst_scope.

Global Instance Up_exp_exp   : Up_exp (_) (_) := @up_exp_exp   .

Notation "s [ sigmaexp ]" := (subst_exp_lam sigmaexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaexp ]" := (subst_exp_lam sigmaexp) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiexp ⟩" := (ren_exp_lam xiexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiexp ⟩" := (ren_exp_lam xiexp) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaexp ]" := (subst_exp_arith sigmaexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaexp ]" := (subst_exp_arith sigmaexp) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiexp ⟩" := (ren_exp_arith xiexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiexp ⟩" := (ren_exp_arith xiexp) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaexp ]" := (subst_exp_bool sigmaexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaexp ]" := (subst_exp_bool sigmaexp) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiexp ⟩" := (ren_exp_bool xiexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiexp ⟩" := (ren_exp_bool xiexp) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaexp ]" := (subst_exp_var sigmaexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaexp ]" := (subst_exp_var sigmaexp) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiexp ⟩" := (ren_exp_var xiexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiexp ⟩" := (ren_exp_var xiexp) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaexp ]" := (subst_exp sigmaexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaexp ]" := (subst_exp sigmaexp) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiexp ⟩" := (ren_exp xiexp s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiexp ⟩" := (ren_exp xiexp) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_exp,  Ren_exp,  VarInstance_exp_var.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_exp,  Ren_exp,  VarInstance_exp_var in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_exp_lam| progress rewrite ?compComp_exp_lam| progress rewrite ?compComp'_exp_lam| progress rewrite ?instId_exp_arith| progress rewrite ?compComp_exp_arith| progress rewrite ?compComp'_exp_arith| progress rewrite ?instId_exp_bool| progress rewrite ?compComp_exp_bool| progress rewrite ?compComp'_exp_bool| progress rewrite ?instId_exp_var| progress rewrite ?compComp_exp_var| progress rewrite ?compComp'_exp_var| progress rewrite ?instId_exp| progress rewrite ?compComp_exp| progress rewrite ?compComp'_exp| progress rewrite ?rinstId_exp_lam| progress rewrite ?compRen_exp_lam| progress rewrite ?compRen'_exp_lam| progress rewrite ?renComp_exp_lam| progress rewrite ?renComp'_exp_lam| progress rewrite ?renRen_exp_lam| progress rewrite ?renRen'_exp_lam| progress rewrite ?rinstId_exp_arith| progress rewrite ?compRen_exp_arith| progress rewrite ?compRen'_exp_arith| progress rewrite ?renComp_exp_arith| progress rewrite ?renComp'_exp_arith| progress rewrite ?renRen_exp_arith| progress rewrite ?renRen'_exp_arith| progress rewrite ?rinstId_exp_bool| progress rewrite ?compRen_exp_bool| progress rewrite ?compRen'_exp_bool| progress rewrite ?renComp_exp_bool| progress rewrite ?renComp'_exp_bool| progress rewrite ?renRen_exp_bool| progress rewrite ?renRen'_exp_bool| progress rewrite ?rinstId_exp_var| progress rewrite ?compRen_exp_var| progress rewrite ?compRen'_exp_var| progress rewrite ?renComp_exp_var| progress rewrite ?renComp'_exp_var| progress rewrite ?renRen_exp_var| progress rewrite ?renRen'_exp_var| progress rewrite ?rinstId_exp| progress rewrite ?compRen_exp| progress rewrite ?compRen'_exp| progress rewrite ?renComp_exp| progress rewrite ?renComp'_exp| progress rewrite ?renRen_exp| progress rewrite ?renRen'_exp| progress rewrite ?varL_exp_var| progress rewrite ?varLRen_exp_var| progress (unfold up_ren, upRen_exp_exp, up_exp_exp)| progress (cbn [subst_exp_lam subst_exp_arith subst_exp_bool subst_exp_var subst_exp ren_exp_lam ren_exp_arith ren_exp_bool ren_exp_var ren_exp])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_exp_lam in *| progress rewrite ?compComp_exp_lam in *| progress rewrite ?compComp'_exp_lam in *| progress rewrite ?instId_exp_arith in *| progress rewrite ?compComp_exp_arith in *| progress rewrite ?compComp'_exp_arith in *| progress rewrite ?instId_exp_bool in *| progress rewrite ?compComp_exp_bool in *| progress rewrite ?compComp'_exp_bool in *| progress rewrite ?instId_exp_var in *| progress rewrite ?compComp_exp_var in *| progress rewrite ?compComp'_exp_var in *| progress rewrite ?instId_exp in *| progress rewrite ?compComp_exp in *| progress rewrite ?compComp'_exp in *| progress rewrite ?rinstId_exp_lam in *| progress rewrite ?compRen_exp_lam in *| progress rewrite ?compRen'_exp_lam in *| progress rewrite ?renComp_exp_lam in *| progress rewrite ?renComp'_exp_lam in *| progress rewrite ?renRen_exp_lam in *| progress rewrite ?renRen'_exp_lam in *| progress rewrite ?rinstId_exp_arith in *| progress rewrite ?compRen_exp_arith in *| progress rewrite ?compRen'_exp_arith in *| progress rewrite ?renComp_exp_arith in *| progress rewrite ?renComp'_exp_arith in *| progress rewrite ?renRen_exp_arith in *| progress rewrite ?renRen'_exp_arith in *| progress rewrite ?rinstId_exp_bool in *| progress rewrite ?compRen_exp_bool in *| progress rewrite ?compRen'_exp_bool in *| progress rewrite ?renComp_exp_bool in *| progress rewrite ?renComp'_exp_bool in *| progress rewrite ?renRen_exp_bool in *| progress rewrite ?renRen'_exp_bool in *| progress rewrite ?rinstId_exp_var in *| progress rewrite ?compRen_exp_var in *| progress rewrite ?compRen'_exp_var in *| progress rewrite ?renComp_exp_var in *| progress rewrite ?renComp'_exp_var in *| progress rewrite ?renRen_exp_var in *| progress rewrite ?renRen'_exp_var in *| progress rewrite ?rinstId_exp in *| progress rewrite ?compRen_exp in *| progress rewrite ?compRen'_exp in *| progress rewrite ?renComp_exp in *| progress rewrite ?renComp'_exp in *| progress rewrite ?renRen_exp in *| progress rewrite ?renRen'_exp in *| progress rewrite ?varL_exp_var in *| progress rewrite ?varLRen_exp_var in *| progress (unfold up_ren, upRen_exp_exp, up_exp_exp in *)| progress (cbn [subst_exp_lam subst_exp_arith subst_exp_bool subst_exp_var subst_exp ren_exp_lam ren_exp_arith ren_exp_bool ren_exp_var ren_exp] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_exp_lam); try repeat (erewrite rinstInst_exp_arith); try repeat (erewrite rinstInst_exp_bool); try repeat (erewrite rinstInst_exp_var); try repeat (erewrite rinstInst_exp).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_exp_lam); try repeat (erewrite <- rinstInst_exp_arith); try repeat (erewrite <- rinstInst_exp_bool); try repeat (erewrite <- rinstInst_exp_var); try repeat (erewrite <- rinstInst_exp).
