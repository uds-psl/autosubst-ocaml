(** * Autosubst Header for Scoped Syntax
    Our development utilises well-scoped de Bruijn syntax. This means that the de Bruijn indices are taken from finite types. As a consequence, any kind of substitution or environment used in conjunction with well-scoped syntax takes the form of a mapping from some finite type _I^n_. In particular, _renamings_ are mappings _I^n -> I^m_. Here we develop the theory of how these parts interact.

Version: December 11, 2019.
*)
Require Import core.
Require Import Setoid Morphisms Relation_Definitions.

Set Implicit Arguments.
Unset Strict Implicit.

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition apc {X Y} {f g : X -> Y} {x y : X} (p : f = g) (q : x = y) : f x = g y :=
  match q with eq_refl => match p with eq_refl => eq_refl end end.

(** ** Primitives of the Sigma Calculus
    We implement the finite type with _n_ elements, _I^n_, as the _n_-fold iteration of the Option Type. _I^0_ is implemented as the empty type.
*)

Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (fin m)
  end.

(** Renamings and Injective Renamings
     _Renamings_ are mappings between finite types.
*)
Definition ren (m n : nat) : Type := fin m -> fin n.

Definition id {X} := @Datatypes.id X.

Definition idren {k: nat} : ren k k := @Datatypes.id (fin k).

(** We give a special name, to the newest element in a non-empty finite type, as it usually corresponds to a freshly bound variable. *)
Definition var_zero {n : nat} : fin (S n) := None.

Definition null {T} (i : fin 0) : T := match i with end.

Definition shift {n : nat} : ren n (S n) :=
  Some.

(** Extension of Finite Mappings
    Assume we are given a mapping _f_ from _I^n_ to some type _X_, then we can _extend_ this mapping with a new value from _x : X_ to a mapping from _I^n+1_ to _X_. We denote this operation by _x . f_ and define it as follows:
*)
Definition scons {X : Type} {n : nat} (x : X) (f : fin n -> X) (m : fin (S n)) : X :=
  match m with
  | None => x
  | Some i => f i
  end.

#[ export ]
Hint Opaque scons : rewrite.

(** ** Type Class Instances for Notation *)

(** *** Type classes for renamings. *)

Class Ren1 (X1  : Type) (Y Z : Type) :=
  ren1 : X1 -> Y -> Z.

Class Ren2 (X1 X2 : Type) (Y Z : Type) :=
  ren2 : X1 -> X2 -> Y -> Z.

Class Ren3 (X1 X2 X3 : Type) (Y Z : Type) :=
  ren3 : X1 -> X2 -> X3 -> Y -> Z.

Class Ren4 (X1 X2 X3 X4 : Type) (Y Z : Type) :=
  ren4 : X1 -> X2 -> X3 -> X4 -> Y -> Z.

Class Ren5 (X1 X2 X3 X4 X5 : Type) (Y Z : Type) :=
  ren5 : X1 -> X2 -> X3 -> X4 -> X5 -> Y -> Z.

Module RenNotations.
  Notation "s ⟨ xi1 ⟩" := (ren1  xi1 s) (at level 7, left associativity, format "s  ⟨ xi1 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ; xi3 ⟩" := (ren3 xi1 xi2 xi3 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩" := (ren4  xi1 xi2 xi3 xi4 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩") : subst_scope.

  Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩" := (ren5  xi1 xi2 xi3 xi4 xi5 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩") : subst_scope.

  Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : fscope.

  Notation "⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2) (at level 1, left associativity, format "⟨ xi1 ; xi2 ⟩") : fscope.
End RenNotations.

(** *** Type Classes for Substiution *)

Class Subst1 (X1 : Type) (Y Z: Type) :=
  subst1 : X1 -> Y -> Z.

Class Subst2 (X1 X2 : Type) (Y Z: Type) :=
  subst2 : X1 -> X2 -> Y  -> Z.

Class Subst3 (X1 X2 X3 : Type) (Y Z: Type) :=
  subst3 : X1 -> X2 -> X3 ->  Y  -> Z.

Class Subst4 (X1 X2 X3 X4: Type) (Y Z: Type) :=
  subst4 : X1 -> X2 -> X3 -> X4 -> Y  -> Z.

Class Subst5 (X1 X2 X3 X4 X5 : Type) (Y Z: Type) :=
  subst5 : X1 -> X2 -> X3 -> X4 -> X5  -> Y  -> Z.

Module SubstNotations.
  Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : subst_scope.

  Notation "s [ sigma ; tau ]" := (subst2 sigma tau s) (at level 7, left associativity, format "s '/' [ sigma ; '/'  tau ]") : subst_scope.
End SubstNotations.

(** ** Type Class for Variables *)
Class Var X Y :=
  ids : X -> Y.


(** ** Proofs for substitution primitives *)

(** Forward Function Composition
    Substitutions represented as functions are ubiquitious in this development and we often have to compose them, without talking about their pointwise behaviour.
    That is, we are interested in the forward compostion of functions, _f o g_, for which we introduce a convenient notation, "f >> g". The direction of the arrow serves as a reminder of the _forward_ nature of this composition, that is first apply _f_, then _g_. *)

Arguments funcomp {X Y Z} (g)%fscope (f)%fscope.

Module CombineNotations.
  Notation "f >> g" := (funcomp g f) (at level 50) : fscope.

  Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.

  #[ global ]
  Open Scope fscope.
  #[ global ]
  Open Scope subst_scope.
End CombineNotations.

Import CombineNotations.


(** Generic lifting operation for renamings *)
Definition up_ren {m n} (xi : ren m n) : ren (S m) (S n) :=
  var_zero .: xi >> shift.

(** Generic proof that lifting of renamings composes. *)
Lemma up_ren_ren k l m (xi: ren k l) (zeta : ren l m) (rho: ren k m) (E: forall x, (xi >> zeta) x = rho x) :
  forall x, (up_ren xi >> up_ren zeta) x = up_ren rho x.
Proof.
  intros [x|].
  - cbn. unfold funcomp. now rewrite <- E.
  - reflexivity.
Qed.

Arguments up_ren_ren {k l m} xi zeta rho E.

Lemma fin_eta {X} (f g : fin 0 -> X) :
  pointwise_relation _ eq f g.
Proof. intros []. Qed.

(** Eta laws *)
Lemma scons_eta' {T} {n : nat} (f : fin (S n) -> T) :
  pointwise_relation _ eq (f var_zero .: (funcomp f shift)) f.
Proof. intros x. destruct x; reflexivity. Qed.

Lemma scons_eta_id' {n : nat} :
  pointwise_relation (fin (S n)) eq (var_zero .: shift) id.
Proof. intros x. destruct x; reflexivity. Qed.

Lemma scons_comp' {T:Type} {U} {m} (s: T) (sigma: fin m -> T) (tau: T -> U) :
  pointwise_relation _ eq (funcomp tau (s .: sigma)) ((tau s) .: (funcomp tau sigma)).
Proof. intros x. destruct x; reflexivity. Qed.

(* Lemma scons_tail'_pointwise {X} {n} (s : X) (f : fin n -> X) : *)
(*   pointwise_relation _ eq (funcomp (scons s f) shift) f. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma scons_tail' {X} {n} (s : X) (f : fin n -> X) x : *)
(*   (scons s f (shift x)) = f x. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Morphism for Setoid Rewriting. The only morphism that can be defined statically. *)
#[export] Instance scons_morphism {X: Type} {n:nat} :
  Proper (eq ==> pointwise_relation _ eq ==> pointwise_relation _ eq) (@scons X n).
Proof.
  intros t t' -> sigma tau H.
  intros [x|].
  cbn. apply H.
  reflexivity.
Qed.

#[export] Instance scons_morphism2 {X: Type} {n: nat} :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq) (@scons X n).
Proof.
  intros ? t -> sigma tau H ? x ->.
  destruct x as [x|].
  cbn. apply H.
  reflexivity.
Qed.

(** ** Variadic Substitution Primitives *)

Fixpoint shift_p (p : nat) {n} : ren n (p + n) :=
  fun n => match p with
        | 0 => n
        | S p => Some (shift_p p n)
        end.

Fixpoint scons_p {X: Type} {m : nat} : forall {n} (f : fin m -> X) (g : fin n -> X), fin (m + n)  -> X.
Proof.
  destruct m.
  - intros n f g. exact g.
  - intros n f g. cbn. apply scons.
    + exact (f var_zero).
    + apply scons_p.
      * intros z. exact (f (Some z)).
      * exact g.
Defined.

#[export] Hint Opaque scons_p : rewrite.

#[export] Instance scons_p_morphism {X: Type} {m n:nat} :
  Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> pointwise_relation _ eq) (@scons_p X m n).
Proof.
  intros sigma sigma' Hsigma tau tau' Htau.
  intros x.
  induction m.
  - cbn. apply Htau.
  - cbn. change (fin (S m + n)) with (fin (S (m + n))) in x.
    destruct x as [x|].
    + cbn. apply IHm.
      intros ?. apply Hsigma.
    + cbn. apply Hsigma.
Qed.

#[export] Instance scons_p_morphism2 {X: Type} {m n:nat} :
  Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq ==> eq) (@scons_p X m n).
Proof.
  intros sigma sigma' Hsigma tau tau' Htau ? x ->.
  induction m.
  - cbn. apply Htau.
  - cbn. change (fin (S m + n)) with (fin (S (m + n))) in x.
    destruct x as [x|].
    + cbn. apply IHm.
      intros ?. apply Hsigma.
    + cbn. apply Hsigma.
Qed.

Definition zero_p {m : nat} {n} : fin m -> fin (m + n).
Proof.
  induction m.
  - intros [].
  - intros [x|].
    + exact (shift_p 1 (IHm x)).
    + exact var_zero.
Defined.

Lemma scons_p_head' {X} {m n} (f : fin m -> X) (g : fin n -> X) z:
  (scons_p  f g) (zero_p  z) = f z.
Proof.
 induction m.
  - inversion z.
  - destruct z.
    + simpl. simpl. now rewrite IHm.
    + reflexivity.
Qed.

Lemma scons_p_head_pointwise {X} {m n} (f : fin m -> X) (g : fin n -> X) :
  pointwise_relation _ eq (funcomp (scons_p f g) zero_p) f.
Proof.
  intros z.
  unfold funcomp.
  induction m.
  - inversion z.
  - destruct z.
    + simpl. now rewrite IHm.
    + reflexivity.
Qed.

Lemma scons_p_tail' X  m n (f : fin m -> X) (g : fin n -> X) z :
  scons_p  f g (shift_p m z) = g z.
Proof. induction m; cbn; eauto. Qed.

Lemma scons_p_tail_pointwise X  m n (f : fin m -> X) (g : fin n -> X) :
  pointwise_relation _ eq (funcomp (scons_p f g) (shift_p m)) g.
Proof. intros z. induction m; cbn; eauto. Qed.

Lemma destruct_fin {m n} (x : fin (m + n)):
  (exists x', x = zero_p  x') \/ exists x', x = shift_p m x'.
Proof.
  induction m; simpl in *.
  - right. eauto.
  - destruct x as [x|].
    + destruct (IHm x) as [[x' ->] |[x' ->]].
      * left. now exists (Some x').
      * right. eauto.
    + left. exists None. eauto.
Qed.

Lemma scons_p_comp' X Y m n (f : fin m -> X) (g : fin n -> X) (h : X -> Y) :
  pointwise_relation _ eq (funcomp h (scons_p f g)) (scons_p (f >> h) (g >> h)).
Proof.
  intros x.
  destruct (destruct_fin x) as [[x' ->]|[x' ->]].
  (* TODO better way to solve this? *)
  - revert x'.
    apply pointwise_forall.
    change (fun x => (scons_p f g >> h) (zero_p x)) with (zero_p >> scons_p f g >> h).
    now setoid_rewrite scons_p_head_pointwise.
  - revert x'.
    apply pointwise_forall.
    change (fun x => (scons_p f g >> h) (shift_p m x)) with (shift_p m >> scons_p f g >> h).
    change (fun x => scons_p (f >> h) (g >> h) (shift_p m x)) with (shift_p m >> scons_p (f >> h) (g >> h)).
    now rewrite !scons_p_tail_pointwise.
Qed.


Lemma scons_p_congr {X} {m n} (f f' : fin m -> X) (g g': fin n -> X) z:
  (forall x, f x = f' x) -> (forall x, g x = g' x) -> scons_p f g z = scons_p f' g' z.
Proof. intros H1 H2. induction m; eauto. cbn. destruct z; eauto. Qed.

(** Generic n-ary lifting operation. *)
Definition upRen_p p { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : fin (p + m) -> fin (p + n)  :=
   scons_p  (zero_p ) (xi >> shift_p _).

Arguments upRen_p p {m n} xi.

(** Generic proof for composition of n-ary lifting. *)
Lemma up_ren_ren_p p k l m (xi: ren k l) (zeta : ren l m) (rho: ren k m) (E: forall x, (xi >> zeta) x = rho x) :
  forall x, (upRen_p p xi >> upRen_p p zeta) x = upRen_p p rho x.
Proof.
  intros x. destruct (destruct_fin x) as [[? ->]|[? ->]].
  - unfold upRen_p. unfold funcomp. now repeat rewrite scons_p_head'.
  - unfold upRen_p. unfold funcomp. repeat rewrite scons_p_tail'.
    now rewrite <- E.
Qed.


Arguments zero_p m {n}.
Arguments scons_p  {X} m {n} f g.

Lemma scons_p_eta {X} {m n} {f : fin m -> X}
      {g : fin n -> X} (h: fin (m + n) -> X) {z: fin (m + n)}:
  (forall x, g x = h (shift_p m x)) -> (forall x, f x = h (zero_p m x)) -> scons_p m f g z = h z.
Proof.
  intros H1 H2. destruct (destruct_fin z) as [[? ->] |[? ->]].
  - rewrite scons_p_head'. eauto.
  - rewrite scons_p_tail'. eauto.
Qed.

Arguments scons_p_eta {X} {m n} {f g} h {z}.
Arguments scons_p_congr {X} {m n} {f f'} {g g'} {z}.

(** ** Notations for Scoped Syntax *)

Module ScopedNotations.
  Include RenNotations.
  Include SubstNotations.
  Include CombineNotations.

(* Notation "s , sigma" := (scons s sigma) (at level 60, format "s ,  sigma", right associativity) : subst_scope. *)

  Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

  Notation "↑" := (shift) : subst_scope.

  #[global]
  Open Scope fscope.
  #[global]
  Open Scope subst_scope.
End ScopedNotations.


(** ** Tactics for Scoped Syntax *)

Tactic Notation "auto_case" tactic(t) :=  (match goal with
                                           | [|- forall (i : fin 0), _] => intros []; t
                                           | [|- forall (i : fin (S (S (S (S _))))), _] => intros [[[[|]|]|]|]; t
                                           | [|- forall (i : fin (S (S (S _)))), _] => intros [[[|]|]|]; t
                                           | [|- forall (i : fin (S (S _))), _] => intros [[?|]|]; t
                                           | [|- forall (i : fin (S _)), _] =>  intros [?|]; t
                                           end).

#[export] Hint Rewrite @scons_p_head' @scons_p_tail' : FunctorInstances.

(** Generic fsimpl tactic: simplifies the above primitives in a goal. *)
Ltac fsimpl :=
  repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *)
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *)
         | [|- context [id ?s]] => change (id s) with s
         | [|- context[(?f >> ?g) >> ?h]] => change ((f >> g) >> h) with (f >> (g >> h)) (* AsimplComp *)
         (* | [|- zero_p >> scons_p ?f ?g] => rewrite scons_p_head *)
         | [|- context[(?s .: ?sigma) var_zero]] => change ((s.:sigma) var_zero) with s
         | [|- context[(?s .: ?sigma) (shift ?m)]] => change ((s.:sigma) (shift m)) with (sigma m)
           (* first [progress setoid_rewrite scons_tail' | progress setoid_rewrite scons_tail'_pointwise ] *)
         | [|- context[idren >> ?f]] => change (idren >> f) with f
         | [|- context[?f >> idren]] => change (f >> idren) with f
         | [|- context[?f >> (?x .: ?g)]] => change (f >> (x .: g)) with g (* f should evaluate to shift *)
         | [|- context[?x2 .: (funcomp ?f shift)]] => change (scons x2 (funcomp f shift)) with (scons (f var_zero) (funcomp f shift)); setoid_rewrite (@scons_eta' _ _ f); eta_reduce
         | [|- context[?f var_zero .: ?g]] => change (scons (f var_zero) g) with (scons (f var_zero) (funcomp f shift)); setoid_rewrite scons_eta'; eta_reduce
         | [|- _ =  ?h (?f ?s)] => change (h (f s)) with ((f >> h) s)
         | [|-  ?h (?f ?s) = _] => change (h (f s)) with ((f >> h) s)
         | [|- context[funcomp _ (scons _ _)]] => setoid_rewrite scons_comp'; eta_reduce
         | [|- context[funcomp _ (scons_p _ _ _)]] => setoid_rewrite scons_p_comp'; eta_reduce
         | [|- context[scons (@var_zero _) shift]] => setoid_rewrite scons_eta_id'; eta_reduce
         (* | _ => progress autorewrite with FunctorInstances *)
         | [|- context[funcomp (scons_p _ _ _) (zero_p _)]] =>
           first [progress setoid_rewrite scons_p_head_pointwise | progress setoid_rewrite scons_p_head' ]
         | [|- context[scons_p _ _ _ (zero_p _ _)]] => setoid_rewrite scons_p_head'
         | [|- context[funcomp (scons_p _ _ _) (shift_p _)]] =>
           first [progress setoid_rewrite scons_p_tail_pointwise | progress setoid_rewrite scons_p_tail' ]
         | [|- context[scons_p _ _ _ (shift_p _ _)]] => setoid_rewrite scons_p_tail'
         | _ => first [progress minimize | progress cbn [shift scons scons_p] ]
         end.
