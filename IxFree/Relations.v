(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import IxFree.UnaryFixpoint.

(** * Relations *)

(** ** Relation Signatures *)

(** Relations are just functions with [WProp _] as codomain. We have a separate
  datatype for representation of relations signatures, with the two
  constructors: [WRel W], which should be used instead od [WProp W], and
  [A ⇒ᵢ Σ], which represents a function from type [A] to another signature [Σ]
  ([WRel W] or another arrow). *)

Inductive WRel_sig' (WPr : Type) : Type :=
| WRel_base  : WRel_sig' WPr
| WRel_arrow : Type → WRel_sig' WPr → WRel_sig' WPr
.

Notation WRel_sig W := (WRel_sig' (WProp W)).
Notation WRel W := (WRel_base (WProp W)).

Arguments WRel_arrow {WPr} _ _.
Notation "T ⇒ᵢ Σ" := (WRel_arrow T Σ) (at level 99, Σ at level 200).

(** Relations signatures can be implicitly coerced to regular Coq types. *)

Fixpoint WRel_type {W} (Σ : WRel_sig' W) : Type :=
  match Σ with
  | WRel_base _ => W
  | T ⇒ᵢ Σ      => T → WRel_type Σ
  end.

Coercion WRel_type : WRel_sig >-> Sortclass.

(** ** Relation Equivalence and Subrelations *)

Section WRelRelations.
  Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.

  Fixpoint WRel_equiv (Σ : WRel_sig W) : Σ → Σ → WProp W :=
    match Σ return Σ → Σ → WProp W with
    | WRel_base _ => λ R₁ R₂, R₁ ↔ᵢ R₂
    | T ⇒ᵢ Σ      => λ R₁ R₂, ∀ᵢ x : T, WRel_equiv Σ (R₁ x) (R₂ x)
    end.

  Fixpoint WRel_subrel (Σ : WRel_sig W) : Σ → Σ → WProp W :=
    match Σ return Σ → Σ → WProp W with
    | WRel_base _ => λ R₁ R₂, R₁ →ᵢ R₂
    | T ⇒ᵢ Σ      => λ R₁ R₂, ∀ᵢ x : T, WRel_subrel Σ (R₁ x) (R₂ x)
    end.
End WRelRelations.

Notation "R ≈ᵢ S" := (WRel_equiv _ R S) (at level 70).
Notation "R ≾ᵢ S" := (WRel_subrel _ R S) (at level 70).

(** ** Fixpoints *)

(** One of the main features of step-indexed logic is a possibility of
  defining recursive predicates (relations) as fixpoints of contractive
  functions. *)

Section WRelFix.
  Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
  Context {IWC : IWorldCore W} {WC : IWorld W}.

  (** *** Contractive Functions *)

  (** A function is contractive if it maps almost equivalent relations
  (this "almost" is expressed by later) to more equivalent ones. *)

  Definition I_contractive (Σ : WRel_sig W) (f : Σ → Σ) : WProp W :=
    ∀ᵢ R₁ R₂, ▷(R₁ ≈ᵢ R₂) →ᵢ f R₁ ≈ᵢ f R₂.

  Definition contractive (Σ : WRel_sig W) (f : Σ → Σ) : Prop :=
    ∀ w, w ⊨ I_contractive Σ f.

  (** *** Curry and Uncurry *)

  (** Here is some technical part, that transform multi-parameter relations
    to single-parameter and the other way around. This is used to express
    general fixpoint as a fixpoint of a function that transforms
    single-parameter relations. *)

  (* begin details *)

  Local Fixpoint WRel_prod (Σ : WRel_sig W) : Type :=
    match Σ with
    | WRel_base _ => unit
    | T ⇒ᵢ Σ => (T * WRel_prod Σ)%type
    end.

  Local Fixpoint WRel_curry (Σ : WRel_sig W) : WRel1 (WRel_prod Σ) → Σ :=
    match Σ return WRel1 (WRel_prod Σ) → Σ with
    | WRel_base _ => λ R, R tt
    | T ⇒ᵢ Σ      => λ R x, WRel_curry Σ (λ y, R (x, y))
    end.

  Local Fixpoint WRel_uncurry (Σ : WRel_sig W) : Σ → WRel1 (WRel_prod Σ) :=
    match Σ return Σ → WRel1 (WRel_prod Σ) with
    | WRel_base _ => λ R _, R
    | T ⇒ᵢ Σ      => λ R p, WRel_uncurry Σ (R (fst p)) (snd p)
    end.

  Local Lemma WRel_equiv_move_curry (Σ : WRel_sig W) (w : W) :
    w ⊨ ∀ᵢ R₁ R₂,
      WRel1_equiv R₁ (WRel_uncurry Σ R₂) →ᵢ WRel_curry Σ R₁ ≈ᵢ R₂.
  Proof.
    revert w; induction Σ; simpl; intro w; iintros R₁ R₂ HR.
    + iapply HR.
    + iintro x; iapply IHΣ.
      iintro y; ispecialize HR (x, y); assumption.
  Qed.

  Local Lemma WRel_curry_equiv (Σ : WRel_sig W) (w : W) :
    w ⊨ ∀ᵢ R₁ R₂,
      WRel1_equiv R₁ R₂ →ᵢ WRel_curry Σ R₁ ≈ᵢ WRel_curry Σ R₂.
  Proof.
    revert w; induction Σ; simpl; intro w; iintros R₁ R₂ HR.
    + iapply HR.
    + iintro x; iapply IHΣ.
      iintro y; iapply HR.
  Qed.

  Local Lemma WRel_uncurry_equiv (Σ : WRel_sig W) (w : W) :
    w ⊨ ∀ᵢ R₁ R₂,
      R₁ ≈ᵢ R₂ →ᵢ WRel1_equiv (WRel_uncurry Σ R₁) (WRel_uncurry Σ R₂).
  Proof.
    revert w; induction Σ; simpl; intro w; iintros R₁ R₂ HR x.
    + assumption.
    + iapply IHΣ; iapply HR.
  Qed.

  (* end details *)

  (** *** Fixpoint *)

  Definition I_fix (Σ : WRel_sig W) (f : Σ → Σ) : Σ :=
    WRel_curry Σ (I_fix1 (λ R, WRel_uncurry Σ (f (WRel_curry Σ R)))).

  Lemma I_fix_is_fixpoint (Σ : WRel_sig W) (f : Σ → Σ) {w : W} :
    w ⊨ I_contractive Σ f →ᵢ I_fix Σ f ≈ᵢ f (I_fix Σ f).
  Proof.
    iintro f_contr.
    iapply WRel_equiv_move_curry.
    iapply I_fix1_is_fixpoint.
    iintros R₁ R₂ HR.
    iapply WRel_uncurry_equiv.
    iapply f_contr.
    later_shift.
    iapply WRel_curry_equiv; assumption.
  Qed.

  #[global] Opaque I_fix.
End WRelFix.
