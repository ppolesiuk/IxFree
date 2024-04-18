(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import RelationClasses.

(** * Base Definitions *)

(** ** Preorders *)

(** Preorders are defined as a type-class. There should be at most one preorder
  relation for each type. *)
Class PreOrderCore (A : Type) : Type :=
  { preord : A → A → Prop }.

Module PreOrderNotations.
  Notation "x ⊑ y" := (preord x y) (at level 70).
End PreOrderNotations.
Import PreOrderNotations.

Class PreOrder (A : Type) {Ord : PreOrderCore A} : Prop :=
  { preord_refl  : ∀ x, x ⊑ x
  ; preord_trans : ∀ x y z, x ⊑ y → y ⊑ z → x ⊑ z
  }.

#[export]
Instance PreOrder_Reflexive (A : Type)
  {OrdCore : PreOrderCore A} {Ord : PreOrder A} :
  Reflexive (preord (A:=A)).
Proof. intro x; apply preord_refl. Qed.

#[export]
Instance PreOrder_Transitive (A : Type)
  {OrdCore : PreOrderCore A} {Ord : PreOrder A} :
  Transitive (preord (A:=A)).
Proof. intros x y z; apply preord_trans. Qed.

(** Prop is a preorder *)

#[export]
Instance PreOrderCore_Prop : PreOrderCore Prop :=
  { preord P Q := P → Q }.

#[export]
Instance PreOrder_Prop : PreOrder Prop.
Proof. split; simpl; auto. Qed.

(** ** Monotone Functions *)

Definition monotone {A B : Type}
    {PCA : PreOrderCore A} {PCB : PreOrderCore B}
    (f : A → B) : Prop :=
  ∀ x y, x ⊑ y → f x ⊑ f y.

Record monotone_arrow (A B : Type)
    {PCA : PreOrderCore A} {PCB : PreOrderCore B} : Type :=
  { ma_apply    : A → B
  ; ma_monotone : monotone ma_apply
  }.

Coercion ma_apply : monotone_arrow >-> Funclass.

Arguments ma_apply    {A B PCA PCB}.
Arguments ma_monotone {A B PCA PCB}.

Notation "A '-mon→' B" := (monotone_arrow A B) (at level 99).

(** ** Step-Indexed Kripke Worlds *)
(** An universe of Step-indexed Kripke worlds is a preorder [W] with
  an additional function [iw_index : W → nat] which gets a step-index of a
  world. *)

Class IWorldCore (W : Type) {PCW : PreOrderCore W} : Type :=
  { world_index : W → nat }.

(** Moreover, we require that future worlds cannot have greater step-index. *)

Class IWorld (W : Type)
    {PCW : PreOrderCore W}
    {PW  : PreOrder W}
    {IWC : IWorldCore W} : Prop :=
  { world_index_ord : ∀ w₁ w₂ : W, w₁ ⊑ w₂ → world_index w₁ ≥ world_index w₂ }.

(** ** World-Indexed Propositions *)

Definition WProp (W : Type) {PCW : PreOrderCore W} := W -mon→ Prop.

Section I_valid.
  Context {W : Type} {PCW : PreOrderCore W}.

  Inductive I_valid_at (w : W) (P : WProp W) : Prop :=
  | I_valid_at_intro : P w → I_valid_at w P
  .

  Lemma I_valid_monotone {w₁ w₂ : W} (P : WProp W) :
    w₁ ⊑ w₂ → I_valid_at w₁ P → I_valid_at w₂ P.
  Proof.
    intros Hw [ H ]; constructor.
    eapply (ma_monotone P); eassumption.
  Qed.
End I_valid.

Notation "w ⊨ P" := (I_valid_at w P) (at level 98, no associativity).