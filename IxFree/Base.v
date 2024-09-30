(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import RelationClasses.
Require Import Decidable PeanoNat.

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
    {ICW : IWorldCore W} : Prop :=
  { world_index_ord : ∀ w₁ w₂ : W, w₁ ⊑ w₂ → world_index w₁ ≥ world_index w₂ }.

(** We define a strict version of world order, which requires step-index to
  be strictly lower. *)

Definition world_strict_preord {W : Type}
  {PCW : PreOrderCore W} {ICW : IWorldCore W} (w₁ w₂ : W) : Prop :=
  w₁ ⊑ w₂ ∧ world_index w₂ < world_index w₁.

Notation "w₁ ⊏↓ w₂" := (world_strict_preord w₁ w₂) (at level 70).

#[export]
Instance Transitive_world_strict_preord (W : Type)
  {PCW : PreOrderCore W} {PW : PreOrder W} {ICW : IWorldCore W} :
  Transitive (world_strict_preord (W:=W)).
Proof.
  intros w₁ w₂ w₃ H1 H2; split; etransitivity; apply H1 || apply H2.
Qed.

Lemma world_strict_preord_trans_l {W : Type}
  {PCW : PreOrderCore W} {PW : PreOrder W} {ICW : IWorldCore W} {IW : IWorld W}
  (w₁ w₂ w₃ : W) :
  w₁ ⊑ w₂ → w₂ ⊏↓ w₃ → w₁ ⊏↓ w₃.
Proof.
  intros H1 H2; split; [ etransitivity; apply H1 || apply H2 | ].
  eapply Nat.lt_le_trans; [ apply H2 | ].
  apply world_index_ord; assumption.
Qed.

Lemma world_strict_preord_trans_r {W : Type}
  {PCW : PreOrderCore W} {PW : PreOrder W} {ICW : IWorldCore W} {IW : IWorld W}
  (w₁ w₂ w₃ : W) :
  w₁ ⊏↓ w₂ → w₂ ⊑ w₃ → w₁ ⊏↓ w₃.
Proof.
  intros H1 H2; split; [ etransitivity; apply H1 || apply H2 | ].
  eapply Nat.le_lt_trans; [ | apply H1 ].
  apply world_index_ord; assumption.
Qed.

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

(** ** Additional Structure of Worlds *)

(** Some desired properties require additional structure of possible worlds.
  See [LaterRules] module for some of such properties. *)

(** *** Lifting Worlds to Higher Index *)

Class IWorldLiftCore (W : Type) : Type :=
  { world_lift : W → W }.

Class IWorldLift (W : Type)
    {PCW : PreOrderCore W} {ICW : IWorldCore W}
    {LCW : IWorldLiftCore W} : Prop :=
  { world_lift_ord     : ∀ w, world_lift w ⊏↓ w
  ; world_lift_limit_l : ∀ w w', world_lift w ⊏↓ w' → w ⊑ w'
  ; world_lift_limit_u : ∀ w w', w ⊏↓ w' → w ⊑ world_lift w'
  }.

(** *** Unlifting World to Lower Index *)

Class IWorldUnliftCore (W : Type) : Type :=
  { world_unlift : W → W }.

Class IWorldUnlift (W : Type)
    {PCW : PreOrderCore W} {ICW : IWorldCore W}
    {UCW : IWorldUnliftCore W} : Prop :=
  { world_unlift_ord   : ∀ w n, S n = world_index w → w ⊏↓ world_unlift w
  ; world_unlift_limit : ∀ w w', w ⊏↓ w' → world_unlift w ⊑ w'
  }.

(** *** Worlds With Decidable Existance of a Lower Index *)

Class IWorldBottomDec (W : Type)
    {PCW : PreOrderCore W} {ICW : IWorldCore W} : Prop :=
  { world_bottom_dec : ∀ w : W, decidable (∃ w', w ⊏↓ w') }.

(** Worlds with unlifting has decidable existance of a lower index. *)
#[export]
Instance IWorldBottomDec_of_IWorldUnlift (W : Type)
  {PCW : PreOrderCore W}
  {ICW : IWorldCore W}
  {UCW : IWorldUnliftCore W} {UW : IWorldUnlift W} : IWorldBottomDec W.
Proof.
  split; intro w.
  remember (world_index w) as n; destruct n as [ | n ].
  + right; intros [ w' [ _ Hidx ] ].
    rewrite <- Heqn in Hidx; apply Nat.nlt_0_r in Hidx; assumption.
  + left; exists (world_unlift w).
    eapply world_unlift_ord; eassumption.
Qed.
