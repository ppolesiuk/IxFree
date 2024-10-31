(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Relations.
Require Import PeanoNat.

(** * Natural Step-Indexed Kripke Model *)
(** This module provides the definition of the standard step-indexed Kripke
  Model, where possible worlds are just natural numbers. These numbers are also
  step-indices of worlds. *)

Record NatWorld : Set := { nw_index : nat }.

#[export]
Instance PreOrderCore_NatWorld : PreOrderCore NatWorld :=
  { preord n m := nw_index n ≥ nw_index m }.

#[export]
Instance PreOrder_NatWorld : PreOrder NatWorld.
Proof.
  split; simpl; intros.
  + apply Nat.le_refl.
  + intros; eapply Nat.le_trans; eassumption.
Qed.

#[export]
Instance IWorldCore_NatWorld : IWorldCore NatWorld :=
  { world_index := nw_index }.

#[export]
Instance IWorld_NatWorld : IWorld NatWorld.
Proof. split; simpl; auto. Qed.

Notation IProp    := (WProp NatWorld).
Notation IRel     := (WRel NatWorld).
Notation IRel_sig := (WRel_sig NatWorld).

#[export]
Instance IWorldLiftCore_NatWorld : IWorldLiftCore NatWorld :=
  { world_lift w := {| nw_index := S (nw_index w) |} }.

#[export]
Instance IWorldUnliftCore_NatWorld : IWorldUnliftCore NatWorld :=
  { world_unlift w := {| nw_index := pred (nw_index w) |} }.

#[export]
Instance IWorldLift_NatWorld : IWorldLift NatWorld.
Proof.
  split.
  + intros [ n ]; repeat constructor.
  + intros [ n ] [ m ] [ _ Hidx ]; apply PeanoNat.lt_n_Sm_le; assumption.
  + intros [ n ] [ m ] [ _ Hidx ]; exact Hidx.
Qed.

#[export]
Instance IWorldUnlift_NatWorld : IWorldUnlift NatWorld.
Proof.
  split.
  + intros [ n ] m H; split; simpl; [ apply Nat.le_pred_l | ].
    apply Nat.lt_pred_l; intro Heq; subst; inversion H.
  + intros [ n ] [ m ] [ _ Hidx ]; apply Nat.lt_le_pred; assumption.
Qed.
