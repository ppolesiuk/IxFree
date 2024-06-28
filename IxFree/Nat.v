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
