(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import IxFree.LaterRules.
Require Import PeanoNat.

(** * Large Numbers *)
(** This module defines "large number" predicate. Intuitively, the number is
  large, if it cannot cannot be distinguished from the infinity inside the
  IxFree logic (assuming that decreasing the number requires moving to the
  later world). Large numbers are useful in defining complex recursive
  structures: they can be defined recursively on natural numbers, and for
  large numbers we get limit-like construction for free. For example, see
  [IxFree.UnaryFixpoint]. *)

Section LargeNum.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
Context {IWC : IWorldCore W} {WC : IWorld W}.

(** The number is large, if it is a successor of almost large number. *)

Fixpoint I_large (n : nat) : WProp W :=
  match n with
  | 0   => (False)ᵢ
  | S n => ▷ I_large n
  end.

(** Zero is not large. For successors, we can roll and unroll the
  definition. *)

Lemma I_large_Z w : ¬(w ⊨ I_large 0).
Proof.
  intro H; idestruct H; auto.
Qed.

Lemma I_large_S_intro n w : w ⊨ ▷ I_large n → w ⊨ I_large (S n).
Proof.
  auto.
Qed.

Lemma I_large_S_elim n w : w ⊨ I_large (S n) → w ⊨ ▷ I_large n.
Proof.
  auto.
Qed.

Lemma I_large_is_S n w :
  w ⊨ I_large n →ᵢ ∃ᵢ m (EQ : n = S m), ▷ I_large m.
Proof.
  iintro Hn; destruct n as [ | n ].
  + exfalso; eapply I_large_Z; eassumption.
  + iexists n; iexists; [ reflexivity | ]; auto.
Qed.

Lemma I_large_le n m w :
  n ≤ m → w ⊨ I_large n →ᵢ I_large m.
Proof.
  intro LE; revert w; induction LE; intro w; iintro Hn.
  + assumption.
  + apply I_large_S_intro; iintro.
    iapply IHLE; assumption.
Qed.

(** Proving that large numbers exist is a bit tricky. We have to directly refer
  to a model. *)

Local Lemma I_large_world_index n :
  ∀ w, n > world_index w → w ⊨ I_large n.
Proof.
  induction n; simpl.
  + intros ? H; apply Nat.nlt_0_r in H; destruct H.
  + intros w Hn; apply I_later_intro.
    intros w' Hw'; apply IHn.
    eapply Nat.lt_le_trans; [ apply Hw' | ].
    apply le_S_n; assumption.
Qed.

Lemma I_large_exists (w : W) : w ⊨ ∃ᵢ n, I_large n.
Proof.
  iexists; apply I_large_world_index; constructor.
Qed.

End LargeNum.
