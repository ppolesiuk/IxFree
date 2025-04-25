(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import IxFree.LaterRules.
Require Import IxFree.Relations.
Require Import IxFree.AutoContr.

Require IxFree.UnaryFixpoint.

(** * Large Numbers *)
(** This module defines "large number" predicate. Intuitively, the number is
  large, if it cannot cannot be distinguished from the infinity inside the
  IxFree logic (assuming that decreasing the number requires moving to the
  later world). Large numbers are useful in defining complex recursive
  structures: they can be defined recursively on natural numbers, and for
  large numbers we get limit-like construction for free. *)

Section LargeNum.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
Context {IWC : IWorldCore W} {WC : IWorld W}.

(** The number is large, if it is a successor of almost large number. *)

Local Definition I_large_F (I_large : nat ⇒ᵢ WRel W) : nat ⇒ᵢ WRel W :=
  λ n, match n with
       | 0   => (False)ᵢ
       | S n => ▷ I_large n
       end.

Local Definition I_large_fix := I_fix I_large_F.
Definition I_large := I_large_F I_large_fix.

Local Lemma I_large_F_contractive : contractive I_large_F.
Proof.
  intro w; iintros R₁ R₂ HR []; simpl; auto_contr.
Qed.

Local Lemma I_large_roll w : w ⊨ I_large ≾ᵢ I_large_fix.
Proof.
  apply I_fix_roll, I_large_F_contractive.
Qed.

Local Lemma I_large_unroll w : w ⊨ I_large_fix ≾ᵢ I_large.
Proof.
  apply I_fix_unroll, I_large_F_contractive.
Qed.

(** Zero is not large. For successors, we can roll and unroll the
  definition. *)

Lemma I_large_Z w : ¬(w ⊨ I_large 0).
Proof.
  intro H; idestruct H; auto.
Qed.

Lemma I_large_S_intro n w : w ⊨ ▷ I_large n → w ⊨ I_large (S n).
Proof.
  intro H; simpl; iintro; iapply I_large_roll; assumption.
Qed.

Lemma I_large_S_elim n w : w ⊨ I_large (S n) → w ⊨ ▷ I_large n.
Proof.
  intro H; simpl in H; iintro; iapply I_large_unroll; assumption.
Qed.

#[global] Opaque I_large.

Lemma I_large_is_S n w :
  w ⊨ I_large n →ᵢ ∃ᵢ m (EQ : n = S m), ▷ I_large m.
Proof.
  iintro Hn; destruct n as [ | n ].
  + exfalso; eapply I_large_Z; eassumption.
  + iexists n; iexists; [ reflexivity | ].
    iapply I_large_S_elim; assumption.
Qed.

Lemma I_large_le n m w :
  n ≤ m → w ⊨ I_large n →ᵢ I_large m.
Proof.
  intro LE; revert w; induction LE; intro w; iintro Hn.
  + assumption.
  + apply I_large_S_intro; iintro.
    iapply IHLE; assumption.
Qed.

(** Proving that large numbers exist is a bit tricky. Fortunately, we can
  show that the auxiliary notion of large numbers from [UnaryFixpoint]
  approximate large numbers from this module. *)

Local Lemma I_large_num_is_large w :
  w ⊨ ∀ᵢ n, UnaryFixpoint.I_large_num n →ᵢ I_large n.
Proof.
  loeb_induction; iintros n Hn.
  iapply UnaryFixpoint.large_num_is_S in Hn.
  idestruct Hn as m EQ Hm; subst.
  apply I_large_S_intro; later_shift; iapply IH; assumption.
Qed.

Lemma I_large_exists (w : W) : w ⊨ ∃ᵢ n, I_large n.
Proof.
  idestruct (UnaryFixpoint.large_num_exists (w := w)) as n Hn.
  iexists n; iapply I_large_num_is_large; assumption.
Qed.

End LargeNum.
