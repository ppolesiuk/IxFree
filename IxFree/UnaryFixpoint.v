(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import PeanoNat.

Import PreOrderNotations.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
Context {IWC : IWorldCore W} {WC : IWorld W}.

Section LargeNums.
  Local Definition I_large_num_func n (w : W) : Prop := world_index w < n.

  Local Lemma I_large_num_monotone n : monotone (I_large_num_func n).
  Proof.
    intros w₁ w₂ Hw H.
    eapply Nat.le_lt_trans; [ apply world_index_ord, Hw | exact H ].
  Qed.

  Definition I_large_num n : WProp W :=
    {| ma_monotone := I_large_num_monotone n |}.

  Lemma large_num_exists {w : W} : w ⊨ ∃ᵢ n, I_large_num n.
  Proof.
    iexists (S (world_index w)); constructor; constructor.
  Qed.

  Lemma large_num_S {w : W} :
    w ⊨ ∀ᵢ n, I_large_num n →ᵢ ∃ᵢ m, (n = S m)ᵢ ∧ᵢ ▷ I_large_num m.
  Proof.
    iintros [ | n ] [ Hn ]; [ inversion Hn | ].
    iexists; isplit; [ iintro; reflexivity | ].
    iintro; constructor.
    eapply Nat.lt_le_trans; [ | apply Nat.lt_succ_r ]; eassumption.
  Qed.

  #[global] Opaque I_large_num.
End LargeNums.
