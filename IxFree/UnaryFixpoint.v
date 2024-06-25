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

  Lemma large_num_Z {w : W} : ¬(w ⊨ I_large_num 0).
  Proof.
    intros [ H ]; inversion H.
  Qed.

  Lemma large_num_S {w : W} n :
    w ⊨ I_large_num (S n) →ᵢ ▷ I_large_num n.
  Proof.
    iintros [ Hn ]; iintro; constructor.
    eapply Nat.lt_le_trans; [ | apply Nat.lt_succ_r ]; eassumption.
  Qed.

  #[global] Opaque I_large_num.

  Lemma large_num_is_S {w : W} :
    w ⊨ ∀ᵢ n, I_large_num n →ᵢ ∃ᵢ m, (n = S m)ᵢ ∧ᵢ ▷ I_large_num m.
  Proof.
    iintros [ | n ] Hn.
    + exfalso; eapply large_num_Z; eassumption.
    + iexists n; isplit; [ iintro; reflexivity | ].
      iapply large_num_S; assumption.
  Qed.
End LargeNums.

Definition IRel1 (A : Type) : Type := A → WProp W.

Section UnaryFixpoint.
  Context {A : Type} (f : IRel1 A → IRel1 A).

  Definition IRel1_equiv (R₁ R₂ : IRel1 A) : WProp W :=
    ∀ᵢ x, R₁ x ↔ᵢ R₂ x.

  Lemma IRel1_equiv_symm w R₁ R₂ :
    w ⊨ IRel1_equiv R₁ R₂ →ᵢ IRel1_equiv R₂ R₁.
  Proof.
    iintros H x; isplit; iintro Hx; iapply H; assumption.
  Qed.

  Lemma IRel1_equiv_trans w R₁ R₂ R₃ :
    w ⊨ IRel1_equiv R₁ R₂ →ᵢ IRel1_equiv R₂ R₃ →ᵢ IRel1_equiv R₁ R₃.
  Proof.
    iintros H1 H2 x; isplit.
    + iintro H; iapply H2; iapply H1; assumption.
    + iintro H; iapply H1; iapply H2; assumption.
  Qed.

  Definition contractive1 : WProp W :=
    ∀ᵢ R₁ R₂, ▷ IRel1_equiv R₁ R₂ →ᵢ IRel1_equiv (f R₁) (f R₂).

  Variable f_contr : ∀ w, w ⊨ contractive1.

  Local Fixpoint I_fix1_n (n : nat) : IRel1 A :=
    match n with
    | 0   => λ _, (False)ᵢ
    | S n => f (I_fix1_n n)
    end.

  Local Lemma I_fix1_n_large w :
    w ⊨ ∀ᵢ n m, I_large_num n →ᵢ I_large_num m →ᵢ
      IRel1_equiv (I_fix1_n n) (I_fix1_n m).
  Proof.
    loeb_induction.
    iintros n m Hn Hm.
    destruct n as [ | n ]; [ exfalso; eapply large_num_Z; eassumption | ].
    destruct m as [ | m ]; [ exfalso; eapply large_num_Z; eassumption | ].
    iapply large_num_S in Hn; iapply large_num_S in Hm.
    simpl; iapply f_contr.
    iintro; iapply IH; assumption.
  Qed.

  Definition I_fix1 : IRel1 A :=
    λ x, ∀ᵢ n, I_large_num n →ᵢ I_fix1_n n x.

  Local Lemma I_fix1_n_equiv w :
    w ⊨ ∀ᵢ n, I_large_num n →ᵢ IRel1_equiv I_fix1 (I_fix1_n n).
  Proof.
    iintros n Hn x; isplit.
    + iintros Hx; iapply Hx; assumption.
    + iintros Hx m Hm.
      iapply I_fix1_n_large; [ exact Hn | exact Hm | exact Hx ].
  Qed.

  Lemma I_fix1_is_fixpoint {w : W} :
    w ⊨ IRel1_equiv I_fix1 (f I_fix1).
  Proof.
    idestruct (@large_num_exists w) as n Hn.
    iapply IRel1_equiv_trans; [ iapply I_fix1_n_equiv; eassumption | ].
    iapply large_num_is_S in Hn; idestruct Hn as m Hnm Hm.
    idestruct Hnm; subst; simpl.
    iapply f_contr.
    later_shift.
    iapply IRel1_equiv_symm; iapply I_fix1_n_equiv; assumption.
  Qed.

  Lemma I_fix1_unroll (w : W) x : w ⊨ I_fix1 x →ᵢ f I_fix1 x.
  Proof.
    iapply I_fix1_is_fixpoint.
  Qed.

  Lemma I_fix1_roll (w : W) x : w ⊨ f I_fix1 x →ᵢ I_fix1 x.
  Proof.
    iapply I_fix1_is_fixpoint.
  Qed.
End UnaryFixpoint.
