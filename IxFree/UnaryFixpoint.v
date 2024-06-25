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
    w ⊨ I_large_num (S n) → w ⊨ ▷ I_large_num n.
  Proof.
    intros [ Hn ]; iintro; constructor.
    eapply Nat.lt_le_trans; [ | apply Nat.lt_succ_r ]; eassumption.
  Qed.

  #[global] Opaque I_large_num.

  Lemma large_num_is_S {w : W} :
    w ⊨ ∀ᵢ n, I_large_num n →ᵢ ∃ᵢ m, (n = S m)ᵢ ∧ᵢ ▷ I_large_num m.
  Proof.
    iintros [ | n ] Hn.
    + exfalso; eapply large_num_Z; eassumption.
    + iexists n; isplit; [ iintro; reflexivity | ].
      (* TODO: to jest słabe. Trzeba poprawić taktykę iapply *)
      apply large_num_S; assumption.
  Qed.
End LargeNums.

Definition IRel1 (A : Type) : Type := A → WProp W.

Section UnaryFixpoint.
  Context {A : Type} (f : IRel1 A → IRel1 A).

  Definition IRel1_equiv (R₁ R₂ : IRel1 A) : WProp W :=
    ∀ᵢ x, R₁ x ↔ᵢ R₂ x.

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
    apply large_num_S in Hn, Hm.
    simpl; iapply (f_contr w).
    iintro; iapply IH; assumption.
  Qed.

  Definition I_fix1 : IRel1 A :=
    λ x, ∀ᵢ n, I_large_num n →ᵢ I_fix1_n n x.

  Local Definition I_fix1_ex : IRel1 A :=
    λ x, ∃ᵢ n, I_large_num n ∧ᵢ I_fix1_n n x.

  Local Lemma I_fix1_ex_equiv {w : W} :
    w ⊨ IRel1_equiv I_fix1 I_fix1_ex.
  Proof.
    iintro x; isplit.
    + iintro Hx.
      idestruct (@large_num_exists w) as n Hn.
      iexists n; isplit; [ | iapply Hx ]; assumption.
    + iintro Hx; idestruct Hx as n Hn Hx.
      (* TODO: make iapply work better *)
      iintros m Hm; iapply (I_fix1_n_large w);
        [ exact Hn | exact Hm | exact Hx ].
  Qed.
End UnaryFixpoint.