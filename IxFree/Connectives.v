(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import PeanoNat.

Import PreOrderNotations.

(** * Logical Connectives *)

Section Connectives.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.

(* ========================================================================= *)
(** ** Prop Embedding *)

Section PropEmbedding.
  Variable P : Prop.

  Definition I_prop_func (w : W) := P.

  Lemma I_prop_monotone : monotone I_prop_func.
  Proof.
    intros w₁ w₂ Hw H; exact H.
  Qed.

  Definition I_prop : WProp W :=
    {| ma_monotone := I_prop_monotone |}.

  Lemma I_prop_intro {w : W} :
    P → w ⊨ I_prop.
  Proof.
    intro H; constructor; exact H.
  Qed.

  Lemma I_prop_elim {w : W} :
    (w ⊨ I_prop) → P.
  Proof.
    intros []; assumption.
  Qed.

  #[global] Opaque I_prop.
End PropEmbedding.

(* ========================================================================= *)
(** ** Implication *)

Section Arrow.
  Variables P Q : WProp W.

  Definition I_arrow_func (w : W) : Prop :=
    ∀ w', w ⊑ w' → w' ⊨ P → w' ⊨ Q.

  Lemma I_arrow_monotone : monotone I_arrow_func.
  Proof.
    intros w₁ w₂ Hw H w' Hw'; apply H.
    eapply preord_trans; eassumption.
  Qed.

  Definition I_arrow : WProp W :=
    {| ma_monotone := I_arrow_monotone |}.

  Lemma I_arrow_intro {w : W} :
    (∀ w', w ⊑ w' → (w' ⊨ P) → (w' ⊨ Q)) → w ⊨ I_arrow.
  Proof.
    intro H; constructor; exact H.
  Qed.

  Lemma I_arrow_elim {w : W} :
    w ⊨ I_arrow → w ⊨ P → w ⊨ Q.
  Proof.
    intros [ H ]; apply H, preord_refl.
  Qed.

  #[global] Opaque I_arrow.
End Arrow.

(* ========================================================================= *)
(** ** Later *)

Section Later.
  Context {IWC : IWorldCore W} {WC : IWorld W}.
  Variables P : WProp W.

  Definition I_later_func (w : W) : Prop :=
    ∀ w', w ⊑ w' → world_index w' < world_index w → w' ⊨ P.

  Lemma I_later_monotone : monotone I_later_func.
  Proof.
    intros w₁ w₂ Hw H w' Hw' Hidx; apply H.
    + eapply preord_trans; eassumption.
    + eapply Nat.lt_le_trans; [ eassumption | ].
      apply world_index_ord; assumption.
  Qed.

  Definition I_later : WProp W :=
    {| ma_monotone := I_later_monotone |}.

  Lemma I_later_intro {w : W} :
    (∀ w', w ⊑ w' → world_index w' < world_index w → w' ⊨ P) → w ⊨ I_later.
  Proof.
    intro H; constructor; exact H.
  Qed.

  Lemma I_later_elim {w w' : W} :
    w ⊑ w' → world_index w' < world_index w → w ⊨ I_later → w' ⊨ P.
  Proof.
    intros Hw Hidx [ H ]; apply H; assumption.
  Qed.

  #[global] Opaque I_later.

  Lemma I_later_zero {w : W} :
    world_index w = 0 → w ⊨ I_later.
  Proof.
    intros Hidx; apply I_later_intro; rewrite Hidx.
    intros w' _ Hlt.
    inversion Hlt.
  Qed.

  Lemma I_loeb_induction {w : W} :
    w ⊨ I_arrow I_later P → w ⊨ P.
  Proof.
    assert (LOEB : ∀ n w, world_index w < n → w ⊨ I_arrow I_later P → w ⊨ P).
    { clear w; intro n; induction n; intros w Hlt H.
      + inversion Hlt.
      + apply (I_arrow_elim I_later _ H), I_later_intro.
        intros w' Hord Hidx; apply IHn.
        - eapply Nat.lt_le_trans; [ eassumption | ].
          apply le_S_n, Hlt.
        - eapply I_valid_monotone; eassumption.
    }
    eapply LOEB, le_n.
  Qed.
End Later.

(* ========================================================================= *)
(** ** Notations *)

End Connectives.

Notation "( P )ᵢ" := (I_prop P).
Notation "P →ᵢ Q" := (I_arrow P Q)
  (at level 90, Q at level 200, right associativity).
Notation "▷ P" := (I_later P) (at level 30).