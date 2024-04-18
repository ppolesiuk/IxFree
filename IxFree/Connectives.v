(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.

Import PreOrderNotations.

(** * Logical Connectives *)

Section Connectives.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.

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
End Arrow.

(* ========================================================================= *)
(** ** Notations *)

End Connectives.

Notation "P →ᵢ Q" := (I_arrow P Q)
  (at level 99, Q at level 200, right associativity).