(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import IxFree.Relations.

(** * [auto_contr] tactic *)

(** This tactic simplifies proofs of contractiveness of functions. *)

Section AutoContrLemmas.
  Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
  Context {IWC : IWorldCore W} {WC : IWorld W}.

  Local Lemma auto_contr_id (w : W) (P : WProp W) :
    w ⊨ P ↔ᵢ P.
  Proof.
    isplit; iintro; assumption.
  Qed.

  Local Lemma auto_contr_arrow (w : W) (P1 Q1 P2 Q2 : WProp W) :
    w ⊨ P1 ↔ᵢ P2 → w ⊨ Q1 ↔ᵢ Q2 → w ⊨ (P1 →ᵢ Q1) ↔ᵢ (P2 →ᵢ Q2).
  Proof.
    intros HP HQ; isplit; iintros H H0;
      iapply HQ; iapply H; iapply HP; assumption.
  Qed.

  Lemma auto_contr_conj (w : W) (P1 Q1 P2 Q2 : WProp W) :
    (w ⊨ P1 ↔ᵢ P2) → (w ⊨ Q1 ↔ᵢ Q2) → (w ⊨ P1 ∧ᵢ Q1 ↔ᵢ P2 ∧ᵢ Q2).
  Proof.
    intros HP HQ; isplit; iintro H; isplit;
      iapply HP || iapply HQ; iapply H.
  Qed.

  Lemma auto_contr_disj (w : W) (P1 Q1 P2 Q2 : WProp W) :
    (w ⊨ P1 ↔ᵢ P2) → (w ⊨ Q1 ↔ᵢ Q2) → (w ⊨ P1 ∨ᵢ Q1 ↔ᵢ P2 ∨ᵢ Q2).
  Proof.
    intros HP HQ; isplit; iintro H; idestruct H as H H;
      (ileft; iapply HP; assumption) || (iright; iapply HQ; assumption).
  Qed.

  Lemma auto_contr_iff (w : W) (P1 Q1 P2 Q2 : WProp W) :
    w ⊨ P1 ↔ᵢ P2 → w ⊨ Q1 ↔ᵢ Q2 → w ⊨ (P1 ↔ᵢ Q1) ↔ᵢ (P2 ↔ᵢ Q2).
  Proof.
    intros HP HQ; isplit; iintro H; isplit; iintro H0;
      iapply HP || iapply HQ; iapply H; iapply HP || iapply HQ; assumption.
  Qed.

  Lemma auto_contr_later (w : W) (P1 P2 : WProp W) :
    w ⊨ ▷ (P1 ↔ᵢ P2) → w ⊨ ▷ P1 ↔ᵢ ▷ P2.
  Proof.
    intro HP; isplit; iintro H; later_shift; iapply HP; assumption.
  Qed.

  Lemma auto_contr_forall (w : W) (A : Type) (P1 P2 : A → WProp W) :
    (w ⊨ ∀ᵢ x : A, P1 x ↔ᵢ P2 x) → w ⊨ (∀ᵢ x, P1 x) ↔ᵢ (∀ᵢ x, P2 x).
  Proof.
    intros HP; isplit; iintros H x; iapply HP; iapply H.
  Qed.

  Lemma auto_contr_exists (w : W) (A : Type) (P1 P2 : A → WProp W) :
    (w ⊨ ∀ᵢ x : A, P1 x ↔ᵢ P2 x) → w ⊨ (∃ᵢ x, P1 x) ↔ᵢ (∃ᵢ x, P2 x).
  Proof.
    intros HP; isplit; iintro H; idestruct H as x H; iexists x; iapply HP;
      assumption.
  Qed.
End AutoContrLemmas.

Ltac auto_contr :=
  lazymatch goal with
  | [ |- ?w ⊨ ?P ↔ᵢ ?P ] =>
    apply (auto_contr_id w P)
  | [ |- ?w ⊨ (?P1 →ᵢ ?Q1) ↔ᵢ (?P2 →ᵢ ?Q2) ] =>
    apply (auto_contr_arrow w P1 Q1 P2 Q2); auto_contr
  | [ |- ?w ⊨ ?P1 ∧ᵢ ?Q1 ↔ᵢ ?P2 ∧ᵢ ?Q2 ] =>
    apply (auto_contr_conj w P1 Q1 P2 Q2); auto_contr
  | [ |- ?w ⊨ ?P1 ∨ᵢ ?Q1 ↔ᵢ ?P2 ∨ᵢ ?Q2 ] =>
    apply (auto_contr_disj w P1 Q1 P2 Q2); auto_contr
  | [ |- ?w ⊨ (?P1 ↔ᵢ ?Q1) ↔ᵢ (?P2 ↔ᵢ ?Q2) ] =>
    apply (auto_contr_iff w P1 Q1 P2 Q2); auto_contr
  | [ |- ?w ⊨ (▷ _) ↔ᵢ (▷ _) ] =>
    apply auto_contr_later; later_shift; auto_contr
  | [ |- ?N ⊨ (∀ᵢ x : ?A, _) ↔ᵢ (∀ᵢ _ : ?A, _) ] =>
    let y := fresh x in
    apply auto_contr_forall; iintro y; auto_contr
  | [ |- ?N ⊨ (∃ᵢ x : ?A, _) ↔ᵢ (∃ᵢ _ : ?A, _) ] =>
    let y := fresh x in
    apply auto_contr_exists; iintro y; auto_contr
  | [ |- _ ] =>
    match goal with
    | [ H: ?w ⊨ _ ≈ᵢ _ |- ?w ⊨ _ ↔ᵢ _ ] => iapply H
    | [ H: ?w ⊨ _ ↔ᵢ _ |- ?w ⊨ _ ↔ᵢ _ ] => exact H
    | _ => idtac
    end
  end.
