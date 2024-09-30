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

  Local Definition I_prop_func (w : W) := P.

  Local Lemma I_prop_monotone : monotone I_prop_func.
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

  Local Definition I_arrow_func (w : W) : Prop :=
    ∀ w', w ⊑ w' → w' ⊨ P → w' ⊨ Q.

  Local Lemma I_arrow_monotone : monotone I_arrow_func.
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
(** ** Conjunction *)

Section Conjunction.
  Variables P Q : WProp W.

  Local Definition I_conj_func (w : W) : Prop :=
    (w ⊨ P) ∧ (w ⊨ Q).

  Local Lemma I_conj_monotone : monotone I_conj_func.
  Proof.
    intros w₁ w₂ Hw [ H1 H2 ].
    split; eapply I_valid_monotone; eassumption.
  Qed.

  Definition I_conj : WProp W :=
    {| ma_monotone := I_conj_monotone |}.

  Lemma I_conj_intro {w : W} :
    w ⊨ P → w ⊨ Q → w ⊨ I_conj.
  Proof.
    intros H1 H2; constructor; split; assumption.
  Qed.

  Lemma I_conj_elim {w : W} :
    w ⊨ I_conj → (w ⊨ P) ∧ (w ⊨ Q).
  Proof.
    intros [ [ H1 H2 ] ]; split; assumption.
  Qed.

  #[global] Opaque I_conj.

  Lemma I_conj_elim1 {w : W} :
    w ⊨ I_conj → w ⊨ P.
  Proof.
    intro; apply I_conj_elim; assumption.
  Qed.

  Lemma I_conj_elim2 {w : W} :
    w ⊨ I_conj → w ⊨ Q.
  Proof.
    intro; apply I_conj_elim; assumption.
  Qed.
End Conjunction.

(* ========================================================================= *)
(** ** Disjunction *)

Section Disjunction.
  Variables P Q : WProp W.

  Local Definition I_disj_func (w : W) : Prop :=
    (w ⊨ P) ∨ (w ⊨ Q).

  Local Lemma I_disj_monotone : monotone I_disj_func.
  Proof.
    intros w₁ w₂ Hw [ H | H ]; [ left | right ];
      eapply I_valid_monotone; eassumption.
  Qed.

  Definition I_disj : WProp W :=
    {| ma_monotone := I_disj_monotone |}.

  Lemma I_disj_intro1 {w : W} :
    w ⊨ P → w ⊨ I_disj.
  Proof.
    intro H; constructor; left; assumption.
  Qed.

  Lemma I_disj_intro2 {w : W} :
    w ⊨ Q → w ⊨ I_disj.
  Proof.
    intro H; constructor; right; assumption.
  Qed.

  Lemma I_disj_elim {w : W} :
    w ⊨ I_disj → (w ⊨ P) ∨ (w ⊨ Q).
  Proof.
    intros [ [ H | H ] ]; [ left | right ]; assumption.
  Qed.

  #[global] Opaque I_disj.
End Disjunction.

(* ========================================================================= *)
(** ** Universal quantifier *)

Section Forall.
  Variable A : Type.
  Variable P : A → WProp W.

  Local Definition I_forall_func (w : W) : Prop :=
    ∀ x : A, w ⊨ P x.

  Local Lemma I_forall_monotone : monotone I_forall_func.
  Proof.
    intros w₁ w₂ Hw H x.
    eapply I_valid_monotone; [ eassumption | apply H ].
  Qed.

  Definition I_forall : WProp W :=
    {| ma_monotone := I_forall_monotone |}.

  Lemma I_forall_intro {w : W} :
    (∀ x : A, w ⊨ P x) → w ⊨ I_forall.
  Proof.
    intros H; constructor; exact H.
  Qed.

  Lemma I_forall_elim {w : W} :
    w ⊨ I_forall → ∀ x, w ⊨ P x.
  Proof.
    intros [ H ]; exact H.
  Qed.

  #[global] Opaque I_forall.
End Forall.

(* ========================================================================= *)
(** ** Existential quantifier *)

Section Exists.
  Variable A : Type.
  Variable P : A → WProp W.

  Local Definition I_exists_func (w : W) : Prop :=
    ∃ x : A, w ⊨ P x.

  Local Lemma I_exists_monotone : monotone I_exists_func.
  Proof.
    intros w₁ w₂ Hw [ x H ]; exists x.
    eapply I_valid_monotone; [ eassumption | apply H ].
  Qed.

  Definition I_exists : WProp W :=
    {| ma_monotone := I_exists_monotone |}.

  Lemma I_exists_intro {w : W} :
    ∀ x : A, w ⊨ P x → w ⊨ I_exists.
  Proof.
    intros x H; constructor; exists x; assumption.
  Qed.

  Lemma I_exists_elim {w : W} :
    w ⊨ I_exists → ∃ x, w ⊨ P x.
  Proof.
    intros [ H ]; exact H.
  Qed.

  #[global] Opaque I_exists.
End Exists.

(* ========================================================================= *)
(** ** Later *)

Section Later.
  Context {ICW : IWorldCore W} {IW : IWorld W}.
  Variables P : WProp W.

  Local Definition I_later_func (w : W) : Prop :=
    ∀ w', w ⊏↓ w' → w' ⊨ P.

  Local Lemma I_later_monotone : monotone I_later_func.
  Proof.
    intros w₁ w₂ Hw H w' Hw'; apply H.
    eapply world_strict_preord_trans_l; eassumption.
  Qed.

  Definition I_later : WProp W :=
    {| ma_monotone := I_later_monotone |}.

  Lemma I_later_intro {w : W} :
    (∀ w', w ⊏↓ w' → w' ⊨ P) → w ⊨ I_later.
  Proof.
    intro H; constructor; exact H.
  Qed.

  Lemma I_later_elim {w w' : W} :
    w ⊏↓ w' → w ⊨ I_later → w' ⊨ P.
  Proof.
    intros Hw [ H ]; apply H; assumption.
  Qed.

  #[global] Opaque I_later.
End Later.

(* ========================================================================= *)
(** ** Iff *)

Definition I_iff P Q := I_conj (I_arrow P Q) (I_arrow Q P).

(* ========================================================================= *)
(** ** Notations *)

End Connectives.

Notation "( P )ᵢ" := (I_prop P).
Notation "P →ᵢ Q" := (I_arrow P Q)
  (at level 90, Q at level 200, right associativity).
Notation "P ↔ᵢ Q" := (I_iff P Q) (at level 95).
Notation "P '∧ᵢ' Q" := (I_conj P Q) (at level 80, right associativity).
Notation "P '∨ᵢ' Q" := (I_disj P Q) (at level 85, right associativity).
Notation "'∀ᵢ' x .. y , P" :=
  (I_forall _ (fun x => .. (I_forall _ (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ᵢ x .. y ']' , '/' P ']'").
Notation "'∃ᵢ' x .. y , P" :=
  (I_exists _ (fun x => .. (I_exists _ (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ᵢ x .. y ']' , '/' P ']'").
Notation "▷ P" := (I_later P) (at level 30).
