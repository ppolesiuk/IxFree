(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import PeanoNat.

Import PreOrderNotations.

Section LaterRules.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
Context {ICW : IWorldCore W} {IW : IWorld W}.

Lemma I_later_zero (P : WProp W) {w : W} :
  world_index w = 0 → w ⊨ ▷ P.
Proof.
  intro Hidx; apply I_later_intro.
  intros w' [ _ Hlt ]; rewrite Hidx in Hlt; inversion Hlt.
Qed.

Lemma I_loeb_induction (P : WProp W) {w : W} :
  (w ⊨ ▷ P →ᵢ P) → w ⊨ P.
Proof.
  assert (LOEB : ∀ n w, world_index w < n → (w ⊨ ▷ P →ᵢ P) → w ⊨ P).
  { clear w; intro n; induction n; intros w Hlt H.
    + inversion Hlt.
    + apply (I_arrow_elim (▷P) _ H), I_later_intro.
      intros w' [ Hord Hidx ]; apply IHn.
      - eapply Nat.lt_le_trans; [ eassumption | ].
        apply le_S_n, Hlt.
      - eapply I_valid_monotone; eassumption.
  }
  eapply LOEB, le_n.
Qed.

Lemma I_arrow_later_down (P Q : WProp W) {w : W} :
  (w ⊨ ▷(P →ᵢ Q)) → w ⊨ ▷P →ᵢ ▷Q.
Proof.
  intro H; iintro HP; later_shift; iapply H; assumption.
Qed.

Lemma I_conj_later_down (P Q : WProp W) {w : W} :
  (w ⊨ ▷(P ∧ᵢ Q)) → w ⊨ ▷P ∧ᵢ ▷Q.
Proof.
  intro H; isplit; later_shift; iapply H.
Qed.

Lemma I_conj_later_up (P Q : WProp W) {w : W} :
  (w ⊨ ▷P ∧ᵢ ▷Q) → w ⊨ ▷(P ∧ᵢ Q).
Proof.
  intro H; idestruct H as H1 H2; later_shift; isplit; assumption.
Qed.

Lemma I_iff_later_down (P Q : WProp W) {w : W} :
  (w ⊨ ▷(P ↔ᵢ Q)) → w ⊨ ▷P ↔ᵢ ▷Q.
Proof.
  intro H; isplit; apply I_arrow_later_down; later_shift; apply H.
Qed.

Lemma I_disj_later_up (P Q : WProp W) {w : W} :
  (w ⊨ ▷P ∨ᵢ ▷Q) → w ⊨ ▷(P ∨ᵢ Q).
Proof.
  intro H; idestruct H; later_shift; [ ileft | iright ]; assumption.
Qed.

Lemma I_forall_later_down (A : Type) (P : A → WProp W) {w : W} :
  (w ⊨ ▷ ∀ᵢ x, P x) → w ⊨ ∀ᵢ x, ▷P x.
Proof.
  intro H; iintro x; later_shift; iapply H.
Qed.

Lemma I_forall_later_up (A : Type) (P : A → WProp W) {w : W} :
  (w ⊨ ∀ᵢ x, ▷P x) → w ⊨ ▷ ∀ᵢ x, P x.
Proof.
  intro H; apply I_later_intro; intros w' Hord.
  iintro x; apply I_forall_elim with (x:=x) in H.
  eapply I_later_elim; eassumption.
Qed.

Lemma I_exists_later_up  (A : Type) (P : A → WProp W) {w : W} :
  (w ⊨ ∃ᵢ x, ▷P x) → w ⊨ ▷ ∃ᵢ x, P x.
Proof.
  intro H; idestruct H as x H; later_shift; iexists x; assumption.
Qed.

Section Lift.
  Context {LCW : IWorldLiftCore W} {LW : IWorldLift W}.

  Lemma I_world_lift_later (P : WProp W) {w : W} :
    (world_lift w ⊨ ▷ P) ↔ (w ⊨ P).
  Proof.
    split; intro HP.
    + apply I_later_elim with (w' := w) in HP;
        [ assumption | apply world_lift_ord ].
    + apply I_later_intro; intros w' Hord.
      eapply I_valid_monotone; [ | eassumption ].
      apply world_lift_limit_l; assumption.
  Qed.

  Lemma I_arrow_later_up (P Q : WProp W) {w : W} :
    (w ⊨ ▷P →ᵢ ▷Q) → w ⊨ ▷(P →ᵢ Q).
  Proof.
    intro H; apply I_later_intro; intros w₁ Hord₁.
    apply I_arrow_intro; intros w₂ Hord₂ HP.
    apply @I_valid_monotone with (w₂ := world_lift w₂) in H;
      [ apply (I_arrow_elim (▷P) (▷Q)) in H | ].
    + apply I_world_lift_later; assumption.
    + apply I_world_lift_later; assumption.
    + apply world_lift_limit_u.
      eapply world_strict_preord_trans_r; eassumption.
  Qed.

  Lemma I_iff_later_up (P Q : WProp W) {w : W} :
    (w ⊨ ▷P ↔ᵢ ▷Q) → w ⊨ ▷(P ↔ᵢ Q).
  Proof.
    intro H; idestruct H as H1 H2.
    apply I_arrow_later_up in H1, H2; later_shift.
    isplit; assumption.
  Qed.
End Lift.

Section Unlift.
  Context {UCW : IWorldUnliftCore W} {LW : IWorldUnlift W}.

  Lemma I_world_unlift_later (P : WProp W) {w : W} :
    (world_unlift w ⊨ P) → (w ⊨ ▷ P).
  Proof.
    intro H; apply I_later_intro; intros w' Hord.
    eapply I_valid_monotone; [ | eassumption ].
    apply world_unlift_limit; assumption.
  Qed.

  Lemma I_disj_later_down (P Q : WProp W) {w : W} :
    (w ⊨ ▷(P ∨ᵢ Q)) → w ⊨ ▷P ∨ᵢ ▷Q.
  Proof.
    intro H.
    remember (world_index w) as n; destruct n as [ | n ].
    + ileft; apply I_later_zero; auto.
    + apply I_later_elim with (w' := world_unlift w) in H;
        [ | eapply world_unlift_ord; eassumption ].
      idestruct H as H H; [ ileft | iright ]; apply I_world_unlift_later;
        assumption.
  Qed.

  Lemma I_exists_later_down (A : Type) (P : A → WProp W) (ex : A) {w : W} :
    (w ⊨ ▷ ∃ᵢ x, P x) → w ⊨ ∃ᵢ x, ▷P x.
  Proof.
    intro H.
    remember (world_index w) as n; destruct n as [ | n ].
    + iexists ex; apply I_later_zero; auto.
    + apply I_later_elim with (w' := world_unlift w) in H;
        [ | eapply world_unlift_ord; eassumption ].
      idestruct H as x H; iexists x.
      apply I_world_unlift_later; assumption.
  Qed.
End Unlift.

Section BottomDec.
  Context {BW : IWorldBottomDec W}.

  Lemma I_index_case (w : W) :
    (w ⊨ ▷(False)ᵢ) ∨ (∀ P, (w ⊨ ▷(P)ᵢ) → P).
  Proof.
    destruct (world_bottom_dec w) as [ [ w' Hord ] | Hbot ].
    + right; intros P HP.
      apply (I_later_elim _ Hord), I_prop_elim in HP; assumption.
    + left; apply I_later_intro.
      intros w' Hord; apply I_prop_intro; eauto.
  Qed.
End BottomDec.

End LaterRules.

(* ========================================================================= *)
(** ** Tactics *)

Local Ltac loeb_induction_named IH :=
  match goal with
  | [ |- _ ⊨ ?P ] =>
    apply (I_loeb_induction P);
    iintro IH
  end.

Local Ltac loeb_induction_anon :=
  let IH := fresh "IH" in
  loeb_induction_named IH.

Local Ltac index_case_named HF :=
  lazymatch goal with
  | [ |- ?w ⊨ _ ] =>
    let HProp := fresh "HProp" in
    destruct (I_index_case w) as [ HF | HProp ];
      [ | repeat lazymatch goal with
                 | [ H: w ⊨ ▷(_)ᵢ |- _ ] => apply HProp in H
                 end; clear HProp
      ]
  end.

(** The key feature of step-indexed logic with later modality is an induction
over step-indices, called Löb induction. When the goal is [w ⊨ φ], these
tactics introduces an assumption [w ⊨ ▷ φ]. The name of this assumption can
be provided as a parameter for [loeb_induction] tactic. If [loeb_induction]
is used without a name, the default name [IH] is used. *)
Tactic Notation "loeb_induction" := loeb_induction_anon.
Tactic Notation "loeb_induction" ident(H) := loeb_induction_named H.

Tactic Notation "index_case" :=
  let HFalse := fresh "HFalse" in
  index_case_named HFalse.
Tactic Notation "index_case" ident(H) := index_case_named H.
