(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import PeanoNat.

Import PreOrderNotations.

(** * Additional Inference Rules for Later Modality *)

(** In this module we provide additional inference rules and lemmas related to
  later modality. *)

Section LaterRules.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
Context {ICW : IWorldCore W} {IW : IWorld W}.

(* ========================================================================= *)
(** ** Rules That Do Not Require Additional Structure on Worlds *)

(** Later is satisfied for step-index 0 *)

Lemma I_later_zero (P : WProp W) {w : W} :
  world_index w = 0 → w ⊨ ▷ P.
Proof.
  intro Hidx; apply I_later_intro.
  intros w' [ _ Hlt ]; rewrite Hidx in Hlt; inversion Hlt.
Qed.

(** Löb induction, i.e., synthetic induction on step indices *)

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

(** Most of later distribution laws do hold for any indexed structure of
  worlds. *)

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

(* ========================================================================= *)
(** ** Additional Laws That Rely on Existence of [world_lift] *)

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

(* ========================================================================= *)
(** ** Additional Laws That Relies on Existence of [world_unlift] *)

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

(* ========================================================================= *)
(** Case Analysis on World Index *)

Section BottomDec.
  Context {BW : IWorldBottomDec W}.

  (** Here we provide a lemma, that in synthetic form expresses the case
    analysis on world index. We are in either locally minimal world (in the
    sense of step-index), expressed as [▷(False)ᵢ], or not, which means that
    [▷(P)ᵢ] implies [P]. For convenience, we also provide a tactic [index_case]
    that performs such an analysis. *)

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

(* ------------------------------------------------------------------------- *)
(** *** Helper Tactics *)

(** We start with defining some helper tactics. They should not be used
  directly by the user of the library. *)

(* begin details *)

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
    let HProp  := fresh "HProp" in
    let HFalse := fresh "HFalse" in
    destruct (I_index_case w) as [ HFalse | HProp ];
      [ revert HFalse;
        repeat lazymatch goal with
               | [ H: w ⊨ ▷(_)ᵢ |- _ ] => clear H
               end; intro HF
      | repeat lazymatch goal with
               | [ H: w ⊨ ▷(_)ᵢ |- _ ] => apply HProp in H
               end; clear HProp
      ]
  end.

(* end details *)

(* ------------------------------------------------------------------------- *)
(** *** Löb Induction *)

(** The key feature of step-indexed logic with later modality is induction
over step-indices, called Löb induction. When the goal is [w ⊨ φ], these
tactics introduce an assumption [w ⊨ ▷ φ]. The name of this assumption can
be provided as a parameter for [loeb_induction] tactic. If [loeb_induction]
is used without a name, the default name [IH] is used. *)
Tactic Notation "loeb_induction" := loeb_induction_anon.
Tactic Notation "loeb_induction" ident(H) := loeb_induction_named H.

(* ------------------------------------------------------------------------- *)
(** *** Index Case Analysis *)

(** When the world structure implements an instance of [IWorldBottomDec], we
can perform an analysis on the step-index by using [index_case] tactic. The
tactic creates two subgoals. The first subgoal corresponds to the situation
when there is no future world with lower step-index, so we get additional
assumption [w ⊨ ▷(False)ᵢ]. The optional parameter to the tactic is the name
of this assumption (the default name is [HFalse]). Since from false we can
deduce anything, all assumptions of the form [w ⊨ ▷(φ)] are cleared. In the
second subgoal, all assumptions of the form [w ⊨ ▷(φ)ᵢ] are changed to [φ]. *)

Tactic Notation "index_case" :=
  let HFalse := fresh "HFalse" in
  index_case_named HFalse.
Tactic Notation "index_case" ident(H) := index_case_named H.
