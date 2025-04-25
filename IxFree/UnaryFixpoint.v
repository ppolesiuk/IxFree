(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.
Require Import IxFree.Tactics.
Require Import IxFree.LaterRules.
Require Import IxFree.LargeNum.

(** * Unary Fixpoints *)
(** This module provides some helper definitions and lemmas needed to define
  general recursive predicates. We use [LargeNum] to define recursive unary
  predicates as fixpoints of contractive functions. Unary predicates are
  functions from some type to world-indexed propositions. *)

Import PreOrderNotations.

Section UnaryFixpoint.

Context {W : Type} {PCW : PreOrderCore W} {PW : PreOrder W}.
Context {IWC : IWorldCore W} {WC : IWorld W}.

Definition WRel1 (A : Type) : Type := A → WProp W.

Context {A : Type} (f : WRel1 A → WRel1 A).

(** We define equivalence of unary predicates as a pointwise world-indexed
  equivalence. Note that this definition is a world-indexed predicate, so
  we can use later operator to say that two predicates are almost
  equivalent [(▷WRel1_equiv R₁ R₂)].  *)

Definition WRel1_equiv (R₁ R₂ : WRel1 A) : WProp W :=
  ∀ᵢ x, R₁ x ↔ᵢ R₂ x.

Lemma WRel1_equiv_symm w R₁ R₂ :
  w ⊨ WRel1_equiv R₁ R₂ →ᵢ WRel1_equiv R₂ R₁.
Proof.
  iintros H x; isplit; iintro Hx; iapply H; assumption.
Qed.

Lemma WRel1_equiv_trans w R₁ R₂ R₃ :
  w ⊨ WRel1_equiv R₁ R₂ →ᵢ WRel1_equiv R₂ R₃ →ᵢ WRel1_equiv R₁ R₃.
Proof.
  iintros H1 H2 x; isplit.
  + iintro H; iapply H2; iapply H1; assumption.
  + iintro H; iapply H1; iapply H2; assumption.
Qed.

(** We say that function is contractive if it maps almost equivalent
  predicates to equivalent predicates. Contractive functions have
  a fixpoint. *)

Definition I_contractive1 : WProp W :=
  ∀ᵢ R₁ R₂, ▷ WRel1_equiv R₁ R₂ →ᵢ WRel1_equiv (f R₁) (f R₂).

(** A main observation needed to construct such a fixpoint is that when we
  iterate a contractive function large number of times, the result does not
  depend on the exact value of this number. *)

Local Fixpoint I_fix1_n (n : nat) : WRel1 A :=
  match n with
  | 0   => λ _, (False)ᵢ
  | S n => f (I_fix1_n n)
  end.

Local Lemma I_fix1_n_large w :
  w ⊨ I_contractive1 →ᵢ
    ∀ᵢ n m, I_large n →ᵢ I_large m →ᵢ
    WRel1_equiv (I_fix1_n n) (I_fix1_n m).
Proof.
  iintro f_contr; loeb_induction.
  iintros n m Hn Hm.
  destruct n as [ | n ]; [ exfalso; eapply I_large_Z; eassumption | ].
  destruct m as [ | m ]; [ exfalso; eapply I_large_Z; eassumption | ].
  simpl in Hn, Hm; simpl; iapply f_contr.
  iintro; iapply IH; assumption.
Qed.

(** Therefore, we can define a fixpoint as any large iteration of a
  function. *)

Definition I_fix1 : WRel1 A :=
  λ x, ∀ᵢ n, I_large n →ᵢ I_fix1_n n x.

Local Lemma I_fix1_n_equiv w :
  w ⊨ I_contractive1 →ᵢ
    ∀ᵢ n, I_large n →ᵢ WRel1_equiv I_fix1 (I_fix1_n n).
Proof.
  iintros f_contr n Hn x; isplit.
  + iintros Hx; iapply Hx; assumption.
  + iintros Hx m Hm.
    iapply I_fix1_n_large;
      [ exact f_contr | exact Hn | exact Hm | exact Hx ].
Qed.

Lemma I_fix1_is_fixpoint {w : W} :
  w ⊨ I_contractive1 →ᵢ WRel1_equiv I_fix1 (f I_fix1).
Proof.
  iintro f_contr.
  idestruct (I_large_exists w) as n Hn.
  iapply WRel1_equiv_trans; [ iapply I_fix1_n_equiv; eassumption | ].
  iapply I_large_is_S in Hn; idestruct Hn as m Hnm Hm; subst; simpl.
  iapply f_contr.
  later_shift.
  iapply WRel1_equiv_symm; iapply I_fix1_n_equiv; assumption.
Qed.

#[global] Opaque I_fix1.

Lemma I_fix1_unroll (w : W) x :
  w ⊨ I_contractive1 →ᵢ I_fix1 x →ᵢ f I_fix1 x.
Proof.
  iintro f_contr; iapply I_fix1_is_fixpoint; assumption.
Qed.

Lemma I_fix1_roll (w : W) x :
  w ⊨ I_contractive1 →ᵢ f I_fix1 x →ᵢ I_fix1 x.
Proof.
  iintro f_contr; iapply I_fix1_is_fixpoint; assumption.
Qed.

End UnaryFixpoint.
