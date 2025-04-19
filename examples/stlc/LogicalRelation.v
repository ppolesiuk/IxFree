Require Import Utf8.
Require Import IxFree.Lib IxFree.Nat.
Require Import Var STLC AbstractMachine.

Definition F_Obs (Obs : conf ⇒ᵢ IRel) : conf ⇒ᵢ IRel :=
  λ c, (is_done c)ᵢ ∨ᵢ (∃ᵢ c', (step c c')ᵢ ∧ᵢ ▷Obs c').

Definition Obs_fix := I_fix F_Obs.
Definition Obs := F_Obs Obs_fix.

Definition SemType := value ⇒ᵢ IRel.

Definition KClo (R : SemType) (κ : cont) : IProp :=
  ∀ᵢ v, R v →ᵢ Obs (c_cont κ v).

Definition EClo {V : vset} (R : SemType) (ρ : env value V) (e : expr V) :
    IProp :=
  ∀ᵢ κ, KClo R κ →ᵢ Obs (c_eval e ρ κ).

Definition AppClo (R : SemType) (v u : value) : IProp :=
  ∀ᵢ κ, KClo R κ →ᵢ Obs (c_cont (k_app2 v κ) u).

Reserved Notation "⟦ τ ⟧".

Fixpoint RelT (τ : type) (v : value) : IProp :=
  match τ with
  | t_unit      => (True)ᵢ
  | t_arrow σ τ => ∀ᵢ u, ⟦ σ ⟧ u →ᵢ AppClo ⟦ τ ⟧ v u
  end
where "⟦ τ ⟧" := (RelT τ).

Definition RelG {V : vset} (Γ : env type V) (ρ : env value V) : IProp :=
  ∀ᵢ x, ⟦ Γ x ⟧ (ρ x).

Notation "G⟦ Γ ⟧" := (RelG Γ).

Definition rel_e {V : vset} (Γ : env type V) e τ : IProp :=
  ∀ᵢ ρ, G⟦ Γ ⟧ ρ →ᵢ EClo ⟦ τ ⟧ ρ e.

Notation "T⟦ Γ ⊢ e ∷ τ ⟧" := (rel_e Γ e τ).

(* ========================================================================= *)

Lemma F_Obs_contractive : contractive F_Obs.
Proof.
  intro w; iintros; unfold F_Obs; auto_contr.
Qed.

Lemma Obs_roll c w :
  w ⊨ Obs c → w ⊨ Obs_fix c.
Proof.
  intro; iapply (I_fix_roll (conf ⇒ᵢ IRel)); [ | assumption ].
  apply F_Obs_contractive.
Qed.

Lemma Obs_unroll c w :
  w ⊨ Obs_fix c → w ⊨ Obs c.
Proof.
  intro; iapply (I_fix_unroll (conf ⇒ᵢ IRel)); [ | assumption ].
  apply F_Obs_contractive.
Qed.

Lemma Obs_step c c' w :
  step c c' → w ⊨ ▷Obs c' → w ⊨ Obs c.
Proof.
  intros Hstep Hc.
  iright; iexists; isplit.
  + iintro; eassumption.
  + iintro.
    apply Obs_roll; assumption.
Qed.

Lemma Obs_done v w : w ⊨ Obs (c_done v).
Proof.
  ileft; iintro; constructor.
Qed.

(* ========================================================================= *)

Local Ltac lrstep := eapply Obs_step; [ constructor | iintro ].

Lemma compat_unit {V : vset} (Γ : env type V) w :
  w ⊨ T⟦ Γ ⊢ e_unit ∷ t_unit ⟧.
Proof.
  iintros ρ Hρ κ Hκ.
  lrstep.
  iapply Hκ.
  iintro; constructor.
Qed.

Lemma compat_var {V : vset} (Γ : env type V) x w :
  w ⊨ T⟦ Γ ⊢ e_var x ∷ Γ x ⟧.
Proof.
  iintros ρ Hρ κ Hκ.
  lrstep.
  iapply Hκ; iapply Hρ.
Qed.

Lemma compat_fix {V : vset} (Γ : env type V) e σ τ w :
  w ⊨ T⟦ Γ ◃ t_arrow σ τ ◃ σ ⊢ e ∷ τ ⟧ →
  w ⊨ T⟦ Γ ⊢ e_fix e ∷ t_arrow σ τ ⟧.
Proof.
  intro He; iintros ρ Hρ κ Hκ.
  lrstep.
  iapply Hκ; clear κ Hκ.
  loeb_induction.
  simpl; iintros u Hu κ Hκ.
  lrstep.
  iapply He; [ | assumption ].
  iintro x; destruct x as [ | [ | x ] ]; simpl; try assumption; [].
  iapply Hρ.
Qed.

Lemma compat_app {V : vset} (Γ : env type V) e₁ e₂ σ τ w :
  w ⊨ T⟦ Γ ⊢ e₁ ∷ t_arrow σ τ ⟧ →
  w ⊨ T⟦ Γ ⊢ e₂ ∷ σ ⟧ →
  w ⊨ T⟦ Γ ⊢ e_app e₁ e₂ ∷ τ ⟧.
Proof.
  intros He₁ He₂; iintros ρ Hρ κ Hκ.
  lrstep.
  iapply He₁; [ assumption | ]; clear e₁ He₁.
  iintros v₁ Hv₁.
  lrstep.
  iapply He₂; [ assumption | ]; clear e₂ He₂.
  iintros v₂ Hv₂.
  simpl in Hv₁; iapply Hv₁; assumption.
Qed.

Theorem fundamental_property {V : vset} (Γ : env type V) e τ w :
  T[ Γ ⊢ e ∷ τ ] → w ⊨ T⟦ Γ ⊢ e ∷ τ ⟧.
Proof.
  intro TYPING; induction TYPING.
  + apply compat_unit.
  + apply compat_var.
  + apply compat_fix; assumption.
  + eapply compat_app; eassumption.
Qed.

(* ========================================================================= *)

Lemma Obs_adequacy c : (∀ w, w ⊨ Obs c) → safe c.
Proof.
  intros Hc c₂ RED; revert Hc.
  induction RED as [ c | c₁ c₂ c₃ Hstep1 ]; intro Hc.
  + specialize (Hc {| nw_index := 0 |}); idestruct Hc.
    - idestruct Hc; auto.
    - idestruct Hc as c' Hc _; idestruct Hc; eauto.
  + apply IHRED; intro w.
    specialize (Hc (world_lift w)); idestruct Hc.
    - idestruct Hc.
      exfalso; eapply cant_step_when_done; eassumption.
    - idestruct Hc as c₂' Hstep2 Hc.
      idestruct Hstep2.
      rewrite I_world_lift_later in Hc; apply Obs_unroll in Hc.
      rewrite (step_deterministic Hstep1 Hstep2); assumption.
Qed.

Theorem type_safety e τ :
  T[ env_empty ⊢ e ∷ τ ] → safe (c_eval e env_empty k_init).
Proof.
  intro TYPING; apply Obs_adequacy; intro w.
  apply fundamental_property with (w := w) in TYPING; iapply TYPING.
  + iintro x; destruct x.
  + iintros v Hv; lrstep.
    apply Obs_done.
Qed.
