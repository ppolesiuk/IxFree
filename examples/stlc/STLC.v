Require Import Utf8.
Require Import Var.

Inductive expr {V : vset} : Set :=
| e_unit
| e_var  (x : V)
| e_fix  (e : @expr (S (S V)))
| e_app  (e₁ e₂ : expr)
.

Arguments expr V : clear implicits.

Inductive type : Set :=
| t_unit
| t_arrow (σ τ : type)
.

Reserved Notation "T[ Γ ⊢ e ∷ τ ]".

Inductive typing {V : vset} (Γ : env type V) : expr V → type → Prop :=

| T_Unit :
  T[ Γ ⊢ e_unit ∷ t_unit ]

| T_Var x :
  T[ Γ ⊢ e_var x ∷ Γ x ]

| T_Fix e σ τ :
  T[ Γ ◃ t_arrow σ τ ◃ σ ⊢ e ∷ τ ] →
  T[ Γ ⊢ e_fix e ∷ t_arrow σ τ ]

| T_App e₁ e₂ σ τ :
  T[ Γ ⊢ e₁ ∷ t_arrow σ τ ] →
  T[ Γ ⊢ e₂ ∷ σ ] →
  T[ Γ ⊢ e_app e₁ e₂ ∷ τ ]

where "T[ Γ ⊢ e ∷ τ ]" := (@typing _ Γ e τ).
