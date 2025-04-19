Require Import Utf8.
Require Import Var STLC.
Require Import Relation_Operators.

Inductive value : Type :=
| v_unit
| v_clo {V : vset} (ρ : env value V) (e : expr (S (S V)))
.

Inductive cont : Type :=
| k_init
| k_app1 {V : vset} (κ : cont) (e : expr V) (ρ : env value V)
| k_app2 (v : value) (κ : cont)
.

Inductive conf : Type :=
| c_done (v : value)
| c_eval {V : vset} (e : expr V) (ρ : env value V) (κ : cont)
| c_cont (κ : cont) (v : value)
.

Inductive is_done : conf → Prop :=
| conf_is_done v : is_done (c_done v)
.

Inductive step : conf → conf → Prop :=
| eval_unit {V : vset} (ρ : env value V) κ :
    step (c_eval e_unit ρ κ)
         (c_cont κ v_unit)

| eval_var {V : vset} (x : V) (ρ : env value V) κ :
    step (c_eval (e_var x) ρ κ)
         (c_cont κ (ρ x))

| eval_fix {V : vset} e (ρ : env value V) κ :
    step (c_eval (e_fix e) ρ κ)
         (c_cont κ (v_clo ρ e))

| eval_app {V : vset} e₁ e₂ (ρ : env value V) κ :
    step (c_eval (e_app e₁ e₂) ρ κ)
         (c_eval e₁ ρ (k_app1 κ e₂ ρ))

| cont_app1 {V : vset} (e : expr V) (ρ : env value V) κ v :
    step (c_cont (k_app1 κ e ρ) v)
         (c_eval e ρ (k_app2 v κ))

| cont_app2 {V : vset} (ρ : env value V) e κ v :
    step (c_cont (k_app2 (v_clo ρ e) κ) v)
         (c_eval e (ρ ◃ v_clo ρ e ◃ v) κ)

| cont_init v :
    step (c_cont k_init v) (c_done v)
.

Notation step_rtc := (clos_refl_trans_1n conf step).

Definition safe c : Prop :=
  ∀ c', step_rtc c c' → is_done c' ∨ ∃ c'', step c' c''.

(* ========================================================================= *)

Require Import Eqdep_dec.

Lemma cant_step_when_done c c' :
  is_done c → ¬ step c c'.
Proof.
  intros []; inversion 1.
Qed.

Lemma step_deterministic {c c₁ c₂} : step c c₁ → step c c₂ → c₁ = c₂.
Proof.
  destruct 1; inversion 1;
    repeat lazymatch goal with
    | [ H: existT _ _ _ = existT _ _ _ |- _ ] =>
      apply inj_pair2_eq_dec in H; [ subst | decide equality ]
    end; reflexivity.
Qed.
