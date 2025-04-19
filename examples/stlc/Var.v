Require Import Utf8.
Require Import Decidable.

Inductive inc {V : Set} : Set :=
| VZ
| VS (x : V)
.

Arguments inc V : clear implicits.

Lemma inc_eq_dec {V : Set} (eq_dec : ∀ x y : V, decidable (x = y)) :
  ∀ x y : inc V, decidable (x = y).
Proof.
  unfold decidable; decide equality; apply eq_dec.
Qed.

Definition vset : Set := nat.

Fixpoint var (V : vset) : Set :=
  match V with
  | 0   => Empty_set
  | S V => inc (var V)
  end.

Coercion var : vset >-> Sortclass.

Lemma var_eq_dec {V : vset} : ∀ x y : V, decidable (x = y).
Proof.
  induction V.
  + intros [].
  + intros; apply inc_eq_dec; assumption.
Qed.

Definition env (X : Set) (V : vset) := V → X.

Definition env_empty {X : Set} : env X 0 :=
  λ x, match x with end.

Definition env_ext {X : Set} {V : vset} (Env : env X V) (El : X) :
    env X (S V) :=
  λ x, match x with
       | VZ   => El
       | VS y => Env y
       end.

Notation "Env ◃ El" := (env_ext Env El) (at level 40).
