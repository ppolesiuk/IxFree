Require Import Utf8.

Definition monotone {A B : Type}
    (A_le : A → A → Prop) (B_le : B → B → Prop) (f : A → B) : Prop :=
  ∀ x y, A_le x y → B_le (f x) (f y).

Record mon_arrow {A B : Type}
    (A_le : A → A → Prop) (B_le : B → B → Prop) : Type :=
  { ma_apply    : A → B
  ; ma_monotone : monotone A_le B_le ma_apply
  }.

Coercion ma_apply : mon_arrow >-> Funclass.

Module Type WorldDescr.
  Parameter PreSemType    : Type.
  Parameter PreSemType_le : PreSemType → PreSemType → Prop.

  (** Functor that makes World out of ▷SemType *)
  Parameter WorldF : Type → Type.

  (** Functorial operation on maps *)
  Parameter WorldF_map :
    ∀ {STA STB : Type}, (STA → STB) → WorldF STA → WorldF STB.

  (** Order on worlds at the same level *)
  Parameter WorldF_le :
    ∀ {SemType : Type}, WorldF SemType → WorldF SemType → Prop.
End WorldDescr.

Module Make(WD : WorldDescr).

Definition mk_SemType {W : Type} (W_le : W → W → Prop) :=
  mon_arrow W_le WD.PreSemType_le.

Definition mk_layer {W : Type} (W_le : W → W → Prop) :=
  WD.WorldF (mk_SemType W_le).

Inductive mk_world {W : Type} (W_le : W → W → Prop) : Type :=
| mw_here  : mk_layer W_le → mk_world W_le
| mw_there : W → mk_world W_le
.

Arguments mw_here  {W} {W_le}.
Arguments mw_there {W} {W_le}.

Record World_str : Type :=
  { ws_world : Type
      (** Worlds below current level *)

  ; ws_world_le : ws_world → ws_world → Prop
      (** Order on worlds below *)

  ; ws_next_world_le : mk_world ws_world_le → mk_world ws_world_le → Prop
      (** Order on worlds, including current level *)

  ; ws_stlift : mk_SemType ws_next_world_le → mk_SemType ws_world_le
      (** Move SemType from one world to the layer below *)
  }.

Definition ws_lift (W : World_str) :
    mk_layer W.(ws_next_world_le) → mk_layer W.(ws_world_le) :=
  WD.WorldF_map W.(ws_stlift).

(* ========================================================================= *)
(* Level 0 *)

Definition ws_world_le_Z (w₁ w₂ : Empty_set) : Prop :=
  match w₁ with end.

Definition ws_next_world_le_Z (w₁ w₂ : mk_world ws_world_le_Z) : Prop :=
  match w₁, w₂ with
  | mw_here w₁, mw_here w₂ => WD.WorldF_le w₁ w₂
  | _, mw_there w => match w with end
  | mw_there w, _ => match w with end
  end.

Lemma ws_stlift_Z_monotone :
  monotone ws_world_le_Z WD.PreSemType_le (λ x, match x with end).
Proof.
  intros [].
Qed.

Definition ws_stlift_Z (R : mk_SemType ws_next_world_le_Z) :
    mk_SemType ws_world_le_Z :=
  {| ma_monotone := ws_stlift_Z_monotone |}.

Definition World_Z : World_str :=
  {| ws_world         := Empty_set
   ; ws_world_le      := ws_world_le_Z
   ; ws_next_world_le := ws_next_world_le_Z
   ; ws_stlift        := ws_stlift_Z
  |}.

(* ========================================================================= *)
(* Next level *)

Definition ws_next_world_le_S (W : World_str)
    (w₁ w₂ : mk_world W.(ws_next_world_le)) : Prop :=
  match w₁, w₂ with
  | mw_here w₁, mw_here w₂  => WD.WorldF_le w₁ w₂
  | mw_here w₁, mw_there w₂ =>
      W.(ws_next_world_le) (mw_here (ws_lift W w₁)) w₂
  | mw_there w₁, mw_there w₂ =>
      W.(ws_next_world_le) w₁ w₂
  | mw_there _, mw_here _ => False
  end.

Definition ws_stlift_S_func (W : World_str)
    (R : mk_SemType (ws_next_world_le_S W))
    (w : mk_world (ws_world_le W)) : WD.PreSemType :=
  R (mw_there w).

Lemma ws_stlift_S_monotone (W : World_str)
  (R : mk_SemType (ws_next_world_le_S W)) :
    monotone (ws_next_world_le W) WD.PreSemType_le
      (ws_stlift_S_func W R).
Proof.
  intros x y Hxy; unfold ws_stlift_S_func.
  apply ma_monotone; simpl.
  assumption.
Qed.

Definition ws_stlift_S (W : World_str)
  (R : mk_SemType (ws_next_world_le_S W)) :
    mk_SemType W.(ws_next_world_le) :=
  {| ma_monotone := ws_stlift_S_monotone W R |}.

Definition World_S (W : World_str) : World_str :=
  {| ws_world         := mk_world W.(ws_world_le)
   ; ws_world_le      := W.(ws_next_world_le)
   ; ws_next_world_le := ws_next_world_le_S W
   ; ws_stlift        := ws_stlift_S W
  |}.

(* ========================================================================= *)
(* Iterative construction of worlds *)

Fixpoint World_it (n : nat) : World_str :=
  match n with
  | 0   => World_Z
  | S n => World_S (World_it n)
  end.

Definition World_at n : Type :=
  mk_layer (World_it n).(ws_world_le).

Definition World_le_at n : World_at n → World_at n → Prop :=
  WD.WorldF_le.

Definition World_lift (n : nat) : World_at (S n) → World_at n :=
  ws_lift (World_it n).

Inductive sle (m : nat) : nat → Set :=
| sle_refl : sle m m
| sle_S    : ∀ n, sle m n → sle m (S n)
.

Arguments sle_refl {m}.
Arguments sle_S    {m}.

Fixpoint World_le_at2 {n m : nat} (LE : sle m n) :
    World_at n → World_at m → Prop :=
  match LE with
  | sle_refl   => World_le_at m
  | sle_S n LE => λ w, World_le_at2 LE (World_lift _ w)
  end.

(* ========================================================================= *)
(* World preorder *)

Record World : Type :=
  { w_index : nat
  ; w_layer : World_at w_index
  }.

Inductive World_le (w₁ w₂ : World) : Prop :=
| wle : ∀ LE : sle (w_index w₂) (w_index w₁),
  World_le_at2 LE (w_layer w₁) (w_layer w₂) → World_le w₁ w₂
.

End Make.