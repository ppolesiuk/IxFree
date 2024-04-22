(* This file is part of IxFree, released under MIT license.
 * See LICENSE for details.
 *)
Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.

(** * Tactics *)

(* ========================================================================= *)
(** ** Helper Tactics

IxFree uses shallow embedding, and therefore allows to reuse many existing
Coq tactics, e.g., for induction, manipulating proof context, etc.. However,
the library requires own tactics for introduction and elimination of logic
connectives. These tactics are written in pure Ltac, which required some extra
amount of work. In this section we define helper tactic, not intended to use
by the user of the library. *)

(* begin details *)
(* ------------------------------------------------------------------------- *)
(** *** General Tactics *)

(** Check if [H] is a hypothesis. *)
Local Ltac is_hyp H :=
  assert_succeeds (rename H into H).

(** Rename the current world name (if possible) and create a fresh name for a
  new world. It tries to use old name if possible. Renamed old world and a name
  for a new world are passed as parameters to [ContTac]. *)
Local Ltac name_worlds ContTac :=
  match goal with
  | [ |- ?W ⊨ _ ] =>
    tryif is_hyp W then
      let W_old := fresh W in
      rename W into W_old;
      ContTac W_old W
    else
      let W_new := fresh "w" in
      ContTac W W_new
  end.

(** Assuming that [Hord] has type [W ⊑ w'], it moves all assumptions of the
  form [W ⊨ φ] to world [w']. *)
Local Ltac move_assumptions W Hord :=
  repeat match goal with
  | [ H: W ⊨ ?P |- _ ] =>
    apply (I_valid_monotone P Hord) in H
  end.

(* ------------------------------------------------------------------------- *)
(** *** Prop embedding *)

(** Ensures that given term is a proof of embedded proposition. Fails
  otherwise. *)
Local Ltac is_iprop H :=
  let _ := constr:(H : _ ⊨ (_)ᵢ) in idtac.

(** Ensures that the goal is an embedded proposition. On success, it reduces
  the goal to the form of an embedded proposition, possibly unfolding some
  definitions. *)
Local Ltac goal_is_iprop :=
  refine (_ : _ ⊨ (_)ᵢ).

Local Ltac iintro_iprop :=
  refine (I_prop_intro _ _).

(* ------------------------------------------------------------------------- *)
(** *** Implication *)

(** Ensures that given term is a proof of implication. Fails otherwise. *)
Local Ltac is_arrow H :=
  let _ := constr:(H : _ ⊨ _ →ᵢ _) in idtac.

(** Ensures that the goal is an implication. On success, it reduces the goal
  to the form of an implication, possibly unfolding some definitions. *)
Local Ltac goal_is_arrow :=
  refine (_ : _ ⊨ _ →ᵢ _).

(** The main tactic for introducing arrow. It changes goal of the form
  [w ⊨ φ →ᵢ ψ] into [w ⊨ φ → w ⊨ ψ]. The new world [w] is a possibly future
  world. *)
Local Ltac iintro_arrow_main :=
  name_worlds ltac:(fun W_old W_new =>
    refine (I_arrow_intro _ _ _);
    let Hord := fresh "Hord" in
    intros W_new Hord;
    move_assumptions W_old Hord;
    try clear W_old Hord
  ).

Local Ltac iintro_arrow_anon :=
  iintro_arrow_main; intro.

Local Ltac iintro_arrow_named H :=
  iintro_arrow_main; intro H.

(* ------------------------------------------------------------------------- *)
(** *** Conjunction *)

(** Ensures that given term is a proof of conjunction. Fails otherwise. *)
Local Ltac is_conj H :=
  let _ := constr:(H : _ ⊨ _ ∧ᵢ _) in idtac.

(** Ensures that the goal is a conjunction. On success, it reduces the goal
  to the form of a conjunction, possibly unfolding some definitions. *)
Local Ltac goal_is_conj :=
  refine (_ : _ ⊨ _ ∧ᵢ _).

(* ------------------------------------------------------------------------- *)
(** *** Disjunction *)

(** Ensures that given term is a proof of disjunction. Fails otherwise. *)
Local Ltac is_disj H :=
  let _ := constr:(H : _ ⊨ _ ∨ᵢ _) in idtac.

(** Ensures that the goal is a disjunction. On success, it reduces the goal
  to the form of a disjunction, possibly unfolding some definitions. *)
Local Ltac goal_is_disj :=
  refine (_ : _ ⊨ _ ∨ᵢ _).

(* ------------------------------------------------------------------------- *)
(** *** Universal quantifier *)

(** Ensures that given term is a proof of universal quantification. Fails
  otherwise. *)
Local Ltac is_forall H :=
  let _ := constr:(H : _ ⊨ ∀ᵢ _, _) in idtac.

(** Ensures that the goal is an universal quantification. On success, it
  reduces the goal to the form of an universal quantification, possibly
  unfolding some definitions. *)
Local Ltac goal_is_forall :=
  refine (_ : _ ⊨ ∀ᵢ _, _).

(** The main tactic for introducing universal quantifier. It changes goal of
  the form [w ⊨ ∀ᵢ x, φ] into [∀ x, w ⊨ φ]. *)
Local Ltac iintro_forall_main :=
  refine (I_forall_intro _ _ _).

Local Ltac iintro_forall_anon :=
  iintro_forall_main; intro.

Local Ltac iintro_forall_named H :=
  iintro_forall_main; intro H.

(* ------------------------------------------------------------------------- *)
(** *** Existential quantifier *)

(** Ensures that given term is a proof of existential quantification. Fails
  otherwise. *)
Local Ltac is_exists H :=
  let _ := constr:(H : _ ⊨ ∃ᵢ _, _) in idtac.

(** Ensures that the goal is an existential quantification. On success, it
  reduces the goal to the form of an existential quantification, possibly
  unfolding some definitions. *)
Local Ltac goal_is_exists :=
  refine (_ : _ ⊨ ∃ᵢ _, _).

Local Tactic Notation "iexists_main" uconstr(t) :=
  tryif goal_is_exists then
    refine (I_exists_intro _ _ t _)
  else
    fail "The goal is not an existential quantifier".

(* ------------------------------------------------------------------------- *)
(** *** Later *)

(** Ensures that given term is a proof of later. Fails otherwise. *)
Local Ltac is_later H :=
  let _ := constr:(H : _ ⊨ ▷ _) in idtac.

(** Ensures that the goal is a later modality. On success, it reduces the goal
  to the form of a later modality, possibly unfolding some definitions. *)
Local Ltac goal_is_later :=
  refine (_ : _ ⊨ ▷ _).

(** Assuming that [Hord] has type [W ⊑ w'], and [Hidx] has type
  [world_index w' < world_index w] it changes all assumptions of the
  form [W ⊨ ▷ φ] into [w' ⊨ φ]. *)
Local Ltac move_later_assumptions W Hord Hidx :=
  repeat match goal with
  | [ H: W ⊨ ▷ ?P |- _ ] =>
    apply (I_later_elim P Hord Hidx) in H
  end.

(** Introduce a later. It changes goal of the form [w ⊨ ▷ φ] into [w ⊨ φ],
  and all assumptions of the form [w ⊨ ▷ ψ] into [w ⊨ ψ]. The new world [w] is
  always future world. *)
Local Ltac iintro_later :=
  name_worlds ltac:(fun W_old W_new =>
    refine (I_later_intro _ _);
    let Hord := fresh "Hord" in
    let Hidx := fresh "Hidx" in
    intros W_new Hord Hidx;
    move_later_assumptions W_old Hord Hidx;
    move_assumptions W_old Hord;
    try clear W_old Hord Hidx
  ).

Local Ltac loeb_induction_named IH :=
  match goal with
  | [ |- _ ⊨ ?P ] =>
    apply (I_loeb_induction P);
    iintro_arrow_named IH
  end.

Local Ltac loeb_induction_anon :=
  let IH := fresh "IH" in
  loeb_induction_named IH.

(* ------------------------------------------------------------------------- *)
(** *** Introduction rules *)

Local Ltac iintro_named H :=
  tryif goal_is_arrow then iintro_arrow_named H
  else tryif goal_is_forall then iintro_forall_named H
  else fail "cannot introduce".

Local Ltac iintro_anon :=
  tryif goal_is_iprop then iintro_iprop
  else tryif goal_is_arrow then iintro_arrow_anon
  else tryif goal_is_forall then iintro_forall_anon
  else tryif goal_is_later then iintro_later
  else fail "cannot introduce".

Local Tactic Notation "iintro_pattern" simple_intropattern(p) :=
  tryif goal_is_arrow then iintro_arrow_main; intros p
  else tryif goal_is_forall then iintro_forall_main; intros p
  else fail "cannot introduce".

Local Ltac iintros_all :=
  repeat
    tryif goal_is_arrow then iintro_arrow_anon
    else tryif goal_is_forall then iintro_forall_anon
    else fail.

(* ------------------------------------------------------------------------- *)
(** *** Elimination rules *)

Local Ltac iapply_in_goal H :=
  first
  [ exact H
  | tryif is_iprop H then
      apply (I_prop_elim _ H)
    else tryif is_arrow H then
      let H1 := fresh "H" in
      refine ((fun H1 => _) (I_arrow_elim _ _ H _));
      cycle 1; [ | iapply_in_goal H1; clear H1 ]
    else tryif is_conj H then
      first
      [ iapply_in_goal (I_conj_elim1 _ _ H)
      | iapply_in_goal (I_conj_elim2 _ _ H)
      ]
    else tryif is_forall H then
      let H1 := fresh "H" in
      refine ((fun H1 => _) (I_forall_elim _ _ H _));
      [ iapply_in_goal H1; clear H1 ]
    else fail "cannot apply"
  ].

(* end details *)

(* ========================================================================= *)
(** ** Introduction rules *)

(** Tactics [iintro] and [iintros] imitates standard [intro] and [intros]
  tactics. *)

Tactic Notation "iintro" := iintro_anon.
Tactic Notation "iintro" ident(H) := iintro_named H.

Tactic Notation "iintros" := iintros_all.
Tactic Notation "iintros"
    simple_intropattern(p1) :=
  iintro_pattern p1.
Tactic Notation "iintros"
    simple_intropattern(p1)
    simple_intropattern(p2) :=
  iintro_pattern p1; iintro_pattern p2.
Tactic Notation "iintros"
    simple_intropattern(p1)
    simple_intropattern(p2)
    simple_intropattern(p3) :=
  iintro_pattern p1; iintro_pattern p2; iintro_pattern p3.
Tactic Notation "iintros"
    simple_intropattern(p1)
    simple_intropattern(p2)
    simple_intropattern(p3)
    simple_intropattern(p4) :=
  iintro_pattern p1; iintro_pattern p2; iintro_pattern p3; iintro_pattern p4.
Tactic Notation "iintros"
    simple_intropattern(p1)
    simple_intropattern(p2)
    simple_intropattern(p3)
    simple_intropattern(p4)
    simple_intropattern(p5) :=
  iintro_pattern p1; iintro_pattern p2; iintro_pattern p3; iintro_pattern p4;
  iintro_pattern p5.
Tactic Notation "iintros"
    simple_intropattern(p1)
    simple_intropattern(p2)
    simple_intropattern(p3)
    simple_intropattern(p4)
    simple_intropattern(p5)
    simple_intropattern(p6) :=
  iintro_pattern p1; iintro_pattern p2; iintro_pattern p3; iintro_pattern p4;
  iintro_pattern p5; iintro_pattern p6.
Tactic Notation "iintros"
    simple_intropattern(p1)
    simple_intropattern(p2)
    simple_intropattern(p3)
    simple_intropattern(p4)
    simple_intropattern(p5)
    simple_intropattern(p6)
    simple_intropattern(p7) :=
  iintro_pattern p1; iintro_pattern p2; iintro_pattern p3; iintro_pattern p4;
  iintro_pattern p5; iintro_pattern p6; iintro_pattern p7.

(** Splitting conjunction goal into two subgoals. *)
Ltac isplit :=
  tryif goal_is_conj then refine (I_conj_intro _ _ _ _)
  else fail "The goal is not a conjunction".

(** Introduction of disjunction *)
Ltac ileft :=
  tryif goal_is_disj then refine (I_disj_intro1 _ _ _)
  else fail "The goal is not a disjunction".
Ltac iright :=
  tryif goal_is_disj then refine (I_disj_intro2 _ _ _)
  else fail "The goal is not a disjunction".

(** Introduction of existential quantifier. The [iexists] tactic imitates
  the standard [eexists] tactic. *)
Tactic Notation "iexists" := iexists_main _.
Tactic Notation "iexists"
    uconstr(t1) :=
  iexists_main t1.
Tactic Notation "iexists"
    uconstr(t1) uconstr(t2) :=
  iexists_main t1; iexists_main t2.
Tactic Notation "iexists"
    uconstr(t1) uconstr(t2) uconstr(t3) :=
  iexists_main t1; iexists_main t2; iexists_main t3.
Tactic Notation "iexists"
    uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) :=
  iexists_main t1; iexists_main t2; iexists_main t3; iexists_main t4.
Tactic Notation "iexists"
    uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5) :=
  iexists_main t1; iexists_main t2; iexists_main t3; iexists_main t4;
  iexists_main t5.
Tactic Notation "iexists"
    uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5) uconstr(t6) :=
  iexists_main t1; iexists_main t2; iexists_main t3; iexists_main t4;
  iexists_main t5; iexists_main t6.
Tactic Notation "iexists"
    uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5) uconstr(t6)
    uconstr(t7) :=
  iexists_main t1; iexists_main t2; iexists_main t3; iexists_main t4;
  iexists_main t5; iexists_main t6; iexists_main t7.

(** Later can be introduced using [iintro] tactic without any parameters, but
  we also define its specialized version to increase proof readiblity. It
  changes goal of the form [w ⊨ ▷ φ] into [w ⊨ φ], and all assumptions of the
  form [w ⊨ ▷ ψ] into [w ⊨ ψ]. *)
Ltac later_shift := 
  tryif goal_is_later then iintro_later
  else fail "The goal is not of the form ?w ⊨ ▷ ?φ".

(* ========================================================================= *)
(** ** Elimination rules *)

(** The [iapply] tactic is similar to standard the [eapply] tactic. *)
Tactic Notation "iapply" constr(H) := iapply_in_goal H.

(* ========================================================================= *)
(** ** Other tactics *)

(** The key feature of step-indexed logic with later modality is an induction
over step-indices, called Löb induction. When the goal is [w ⊨ φ], these
tactics introduces an assumption [w ⊨ ▷ φ]. The name of this assumption can
be provided as a parameter for [loeb_induction] tactic. If [loeb_induction]
is used without a name, the default name [IH] is used. *)
Tactic Notation "loeb_induction" := loeb_induction_anon.
Tactic Notation "loeb_induction" ident(H) := loeb_induction_named H.
