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
(** *** Implication *)

(** Fails if given term is not a proof of implication. *)
Local Ltac is_arrow H :=
  let _ := constr:(H : _ ⊨ _ →ᵢ _) in idtac.

(** Fails if the goal is not an implication. On success, it reduces the goal
  to the form of an implication, possibly unfolding some definitions. *)
Local Ltac goal_is_arrow :=
  refine (_ : _ ⊨ _ →ᵢ _).

(** The main tactic for introducing arrow. It changes the goal of the form
  [w ⊨ φ →ᵢ ψ] to [w ⊨ φ → w ⊨ ψ]. The new world [w] is a possibly future
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
(** *** Introduction rules *)

Local Ltac iintro_named H :=
  tryif goal_is_arrow then iintro_arrow_named H
  else fail "cannot introduce".

Local Ltac iintro_anon :=
  tryif goal_is_arrow then iintro_arrow_anon
  else fail "cannot introduce".

Local Tactic Notation "iintro_pattern" simple_intropattern(p) :=
  tryif goal_is_arrow then iintro_arrow_main; intros p
  else fail "cannot introduce".

Local Ltac iintros_all :=
  repeat iintro_anon.

(* ------------------------------------------------------------------------- *)
(** *** Elimination rules *)

Local Ltac iapply_in_goal H :=
  first
  [ exact H
  | tryif is_arrow H then
      let H1 := fresh "H" in
      refine ((fun H1 => _) (I_arrow_elim _ _ H _));
      cycle 1; [ | iapply_in_goal H1; clear H1 ]
    else fail "cannot apply"
  ].

(* end details *)

(* ========================================================================= *)
(** ** Introduction rules *)

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

(* ========================================================================= *)
(** ** Elimination rules *)

Tactic Notation "iapply" constr(H) :=
  iapply_in_goal H.
