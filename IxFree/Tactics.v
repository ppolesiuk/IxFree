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

(** Check if [H] is a valid IxFree proposition *)
Local Ltac is_ixfree H :=
  let _ := constr:(H : _ ⊨ _) in idtac.

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

Local Ltac idestruct_iprop_any H :=
  tryif is_hyp H then
    apply I_prop_elim in H
  else
    let H1 := fresh "H" in
    assert (H1 := I_prop_elim _ H).

Local Ltac idestruct_iprop_as H H_new :=
  tryif is_hyp H then
    apply I_prop_elim in H;
    rename H into H_new
  else
    assert (H_new := I_prop_elim _ H).

Local Tactic Notation
    "idestruct_iprop" constr(H) "as" simple_intropattern(p) :=
  (tryif is_hyp H then
    apply I_prop_elim in H; revert H
  else
    generalize (I_prop_elim _ H)); intros p.

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

Local Ltac idestruct_conj_as H H1 H2 :=
  tryif is_hyp H then
    apply I_conj_elim in H;
    destruct H as [ H1 H2 ]
  else
    destruct (I_conj_elim _ _ H) as [ H1 H2 ].

Local Ltac idestruct_conj_any H :=
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  idestruct_conj_as H H1 H2.

(* ------------------------------------------------------------------------- *)
(** *** Disjunction *)

(** Ensures that given term is a proof of disjunction. Fails otherwise. *)
Local Ltac is_disj H :=
  let _ := constr:(H : _ ⊨ _ ∨ᵢ _) in idtac.

(** Ensures that the goal is a disjunction. On success, it reduces the goal
  to the form of a disjunction, possibly unfolding some definitions. *)
Local Ltac goal_is_disj :=
  refine (_ : _ ⊨ _ ∨ᵢ _).

Local Ltac idestruct_disj_as H H1 H2 :=
  tryif is_hyp H then
    apply I_disj_elim in H;
    destruct H as [ H1 | H2 ]
  else
    destruct (I_disj_elim _ _ H) as [ H1 | H2 ].

Local Ltac idestruct_disj_any H :=
  tryif is_hyp H then
    apply I_disj_elim in H;
    destruct H as [ H | H ]
  else
    let H1 := fresh "H" in
    destruct (I_disj_elim _ _ H) as [ H1 | H1 ].

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

Local Ltac idestruct_exists_any H :=
  tryif is_hyp H then
    apply I_exists_elim in H;
    destruct H
  else
    destruct (I_exists_elim _ _ H).

Local Tactic Notation "idestruct_exists" constr(H) "as"
    simple_intropattern(p) simple_intropattern(Hr) :=
  tryif is_hyp H then
    apply I_exists_elim in H;
    destruct H as [ p Hr ]
  else
    destruct (I_exists_elim _ _ H) as [ p Hr ].

(* ------------------------------------------------------------------------- *)
(** *** Later *)

(** Ensures that given term is a proof of later. Fails otherwise. *)
Local Ltac is_later H :=
  let _ := constr:(H : _ ⊨ ▷ _) in idtac.

(** Ensures that the goal is a later modality. On success, it reduces the goal
  to the form of a later modality, possibly unfolding some definitions. *)
Local Ltac goal_is_later :=
  refine (_ : _ ⊨ ▷ _).

(** Assuming that [Hord] has type [W ⊏↓ w'] it changes all assumptions of the
  form [W ⊨ ▷ φ] into [w' ⊨ φ]. *)
Local Ltac move_later_assumptions W Hord :=
  repeat match goal with
  | [ H: W ⊨ ▷ ?P |- _ ] =>
    apply (I_later_elim P Hord) in H
  end.

(** Introduce a later. It changes goal of the form [w ⊨ ▷ φ] into [w ⊨ φ],
  and all assumptions of the form [w ⊨ ▷ ψ] into [w ⊨ ψ]. The new world [w] is
  always future world. *)
Local Ltac iintro_later :=
  name_worlds ltac:(fun W_old W_new =>
    refine (I_later_intro _ _);
    let Hord := fresh "Hord" in
    intros W_new Hord;
    move_later_assumptions W_old Hord;
    move_assumptions W_old (proj1 Hord);
    try clear W_old Hord
  ).

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

Local Ltac prepare_elim H ContTac :=
  tryif is_ixfree H then
    ContTac H
  else
    let H1 := fresh "Helim" in
    refine ((fun (H1 : _ ⊨ _) => _) _);
    cycle 1; [ eapply H | ContTac H1; clear H1 ].

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

Local Ltac iapply_in_hyp H Hyp :=
  tryif is_iprop H then
    apply (I_prop_elim _ H) in Hyp
  else tryif is_arrow H then
    let H1 := fresh "H" in
    first
    [ assert (H1 := I_arrow_elim _ _ H Hyp); clear Hyp; rename H1 into Hyp
    | refine ((fun H1 => _) (I_arrow_elim _ _ H _));
      cycle 1; [ | iapply_in_hyp H1 Hyp; clear H1 ]
    ]
  else tryif is_conj H then
    first
    [ iapply_in_hyp (I_conj_elim1 _ _ H) Hyp
    | iapply_in_hyp (I_conj_elim2 _ _ H) Hyp
    ]
  else tryif is_forall H then
    let H1 := fresh "H" in
    refine ((fun H1 => _) (I_forall_elim _ _ H _));
    [ iapply_in_hyp H1 Hyp; clear H1 ]
  else fail "cannot apply".

Local Ltac prepare_idestruct_main H ContTac :=
  tryif first [ is_iprop H | is_conj H | is_disj H | is_exists H ] then
    ContTac H
  else tryif is_arrow H then
    let H1 := fresh "H" in
    refine ((fun H1 => _) (I_arrow_elim _ _ H _));
    cycle 1; [ | prepare_idestruct_main (id H1) ContTac; clear H1 ]
  else tryif is_forall H then
    let H1 := fresh "H" in
    refine ((fun H1 => _) (I_forall_elim _ _ H _));
    [ prepare_idestruct_main (id H1) ContTac; clear H1 ]
  else
    let T := type of H in
    fail "cannot destruct " T.

Local Ltac prepare_idestruct H ContTac :=
  prepare_elim H ltac:(fun H1 => prepare_idestruct_main H1 ContTac).

Local Ltac idestruct_simple H :=
  tryif is_iprop H then
    idestruct_iprop_any H
  else tryif is_conj H then
    idestruct_conj_any H
  else tryif is_disj H then
    idestruct_disj_any H
  else tryif is_exists H then
    idestruct_exists_any H
  else
    let T := type of H in
    fail "cannot destruct " T.

Local Tactic Notation "idestruct_unary" constr(H) "as"
    simple_intropattern(p) :=
  tryif is_iprop H then
    idestruct_iprop H as p
  else tryif first [ is_conj H | is_disj H | is_exists H ] then
    let T := type of H in
    fail "idestruct on " T " expects two patterns"
  else
    let T := type of H in
    fail "cannot destruct " T.

Local Tactic Notation "idestruct_binary" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) :=
  tryif is_iprop H then
    fail "idestruct on (_)ᵢ expects one pattern"
  else tryif is_conj H then
    idestruct_conj_as H p1 p2
  else tryif is_disj H then
    idestruct_disj_as H p1 p2
  else tryif is_exists H then
    idestruct_exists H as p1 p2
  else
    let T := type of H in
    fail "cannot destruct " T.

Local Tactic Notation "idestruct_prefix" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) :=
  tryif is_iprop H then
    fail "idestruct on (_)ᵢ expects one pattern"
  else tryif is_conj H then
    idestruct_conj_as H p1 p2
  else tryif is_disj H then
    fail "idestruct on (_ ∨ᵢ )ᵢ expects two patterns"
  else tryif is_exists H then
    idestruct_exists H as p1 p2
  else
    let T := type of H in
    fail "cannot destruct " T.

Local Ltac ispecialize_one H t HCont :=
  let H1 := fresh H in
  tryif is_iprop H then
    refine ((fun H1 => _) (I_prop_elim _ H));
    clear H;
    rename H1 into H;
    ispecialize_one H t HCont
  else tryif is_arrow H then
    refine ((fun H1 => _) (I_arrow_elim _ _ H t));
    cycle 1; [ | simpl in H1; clear H; rename H1 into H; HCont ]
  else tryif is_forall H then
    refine ((fun H1 => _) (I_forall_elim _ _ H t));
    cycle 1; [ simpl in H1; clear H; rename H1 into H; HCont ]
  else tryif is_ixfree H then
    let T := type of H in
    fail "cannot specialize" T
  else
    specialize (H t); [ HCont ].

Local Ltac igeneralize_one H :=
  generalize H;
  match goal with
  | [ |- _ → _ ] =>
    apply I_arrow_elim
  | _ =>
    apply I_forall_elim;
    refine (_ : _ ⊨ ∀ᵢ H, _)
  end.

Local Ltac irevert_one H :=
  igeneralize_one H; clear H.

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
Tactic Notation "iapply" uconstr(H) :=
  prepare_elim H iapply_in_goal.

Tactic Notation "iapply" uconstr(H) "in" hyp(Hyp) :=
  prepare_elim H ltac:(fun H1 => iapply_in_hyp H1 Hyp).

(** The [idestruct] tactic is similar to standard the [edestruct] tactic.
  However, due to limitation of Ltac, all intro-patterns are given as separate
  parameters, and their meaning is right-associated tree. For instance,
  [idestruct H as x _ [ y z ] H1 H2] should behave similar to
  [edestruct H as [ x [ _ [ [ y z ] [ H1 H2 ] ] ] ]] or
  [edestruct H as [ x [ _ [ [ y z ] [ H1 | H2 ] ] ] ]]. Each intro-pattern
  should be trivial, except patterns for existentially quantified variables
  ([[ y z ]] in above example). Only the last two patterns can be disjunctive,
  if the destructed formula is a disjunction. *)
Tactic Notation "idestruct" constr(H) :=
  prepare_idestruct H idestruct_simple.

Tactic Notation "idestruct" constr(H) "as" simple_intropattern(p) :=
  prepare_idestruct H ltac:(fun H1 => idestruct_unary H1 as p).

Tactic Notation "idestruct" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) :=
  prepare_idestruct H ltac:(fun H1 => idestruct_binary H1 as p1 p2).

Tactic Notation "idestruct" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) simple_intropattern(p3) :=
  let Ht := fresh "H_temp" in
  prepare_idestruct H  ltac:(fun H1 => idestruct_prefix H1 as p1 Ht;
  prepare_idestruct Ht ltac:(fun H2 => idestruct_binary H2 as p2 p3;
  try clear Ht)).

Tactic Notation "idestruct" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) simple_intropattern(p3)
    simple_intropattern(p4) :=
  let Ht1 := fresh "H_temp" in
  let Ht2 := fresh "H_temp" in
  prepare_idestruct H   ltac:(fun H1 => idestruct_prefix H1 as p1 Ht1;
  prepare_idestruct Ht1 ltac:(fun H2 => idestruct_prefix H2 as p2 Ht2;
  prepare_idestruct Ht2 ltac:(fun H3 => idestruct_binary H3 as p3 p4;
  try clear Ht1; try clear Ht2))).

Tactic Notation "idestruct" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) simple_intropattern(p3)
    simple_intropattern(p4) simple_intropattern(p5) :=
  let Ht1 := fresh "H_temp" in
  let Ht2 := fresh "H_temp" in
  let Ht3 := fresh "H_temp" in
  prepare_idestruct H   ltac:(fun H1 => idestruct_prefix H1 as p1 Ht1;
  prepare_idestruct Ht1 ltac:(fun H2 => idestruct_prefix H2 as p2 Ht2;
  prepare_idestruct Ht2 ltac:(fun H3 => idestruct_prefix H3 as p3 Ht3;
  prepare_idestruct Ht3 ltac:(fun H4 => idestruct_binary H4 as p4 p5;
  try clear Ht1; try clear Ht2; try clear Ht3)))).

Tactic Notation "idestruct" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) simple_intropattern(p3)
    simple_intropattern(p4) simple_intropattern(p5) simple_intropattern(p6) :=
  let Ht1 := fresh "H_temp" in
  let Ht2 := fresh "H_temp" in
  let Ht3 := fresh "H_temp" in
  let Ht4 := fresh "H_temp" in
  prepare_idestruct H   ltac:(fun H1 => idestruct_prefix H1 as p1 Ht1;
  prepare_idestruct Ht1 ltac:(fun H2 => idestruct_prefix H2 as p2 Ht2;
  prepare_idestruct Ht2 ltac:(fun H3 => idestruct_prefix H3 as p3 Ht3;
  prepare_idestruct Ht3 ltac:(fun H4 => idestruct_prefix H4 as p4 Ht4;
  prepare_idestruct Ht4 ltac:(fun H5 => idestruct_binary H5 as p5 p6;
  try clear Ht1; try clear Ht2; try clear Ht3; try clear Ht4))))).

Tactic Notation "idestruct" constr(H) "as"
    simple_intropattern(p1) simple_intropattern(p2) simple_intropattern(p3)
    simple_intropattern(p4) simple_intropattern(p5) simple_intropattern(p6)
    simple_intropattern(p7) :=
  let Ht1 := fresh "H_temp" in
  let Ht2 := fresh "H_temp" in
  let Ht3 := fresh "H_temp" in
  let Ht4 := fresh "H_temp" in
  let Ht5 := fresh "H_temp" in
  prepare_idestruct H   ltac:(fun H1 => idestruct_prefix H1 as p1 Ht1;
  prepare_idestruct Ht1 ltac:(fun H2 => idestruct_prefix H2 as p2 Ht2;
  prepare_idestruct Ht2 ltac:(fun H3 => idestruct_prefix H3 as p3 Ht3;
  prepare_idestruct Ht3 ltac:(fun H4 => idestruct_prefix H4 as p4 Ht4;
  prepare_idestruct Ht4 ltac:(fun H5 => idestruct_prefix H5 as p5 Ht5;
  prepare_idestruct Ht5 ltac:(fun H6 => idestruct_binary H6 as p6 p7;
  try clear Ht1; try clear Ht2; try clear Ht3; try clear Ht4;
  try clear Ht5)))))).

(** The [ispecialize] tactic is similar to standard the [specialize] tactic.
  However, since the tactic uses refine, the provided terms can contain some
  placeholders. *)
Tactic Notation "ispecialize" hyp(H) uconstr(t1) :=
  ispecialize_one H t1 idtac.

Tactic Notation "ispecialize" hyp(H) uconstr(t1) uconstr(t2) :=
  ispecialize_one H t1 ltac:(
  ispecialize_one H t2 idtac).

Tactic Notation "ispecialize" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) :=
  ispecialize_one H t1 ltac:(
  ispecialize_one H t2 ltac:(
  ispecialize_one H t3 idtac)).

Tactic Notation "ispecialize" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3)
    uconstr(t4) :=
  ispecialize_one H t1 ltac:(
  ispecialize_one H t2 ltac:(
  ispecialize_one H t3 ltac:(
  ispecialize_one H t4 idtac))).

Tactic Notation "ispecialize" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3)
    uconstr(t4) uconstr(t5) :=
  ispecialize_one H t1 ltac:(
  ispecialize_one H t2 ltac:(
  ispecialize_one H t3 ltac:(
  ispecialize_one H t4 ltac:(
  ispecialize_one H t5 idtac)))).

Tactic Notation "ispecialize" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3)
    uconstr(t4) uconstr(t5) uconstr(t6) :=
  ispecialize_one H t1 ltac:(
  ispecialize_one H t2 ltac:(
  ispecialize_one H t3 ltac:(
  ispecialize_one H t4 ltac:(
  ispecialize_one H t5 ltac:(
  ispecialize_one H t6 idtac))))).

Tactic Notation "ispecialize" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3)
    uconstr(t4) uconstr(t5) uconstr(t6) uconstr(t7) :=
  ispecialize_one H t1 ltac:(
  ispecialize_one H t2 ltac:(
  ispecialize_one H t3 ltac:(
  ispecialize_one H t4 ltac:(
  ispecialize_one H t5 ltac:(
  ispecialize_one H t6 ltac:(
  ispecialize_one H t7 idtac)))))).

Tactic Notation "igeneralize" constr(H1) := igeneralize_one H1.
Tactic Notation "igeneralize" constr(H1) constr(H2) :=
  igeneralize_one H2; igeneralize_one H1.
Tactic Notation "igeneralize" constr(H1) constr(H2) constr(H3) :=
  igeneralize_one H3; igeneralize_one H2; igeneralize_one H1.
Tactic Notation "igeneralize" constr(H1) constr(H2) constr(H3) constr(H4) :=
  igeneralize_one H4; igeneralize_one H3; igeneralize_one H2;
  igeneralize_one H1.
Tactic Notation "igeneralize" constr(H1) constr(H2) constr(H3) constr(H4)
    constr(H5) :=
  igeneralize_one H5; igeneralize_one H4; igeneralize_one H3;
  igeneralize_one H2; igeneralize_one H1.
Tactic Notation "igeneralize" constr(H1) constr(H2) constr(H3) constr(H4)
    constr(H5) constr(H6) :=
  igeneralize_one H6; igeneralize_one H5; igeneralize_one H4;
  igeneralize_one H3; igeneralize_one H2; igeneralize_one H1.
Tactic Notation "igeneralize" constr(H1) constr(H2) constr(H3) constr(H4)
    constr(H5) constr(H6) constr(H7) :=
  igeneralize_one H7; igeneralize_one H6; igeneralize_one H5;
  igeneralize_one H4; igeneralize_one H3; igeneralize_one H2;
  igeneralize_one H1.

Tactic Notation "irevert" constr(H1) := irevert_one H1.
Tactic Notation "irevert" constr(H1) constr(H2) :=
  irevert_one H2; irevert_one H1.
Tactic Notation "irevert" constr(H1) constr(H2) constr(H3) :=
  irevert_one H3; irevert_one H2; irevert_one H1.
Tactic Notation "irevert" constr(H1) constr(H2) constr(H3) constr(H4) :=
  irevert_one H4; irevert_one H3; irevert_one H2; irevert_one H1.
Tactic Notation "irevert" constr(H1) constr(H2) constr(H3) constr(H4)
    constr(H5) :=
  irevert_one H5; irevert_one H4; irevert_one H3; irevert_one H2;
  irevert_one H1.
Tactic Notation "irevert" constr(H1) constr(H2) constr(H3) constr(H4)
    constr(H5) constr(H6) :=
  irevert_one H6; irevert_one H5; irevert_one H4; irevert_one H3;
  irevert_one H2; irevert_one H1.
Tactic Notation "irevert" constr(H1) constr(H2) constr(H3) constr(H4)
    constr(H5) constr(H6) constr(H7) :=
  irevert_one H7; irevert_one H6; irevert_one H5; irevert_one H4;
  irevert_one H3; irevert_one H2; irevert_one H1.
