(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import List.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Inductive Types}% *)

(** In a sense, CIC is built from just two relatively straightforward features: function types and inductive types.  From this modest foundation, we can prove effectively all of the theorems of math and carry out effectively all program verifications, with enough effort expended.  This chapter introduces induction and recursion in Coq and shares some "design patterns" for overcoming common pitfalls with them. *)


(** * Enumerations *)

(** Coq inductive types generalize the algebraic datatypes found in Haskell and ML.  Confusingly enough, inductive types also generalize generalized algebraic datatypes (GADTs), by adding the possibility for type dependency.  Even so, it is worth backing up from the examples of the last chapter and going over basic, algebraic datatype uses of inductive datatypes, because the chance to prove things about the values of these types adds new wrinkles beyond usual practice in Haskell and ML.

The singleton type [unit] is an inductive type: *)

Inductive unit : Set :=
  | tt.

(** This vernacular command defines a new inductive type [unit] whose only value is [tt], as we can see by checking the types of the two identifiers: *)

Check unit.
(** [[

  unit : Set
]] *)
Check tt.
(** [[

  tt : unit
]] *)

(** We can prove that [unit] is a genuine singleton type. *)

Theorem unit_singleton : forall x : unit, x = tt.
(** The important thing about an inductive type is, unsurprisingly, that you can do induction over its values, and induction is the key to proving this theorem.  We ask to proceed by induction on the variable [x]. *)
  induction x.
(** The goal changes to: [[

 tt = tt
]] *)
  (** ...which we can discharge trivially. *)
  reflexivity.
Qed.

(** It seems kind of odd to write a proof by induction with no inductive hypotheses.  We could have arrived at the same result by beginning the proof with: [[

  destruct x.
...which corresponds to "proof by case analysis" in classical math.  For non-recursive inductive types, the two tactics will always have identical behavior.  Often case analysis is sufficient, even in proofs about recursive types, and it is nice to avoid introducing unneeded induction hypotheses.

What exactly %\textit{%#<i>#is#</i>#%}% the induction principle for [unit]?  We can ask Coq: *)

Check unit_ind.
(** [[

unit_ind : forall P : unit -> Prop, P tt -> forall u : unit, P u
]]

Every [Inductive] command defining a type [T] also defines an induction principle named [T_ind].  Coq follows the Curry-Howard correspondence and includes the ingredients of programming and proving in the same single syntactic class.  Thus, our type, operations over it, and principles for reasoning about it all live in the same language and are described by the same type system.  The key to telling what is a program and what is a proof lies in the distinction between the type [Prop], which appears in our induction principle; and the type [Set], which we have seen a few times already.

The convention goes like this: [Set] is the type of normal types, and the values of such types are programs.  [Prop] is the type of logical propositions, and the values of such types are proofs.  Thus, an induction principle has a type that shows us that it is a function for building proofs.

Specifically, [unit_ind] quantifies over a predicate [P] over [unit] values.  If we can present a proof that [P] holds of [tt], then we are rewarded with a proof that [P] holds for any value [u] of type [unit].  In our last proof, the predicate was [(fun u : unit => u = tt)].

%\medskip%

We can define an inductive type even simpler than [unit]: *)

Inductive Empty_set : Set := .

(** [Empty_set] has no elements.  We can prove fun theorems about it: *)

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
  destruct 1.
Qed.

(** Because [Empty_set] has no elements, the fact of having an element of this type implies anything.  We use [destruct 1] instead of [destruct x] in the proof because unused quantified variables are relegated to being referred to by number.  (There is a good reason for this, related to the unity of quantifiers and dependent function types.)

We can see the induction principle that made this proof so easy: *)

Check Empty_set_ind.
(** [[

Empty_set_ind : forall (P : Empty_set -> Prop) (e : Empty_set), P e
]]

In other words, any predicate over values from the empty set holds vacuously of every such element.  In the last proof, we chose the predicate [(fun _ : Empty_set => 2 + 2 = 5)].

We can also apply this get-out-of-jail-free card programmatically.  Here is a lazy way of converting values of [Empty_set] to values of [unit]: *)

Definition e2u (e : Empty_set) : unit := match e with end.

(** We employ [match] pattern matching as in the last chapter.  Since we match on a value whose type has no constructors, there is no need to provide any branches.

%\medskip%

Moving up the ladder of complexity, we can define the booleans: *)

Inductive bool : Set :=
| true
| false.

(** We can use less vacuous pattern matching to define boolean negation. *)

Definition not (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

(** We might want to prove that [not] is its own inverse operation. *)

Theorem not_inverse : forall b : bool, not (not b) = b.
  destruct b.

  (** After we case analyze on [b], we are left with one subgoal for each constructor of [bool].

[[

2 subgoals
  
  ============================
   not (not true) = true
]]

[[
subgoal 2 is:
 not (not false) = false
]]

The first subgoal follows by Coq's rules of computation, so we can dispatch it easily: *)

  reflexivity.

(** Likewise for the second subgoal, so we can restart the proof and give a very compact justification. *)

Restart.
  destruct b; reflexivity.
Qed.
