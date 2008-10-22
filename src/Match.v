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


(** %\part{Proof Engineering}

   \chapter{Proof Search in Ltac}% *)

(** We have seen many examples of proof automation so far.  This chapter aims to give a principled presentation of the features of Ltac, focusing in particular on the Ltac [match] construct, which supports a novel approach to backtracking search.  First, though, we will run through some useful automation tactics that are built into Coq.  They are described in detail in the manual, so we only outline what is possible. *)

(** * Some Built-In Automation Tactics *)

(** A number of tactics are called repeatedly by [crush].  [intuition] simplifies propositional structure of goals.  [congruence] applies the rules of equality and congruence closure, plus properties of constructors of inductive types.  The [omega] tactic provides a complete decision procedure for a theory that is called quantifier-free linear arithmetic or Presburger arithmetic, depending on whom you ask.  That is, [omega] proves any goal that follows from looking only at parts of that goal that can be interpreted as propositional formulas whose atomic formulas are basic comparison operations on natural numbers or integers.

   The [ring] tactic solves goals by appealing to the axioms of rings or semi-rings (as in algebra), depending on the type involved.  Coq developments may declare new types to be parts of rings and semi-rings by proving the associated axioms.  There is a simlar tactic [field] for simplifying values in fields by conversion to fractions over rings.  Both [ring] and [field] can only solve goals that are equalities.  The [fourier] tactic uses Fourier's method to prove inequalities over real numbers, which are axiomatized in the Coq standard library.

   The %\textit{%#<i>#setoid#</i>#%}% facility makes it possible to register new equivalence relations to be understood by tactics like [rewrite].  For instance, [Prop] is registered as a setoid with the equivalence relation "if and only if."  The ability to register new setoids can be very useful in proofs of a kind common in math, where all reasoning is done after "modding out by a relation."

   We have seen [auto] and [eauto] put to good use.  Both are based on databases of hints to be applied in Prolog-style logic programming.  The most general form of [auto] hint is [Hint Extern], which takes the form [Hint Extern num pattern => tactic : db].  This command asks to apply [tactic] during an [auto] or [eauto] proof search with database [db], whenever the conclusion matches the pattern.  The pattern may bind variables to be used in the tactic.  The argument [num] assigns a cost to this rule.  When [auto] finds multiple applicable rules at some point during proof search, it tries them in increasing order of cost.  A normal [Hint Resolve lemma] adds [eapply lemma] as a hint with a cost equal to the number of subgoals that would be introduced.

   We have also seen many uses of [autorewrite], which is based on databases of quantified equalities for rewriting.  One feature which we have not focused on, but that is worth mentioning, is that each [Rewrite] hint may specify a tactic to use to discharge any subgoals required by the rewrite lemma.  By choosing a tactic like [solve [ trivial ]], which fails if [trivial] fails to prove the goal completely, we can prevent [autorewrite] from "going down the wrong path." *)

