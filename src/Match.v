(* Copyright (c) 2008-2011, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Proof Search in Ltac}% *)

(** We have seen many examples of proof automation so far, some with tantalizing code snippets from Ltac, Coq's domain-specific language for proof search procedures.  This chapter aims to give a bottom-up presentation of the features of Ltac, focusing in particular on the Ltac %\index{tactics!match}%[match] construct, which supports a novel approach to backtracking search.  First, though, we will run through some useful automation tactics that are built into Coq.  They are described in detail in the manual, so we only outline what is possible. *)

(** * Some Built-In Automation Tactics *)

(** A number of tactics are called repeatedly by [crush].  The %\index{tactics!intuition}%[intuition] tactic simplifies propositional structure of goals.  The %\index{tactics!congruence}%[congruence] tactic applies the rules of equality and congruence closure, plus properties of constructors of inductive types.  The %\index{tactics!omega}%[omega] tactic provides a complete decision procedure for a theory that is called %\index{linear arithmetic}%quantifier-free linear arithmetic or %\index{Presburger arithmetic}%Presburger arithmetic, depending on whom you ask.  That is, [omega] proves any goal that follows from looking only at parts of that goal that can be interpreted as propositional formulas whose atomic formulas are basic comparison operations on natural numbers or integers.

   The %\index{tactics!ring}%[ring] tactic solves goals by appealing to the axioms of rings or semi-rings (as in algebra), depending on the type involved.  Coq developments may declare new types to be parts of rings and semi-rings by proving the associated axioms.  There is a similar tactic %\index{tactics!field}\coqdockw{%#<tt>#field#</tt>#%}% for simplifying values in fields by conversion to fractions over rings.  Both [ring] and %\coqdockw{%#<tt>#field#</tt>#%}% can only solve goals that are equalities.  The %\index{tactics!fourier}\coqdockw{%#<tt>#fourier#</tt>#%}% tactic uses Fourier's method to prove inequalities over real numbers, which are axiomatized in the Coq standard library.

   The %\index{setoids}\textit{%#<i>#setoid#</i>#%}% facility makes it possible to register new equivalence relations to be understood by tactics like [rewrite].  For instance, [Prop] is registered as a setoid with the equivalence relation %``%#"#if and only if.#"#%''%  The ability to register new setoids can be very useful in proofs of a kind common in math, where all reasoning is done after %``%#"#modding out by a relation.#"#%''%

   There are several other built-in %``%#"#black box#"#%''% automation tactics, which one can learn about by perusing the Coq manual.  The real promise of Coq, though, is in the coding of problem-specific tactics with Ltac. *)


(** * Ltac Programming Basics *)

(** We have already seen many examples of Ltac programs.  In the rest of this chapter, we attempt to give a thorough introduction to the important features and design patterns.

   One common use for [match] tactics is identification of subjects for case analysis, as we see in this tactic definition. *)

(* begin thide *)
Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => destruct X
  end.
(* end thide *)

(** The tactic checks if the conclusion is an [if], [destruct]ing the test expression if so.  Certain classes of theorem are trivial to prove automatically with such a tactic. *)

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
(* begin thide *)
  intros; repeat find_if; constructor.
Qed.
(* end thide *)

(** The %\index{tactics!repeat}%[repeat] that we use here is called a %\index{tactical}\textit{%#<i>#tactical#</i>#%}%, or tactic combinator.  The behavior of [repeat t] is to loop through running [t], running [t] on all generated subgoals, running [t] on %\textit{%#<i>#their#</i>#%}% generated subgoals, and so on.  When [t] fails at any point in this search tree, that particular subgoal is left to be handled by later tactics.  Thus, it is important never to use [repeat] with a tactic that always succeeds.

   Another very useful Ltac building block is %\index{context patterns}\textit{%#<i>#context patterns#</i>#%}%. *)

(* begin thide *)
Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.
(* end thide *)

(** The behavior of this tactic is to find any subterm of the conclusion that is an [if] and then [destruct] the test expression.  This version subsumes [find_if]. *)

Theorem hmm' : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
(* begin thide *)
  intros; repeat find_if_inside; constructor.
Qed.
(* end thide *)

(** We can also use [find_if_inside] to prove goals that [find_if] does not simplify sufficiently. *)

Theorem hmm2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
(* begin thide *)
  intros; repeat find_if_inside; reflexivity.
Qed.
(* end thide *)

(** Many decision procedures can be coded in Ltac via %``%#"#[repeat match] loops.#"#%''%  For instance, we can implement a subset of the functionality of [tauto]. *)

(* begin thide *)
Ltac my_tauto :=
  repeat match goal with
	   | [ H : ?P |- ?P ] => exact H

	   | [ |- True ] => constructor
	   | [ |- _ /\ _ ] => constructor
	   | [ |- _ -> _ ] => intro

	   | [ H : False |- _ ] => destruct H
	   | [ H : _ /\ _ |- _ ] => destruct H
	   | [ H : _ \/ _ |- _ ] => destruct H

	   | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
	 end.
(* end thide *)

(** Since [match] patterns can share unification variables between hypothesis and conclusion patterns, it is easy to figure out when the conclusion matches a hypothesis.  The %\index{tactics!exact}%[exact] tactic solves a goal completely when given a proof term of the proper type.

   It is also trivial to implement the introduction rules (in the sense of %\index{natural deduction}%natural deduction%~\cite{TAPLNatDed}%) for a few of the connectives.  Implementing elimination rules is only a little more work, since we must give a name for a hypothesis to [destruct].

   The last rule implements modus ponens, using a tactic %\index{tactics!specialize}\coqdockw{%#<tt>#specialize#</tt>#%}% which will replace a hypothesis with a version that is specialized to a provided set of arguments (for quantified variables or local hypotheses from implications). *)

Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
(* begin thide *)
    my_tauto.
  Qed.
(* end thide *)
End propositional.

(** It was relatively easy to implement modus ponens, because we do not lose information by clearing every implication that we use.  If we want to implement a similarly complete procedure for quantifier instantiation, we need a way to ensure that a particular proposition is not already included among our hypotheses.  To do that effectively, we first need to learn a bit more about the semantics of [match].

It is tempting to assume that [match] works like it does in ML.  In fact, there are a few critical differences in its behavior.  One is that we may include arbitrary expressions in patterns, instead of being restricted to variables and constructors.  Another is that the same variable may appear multiple times, inducing an implicit equality constraint.

There is a related pair of two other differences that are much more important than the others.  The [match] construct has a %\textit{%#<i>#backtracking semantics for failure#</i>#%}%.  In ML, pattern matching works by finding the first pattern to match and then executing its body.  If the body raises an exception, then the overall match raises the same exception.  In Coq, failures in case bodies instead trigger continued search through the list of cases.

For instance, this (unnecessarily verbose) proof script works: *)

Theorem m1 : True.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
(* begin thide *)
Qed.
(* end thide *)

(** The first case matches trivially, but its body tactic fails, since the conclusion does not begin with a quantifier or implication.  In a similar ML match, that would mean that the whole pattern-match fails.  In Coq, we backtrack and try the next pattern, which also matches.  Its body tactic succeeds, so the overall tactic succeeds as well.

   The example shows how failure can move to a different pattern within a [match].  Failure can also trigger an attempt to find %\textit{%#<i>#a different way of matching a single pattern#</i>#%}%.  Consider another example: *)

Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
  intros; match goal with
            | [ H : _ |- _ ] => idtac H
          end.

  (** Coq prints %``%#"#[H1]#"#%''%.  By applying %\index{tactics!idtac}%[idtac] with an argument, a convenient debugging tool for %``%#"#leaking information out of [match]es,#"#%''% we see that this [match] first tries binding [H] to [H1], which cannot be used to prove [Q].  Nonetheless, the following variation on the tactic succeeds at proving the goal: *)

(* begin thide *)
  match goal with
    | [ H : _ |- _ ] => exact H
  end.
Qed.
(* end thide *)

(** The tactic first unifies [H] with [H1], as before, but [exact H] fails in that case, so the tactic engine searches for more possible values of [H].  Eventually, it arrives at the correct value, so that [exact H] and the overall tactic succeed. *)

(** Now we are equipped to implement a tactic for checking that a proposition is not among our hypotheses: *)

(* begin thide *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.
(* end thide *)

(** We use the equality checking that is built into pattern-matching to see if there is a hypothesis that matches the proposition exactly.  If so, we use the %\index{tactics!fail}%[fail] tactic.  Without arguments, [fail] signals normal tactic failure, as you might expect.  When [fail] is passed an argument [n], [n] is used to count outwards through the enclosing cases of backtracking search.  In this case, [fail 1] says %``%#"#fail not just in this pattern-matching branch, but for the whole [match].#"#%''%  The second case will never be tried when the [fail 1] is reached.

This second case, used when [P] matches no hypothesis, checks if [P] is a conjunction.  Other simplifications may have split conjunctions into their component formulas, so we need to check that at least one of those components is also not represented.  To achieve this, we apply the %\index{tactics!first}%[first] tactical, which takes a list of tactics and continues down the list until one of them does not fail.  The [fail 2] at the end says to [fail] both the [first] and the [match] wrapped around it.

The body of the [?P1 /\ ?P2] case guarantees that, if it is reached, we either succeed completely or fail completely.  Thus, if we reach the wildcard case, [P] is not a conjunction.  We use %\index{tactics!idtac}%[idtac], a tactic that would be silly to apply on its own, since its effect is to succeed at doing nothing.  Nonetheless, [idtac] is a useful placeholder for cases like what we see here.

With the non-presence check implemented, it is easy to build a tactic that takes as input a proof term and adds its conclusion as a new hypothesis, only if that conclusion is not already present, failing otherwise. *)

(* begin thide *)
Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.
(* end thide *)

(** We see the useful %\index{tactics!type of}%[type of] operator of Ltac.  This operator could not be implemented in Gallina, but it is easy to support in Ltac.  We end up with [t] bound to the type of [pf].  We check that [t] is not already present.  If so, we use a [generalize]/[intro] combo to add a new hypothesis proved by [pf].  The tactic %\index{tactics!generalize}%[generalize] takes as input a term [t] (for instance, a proof of some proposition) and then changes the conclusion from [G] to [T -> G], where [T] is the type of [t] (for instance, the proposition proved by a proof given as argument).

   With these tactics defined, we can write a tactic [completer] for adding to the context all consequences of a set of simple first-order formulas. *)

(* begin thide *)
Ltac completer :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
	   | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.
(* end thide *)

(** We use the same kind of conjunction and implication handling as previously.  Note that, since [->] is the special non-dependent case of [forall], the fourth rule handles [intro] for implications, too.

   In the fifth rule, when we find a [forall] fact [H] with a premise matching one of our hypotheses, we add the appropriate instantiation of [H]'s conclusion, if we have not already added it.

   We can check that [completer] is working properly: *)

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall x, P x -> S x.
(* begin thide *)
    completer.
    (** [[
  x : A
  H : P x
  H0 : Q x
  H3 : R x
  H4 : S x
  ============================
   S x
   ]]
   *)

    assumption.
  Qed.
(* end thide *)
End firstorder.

(** We narrowly avoided a subtle pitfall in our definition of [completer].  Let us try another definition that even seems preferable to the original, to the untrained eye. *)

(* begin thide *)
Ltac completer' :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
	   | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.
(* end thide *)

(** The only difference is in the modus ponens rule, where we have replaced an unused unification variable [?][Q] with a wildcard.  Let us try our example again with this version: *)

Section firstorder'.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo' : forall x, P x -> S x.
(* begin thide *)
    (** [[
    completer'.
 
    ]]

    Coq loops forever at this point.  What went wrong? *)

  Abort.
(* end thide *)
End firstorder'.

(** A few examples should illustrate the issue.  Here we see a [match]-based proof that works fine: *)

Theorem t1 : forall x : nat, x = x.
  match goal with
    | [ |- forall x, _ ] => trivial
  end.
(* begin thide *)
Qed.
(* end thide *)

(** This one fails. *)

(* begin thide *)
Theorem t1' : forall x : nat, x = x.
(** [[
  match goal with
    | [ |- forall x, ?P ] => trivial
  end.
]]

<<
User error: No matching clauses for match goal
>>
*)

Abort.
(* end thide *)

(** The problem is that unification variables may not contain locally bound variables.  In this case, [?][P] would need to be bound to [x = x], which contains the local quantified variable [x].  By using a wildcard in the earlier version, we avoided this restriction.  To understand why this applies to the [completer] tactics, recall that, in Coq, implication is shorthand for degenerate universal quantification where the quantified variable is not used.  Nonetheless, in an Ltac pattern, Coq is happy to match a wildcard implication against a universal quantification.

   The Coq 8.2 release includes a special pattern form for a unification variable with an explicit set of free variables.  That unification variable is then bound to a function from the free variables to the %``%#"#real#"#%''% value.  In Coq 8.1 and earlier, there is no such workaround.

   No matter which version you use, it is important to be aware of this restriction.  As we have alluded to, the restriction is the culprit behind the infinite-looping behavior of [completer'].  We unintentionally match quantified facts with the modus ponens rule, circumventing the %``%#"#already present#"#%''% check and leading to different behavior, where the same fact may be added to the context repeatedly in an infinite loop.  Our earlier [completer] tactic uses a modus ponens rule that matches the implication conclusion with a variable, which blocks matching against non-trivial universal quantifiers. *)


(** * Functional Programming in Ltac *)

(* EX: Write a list length function in Ltac. *)

(** Ltac supports quite convenient functional programming, with a Lisp-with-syntax kind of flavor.  However, there are a few syntactic conventions involved in getting programs to be accepted.  The Ltac syntax is optimized for tactic-writing, so one has to deal with some inconveniences in writing more standard functional programs.

   To illustrate, let us try to write a simple list length function.  We start out writing it just like in Gallina, simply replacing [Fixpoint] (and its annotations) with [Ltac].

   [[
Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ls' => S (length ls')
  end.
]]

<<
Error: The reference ls' was not found in the current environment
>>

   At this point, we hopefully remember that pattern variable names must be prefixed by question marks in Ltac.

   [[
Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' => S (length ls')
  end.
]]

<<
Error: The reference S was not found in the current environment
>>

   The problem is that Ltac treats the expression [S (][length ls')] as an invocation of a tactic [S] with argument [length ls'].  We need to use a special annotation to %``%#"#escape into#"#%''% the Gallina parsing nonterminal.%\index{tactics!constr}% *)

(* begin thide *)
Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' => constr:(S (length ls'))
  end.

(** This definition is accepted.  It can be a little awkward to test Ltac definitions like this.  Here is one method. *)

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
  (** [[
  n := S (length (2 :: 3 :: nil)) : nat
  ============================
   False
 
   ]]

   We use the %\index{tactics!pose}%[pose] tactic, which extends the proof context with a new variable that is set equal to a particular term.  We could also have used [idtac n] in place of [pose n], which would have printed the result without changing the context.

   The value of [n] only has the length calculation unrolled one step.  What has happened here is that, by escaping into the [constr] nonterminal, we referred to the [length] function of Gallina, rather than the [length] Ltac function that we are defining. *)

Abort.

(* begin hide *)
Reset length.
(* end hide *)
(** %\noindent\coqdockw{%#<tt>#Reset#</tt>#%}% [length.] *)

(** The thing to remember is that Gallina terms built by tactics must be bound explicitly via [let] or a similar technique, rather than inserting Ltac calls directly in other Gallina terms. *)

Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
  (** [[
  n := 3 : nat
  ============================
   False
   ]]
   *)

Abort.
(* end thide *)

(* EX: Write a list map function in Ltac. *)

(** We can also use anonymous function expressions and local function definitions in Ltac, as this example of a standard list [map] function shows. *)

(* begin thide *)
Ltac map T f :=
  let rec map' ls :=
    match ls with
      | nil => constr:( @nil T)
      | ?x :: ?ls' =>
        let x' := f x in
          let ls'' := map' ls' in
            constr:( x' :: ls'')
    end in
  map'.

(** Ltac functions can have no implicit arguments.  It may seem surprising that we need to pass [T], the carried type of the output list, explicitly.  We cannot just use [type of f], because [f] is an Ltac term, not a Gallina term, and Ltac programs are dynamically typed.  The function [f] could use very syntactic methods to decide to return differently typed terms for different inputs.  We also could not replace [constr:( @][nil T)] with [constr: nil], because we have no strongly typed context to use to infer the parameter to [nil].  Luckily, we do have sufficient context within [constr:( x' :: ls'')].

Sometimes we need to employ the opposite direction of %``%#"#nonterminal escape,#"#%''% when we want to pass a complicated tactic expression as an argument to another tactic, as we might want to do in invoking [map]. *)

Goal False.
  let ls := map (nat * nat)%type ltac:(fun x => constr:( x, x)) (1 :: 2 :: 3 :: nil) in
    pose ls.
  (** [[
  l := (1, 1) :: (2, 2) :: (3, 3) :: nil : list (nat * nat)
  ============================
   False
   ]]
   *)

Abort.
(* end thide *)

(** One other gotcha shows up when we want to debug our Ltac functional programs.  We might expect the following code to work, to give us a version of [length] that prints a debug trace of the arguments it is called with. *)

(* begin hide *)
Reset length.
(* end hide *)
(** %\noindent\coqdockw{%#<tt>#Reset#</tt>#%}% [length.] *)

Ltac length ls :=
  idtac ls;
  match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.

(** Coq accepts the tactic definition, but the code is fatally flawed and will always lead to dynamic type errors. *)

Goal False.
(** %\vspace{-.15in}%[[
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
]]

<<
Error: variable n should be bound to a term.
>> *)
Abort.

(** What is going wrong here?  The answer has to do with the dual status of Ltac as both a purely functional and an imperative programming language.  The basic programming language is purely functional, but tactic scripts are one %``%#"#datatype#"#%''% that can be returned by such programs, and Coq will run such a script using an imperative semantics that mutates proof states.  Readers familiar with %\index{monads}\index{Haskell}%monadic programming in Haskell%~\cite{monads,IO}% may recognize a similarity.  Side-effecting Haskell programs can be thought of as pure programs that return %\emph{%#<i>#the code of programs in an imperative language#</i>#%}%, where some out-of-band mechanism takes responsibility for running these derived programs.  In this way, Haskell remains pure, while supporting usual input-output side effects and more.  Ltac uses the same basic mechanism, but in a dynamically typed setting.  Here the embedded imperative language includes all the tactics we have been applying so far.

   Even basic [idtac] is an embedded imperative program, so we may not automatically mix it with purely functional code.  In fact, a semicolon operator alone marks a span of Ltac code as an embedded tactic script.  This makes some amount of sense, since pure functional languages have no need for sequencing: since they lack side effects, there is no reason to run an expression and then just throw away its value and move on to another expression.

   The solution is like in Haskell: we must %``%#"#monadify#"#%''% our pure program to give it access to side effects.  The trouble is that the embedded tactic language has no [return] construct.  Proof scripts are about proving theorems, not calculating results.  We can apply a somewhat awkward workaround that requires translating our program into %\index{continuation-passing style}\emph{%#<i>#continuation-passing style#</i>#%}%, a program structuring idea popular in functional programming. *)

(* begin hide *)
Reset length.
(* end hide *)
(** %\noindent\coqdockw{%#<tt>#Reset#</tt>#%}% [length.] *)

Ltac length ls k :=
  idtac ls;
  match ls with
    | nil => k O
    | _ :: ?ls' => length ls' ltac:(fun n => k (S n))
  end.

(** The new [length] takes a new input: a %\emph{%#<i>#continuation#</i>#%}% [k], which is a function to be called to continue whatever proving process we were in the middle of when we called [length].  The argument passed to [k] may be thought of as the return value of [length]. *)

Goal False.
  length (1 :: 2 :: 3 :: nil) ltac:(fun n => pose n).
(** [[
(1 :: 2 :: 3 :: nil)
(2 :: 3 :: nil)
(3 :: nil)
nil
]]
*)
Abort.

(** We see exactly the trace of function arguments that we expected initially, and an examination of the proof state afterward would show that variable [n] has been added with value [3]. *)


(** * Recursive Proof Search *)

(** Deciding how to instantiate quantifiers is one of the hardest parts of automated first-order theorem proving.  For a given problem, we can consider all possible bounded-length sequences of quantifier instantiations, applying only propositional reasoning at the end.  This is probably a bad idea for almost all goals, but it makes for a nice example of recursive proof search procedures in Ltac.

   We can consider the maximum %``%#"#dependency chain#"#%''% length for a first-order proof.  We define the chain length for a hypothesis to be 0, and the chain length for an instantiation of a quantified fact to be one greater than the length for that fact.  The tactic [inster n] is meant to try all possible proofs with chain length at most [n]. *)

(* begin thide *)
Ltac inster n :=
  intuition;
    match n with
      | S ?n' =>
        match goal with
          | [ H : forall x : ?T, _, x : ?T |- _ ] => generalize (H x); inster n'
        end
    end.
(* end thide *)

(** The tactic begins by applying propositional simplification.  Next, it checks if any chain length remains.  If so, it tries all possible ways of instantiating quantified hypotheses with properly typed local variables.  It is critical to realize that, if the recursive call [inster n'] fails, then the [match goal] just seeks out another way of unifying its pattern against proof state.  Thus, this small amount of code provides an elegant demonstration of how backtracking [match] enables exhaustive search.

   We can verify the efficacy of [inster] with two short examples.  The built-in [firstorder] tactic (with no extra arguments) is able to prove the first but not the second. *)

Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).

  Theorem test_inster : forall x, P (g x x) -> Q (f x).
    inster 2.
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).

  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
    inster 3.
  Qed.
End test_inster.

(** The style employed in the definition of [inster] can seem very counterintuitive to functional programmers.  Usually, functional programs accumulate state changes in explicit arguments to recursive functions.  In Ltac, the state of the current subgoal is always implicit.  Nonetheless, in contrast to general imperative programming, it is easy to undo any changes to this state, and indeed such %``%#"#undoing#"#%''% happens automatically at failures within [match]es.  In this way, Ltac programming is similar to programming in Haskell with a stateful failure monad that supports a composition operator along the lines of the [first] tactical.  The key pieces of state include not only the form of the goal, but also decisions about the values of unification variables.  These decisions are rolled back with all the other state after failure.

   Functional programming purists may react indignantly to the suggestion of programming this way.  Nonetheless, as with other kinds of %``%#"#monadic programming,#"#%''% many problems are much simpler to solve with Ltac than they would be with explicit, pure proof manipulation in ML or Haskell.  To demonstrate, we will write a basic simplification procedure for logical implications.

   This procedure is inspired by one for separation logic%~\cite{separation}%, where conjuncts in formulas are thought of as %``%#"#resources,#"#%''% such that we lose no completeness by %``%#"#crossing out#"#%''% equal conjuncts on the two sides of an implication.  This process is complicated by the fact that, for reasons of modularity, our formulas can have arbitrary nested tree structure (branching at conjunctions) and may include existential quantifiers.  It is helpful for the matching process to %``%#"#go under#"#%''% quantifiers and in fact decide how to instantiate existential quantifiers in the conclusion.

   To distinguish the implications that our tactic handles from the implications that will show up as %``%#"#plumbing#"#%''% in various lemmas, we define a wrapper definition, a notation, and a tactic. *)

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).
Ltac imp := unfold imp; firstorder.

(** These lemmas about [imp] will be useful in the tactic that we will write. *)

Theorem and_True_prem : forall P Q,
  (P /\ True --> Q)
  -> (P --> Q).
  imp.
Qed.

Theorem and_True_conc : forall P Q,
  (P --> Q /\ True)
  -> (P --> Q).
  imp.
Qed.

Theorem assoc_prem1 : forall P Q R S,
  (P /\ (Q /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem assoc_prem2 : forall P Q R S,
  (Q /\ (P /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem comm_prem : forall P Q R,
  (P /\ Q --> R)
  -> (Q /\ P --> R).
  imp.
Qed.

Theorem assoc_conc1 : forall P Q R S,
  (S --> P /\ (Q /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem assoc_conc2 : forall P Q R S,
  (S --> Q /\ (P /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem comm_conc : forall P Q R,
  (R --> P /\ Q)
  -> (R --> Q /\ P).
  imp.
Qed.

(** The first order of business in crafting our [matcher] tactic will be auxiliary support for searching through formula trees.  The [search_prem] tactic implements running its tactic argument [tac] on every subformula of an [imp] premise.  As it traverses a tree, [search_prem] applies some of the above lemmas to rewrite the goal to bring different subformulas to the head of the goal.  That is, for every subformula [P] of the implication premise, we want [P] to %``%#"#have a turn,#"#%''% where the premise is rearranged into the form [P /\ Q] for some [Q].  The tactic [tac] should expect to see a goal in this form and focus its attention on the first conjunct of the premise. *)

Ltac search_prem tac :=
  let rec search P :=
    tac
    || (apply and_True_prem; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply assoc_prem1; search P1)
           || (apply assoc_prem2; search P2)
       end
  in match goal with
       | [ |- ?P /\ _ --> _ ] => search P
       | [ |- _ /\ ?P --> _ ] => apply comm_prem; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_prem; tac))
     end.

(** To understand how [search_prem] works, we turn first to the final [match].  If the premise begins with a conjunction, we call the [search] procedure on each of the conjuncts, or only the first conjunct, if that already yields a case where [tac] does not fail.  The call [search P] expects and maintains the invariant that the premise is of the form [P /\ Q] for some [Q].  We pass [P] explicitly as a kind of decreasing induction measure, to avoid looping forever when [tac] always fails.  The second [match] case calls a commutativity lemma to realize this invariant, before passing control to [search].  The final [match] case tries applying [tac] directly and then, if that fails, changes the form of the goal by adding an extraneous [True] conjunct and calls [tac] again.

   The [search] function itself tries the same tricks as in the last case of the final [match].  Additionally, if neither works, it checks if [P] is a conjunction.  If so, it calls itself recursively on each conjunct, first applying associativity lemmas to maintain the goal-form invariant.

   We will also want a dual function [search_conc], which does tree search through an [imp] conclusion. *)

Ltac search_conc tac :=
  let rec search P :=
    tac
    || (apply and_True_conc; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply assoc_conc1; search P1)
           || (apply assoc_conc2; search P2)
       end
  in match goal with
       | [ |- _ --> ?P /\ _ ] => search P
       | [ |- _ --> _ /\ ?P ] => apply comm_conc; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_conc; tac))
     end.

(** Now we can prove a number of lemmas that are suitable for application by our search tactics.  A lemma that is meant to handle a premise should have the form [P /\ Q --> R] for some interesting [P], and a lemma that is meant to handle a conclusion should have the form [P --> Q /\ R] for some interesting [Q]. *)

(* begin thide *)
Theorem False_prem : forall P Q,
  False /\ P --> Q.
  imp.
Qed.

Theorem True_conc : forall P Q : Prop,
  (P --> Q)
  -> (P --> True /\ Q).
  imp.
Qed.

Theorem Match : forall P Q R : Prop,
  (Q --> R)
  -> (P /\ Q --> P /\ R).
  imp.
Qed.

Theorem ex_prem : forall (T : Type) (P : T -> Prop) (Q R : Prop),
  (forall x, P x /\ Q --> R)
  -> (ex P /\ Q --> R).
  imp.
Qed.

Theorem ex_conc : forall (T : Type) (P : T -> Prop) (Q R : Prop) x,
  (Q --> P x /\ R)
  -> (Q --> ex P /\ R).
  imp.
Qed.

(** We will also want a %``%#"#base case#"#%''% lemma for finishing proofs where cancelation has removed every constituent of the conclusion. *)

Theorem imp_True : forall P,
  P --> True.
  imp.
Qed.

(** Our final [matcher] tactic is now straightforward.  First, we [intros] all variables into scope.  Then we attempt simple premise simplifications, finishing the proof upon finding [False] and eliminating any existential quantifiers that we find.  After that, we search through the conclusion.  We remove [True] conjuncts, remove existential quantifiers by introducing unification variables for their bound variables, and search for matching premises to cancel.  Finally, when no more progress is made, we see if the goal has become trivial and can be solved by [imp_True].  In each case, we use the tactic [simple apply] in place of [apply] to use a simpler, less expensive unification algorithm. *)

Ltac matcher :=
  intros;
    repeat search_prem ltac:( simple apply False_prem || ( simple apply ex_prem; intro));
      repeat search_conc ltac:( simple apply True_conc || simple eapply ex_conc
        || search_prem ltac:( simple apply Match));
      try simple apply imp_True.
(* end thide *)

(** Our tactic succeeds at proving a simple example. *)

Theorem t2 : forall P Q : Prop,
  Q /\ (P /\ False) /\ P --> P /\ Q.
  matcher.
Qed.

(** In the generated proof, we find a trace of the workings of the search tactics. *)

Print t2.
(** %\vspace{-.15in}% [[
t2 = 
fun P Q : Prop =>
comm_prem (assoc_prem1 (assoc_prem2 (False_prem (P:=P /\ P /\ Q) (P /\ Q))))
     : forall P Q : Prop, Q /\ (P /\ False) /\ P --> P /\ Q
 
     ]]

We can also see that [matcher] is well-suited for cases where some human intervention is needed after the automation finishes. *)

Theorem t3 : forall P Q R : Prop,
  P /\ Q --> Q /\ R /\ P.
  matcher.
  (** [[
  ============================
   True --> R
 
   ]]

   Our tactic canceled those conjuncts that it was able to cancel, leaving a simplified subgoal for us, much as [intuition] does. *)

Abort.

(** The [matcher] tactic even succeeds at guessing quantifier instantiations.  It is the unification that occurs in uses of the [Match] lemma that does the real work here. *)

Theorem t4 : forall (P : nat -> Prop) Q, (exists x, P x /\ Q) --> Q /\ (exists x, P x).
  matcher.
Qed.

Print t4.
(** %\vspace{-.15in}% [[
t4 = 
fun (P : nat -> Prop) (Q : Prop) =>
and_True_prem
  (ex_prem (P:=fun x : nat => P x /\ Q)
     (fun x : nat =>
      assoc_prem2
        (Match (P:=Q)
           (and_True_conc
              (ex_conc (fun x0 : nat => P x0) x
                 (Match (P:=P x) (imp_True (P:=True))))))))
     : forall (P : nat -> Prop) (Q : Prop),
       (exists x : nat, P x /\ Q) --> Q /\ (exists x : nat, P x)
]]
*)


(** * Creating Unification Variables *)

(** A final useful ingredient in tactic crafting is the ability to allocate new unification variables explicitly.  Tactics like [eauto] introduce unification variable internally to support flexible proof search.  While [eauto] and its relatives do %\textit{%#<i>#backward#</i>#%}% reasoning, we often want to do similar %\textit{%#<i>#forward#</i>#%}% reasoning, where unification variables can be useful for similar reasons.

   For example, we can write a tactic that instantiates the quantifiers of a universally quantified hypothesis.  The tactic should not need to know what the appropriate instantiantiations are; rather, we want these choices filled with placeholders.  We hope that, when we apply the specialized hypothesis later, syntactic unification will determine concrete values.

   Before we are ready to write a tactic, we can try out its ingredients one at a time. *)

Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
  intros.

  (** [[
  H : forall x : nat, S x > x
  ============================
   2 > 1
 
   ]]

   To instantiate [H] generically, we first need to name the value to be used for [x].%\index{tactics!evar}% *)

  evar (y : nat).

  (** [[
  H : forall x : nat, S x > x
  y := ?279 : nat
  ============================
   2 > 1
 
   ]]

   The proof context is extended with a new variable [y], which has been assigned to be equal to a fresh unification variable [?279].  We want to instantiate [H] with [?279].  To get ahold of the new unification variable, rather than just its alias [y], we perform a trivial unfolding in the expression [y], using the %\index{tactics!eval}%[eval] Ltac construct, which works with the same reduction strategies that we have seen in tactics (e.g., [simpl], [compute], etc.).  *)

  let y' := eval unfold y in y in
    clear y; generalize (H y').

  (** [[
  H : forall x : nat, S x > x
  ============================
   S ?279 > ?279 -> 2 > 1
 
   ]]

   Our instantiation was successful.  We can finish by using the refined formula to replace the original. *)

  clear H; intro H.

  (** [[
  H : S ?281 > ?281
  ============================
   2 > 1
 
   ]]

   We can finish the proof by using [apply]'s unification to figure out the proper value of [?281].  (The original unification variable was replaced by another, as often happens in the internals of the various tactics' implementations.) *)

  apply H.
Qed.

(** Now we can write a tactic that encapsulates the pattern we just employed, instantiating all quantifiers of a particular hypothesis. *)

Ltac insterU H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             let x := fresh "x" in
               evar (x : T);
               let x' := eval unfold x in x in
                 clear x; specialize (H x')
         end.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1.
  intro H; insterU H; apply H.
Qed.

(** This particular example is somewhat silly, since [apply] by itself would have solved the goal originally.  Separate forward reasoning is more useful on hypotheses that end in existential quantifications.  Before we go through an example, it is useful to define a variant of [insterU] that does not clear the base hypothesis we pass to it.  We use the Ltac construct %\index{tactics!fresh}%[fresh] to generate a hypothesis name that is not already used, based on a string suggesting a good name. *)

Ltac insterKeep H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros.

    (** Neither [eauto] nor [firstorder] is clever enough to prove this goal.  We can help out by doing some of the work with quantifiers ourselves, abbreviating the proof with the %\index{tactics!do}%[do] tactical for repetition of a tactic a set number of times. *)

    do 2 insterKeep H1.

    (** Our proof state is extended with two generic instances of [H1].

       [[
  H' : exists u : B, P ?4289 u
  H'0 : exists u : B, P ?4288 u
  ============================
   exists u1 : B, exists u2 : B, P (f v1 v2) (g u1 u2)
 
   ]]

   [eauto] still cannot prove the goal, so we eliminate the two new existential quantifiers.  (Recall that [ex] is the underlying type family to which uses of the [exists] syntax are compiled.) *)

    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end.

    (** Now the goal is simple enough to solve by logic programming. *)

    eauto.
  Qed.
End t6.

(** Our [insterU] tactic does not fare so well with quantified hypotheses that also contain implications.  We can see the problem in a slight modification of the last example.  We introduce a new unary predicate [Q] and use it to state an additional requirement of our hypothesis [H1]. *)

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros; do 2 insterKeep H1;
      repeat match goal with
               | [ H : ex _ |- _ ] => destruct H
             end; eauto.

    (** This proof script does not hit any errors until the very end, when an error message like this one is displayed.

<<
No more subgoals but non-instantiated existential variables :
Existential 1 =
>>
       [[
?4384 : [A : Type
         B : Type
         Q : A -> Prop
         P : A -> B -> Prop
         f : A -> A -> A
         g : B -> B -> B
         H1 : forall v : A, Q v -> exists u : B, P v u
         H2 : forall (v1 : A) (u1 : B) (v2 : A) (u2 : B),
              P v1 u1 -> P v2 u2 -> P (f v1 v2) (g u1 u2)
         v1 : A
         v2 : A
         H : Q v1
         H0 : Q v2
         H' : Q v2 -> exists u : B, P v2 u |- Q v2] 
 
         ]]

         There is another similar line about a different existential variable.  Here, %``%#"#existential variable#"#%''% means what we have also called %``%#"#unification variable.#"#%''%  In the course of the proof, some unification variable [?4384] was introduced but never unified.  Unification variables are just a device to structure proof search; the language of Gallina proof terms does not include them.  Thus, we cannot produce a proof term without instantiating the variable.

         The error message shows that [?4384] is meant to be a proof of [Q v2] in a particular proof state, whose variables and hypotheses are displayed.  It turns out that [?4384] was created by [insterU], as the value of a proof to pass to [H1].  Recall that, in Gallina, implication is just a degenerate case of [forall] quantification, so the [insterU] code to match against [forall] also matched the implication.  Since any proof of [Q v2] is as good as any other in this context, there was never any opportunity to use unification to determine exactly which proof is appropriate.  We expect similar problems with any implications in arguments to [insterU]. *)

  Abort.
End t7.

(* begin hide *)
Reset insterU.
(* end hide *)
(** %\noindent\coqdockw{%#<tt>#Reset#</tt>#%}% [insterU.] *)

(** We can redefine [insterU] to treat implications differently.  In particular, we pattern-match on the type of the type [T] in [forall x : ?T, ...].  If [T] has type [Prop], then [x]'s instantiation should be thought of as a proof.  Thus, instead of picking a new unification variable for it, we instead apply a user-supplied tactic [tac].  It is important that we end this special [Prop] case with [|| fail 1], so that, if [tac] fails to prove [T], we abort the instantiation, rather than continuing on to the default quantifier handling.  Also recall that the tactic form %\index{tactics!solve}%[solve [ t ]] fails if [t] does not completely solve the goal. *)

Ltac insterU tac H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T) by solve [ tac ];
                     specialize (H H'); clear H')
                 || fail 1
               | _ =>
                 let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

Ltac insterKeep tac H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU tac H'.

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).

    (** We can prove the goal by calling [insterKeep] with a tactic that tries to find and apply a [Q] hypothesis over a variable about which we do not yet know any [P] facts.  We need to begin this tactic code with [idtac; ] to get around a strange limitation in Coq's proof engine, where a first-class tactic argument may not begin with a [match]. *)

    intros; do 2 insterKeep ltac:(idtac; match goal with
                                           | [ H : Q ?v |- _ ] =>
                                             match goal with
                                               | [ _ : context[P v _] |- _ ] => fail 1
                                               | _ => apply H
                                             end
                                         end) H1;
    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end; eauto.
  Qed.
End t7.

(** It is often useful to instantiate existential variables explicitly.  A built-in tactic provides one way of doing so. *)

Theorem t8 : exists p : nat * nat, fst p = 3.
  econstructor; instantiate (1 := (3, 2)); reflexivity.
Qed.

(** The [1] above is identifying an existential variable appearing in the current goal, with the last existential appearing assigned number 1, the second last assigned number 2, and so on.  The named existential is replaced everywhere by the term to the right of the [:=].

   The %\index{tactics!instantiate}%[instantiate] tactic can be convenient for exploratory proving, but it leads to very brittle proof scripts that are unlikely to adapt to changing theorem statements.  It is often more helpful to have a tactic that can be used to assign a value to a term that is known to be an existential.  By employing a roundabout implementation technique, we can build a tactic that generalizes this functionality.  In particular, our tactic [equate] will assert that two terms are equal.  If one of the terms happens to be an existential, then it will be replaced everywhere with the other term. *)

Ltac equate x y :=
  let H := fresh "H" in
    assert (H : x = y) by reflexivity; clear H.

(** This tactic fails if it is not possible to prove [x = y] by [reflexivity].  We perform the proof only for its unification side effects, clearing the fact [x = y] afterward.  With [equate], we can build a less brittle version of the prior example. *)

Theorem t9 : exists p : nat * nat, fst p = 3.
  econstructor; match goal with
                  | [ |- fst ?x = 3 ] => equate x (3, 2)
                end; reflexivity.
Qed.


(** * Exercises *)

(** %\begin{enumerate}%#<ol>#

   %\item%#<li># An anonymous Coq fan from the Internet was excited to come up with this tactic definition shortly after getting started learning Ltac: *)

Ltac deSome :=
  match goal with
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst; deSome
    | _ => reflexivity
  end.

(** Without lifting a finger, exciting theorems can be proved: *)

Theorem test : forall (a b c d e f g : nat),
  Some a = Some b
  -> Some b = Some c
  -> Some e = Some c
  -> Some f = Some g
  -> c = a.
  intros; deSome.
Qed.

(** Unfortunately, this tactic exhibits some degenerate behavior.  Consider the following example: *)

Theorem test2 : forall (a x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : nat),
  Some x1 = Some y1
  -> Some x2 = Some y2
  -> Some x3 = Some y3
  -> Some x4 = Some y4
  -> Some x5 = Some y5
  -> Some x6 = Some y6
  -> Some a = Some a
  -> x1 = x2.
  intros.
  Time try deSome.
Abort.

(* begin hide *)
Reset test.
(* end hide *)

(** This (failed) proof already takes about one second on my workstation.  I hope a pattern in the theorem statement is clear; this is a representative of a class of theorems, where we may add more matched pairs of [x] and [y] variables, with equality hypotheses between them.  The running time of [deSome] is exponential in the number of such hypotheses.

   The task in this exercise is twofold.  First, figure out why [deSome] exhibits exponential behavior for this class of examples and record your explanation in a comment.  Second, write an improved version of [deSome] that runs in polynomial time.#</li>#

   %\item%#<li># Sometimes it can be convenient to know that a proof attempt is doomed because the theorem is false.  For instance, here are three non-theorems about lists: *)

Theorem test1 : forall A (ls1 ls2 : list A), ls1 ++ ls2 = ls2 ++ ls1.
(* begin hide *)
Abort.
(* end hide *)

Theorem test2 : forall A (ls1 ls2 : list A), length (ls1 ++ ls2) = length ls1 - length ls2.
(* begin hide *)
Abort.
(* end hide *)

Theorem test3 : forall A (ls : list A), length (rev ls) - 3 = 0.
(* begin hide *)
Abort.
(* end hide *)

(** The task in this exercise is to write a tactic that disproves these and many other related %``%#"#theorems#"#%''% about lists.  Your tactic should follow a simple brute-force enumeration strategy, considering all [list bool] values with length up to some bound given by the user, as a [nat] argument to the tactic.  A successful invocation should add a new hypothesis of the negation of the theorem (guaranteeing that the tactic has made a sound decision about falsehood).

   A few hints: A good starting point is to pattern-match the conclusion formula and use the [assert] tactic on its negation.  An [assert] invocation may include a [by] clause to specify a tactic to use to prove the assertion.

   The idea in this exercise is to disprove a quantified formula by finding instantiations for the quantifiers that make it manifestly false.  Recall the [specialize] tactic for specializing a hypothesis to particular quantifier instantiations.  When you have instantiated quantifiers fully, [discriminate] is a good choice to derive a contradiction.  (It at least works for the three examples above and is smart enough for this exercise's purposes.)  The [type of] Ltac construct may be useful to analyze the type of a hypothesis to choose how to instantiate its quantifiers.

   To enumerate all boolean lists up to a certain length, it will be helpful to write a recursive tactic in continuation-passing style, where the continuation is meant to be called on each candidate list.

   Remember that arguments to Ltac functions may not be type-checked in contexts large enough to allow usual implicit argument inference, so instead of [nil] it will be useful to write [@][nil bool], which specifies the usually implicit argument explicitly.

   %\item%#<li># Some theorems involving existential quantifiers are easy to prove with [eauto]. *)

Theorem test1 : exists x, x = 0.
  eauto.
Qed.

(** Others are harder.  The problem with the next theorem is that the existentially quantified variable does not appear in the rest of the theorem, so [eauto] has no way to deduce its value.  However, we know that we had might as well instantiate that variable to [tt], the only value of type [unit]. *)

Theorem test2 : exists x : unit, 0 = 0.
(* begin hide *)
  eauto.
Abort.
(* end hide *)

(** We also run into trouble in the next theorem, because [eauto] does not understand the [fst] and [snd] projection functions for pairs. *)

Theorem test3 : exists x : nat * nat, fst x = 7 /\ snd x = 2 + fst x.
(* begin hide *)
  eauto.
Abort.
(* end hide *)

(** Both problems show up in this monster example. *)

Theorem test4 : exists x : (unit * nat) * (nat * bool),
  snd (fst x) = 7 /\ fst (snd x) = 2 + snd (fst x) /\ snd (snd x) = true.
(* begin hide *)
  eauto.
Abort.
(* end hide *)

(** The task in this problem is to write a tactic that preprocesses such goals so that [eauto] can finish them.  Your tactic should serve as a complete proof of each of the above examples, along with the wide class of similar examples.  The key smarts that your tactic will bring are: first, it introduces separate unification variables for all the %``%#"#leaf types#"#%''% of compound types built out of pairs; and second, leaf unification variables of type [unit] are simply replaced by [tt].

   A few hints: The following tactic is more convenient than direct use of the built-in tactic [evar], for generation of new unification variables: *)

Ltac makeEvar T k := let x := fresh in
  evar (x : T); let y := eval unfold x in x in clear x; k y.

(** remove printing exists *)

(** This is a continuation-passing style tactic.  For instance, when the goal begins with existential quantification over a type [T], the following tactic invocation will create a new unification variable to use as the quantifier instantiation:

[makeEvar T ltac:(][fun x => exists x)] *)

(** printing exists $\exists$ *)

(** Recall that [exists] formulas are desugared to uses of the [ex] inductive family.  In particular, a pattern like the following can be used to extract the domain of an [exists] quantifier into variable [T]:

[| [ |- ex ( A := ?T) _ ] => ...]

    The [equate] tactic used as an example in this chapter will probably be useful, to unify two terms, for instance if the first is a unification variable whose value you want to set.
[[
Ltac equate E1 E2 := let H := fresh in
  assert (H : E1 = E2) by reflexivity; clear H.
]]

    Finally, there are some minor complications surrounding overloading of the [*] operator for both numeric multiplication and Cartesian product for sets (i.e., pair types).  To ensure that an Ltac pattern is using the type version, write it like this:

[| (?T1 * ?T2)%type => ...]#</li>#

%\item%#<li># An exercise in the last chapter dealt with automating proofs about rings using [eauto], where we must prove some odd-looking theorems to push proof search in a direction where unification does all the work.  Algebraic proofs consist mostly of rewriting in equations, so we might hope that the [autorewrite] tactic would yield more natural automated proofs.  Indeed, consider this example within the same formulation of ring theory that we dealt with last chapter, where each of the three axioms has been added to the rewrite hint database [cpdt] using [Hint Rewrite]:
[[
Theorem test1 : forall a b, a * b * i b = a.
  intros; autorewrite with cpdt; reflexivity.
Qed.
]]

So far so good.  However, consider this further example:
[[
Theorem test2 : forall a, a * e * i a * i e = e.
  intros; autorewrite with cpdt.
]]

The goal is merely reduced to [a * (i a * i e) = e], which of course [reflexivity] cannot prove.  The essential problem is that [autorewrite] does not do backtracking search.  Instead, it follows a %``%#"#greedy#"#%''% approach, at each stage choosing a rewrite to perform and then never allowing that rewrite to be undone.  An early mistake can doom the whole process.

The task in this problem is to use Ltac to implement a backtracking version of [autorewrite] that works much like [eauto], in that its inputs are a database of hint lemmas and a bound on search depth.  Here our search trees will have uses of [rewrite] at their nodes, rather than uses of [eapply] as in the case of [eauto], and proofs must be finished by [reflexivity].

An invocation to the tactic to prove [test2] might look like this:
[[
  rewriter (right_identity, (right_inverse, tt)) 3.
]]

The first argument gives the set of lemmas to consider, as a kind of list encoded with pair types.  Such a format cannot be analyzed directly by Gallina programs, but Ltac allows us much more freedom to deconstruct syntax.  For example, to case analyze such a list found in a variable [x], we need only write:
[[
  match x with
    | (?lemma, ?more) => ...
  end
]]

In the body of the case analysis, [lemma] will be bound to the first lemma, and [more] will be bound to the remaining lemmas.  There is no need to consider a case for [tt], our stand-in for [nil].  This is because lack of any matching pattern will trigger failure, which is exactly the outcome we would like upon reaching the end of the lemma list without finding one that applies.  The tactic will fail, triggering backtracking to some previous [match].

There are different kinds of backtracking, corresponding to different sorts of decisions to be made.  The examples considered above can be handled with backtracking that only reconsiders decisions about the order in which to apply rewriting lemmas.  A full-credit solution need only handle that kind of backtracking, considering all rewriting sequences up to the length bound passed to your tactic.  A good test of this level of applicability is to prove both [test1] and [test2] above.  However, some theorems could only be proved using a smarter tactic that considers not only order of rewriting lemma uses, but also choice of arguments to the lemmas.  That is, at some points in a proof, the same lemma may apply at multiple places within the goal formula, and some choices may lead to stuck proof states while others lead to success.  For an extra challenge (without any impact on the grade for the problem), you might try beefing up your tactic to do backtracking on argument choice, too.#</li>#

#</ol>#%\end{enumerate}% *)
