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

   The %\textit{%#<i>#setoid#</i>#%}% facility makes it possible to register new equivalence relations to be understood by tactics like [rewrite].  For instance, [Prop] is registered as a setoid with the equivalence relation "if and only if."  The ability to register new setoids can be very useful in proofs of a kind common in math, where all reasoning is done after "modding out by a relation." *)


(** * Hint Databases *)

(** Another class of built-in tactics includes [auto], [eauto], and [autorewrite].  These are based on %\textit{%#<i>#hint databases#</i>#%}%, which we have seen extended in many examples so far.  These tactics are important, because, in Ltac programming, we cannot create "global variables" whose values can be extended seamlessly by different modules in different source files.  We have seen the advantages of hints so far, where [crush] can be defined once and for all, while still automatically applying the hints we add throughout developments.

The basic hints for [auto] and [eauto] are [Hint Immediate lemma], asking to try solving a goal immediately by applying the premise-free lemma; [Resolve lemma], which does the same but may add new premises that are themselves to be subjects of proof search; [Constructor type], which acts like [Resolve] applied to every constructor of an inductive type; and [Unfold ident], which tries unfolding [ident] when it appears at the head of a proof goal.  Each of these [Hint] commands may be used with a suffix, as in [Hint Resolve lemma : my_db].  This adds the hint only to the specified database, so that it would only be used by, for instance, [auto with my_db].  An additional argument to [auto] specifies the maximum depth of proof trees to search in depth-first order, as in [auto 8] or [auto 8 with my_db].  The default depth is 5.

All of these [Hint] commands can be issued alternatively with a more primitive hint kind, [Extern].  A few examples should do best to explain how [Hint Extern] works. *)

Theorem bool_neq : true <> false.
  auto.
  (** [crush] would have discharged this goal, but the default hint database for [auto] contains no hint that applies. *)
Abort.

(** It is hard to come up with a [bool]-specific hint that is not just a restatement of the theorem we mean to prove.  Luckily, a simpler form suffices. *)

Hint Extern 1 (_ <> _) => congruence.

Theorem bool_neq : true <> false.
  auto.
Qed.

(** Our hint says: "whenever the conclusion matches the pattern [_ <> _], try applying [congruence]."  The [1] is a cost for this rule.  During proof search, whenever multiple rules apply, rules are tried in increasing cost order, so it pays to assign high costs to relatively expensive [Extern] hints.

[Extern] hints may be implemented with the full Ltac language.  This example shows a case where a hint uses a [match]. *)

Section forall_and.
  Variable A : Set.
  Variables P Q : A -> Prop.

  Hypothesis both : forall x, P x /\ Q x.

  Theorem forall_and : forall z, P z.
    crush.
    (** [crush] makes no progress beyond what [intros] would have accomplished.  [auto] will not apply the hypothesis [both] to prove the goal, because the conclusion of [both] does not unify with the conclusion of the goal.  However, we can teach [auto] to handle this kind of goal. *)

    Hint Extern 1 (P ?X) =>
      match goal with
        | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
      end.

    auto.
  Qed.

  (** We see that an [Extern] pattern may bind unification variables that we use in the associated tactic.  [proj1] is a function from the standard library for extracting a proof of [R] from a proof of [R /\ S]. *)
End forall_and.

(** After our success on this example, we might get more ambitious and seek to generalize the hint to all possible predicates [P].

   [[
  Hint Extern 1 (?P ?X) =>
    match goal with
      | [ H : forall x, ?P x /\ _ |- _ ] => apply (proj1 (H X))
    end.

   [[
User error: Bound head variable
   ]]

   Coq's [auto] hint databases work as tables mapping %\textit{%#<i>#head symbols#</i>#%}% to lists of tactics to try.  Because of this, the constant head of an [Extern] pattern must be determinable statically.  In our first [Extern] hint, the head symbol was [not], since [x <> y] desugars to [not (eq x y)]; and, in the second example, the head symbol was [P].

   This restriction on [Extern] hints is the main limitation of the [auto] mechanism, preventing us from using it for general context simplifications that are not keyed off of the form of the conclusion.  This is perhaps just as well, since we can often code more efficient tactics with specialized Ltac programs, and we will see how in later sections of the chapter.

   We have used [Hint Rewrite] in many examples so far.  [crush] uses these hints by calling [autorewrite].  Our rewrite hints have taken the form [Hint Rewrite lemma : cpdt], adding them to the [cpdt] rewrite database.  This is because, in contrast to [auto], [autorewrite] has no default database.  Thus, we set the convention that [crush] uses the [cpdt] database.

   This example shows a direct use of [autorewrite]. *)

Section autorewrite.
  Variable A : Set.
  Variable f : A -> A.

  Hypothesis f_f : forall x, f (f x) = f x.

  Hint Rewrite f_f : my_db.

  Lemma f_f_f : forall x, f (f (f x)) = f x.
    intros; autorewrite with my_db; reflexivity.
  Qed.

  (** There are a few ways in which [autorewrite] can lead to trouble when insufficient care is taken in choosing hints.  First, the set of hints may define a nonterminating rewrite system, in which case invocations to [autorewrite] may not terminate.  Second, we may add hints that "lead [autorewrite] down the wrong path."  For instance: *)

  Section garden_path.
    Variable g : A -> A.
    Hypothesis f_g : forall x, f x = g x.
    Hint Rewrite f_g : my_db.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with my_db.
      (** [[

============================
 g (g (g x)) = g x
          ]] *)
    Abort.

    (** Our new hint was used to rewrite the goal into a form where the old hint could no longer be applied.  This "non-monotonicity" of rewrite hints contrasts with the situation for [auto], where new hints may slow down proof search but can never "break" old proofs. *)

  Reset garden_path.

  (** [autorewrite] works with quantified equalities that include additional premises, but we must be careful to avoid similar incorrect rewritings. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
    Hint Rewrite f_g : my_db.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with my_db.
      (** [[

  ============================
   g (g (g x)) = g x

subgoal 2 is:
 P x
subgoal 3 is:
 P (f x)
subgoal 4 is:
 P (f x)
          ]] *)
    Abort.

    (** The inappropriate rule fired the same three times as before, even though we know we will not be able to prove the premises. *)

  Reset garden_path.

  (** Our final, successful, attempt uses an extra argument to [Hint Rewrite] that specifies a tactic to apply to generated premises. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
    Hint Rewrite f_g using assumption : my_db.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with my_db; reflexivity.
    Qed.

    (** [autorewrite] will still use [f_g] when the generated premise is among our assumptions. *)

    Lemma f_f_f_g : forall x, P x -> f (f x) = g x.
      intros; autorewrite with my_db; reflexivity.
    Qed.
  End garden_path.

  (** It can also be useful to use the [autorewrite with db in *] form, which does rewriting in hypotheses, as well as in the conclusion. *)

  Lemma in_star : forall x y, f (f (f (f x))) = f (f y)
    -> f x = f (f (f y)).
    intros; autorewrite with my_db in *; assumption.
  Qed.

End autorewrite.


(** * Ltac Programming Basics *)

(** We have already seen many examples of Ltac programs.  In the rest of this chapter, we attempt to give a more principled introduction to the important features and design patterns.

   One common use for [match] tactics is identification of subjects for case analysis, as we see in this tactic definition. *)

Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => destruct X
  end.

(** The tactic checks if the conclusion is an [if], [destruct]ing the test expression if so.  Certain classes of theorem are trivial to prove automatically with such a tactic. *)

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
  intros; repeat find_if; constructor.
Qed.

(** The [repeat] that we use here is called a %\textit{%#<i>#tactical#</i>#%}%, or tactic combinator.  The behavior of [repeat t] is to loop through running [t], running [t] on all generated subgoals, running [t] on %\textit{%#<i>#their#</i>#%}% generated subgoals, and so on.  When [t] fails at any point in this search tree, that particular subgoal is left to be handled by later tactics.  Thus, it is important never to use [repeat] with a tactic that always succeeds.

   Another very useful Ltac building block is %\textit{%#<i>#context patterns#</i>#%}%. *)

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

(** The behavior of this tactic is to find any subterm of the conclusion that is an [if] and then [destruct] the test expression.  This version subsumes [find_if]. *)

Theorem hmm' : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
  intros; repeat find_if_inside; constructor.
Qed.

(** We can also use [find_if_inside] to prove goals that [find_if] does not simplify sufficiently. *)

Theorem duh2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
  intros; repeat find_if_inside; reflexivity.
Qed.

(** Many decision procedures can be coded in Ltac via "[repeat match] loops."  For instance, we can implement a subset of the functionality of [tauto]. *)

Ltac my_tauto :=
  repeat match goal with
	   | [ H : ?P |- ?P ] => exact H

	   | [ |- True ] => constructor
	   | [ |- _ /\ _ ] => constructor
	   | [ |- _ -> _ ] => intro

	   | [ H : False |- _ ] => destruct H
	   | [ H : _ /\ _ |- _ ] => destruct H
	   | [ H : _ \/ _ |- _ ] => destruct H

	   | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] =>
	     let H := fresh "H" in
	       generalize (H1 H2); clear H1; intro H
	 end.

(** Since [match] patterns can share unification variables between hypothesis and conclusion patterns, it is easy to figure out when the conclusion matches a hypothesis.  The [exact] tactic solves a goal completely when given a proof term of the proper type.

   It is also trivial to implement the "introduction rules" for a few of the connectives.  Implementing elimination rules is only a little more work, since we must bind a name for a hypothesis to [destruct].

   The last rule implements modus ponens.  The most interesting part is the use of the Ltac-level [let] with a [fresh] expression.  [fresh] takes in a name base and returns a fresh hypothesis variable based on that name.  We use the new name variable [H] as the name we assign to the result of modus ponens.  The use of [generalize] changes our conclusion to be an implication from [Q].  We clear the original hypothesis and move [Q] into the context with name [H]. *)

Section propositional.
  Variables P Q R : Prop.

  Theorem and_comm : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
    my_tauto.
  Qed.
End propositional.

(** It was relatively easy to implement modus ponens, because we do not lose information by clearing every implication that we use.  If we want to implement a similarly-complete procedure for quantifier instantiation, we need a way to ensure that a particular proposition is not already included among our hypotheses.  To do that effectively, we first need to learn a bit more about the semantics of [match].

It is tempting to assume that [match] works like it does in ML.  In fact, there are a few critical differences in its behavior.  One is that we may include arbitrary expressions in patterns, instead of being restricted to variables and constructors.  Another is that the same variable may appear multiple times, inducing an implicit equality constraint.

There is a related pair of two other differences that are much more important than the others.  [match] has a %\textit{%#<i>#backtracking semantics for failure#</i>#%}%.  In ML, pattern matching works by finding the first pattern to match and then executing its body.  If the body raises an exception, then the overall match raises the same exception.  In Coq, failures in case bodies instead trigger continued search through the list of cases.

For instance, this (unnecessarily verbose) proof script works: *)

Theorem m1 : True.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
Qed.

(** The first case matches trivially, but its body tactic fails, since the conclusion does not begin with a quantifier or implication.  In a similar ML match, that would mean that the whole pattern-match fails.  In Coq, we backtrack and try the next pattern, which also matches.  Its body tactic succeeds, so the overall tactic succeeds as well.

   The example shows how failure can move to a different pattern within a [match].  Failure can also trigger an attempt to find %\textit{%#<i>#a different way of matching a single pattern#</i>#%}%.  Consider another example: *)

Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
  intros; match goal with
            | [ H : _ |- _ ] => pose H
          end.
  (** [[

    r := H1 : R
  ============================
   Q
   ]]

   By applying [pose], a convenient debugging tool for "leaking information out of [match]es," we see that this [match] first tries binding [H] to [H1], which cannot be used to prove [Q].  Nonetheless, the following variation on the tactic succeeds at proving the goal: *)

  match goal with
    | [ H : _ |- _ ] => exact H
  end.
Qed.

(** The tactic first unifies [H] with [H1], as before, but [exact H] fails in that case, so the tactic engine searches for more possible values of [H].  Eventually, it arrives at the correct value, so that [exact H] and the overall tactic succeed. *)

(** Now we are equipped to implement a tactic for checking that a proposition is not among our hypotheses: *)

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

(** We use the equality checking that is built into pattern-matching to see if there is a hypothesis that matches the proposition exactly.  If so, we use the [fail] tactic.  Without arguments, [fail] signals normal tactic failure, as you might expect.  When [fail] is passed an argument [n], [n] is used to count outwards through the enclosing cases of backtracking search.  In this case, [fail 1] says "fail not just in this pattern-matching branch, but for the whole [match]."  The second case will never be tried when the [fail 1] is reached.

This second case, used when [P] matches no hypothesis, checks if [P] is a conjunction.  Other simplifications may have split conjunctions into their component formulas, so we need to check that at least one of those components is also not represented.  To achieve this, we apply the [first] tactical, which takes a list of tactics and continues down the list until one of them does not fail.  The [fail 2] at the end says to [fail] both the [first] and the [match] wrapped around it.

The body of the [?P1 /\ ?P2] case guarantees that, if it is reached, we either succeed completely or fail completely.  Thus, if we reach the wildcard case, [P] is not a conjunction.  We use [idtac], a tactic that would be silly to apply on its own, since its effect is to succeed at doing nothing.  Nonetheless, [idtac] is a useful placeholder for cases like what we see here.

With the non-presence check implemented, it is easy to build a tactic that takes as input a proof term and adds its conclusion as a new hypothesis, only if that conclusion is not already present, failing otherwise. *)

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

(** We see the useful [type of] operator of Ltac.  This operator could not be implemented in Gallina, but it is easy to support in Ltac.  We end up with [t] bound to the type of [pf].  We check that [t] is not already present.  If so, we use a [generalize]/[intro] combo to add a new hypothesis proved by [pf].

   With these tactics defined, we can write a tactic [completer] for adding to the context all consequences of a set of simple first-order formulas. *)

Ltac completer :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
	   | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] =>
             generalize (H H'); clear H; intro H
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] =>
             extend (H X H')
         end.

(** We use the same kind of conjunction and implication handling as previously.  Note that, since [->] is the special non-dependent case of [forall], the fourth rule handles [intro] for implications, too.

   In the fifth rule, when we find a [forall] fact [H] with a premise matching one of our hypotheses, we add the appropriate instantiation of [H]'s conclusion, if we have not already added it.

   We can check that [completer] is working properly: *)

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall x, P x -> S x.
    completer.
    (** [[

  x : A
  H : P x
  H0 : Q x
  H3 : R x
  H4 : S x
  ============================
   S x
   ]] *)

    assumption.
  Qed.
End firstorder.

(** We narrowly avoided a subtle pitfall in our definition of [completer].  Let us try another definition that even seems preferable to the original, to the untrained eye. *)

Ltac completer' :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
	   | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> _, H' : ?P |- _ ] =>
             generalize (H H'); clear H; intro H
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] =>
             extend (H X H')
         end.

(** The only difference is in the modus ponens rule, where we have replaced an unused unification variable [?Q] with a wildcard.  Let us try our example again with this version: *)

Section firstorder'.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo' : forall x, P x -> S x.
    (** [[

    completer'.

    Coq loops forever at this point.  What went wrong? *)
  Abort.
End firstorder'.
