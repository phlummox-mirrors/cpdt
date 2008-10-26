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
