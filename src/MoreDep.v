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


(** %\chapter{More Dependent Types}% *)

(** Subset types and their relatives help us integrate verification with programming.  Though they reorganize the certified programmer's workflow, they tend not to have deep effects on proofs.  We write largely the same proofs as we would for classical verification, with some of the structure moved into the programs themselves.  It turns out that, when we use dependent types to their full potential, we warp the development and proving process even more than that, picking up "free theorems" to the extent that often a certified program is hardly more complex than its uncertified counterpart in Haskell or ML.

   In particular, we have only scratched the tip of the iceberg that is Coq's inductive definition mechanism.  The inductive types we have seen so far have their counterparts in the other proof assistants that we surveyed in Chapter 1.  This chapter explores the strange new world of dependent inductive datatypes (that is, dependent inductive types outside [Prop]), a possibility which sets Coq apart from all of the competition not based on type theory. *)


(** * Length-Indexed Lists *)

(** Many introductions to dependent types start out by showing how to use them to eliminate array bounds checks.  When the type of an array tells you how many elements it has, your compiler can detect out-of-bounds dereferences statically.  Since we are working in a pure functional language, the next best thing is length-indexed lists, which the following code defines. *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

(** We see that, within its section, [ilist] is given type [nat -> Set].  Previously, every inductive type we have seen has either had plain [Set] as its type or has been a predicate with some type ending in [Prop].  The full generality of inductive definitions lets us integrate the expressivity of predicates directly into our normal programming.

   The [nat] argument to [ilist] tells us the length of the list.  The types of [ilist]'s constructors tell us that a [Nil] list has length [O] and that a [Cons] list has length one greater than the length of its sublist.  We may apply [ilist] to any natural number, even natural numbers that are only known at runtime.  It is this breaking of the %\textit{%#<i>#phase distinction#</i>#%}% that characterizes [ilist] as %\textit{%#<i>#dependently typed#</i>#%}%.

   In expositions of list types, we usually see the length function defined first, but here that would not be a very productive function to code.  Instead, let us implement list concatenation.

   [[
Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) {struct ls1} : ilist (n1 + n2) :=
  match ls1 with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app ls1' ls2)
  end.

  Coq is not happy with this definition:

[[
The term "ls2" has type "ilist n2" while it is expected to have type
 "ilist (?14 + n2)"
]]

  We see the return of a problem we have considered before.  Without explicit annotations, Coq does not enrich our typing assumptions in the branches of a [match] expression.  It is clear that the unification variable [?14] should be resolved to 0 in this context, so that we have [0 + n2] reducing to [n2], but Coq does not realize that.  We cannot fix the problem using just the simple [return] clauses we applied in the last chapter.  We need to combine a [return] clause with a new kind of annotation, an [in] clause. *)

Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) {struct ls1} : ilist (n1 + n2) :=
  match ls1 in (ilist n1) return (ilist (n1 + n2)) with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app ls1' ls2)
  end.

(** This version of [app] passes the type checker.  Using [return] alone allowed us to express a dependency of the [match] result type on the %\textit{%#<i>#value#</i>#%}% of the discriminee.  What [in] adds to our arsenal is a way of expressing a dependency on the %\textit{%#<i>#type#</i>#%}% of the discriminee.  Specifically, the [n1] in the [in] clause above is a %\textit{%#<i>#binding occurrence#</i>#%}% whose scope is the [return] clause.

We may use [in] clauses only to bind names for the arguments of an inductive type family.  That is, each [in] clause must be an inductive type family name applied to a sequence of underscores and variable names of the proper length.  The positions for %\textit{%#<i>#parameters#</i>#%}% to the type family must all be underscores.  Parameters are those arguments declared with section variables or with entries to the left of the first colon in an inductive definition.  They cannot vary depending on which constructor was used to build the discriminee, so Coq prohibits pointless matches on them.  It is those arguments defined in the type to the right of the colon that we may name with [in] clauses.

Our [app] function could be typed in so-called %\textit{%#<i>#stratified#</i>#%}% type systems, which avoid true dependency.  We could consider the length indices to lists to live in a separate, compile-time-only universe from the lists themselves.  Our next example would be harder to implement in a stratified system.  We write an injection function from regular lists to length-indexed lists.  A stratified implementation would need to duplicate the definition of lists across compile-time and run-time versions, and the run-time versions would need to be indexed by the compile-time versions. *)

Fixpoint inject (ls : list A) : ilist (length ls) :=
  match ls return (ilist (length ls)) with
    | nil => Nil
    | h :: t => Cons h (inject t)
  end.

(** We can define an inverse conversion and prove that it really is an inverse. *)

Fixpoint unject n (ls : ilist n) {struct ls} : list A :=
  match ls with
    | Nil => nil
    | Cons _ h t => h :: unject t
  end.

Theorem inject_inverse : forall ls, unject (inject ls) = ls.
  induction ls; crush.
Qed.

(** Now let us attempt a function that is surprisingly tricky to write.  In ML, the list head function raises an exception when passed an empty list.  With length-indexed lists, we can rule out such invalid calls statically, and here is a first attempt at doing so.

[[
Definition hd n (ls : ilist (S n)) : A :=
  match ls with
    | Nil => ???
    | Cons _ h _ => h
  end.

It is not clear what to write for the [Nil] case, so we are stuck before we even turn our function over to the type checker.  We could try omitting the [Nil] case:

[[
Definition hd n (ls : ilist (S n)) : A :=
  match ls with
    | Cons _ h _ => h
  end.

[[
Error: Non exhaustive pattern-matching: no clause found for pattern Nil
]]

Unlike in ML, we cannot use inexhaustive pattern matching, becuase there is no conception of a %\texttt{%#<tt>#Match#</tt>#%}% exception to be thrown.  We might try using an [in] clause somehow.

[[
Definition hd n (ls : ilist (S n)) : A :=
  match ls in (ilist (S n)) with
    | Cons _ h _ => h
  end.

[[
Error: The reference n was not found in the current environment
]]

In this and other cases, we feel like we want [in] clauses with type family arguments that are not variables.  Unfortunately, Coq only supports variables in those positions.  A completely general mechanism could only be supported with a solution to the problem of higher-order unification, which is undecidable.  There %\textit{%#<i>#are#</i>#%}% useful heuristics for handling non-variable indices which are gradually making their way into Coq, but we will spend some time in this and the next few chapters on effective pattern matching on dependent types using only the primitive [match] annotations.

Our final, working attempt at [hd] uses an auxiliary function and a surprising [return] annotation. *)

Definition hd' n (ls : ilist n) :=
  match ls in (ilist n) return (match n with O => unit | S _ => A end) with
    | Nil => tt
    | Cons _ h _ => h
  end.

Definition hd n (ls : ilist (S n)) : A := hd' ls.

(** We annotate our main [match] with a type that is itself a [match].  We write that the function [hd'] returns [unit] when the list is empty and returns the carried type [A] in all other cases.  In the definition of [hd], we just call [hd'].  Because the index of [ls] is known to be nonzero, the type checker reduces the [match] in the type of [hd'] to [A]. *)

End ilist.
