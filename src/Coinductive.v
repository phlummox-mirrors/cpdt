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


(** %\chapter{Infinite Data and Proofs}% *)

(** In lazy functional programming languages like Haskell, infinite data structures are everywhere.  Infinite lists and more exotic datatypes provide convenient abstractions for communication between parts of a program.  Achieving similar convenience without infinite lazy structures would, in many cases, require acrobatic inversions of control flow.

Laziness is easy to implement in Haskell, where all the definitions in a program may be thought of as mutually recursive.  In such an unconstrained setting, it is easy to implement an infinite loop when you really meant to build an infinite list, where any finite prefix of the list should be forceable in finite time.  Haskell programmers learn how to avoid such slip-ups.  In Coq, such a laissez-faire policy is not good enough.

We spent some time in the last chapter discussing the Curry-Howard isomorphism, where proofs are identified with functional programs.  In such a setting, infinite loops, intended or otherwise, are disastrous.  If Coq allowed the full breadth of definitions that Haskell did, we could code up an infinite loop and use it to prove any proposition vacuously.  That is, the addition of general recursion would make CIC %\textit{%#<i>#inconsistent#</i>#%}%.

There are also algorithmic considerations that make universal termination very desirable.  We have seen how tactics like [reflexivity] compare terms up to equivalence under computational rules.  Calls to recursive, pattern-matching functions are simplified automatically, with no need for explicit proof steps.  It would be very hard to hold onto that kind of benefit if it became possible to write non-terminating programs; we would be running smack into the halting problem.

One solution is to use types to contain the possibility of non-termination.  For instance, we can create a "non-termination monad," inside which we must write all of our general-recursive programs.  In later chapters, we will spend some time on this idea and its applications.  For now, we will just say that it is a heavyweight solution, and so we would like to avoid it whenever possible.

Luckily, Coq has special support for a class of lazy data structures that happens to contain most examples found in Haskell.  That mechanism, %\textit{%#<i>#co-inductive types#</i>#%}%, is the subject of this chapter. *)


(** * Computing with Infinite Data *)

(** Let us begin with the most basic type of infinite data, %\textit{%#<i>#streams#</i>#%}%, or lazy lists. *)

Section stream.
  Variable A : Set.

  CoInductive stream : Set :=
  | Cons : A -> stream -> stream.
End stream.

(** The definition is surprisingly simple.  Starting from the definition of [list], we just need to change the keyword [Inductive] to [CoInductive].  We could have left a [Nil] constructor in our definition, but we will leave it out to force all of our streams to be infinite.

   How do we write down a stream constant?  Obviously simple application of constructors is not good enough, since we could only denote finite objects that way.  Rather, whereas recursive definitions were necessary to %\textit{%#<i>#use#</i>#%}% values of recursive inductive types effectively, here we find that we need %\textit{%#<i>#co-recursive definitions#</i>#%}% to %\textit{%#<i>#build#</i>#%}% values of co-inductive types effectively.

   We can define a stream consisting only of zeroes. *)

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

(** We can also define a stream that alternates between [true] and [false]. *)

CoFixpoint trues : stream bool := Cons true falses
with falses : stream bool := Cons false trues.

(** Co-inductive values are fair game as arguments to recursive functions, and we can use that fact to write a function to take a finite approximation of a stream. *)

Fixpoint approx A (s : stream A) (n : nat) {struct n} : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx t n'
      end
  end.

Eval simpl in approx zeroes 10.
(** [[

     = 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: nil
     : list nat
     ]] *)
Eval simpl in approx trues 10.
(** [[

     = true
       :: false
          :: true
             :: false
                :: true :: false :: true :: false :: true :: false :: nil
     : list bool
     ]] *)

(** So far, it looks like co-inductive types might be a magic bullet, allowing us to import all of the Haskeller's usual tricks.  However, there are important restrictions that are dual to the restrictions on the use of inductive types.  Fixpoints %\textit{%#<i>#consume#</i>#%}% values of inductive types, with restrictions on which %\textit{%#<i>#arguments#</i>#%}% may be passed in recursive calls.  Dually, co-fixpoints %\textit{%#<i>#produce#</i>#%}% values of co-inductive types, with restrictions on what may be done with the %\textit{%#<i>#results#</i>#%}% of co-recursive calls.

The restriction for co-inductive types shows up as the %\textit{%#<i>#guardedness condition#</i>#%}%, and it can be broken into two parts.  First, consider this stream definition, which would be legal in Haskell.

[[
CoFixpoint looper : stream nat := looper.
[[
Error:
Recursive definition of looper is ill-formed.
In environment
looper : stream nat

unguarded recursive call in "looper"
*)

(** The rule we have run afoul of here is that %\textit{%#<i>#every co-recursive call must be guarded by a constructor#</i>#%}%; that is, every co-recursive call must be a direct argument to a constructor of the co-inductive type we are generating.  It is a good thing that this rule is enforced.  If the definition of [looper] were accepted, our [approx] function would run forever when passed [looper], and we would have fallen into inconsistency.

The second rule of guardedness is easiest to see by first introducing a more complicated, but legal, co-fixpoint. *)

Section map.
  Variables A B : Set.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

(** This code is a literal copy of that for the list [map] function, with the [Nil] case removed and [Fixpoint] changed to [CoFixpoint].  Many other standard functions on lazy data structures can be implemented just as easily.  Some, like [filter], cannot be implemented.  Since the predicate passed to [filter] may reject every element of the stream, we cannot satisfy even the first guardedness condition.

   The second condition is subtler.  To illustrate it, we start off with another co-recursive function definition that %\textit{%#<i>#is#</i>#%}% legal.  The function [interleaves] takes two streams and produces a new stream that alternates between their elements. *)

Section interleave.
  Variable A : Set.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
      | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

(** Now say we want to write a weird stuttering version of [map] that repeats elements in a particular way, based on interleaving. *)

Section map'.
  Variables A B : Set.
  Variable f : A -> B.

  (** [[

  CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' s)) (Cons (f h) (map' s))
    end. *)

  (** We get another error message about an unguarded recursive call.  This is because we are violating the second guardedness condition, which says that, not only must co-recursive calls be arguments to constructors, there must also %\textit{%#<i>#not be anything but [match]es and calls to constructors of the same co-inductive type#</i>#%}% wrapped around these immediate uses of co-recursive calls.  The actual implemented rule for guardedness is a little more lenient than what we have just stated, but you can count on the illegality of any exception that would enhance the expressive power of co-recursion.

     Why enforce a rule like this?  Imagine that, instead of [interleave], we had called some other, less well-behaved function on streams.  Perhaps this other function might be defined mutually with [map'].  It might deconstruct its first argument, retrieving [map' s] from within [Cons (f h) (map' s)].  Next it might try a [match] on this retrieved value, which amounts to deconstructing [map' s].  To figure out how this [match] turns out, we need to know the top-level structure of [map' s], but this is exactly what we started out trying to determine!  We run into a loop in the evaluation process, and we have reached a witness of inconsistency if we are evaluating [approx (map' s) 1] for any [s]. *)
End map'.

