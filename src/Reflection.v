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

Require Import Tactics MoreSpecif.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Proof by Reflection}% *)

(** The last chapter highlighted a very heuristic approach to proving.  In this chapter, we will study an alternative technique, %\textit{%#<i>#proof by reflection#</i>#%}%.  We will write, in Gallina, decision procedures with proofs of correctness, and we will appeal to these procedures in writing very short proofs.  Such a proof is checked by running the decision procedure.  The term %\textit{%#<i>#reflection#</i>#%}% applies because we will need to translate Gallina propositions into values of inductive types representing syntax, so that Gallina programs may analyze them. *)


(** * Proving Evenness *)

(** Proving that particular natural number constants are even is certainly something we would rather have happen automatically.  The Ltac-programming techniques that we learned in the last chapter make it easy to implement such a procedure. *)

Inductive isEven : nat -> Prop :=
  | Even_O : isEven O
  | Even_SS : forall n, isEven n -> isEven (S (S n)).

Ltac prove_even := repeat constructor.

Theorem even_256 : isEven 256.
  prove_even.
Qed.

Print even_256.
(** [[

even_256 = 
Even_SS
  (Even_SS
     (Even_SS
        (Even_SS
    ]]

    ...and so on.  This procedure always works (at least on machines with infinite resources), but it has a serious drawback, which we see when we print the proof it generates that 256 is even.  The final proof term has length linear in the input value.  This seems like a shame, since we could write a trivial and trustworthy program to verify evenness of constants.  The proof checker could simply call our program where needed.

    It is also unfortunate not to have static typing guarantees that our tactic always behaves appropriately.  Other invocations of similar tactics might fail with dynamic type errors, and we would not know about the bugs behind these errors until we happened to attempt to prove complex enough goals.

    The techniques of proof by reflection address both complaints.  We will be able to write proofs like this with constant size overhead beyond the size of the input, and we will do it with verified decision procedures written in Gallina.

    For this example, we begin by using a type from the [MoreSpecif] module to write a certified evenness checker. *)

Print partial.
(** [[

Inductive partial (P : Prop) : Set :=  Proved : P -> [P] | Uncertain : [P]
    ]] *)

(** A [partial P] value is an optional proof of [P]. The notation [[P]] stands for [partial P]. *)

Open Local Scope partial_scope.

(** We bring into scope some notations for the [partial] type.  These overlap with some of the notations we have seen previously for specification types, so they were placed in a separate scope that needs separate opening. *)

Definition check_even (n : nat) : [isEven n].
  Hint Constructors isEven.

  refine (fix F (n : nat) : [isEven n] :=
    match n return [isEven n] with
      | 0 => Yes
      | 1 => No
      | S (S n') => Reduce (F n')
    end); auto.
Defined.

(** We can use dependent pattern-matching to write a function that performs a surprising feat.  When given a [partial P], this function [partialOut] returns a proof of [P] if the [partial] value contains a proof, and it returns a (useless) proof of [True] otherwise.  From the standpoint of ML and Haskell programming, it seems impossible to write such a type, but it is trivial with a [return] annotation. *)

Definition partialOut (P : Prop) (x : [P]) :=
  match x return (match x with
                    | Proved _ => P
                    | Uncertain => True
                  end) with
    | Proved pf => pf
    | Uncertain => I
  end.

(** It may seem strange to define a function like this.  However, it turns out to be very useful in writing a reflective verison of our earlier [prove_even] tactic: *)

Ltac prove_even_reflective :=
  match goal with
    | [ |- isEven ?N] => exact (partialOut (check_even N))
  end.

(** We identify which natural number we are considering, and we "prove" its evenness by pulling the proof out of the appropriate [check_even] call. *)

Theorem even_256' : isEven 256.
  prove_even_reflective.
Qed.

Print even_256'.
(** [[

even_256' = partialOut (check_even 256)
     : isEven 256
    ]]

    We can see a constant wrapper around the object of the proof.  For any even number, this form of proof will suffice.  What happens if we try the tactic with an odd number? *)

Theorem even_255 : isEven 255.
  (** [[

  prove_even_reflective.

  [[

User error: No matching clauses for match goal
  ]]

  Thankfully, the tactic fails.  To see more precisely what goes wrong, we can run manually the body of the [match].

  [[

  exact (partialOut (check_even 255)).

  [[

  Error: The term "partialOut (check_even 255)" has type
 "match check_even 255 with
  | Yes => isEven 255
  | No => True
  end" while it is expected to have type "isEven 255"
  ]]

  As usual, the type-checker performs no reductions to simplify error messages.  If we reduced the first term ourselves, we would see that [check_even 255] reduces to a [No], so that the first term is equivalent to [True], which certainly does not unify with [isEven 255]. *)
Abort.
