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


(** %\chapter{Dependent Data Structures}% *)

(** Our red-black tree example from the last chapter illustrated how dependent types enable static enforcement of data structure invariants.  To find interesting uses of dependent data structures, however, we need not look to the favorite examples of data structures and algorithms textbooks.  More basic examples like length-indexed and heterogeneous lists come up again and again as the building blocks of dependent programs.  There is a surprisingly large design space for this class of data structure, and we will spend this chapter exploring it. *)


(** * More Length-Indexed Lists *)

(** We begin with a deeper look at the length-indexed lists that began the last chapter. *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  (** We might like to have a certified function for selecting an element of an [ilist] by position.  We could do this using subset types and explicit manipulation of proofs, but dependent types let us do it more directly.  It is helpful to define a type family [index], where [index n] is isomorphic to [{m : nat | m < n}].  Such a type family is also often called [Fin] or similar, standing for "finite." *)

  Inductive index : nat -> Set :=
  | First : forall n, index (S n)
  | Next : forall n, index n -> index (S n).

  (** [index] essentially makes a more richly-typed copy of the natural numbers.  Every element is a [First] iterated through applying [Next] a number of times that indicates which number is being selected.

     Now it is easy to pick a [Prop]-free type for a selection function.  As usual, our first implementation attempt will not convince the type checker, and we will attack the deficiencies one at a time.

     [[
  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx => ?
      | Cons _ x ls' => fun idx =>
        match idx with
          | First _ => x
          | Next _ idx' => get ls' idx'
        end
    end.

    We apply the usual wisdom of delaying arguments in [Fixpoint]s so that they may be included in [return] clauses.  This still leaves us with a quandary in each of the [match] cases.  First, we need to figure out how to take advantage of the contradiction in the [Nil] case.  Every [index] has a type of the form [S n], which cannot unify with the [O] value that we learn for [n] in the [Nil] case.  The solution we adopt is another case of [match]-within-[return].

    [[
  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx =>
        match idx in index n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | Cons _ x ls' => fun idx =>
        match idx with
          | First _ => x
          | Next _ idx' => get ls' idx'
        end
    end.

    Now the first [match] case type-checks, and we see that the problem with the [Cons] case is that the pattern-bound variable [idx'] does not have an apparent type compatible with [ls'].  We need to use [match] annotations to make the relationship explicit.  Unfortunately, the usual trick of postponing argument binding will not help us here.  We need to match on both [ls] and [idx]; one or the other must be matched first.  To get around this, we apply a trick that we will call "the convoy pattern," introducing a new function and applying it immediately, to satisfy the type checker.

    [[
  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx =>
        match idx in index n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | Cons _ x ls' => fun idx =>
        match idx in index n' return ilist (pred n') -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun ls' => get ls' idx'
        end ls'
    end.

    There is just one problem left with this implementation.  Though we know that the local [ls'] in the [Next] case is equal to the original [ls'], the type-checker is not satisfied that the recursive call to [get] does not introduce non-termination.  We solve the problem by convoy-binding the partial application of [get] to [ls'], rather than [ls'] by itself. *)

  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx =>
        match idx in index n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | Cons _ x ls' => fun idx =>
        match idx in index n' return (index (pred n') -> A) -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun get_ls' => get_ls' idx'
        end (get ls')
    end.
End ilist.

Implicit Arguments Nil [A].

Section ilist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Fixpoint imap n (ls : ilist A n) {struct ls} : ilist B n :=
    match ls in ilist _ n return ilist B n with
      | Nil => Nil
      | Cons _ x ls' => Cons (f x) (imap ls')
    end.

  Theorem get_imap : forall n (ls : ilist A n) (idx : index n),
    get (imap ls) idx = f (get ls idx).
    induction ls; crush;
      match goal with
        | [ |- context[match ?IDX with First _ => _ | Next _ _ => _ end] ] =>
          dep_destruct IDX; crush
      end.
  Qed.
End ilist_map.
