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

(** Our red-black tree example from the last chapter illustrated how dependent types enable static enforcement of data structure invariants.  To find interesting uses of dependent data structures, however, we need not look to the favorite examples of data structures and algorithms textbooks.  More basic examples like known-length and heterogeneous lists prop up again and again as the building blocks of dependent programs.  There is a surprisingly large design space for this class of data structure, and we will spend this chapter exploring it. *)


(** * More Known-Length Lists *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Inductive index : nat -> Set :=
  | First : forall n, index (S n)
  | Next : forall n, index n -> index (S n).

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
