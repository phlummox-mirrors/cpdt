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

Require Import Tactics DepList.

Set Implicit Arguments.
(* end hide *)


(** %\part{Chapters to be Moved Earlier}

\chapter{Generic Programming}% *)

(** TODO: Prose for this chapter *)


(** * Simple Algebraic Datatypes *)

Record constructor : Type := Con {
  nonrecursive : Type;
  recursive : nat
}.

Definition datatype := list constructor.

Definition Empty_set_dt : datatype := nil.
Definition unit_dt : datatype := Con unit 0 :: nil.
Definition bool_dt : datatype := Con unit 0 :: Con unit 0 :: nil.
Definition nat_dt : datatype := Con unit 0 :: Con unit 1 :: nil.
Definition list_dt (A : Type) : datatype := Con unit 0 :: Con A 1 :: nil.

Section tree.
  Variable A : Type.

  Inductive tree : Type :=
  | Leaf : A -> tree
  | Node : tree -> tree -> tree.
End tree.

Definition tree_dt (A : Type) : datatype := Con A 0 :: Con unit 2 :: nil.

Section denote.
  Variable T : Type.

  Definition constructorDenote (c : constructor) :=
    nonrecursive c -> ilist T (recursive c) -> T.

  Definition datatypeDenote := hlist constructorDenote.
End denote.

Notation "[ ! , ! ~> x ]" := ((fun _ _ => x) : constructorDenote _ (Con _ _)).
Notation "[ v , ! ~> x ]" := ((fun v _ => x) : constructorDenote _ (Con _ _)).
Notation "[ ! , r # n ~> x ]" := ((fun _ r => x) : constructorDenote _ (Con _ n)).
Notation "[ v , r # n ~> x ]" := ((fun v r => x) : constructorDenote _ (Con _ n)).

Definition Empty_set_den : datatypeDenote Empty_set Empty_set_dt :=
  hnil.
Definition unit_den : datatypeDenote unit unit_dt :=
  [!, ! ~> tt] ::: hnil.
Definition bool_den : datatypeDenote bool bool_dt :=
  [!, ! ~> true] ::: [!, ! ~> false] ::: hnil.
Definition nat_den : datatypeDenote nat nat_dt :=
  [!, ! ~> O] ::: [!, r # 1 ~> S (hd r)] ::: hnil.
Definition list_den (A : Type) : datatypeDenote (list A) (list_dt A) :=
  [!, ! ~> nil] ::: [x, r # 1 ~> x :: hd r] ::: hnil.
Definition tree_den (A : Type) : datatypeDenote (tree A) (tree_dt A) :=
  [v, ! ~> Leaf v] ::: [!, r # 2 ~> Node (hd r) (hd (tl r))] ::: hnil.
