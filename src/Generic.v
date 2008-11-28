(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import String List.

Require Import Tactics DepList.

Set Implicit Arguments.
(* end hide *)


(** %\part{Chapters to be Moved Earlier}

\chapter{Generic Programming}% *)

(** TODO: Prose for this chapter *)


(** * Reflecting Datatype Definitions *)

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


(** * Recursive Definitions *)

Definition fixDenote (T : Type) (dt : datatype) :=
  forall (R : Type), datatypeDenote R dt -> (T -> R).

Definition size T dt (fx : fixDenote T dt) : T -> nat :=
  fx nat (hmake (B := constructorDenote nat) (fun _ _ r => foldr plus 1 r) dt).

Definition Empty_set_fix : fixDenote Empty_set Empty_set_dt :=
  fun R _ emp => match emp with end.
Eval compute in size Empty_set_fix.

Definition unit_fix : fixDenote unit unit_dt :=
  fun R cases _ => (fst cases) tt inil.
Eval compute in size unit_fix.

Definition bool_fix : fixDenote bool bool_dt :=
  fun R cases b => if b
    then (fst cases) tt inil
    else (fst (snd cases)) tt inil.
Eval compute in size bool_fix.

Definition nat_fix : fixDenote nat nat_dt :=
  fun R cases => fix F (n : nat) : R :=
    match n with
      | O => (fst cases) tt inil
      | S n' => (fst (snd cases)) tt (icons (F n') inil)
    end.
Eval cbv beta iota delta -[plus] in size nat_fix.

Definition list_fix (A : Type) : fixDenote (list A) (list_dt A) :=
  fun R cases => fix F (ls : list A) : R :=
    match ls with
      | nil => (fst cases) tt inil
      | x :: ls' => (fst (snd cases)) x (icons (F ls') inil)
    end.
Eval cbv beta iota delta -[plus] in fun A => size (@list_fix A).

Definition tree_fix (A : Type) : fixDenote (tree A) (tree_dt A) :=
  fun R cases => fix F (t : tree A) : R :=
    match t with
      | Leaf x => (fst cases) x inil
      | Node t1 t2 => (fst (snd cases)) tt (icons (F t1) (icons (F t2) inil))
    end.
Eval cbv beta iota delta -[plus] in fun A => size (@tree_fix A).


(** ** Pretty-Printing *)

Record print_constructor (c : constructor) : Type := PI {
  printName : string;
  printNonrec : nonrecursive c -> string
}.

Notation "^" := (PI (Con _ _)).

Definition print_datatype := hlist print_constructor.

Open Local Scope string_scope.

Definition print T dt (pr : print_datatype dt) (fx : fixDenote T dt) : T -> string :=
  fx string (hmap (B1 := print_constructor) (B2 := constructorDenote string)
    (fun _ pc x r => printName pc ++ "(" ++ printNonrec pc x
      ++ foldr (fun s acc => ", " ++ s ++ acc) ")" r) pr).

Eval compute in print hnil Empty_set_fix.
Eval compute in print (^ "tt" (fun _ => "") ::: hnil) unit_fix.
Eval compute in print (^ "true" (fun _ => "")
  ::: ^ "false" (fun _ => "")
  ::: hnil) bool_fix.

Definition print_nat := print (^ "O" (fun _ => "")
  ::: ^ "S" (fun _ => "")
  ::: hnil) nat_fix.
Eval cbv beta iota delta -[append] in print_nat.
Eval simpl in print_nat 0.
Eval simpl in print_nat 1.
Eval simpl in print_nat 2.

Eval cbv beta iota delta -[append] in fun A (pr : A -> string) =>
  print (^ "nil" (fun _ => "")
  ::: ^ "cons" pr
  ::: hnil) (@list_fix A).
Eval cbv beta iota delta -[append] in fun A (pr : A -> string) =>
  print (^ "Leaf" pr
  ::: ^ "Node" (fun _ => "")
  ::: hnil) (@tree_fix A).
