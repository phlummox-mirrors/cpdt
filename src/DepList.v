(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Dependent list types presented in Chapter 8 *)

Require Import List.

Set Implicit Arguments.


Section ilist.
  Variable A : Set.

  Fixpoint ilist (n : nat) : Set :=
    match n with
      | O => unit
      | S n' => A * ilist n'
    end%type.

  Fixpoint index (n : nat) : Set :=
    match n with
      | O => Empty_set
      | S n' => option (index n')
    end.

  Fixpoint get (n : nat) : ilist n -> index n -> A :=
    match n return ilist n -> index n -> A with
      | O => fun _ idx => match idx with end
      | S n' => fun ls idx =>
        match idx with
          | None => fst ls
          | Some idx' => get n' (snd ls) idx'
        end
    end.
End ilist.

Implicit Arguments get [A n].

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Fixpoint hlist (ls : list A) : Type :=
    match ls with
      | nil => unit
      | x :: ls' => B x * hlist ls'
    end%type.

  Variable elm : A.

  Fixpoint member (ls : list A) : Type :=
    match ls with
      | nil => Empty_set
      | x :: ls' => (x = elm) + member ls'
    end%type.

  Fixpoint hget (ls : list A) : hlist ls -> member ls -> B elm :=
    match ls return hlist ls -> member ls -> B elm with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx =>
        match idx with
          | inl pf => match pf with
                        | refl_equal => fst mls
                      end
          | inr idx' => hget ls' (snd mls) idx'
        end
    end.
End hlist.

Implicit Arguments hget [A B elm ls].
