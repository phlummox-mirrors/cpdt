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
  Variable A : Type.

  Fixpoint ilist (n : nat) : Type :=
    match n with
      | O => unit
      | S n' => A * ilist n'
    end%type.

  Fixpoint index (n : nat) : Type :=
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

  Definition hnil : hlist nil := tt.
  Definition hcons (x : A) (ls : list A) (v : B x) (hls : hlist ls) : hlist (x :: ls) :=
    (v, hls).

  Variable elm : A.

  Fixpoint member (ls : list A) : Type :=
    match ls with
      | nil => Empty_set
      | x :: ls' => (x = elm) + member ls'
    end%type.

  Definition hfirst (x : A) (ls : list A) (pf : x = elm) : member (x :: ls) :=
    inl _ pf.
  Definition hnext (x : A) (ls : list A) (m : member ls) : member (x :: ls) :=
    inr _ m.

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

  Fixpoint happ (ls1 ls2 : list A) {struct ls1} : hlist ls1 -> hlist ls2 -> hlist (ls1 ++ ls2) :=
    match ls1 return hlist ls1 -> hlist ls2 -> hlist (ls1 ++ ls2) with
      | nil => fun _ hls2 => hls2
      | _ :: _ => fun hls1 hls2 => (fst hls1, happ _ _ (snd hls1) hls2)
    end.
End hlist.

Implicit Arguments hnil [A B].
Implicit Arguments hcons [A B x ls].
Implicit Arguments hget [A B elm ls].
Implicit Arguments happ [A B ls1 ls2].

Implicit Arguments hfirst [A elm x ls].
Implicit Arguments hnext [A elm x ls].

Infix ":::" := hcons (right associativity, at level 60).
Infix "+++" := happ (right associativity, at level 60).
