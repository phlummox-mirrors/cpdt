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
(* end hide *)


(** * Arithmetic expressions over natural numbers *)

  (** ** Source language *)

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.


  (** ** Target language *)

Inductive instr : Set :=
| IConst : nat -> instr
| IBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | IConst n => Some (n :: s)
    | IBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.

Fixpoint progDenote (p : prog) (s : stack) {struct p} : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.


  (** ** Translation *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => IConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ IBinop b :: nil
  end.


  (** ** Translation correctness *)

Lemma compileCorrect' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e.

  intros.
  unfold compile.
  unfold expDenote.
  simpl.
  reflexivity.

  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.
  rewrite app_ass.
  rewrite IHe2.
  rewrite app_ass.
  rewrite IHe1.
  simpl.
  reflexivity.
Abort.

Lemma compileCorrect' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

Theorem compileCorrect : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intro.
  rewrite (app_nil_end (compile e)).
  rewrite compileCorrect'.
  reflexivity.
Qed.
