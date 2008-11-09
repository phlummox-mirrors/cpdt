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

Require Import Axioms Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Type-Theoretic Interpreters}% *)

(** TODO: Prose for this chapter *)


(** * Simply-Typed Lambda Calculus *)

Module STLC.
  Inductive type : Type :=
  | Nat : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

  Section vars.
    Variable var : type -> Type.

    Inductive exp : type -> Type :=
    | Var : forall t,
      var t
      -> exp t

    | Const : nat -> exp Nat
    | Plus : exp Nat -> exp Nat -> exp Nat

    | App : forall t1 t2,
      exp (t1 --> t2)
      -> exp t1
      -> exp t2
    | Abs : forall t1 t2,
      (var t1 -> exp t2)
      -> exp (t1 --> t2).
  End vars.

  Definition Exp t := forall var, exp var t.

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments Plus [var].
  Implicit Arguments App [var t1 t2].
  Implicit Arguments Abs [var t1 t2].

  Notation "# v" := (Var v) (at level 70).

  Notation "^ n" := (Const n) (at level 70).
  Infix "++" := Plus.

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
    end.

  Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
    match e in (exp _ t) return (typeDenote t) with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).

  Section cfold.
    Variable var : type -> Type.

    Fixpoint cfold t (e : exp var t) {struct e} : exp var t :=
      match e in exp _ t return exp _ t with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' ++ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => Abs (fun x => cfold (e' x))
      end.
  End cfold.

  Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).

  Lemma cfold_correct : forall t (e : exp _ t),
    expDenote (cfold e) = expDenote e.
    induction e; crush; try (ext_eq; crush);
      repeat (match goal with
                | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
              end; crush).
  Qed.

  Theorem Cfold_correct : forall t (E : Exp t),
    ExpDenote (Cfold E) = ExpDenote E.
    unfold ExpDenote, Cfold; intros; apply cfold_correct.
  Qed.
End STLC.
