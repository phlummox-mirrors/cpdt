(* Copyright (c) 2008-2009, Adam Chlipala
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
  Infix "+^" := Plus (left associativity, at level 79).

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

  Definition zero : Exp Nat := fun _ => ^0.
  Definition one : Exp Nat := fun _ => ^1.
  Definition zpo : Exp Nat := fun _ => zero _ +^ one _.
  Definition ident : Exp (Nat --> Nat) := fun _ => \x, #x.
  Definition app_ident : Exp Nat := fun _ => ident _ @ zpo _.
  Definition app : Exp ((Nat --> Nat) --> Nat --> Nat) := fun _ =>
    \f, \x, #f @ #x.
  Definition app_ident' : Exp Nat := fun _ => app _ @ ident _ @ zpo _.

  (* EX: Define an interpreter for [Exp]s. *)

(* begin thide *)
  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
    end.

  Fixpoint expDenote t (e : exp typeDenote t) : typeDenote t :=
    match e with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).
(* end thide *)

  Eval compute in ExpDenote zero.
  Eval compute in ExpDenote one.
  Eval compute in ExpDenote zpo.
  Eval compute in ExpDenote ident.
  Eval compute in ExpDenote app_ident.
  Eval compute in ExpDenote app.
  Eval compute in ExpDenote app_ident'.

  (* EX: Define a constant-folding function for [Exp]s. *)

(* begin thide *)
  Section cfold.
    Variable var : type -> Type.

    Fixpoint cfold t (e : exp var t) : exp var t :=
      match e with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' return _ with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' +^ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => Abs (fun x => cfold (e' x))
      end.
  End cfold.

  Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).
(* end thide *)

  (* EX: Prove the correctness of constant-folding. *)

(* begin thide *)
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
(* end thide *)
End STLC.


(** * Adding Products and Sums *)

Module PSLC.
  (* EX: Extend the development with products and sums. *)

(* begin thide *)
  Inductive type : Type :=
  | Nat : type
  | Arrow : type -> type -> type
  | Prod : type -> type -> type
  | Sum : type -> type -> type.
(* end thide *)

  Infix "-->" := Arrow (right associativity, at level 62).
  Infix "**" := Prod (right associativity, at level 61).
  Infix "++" := Sum (right associativity, at level 60).

(* begin thide *)
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
      -> exp (t1 --> t2)

    | Pair : forall t1 t2,
      exp t1
      -> exp t2
      -> exp (t1 ** t2)
    | Fst : forall t1 t2,
      exp (t1 ** t2)
      -> exp t1
    | Snd : forall t1 t2,
      exp (t1 ** t2)
      -> exp t2

    | Inl : forall t1 t2,
      exp t1
      -> exp (t1 ++ t2)
    | Inr : forall t1 t2,
      exp t2
      -> exp (t1 ++ t2)
    | SumCase : forall t1 t2 t,
      exp (t1 ++ t2)
      -> (var t1 -> exp t)
      -> (var t2 -> exp t)
      -> exp t.
  End vars.

  Definition Exp t := forall var, exp var t.
(* end thide *)

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments Abs [var t1 t2].
  Implicit Arguments Inl [var t1 t2].
  Implicit Arguments Inr [var t1 t2].

  Notation "# v" := (Var v) (at level 70).

  Notation "^ n" := (Const n) (at level 70).
  Infix "+^" := Plus (left associativity, at level 78).

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

  Notation "[ e1 , e2 ]" := (Pair e1 e2).
  Notation "#1 e" := (Fst e) (at level 75).
  Notation "#2 e" := (Snd e) (at level 75).

  Notation "'case' e 'of' x => e1 | y => e2" := (SumCase e (fun x => e1) (fun y => e2))
    (at level 79).

  Definition swap : Exp (Nat ** Nat --> Nat ** Nat) := fun _ =>
    \p, [#2 #p, #1 #p].
  Definition zo : Exp (Nat ** Nat) := fun _ => [^0, ^1].
  Definition swap_zo : Exp (Nat ** Nat) := fun _ => swap _ @ zo _.

  Definition natOut : Exp (Nat ++ Nat --> Nat) := fun _ =>
    \s, case #s of x => #x | y => #y +^ #y.
  Definition ns1 : Exp (Nat ++ Nat) := fun _ => Inl (^3).
  Definition ns2 : Exp (Nat ++ Nat) := fun _ => Inr (^5).
  Definition natOut_ns1 : Exp Nat := fun _ => natOut _ @ ns1 _.
  Definition natOut_ns2 : Exp Nat := fun _ => natOut _ @ ns2 _.

(* begin thide *)
  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
      | t1 ** t2 => typeDenote t1 * typeDenote t2
      | t1 ++ t2 => typeDenote t1 + typeDenote t2
    end%type.

  Fixpoint expDenote t (e : exp typeDenote t) : typeDenote t :=
    match e with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)

      | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
      | Fst _ _ e' => fst (expDenote e')
      | Snd _ _ e' => snd (expDenote e')

      | Inl _ _ e' => inl _ (expDenote e')
      | Inr _ _ e' => inr _ (expDenote e')
      | SumCase _ _ _ e' e1 e2 =>
        match expDenote e' with
          | inl v => expDenote (e1 v)
          | inr v => expDenote (e2 v)
        end
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).
(* end thide *)

  Eval compute in ExpDenote swap.
  Eval compute in ExpDenote zo.
  Eval compute in ExpDenote swap_zo.

  Eval compute in ExpDenote natOut.
  Eval compute in ExpDenote ns1.
  Eval compute in ExpDenote ns2.
  Eval compute in ExpDenote natOut_ns1.
  Eval compute in ExpDenote natOut_ns2.

(* begin thide *)
  Section cfold.
    Variable var : type -> Type.

    Definition pairOutType t :=
      match t return Type with
        | t1 ** t2 => option (exp var t1 * exp var t2)
        | _ => unit
      end.

    Definition pairOutDefault (t : type) : pairOutType t :=
      match t return pairOutType t with
        | _ ** _ => None
        | _ => tt
      end.

    Definition pairOut t1 t2 (e : exp var (t1 ** t2))
      : option (exp var t1 * exp var t2) :=
      match e in exp _ t return pairOutType t with
        | Pair _ _ e1 e2 => Some (e1, e2)
        | _ => pairOutDefault _
      end.

    Fixpoint cfold t (e : exp var t) : exp var t :=
      match e with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' return _ with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' +^ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => Abs (fun x => cfold (e' x))

        | Pair _ _ e1 e2 => [cfold e1, cfold e2]
        | Fst t1 _ e' =>
          let e'' := cfold e' in
            match pairOut e'' with
              | None => #1 e''
              | Some (e1, _) => e1
            end
        | Snd _ _ e' =>
          let e'' := cfold e' in
            match pairOut e'' with
              | None => #2 e''
              | Some (_, e2) => e2
            end

        | Inl _ _ e' => Inl (cfold e')
        | Inr _ _ e' => Inr (cfold e')
        | SumCase _ _ _ e' e1 e2 =>
          case cfold e' of
            x => cfold (e1 x)
          | y => cfold (e2 y)
      end.
  End cfold.

  Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).

  Section pairs.
    Variables A B : Type.

    Variable v1 : A.
    Variable v2 : B.
    Variable v : A * B.

    Theorem pair_eta1 : (v1, v2) = v -> v1 = fst v.
      destruct v; crush.
    Qed.

    Theorem pair_eta2 : (v1, v2) = v -> v2 = snd v.
      destruct v; crush.
    Qed.
  End pairs.

  Hint Resolve pair_eta1 pair_eta2.

  Lemma cfold_correct : forall t (e : exp _ t),
    expDenote (cfold e) = expDenote e.
    induction e; crush; try (ext_eq; crush);
      repeat (match goal with
                | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
                | [ |- match ?E with inl _ => _ | inr _ => _ end = _ ] => destruct E
              end; crush); eauto.
  Qed.

  Theorem Cfold_correct : forall t (E : Exp t),
    ExpDenote (Cfold E) = ExpDenote E.
    unfold ExpDenote, Cfold; intros; apply cfold_correct.
  Qed.
(* end thide *)
End PSLC.
