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

Require Import AxiomsImpred Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Certifying Extensional Transformations}% *)

(** TODO: Prose for this chapter *)


(** * Simply-Typed Lambda Calculus *)

Module STLC.
  Module Source.
    Inductive type : Type :=
    | TNat : type
    | Arrow : type -> type -> type.

    Notation "'Nat'" := TNat : source_scope.
    Infix "-->" := Arrow (right associativity, at level 60) : source_scope.

    Open Scope source_scope.
    Bind Scope source_scope with type.
    Delimit Scope source_scope with source.

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

    Notation "# v" := (Var v) (at level 70) : source_scope.

    Notation "^ n" := (Const n) (at level 70) : source_scope.
    Infix "+^" := Plus (left associativity, at level 79) : source_scope.

    Infix "@" := App (left associativity, at level 77) : source_scope.
    Notation "\ x , e" := (Abs (fun x => e)) (at level 78) : source_scope.
    Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78) : source_scope.

    Bind Scope source_scope with exp.

    Definition zero : Exp Nat := fun _ => ^0.
    Definition one : Exp Nat := fun _ => ^1.
    Definition zpo : Exp Nat := fun _ => zero _ +^ one _.
    Definition ident : Exp (Nat --> Nat) := fun _ => \x, #x.
    Definition app_ident : Exp Nat := fun _ => ident _ @ zpo _.
    Definition app : Exp ((Nat --> Nat) --> Nat --> Nat) := fun _ =>
      \f, \x, #f @ #x.
    Definition app_ident' : Exp Nat := fun _ => app _ @ ident _ @ zpo _.

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
  End Source.

  Module CPS.
    Inductive type : Type :=
    | TNat : type
    | Cont : type -> type
    | TUnit : type
    | Prod : type -> type -> type.

    Notation "'Nat'" := TNat : cps_scope.
    Notation "'Unit'" := TUnit : cps_scope.
    Notation "t --->" := (Cont t) (at level 61) : cps_scope.
    Infix "**" := Prod (right associativity, at level 60) : cps_scope.

    Bind Scope cps_scope with type.
    Delimit Scope cps_scope with cps.

    Section vars.
      Variable var : type -> Type.

      Inductive prog : Type :=
      | PHalt :
        var Nat
        -> prog
      | App : forall t,
        var (t --->)
        -> var t
        -> prog
      | Bind : forall t,
        primop t
        -> (var t -> prog)
        -> prog

      with primop : type -> Type :=
      | Var : forall t,
        var t
        -> primop t
        
      | Const : nat -> primop Nat
      | Plus : var Nat -> var Nat -> primop Nat
        
      | Abs : forall t,
        (var t -> prog)
        -> primop (t --->)

      | Pair : forall t1 t2,
        var t1
        -> var t2
        -> primop (t1 ** t2)
      | Fst : forall t1 t2,
        var (t1 ** t2)
        -> primop t1
      | Snd : forall t1 t2,
        var (t1 ** t2)
        -> primop t2.
    End vars.

    Implicit Arguments PHalt [var].
    Implicit Arguments App [var t].

    Implicit Arguments Var [var t].
    Implicit Arguments Const [var].
    Implicit Arguments Plus [var].
    Implicit Arguments Abs [var t].
    Implicit Arguments Pair [var t1 t2].
    Implicit Arguments Fst [var t1 t2].
    Implicit Arguments Snd [var t1 t2].

    Notation "'Halt' x" := (PHalt x) (no associativity, at level 75) : cps_scope.
    Infix "@@" := App (no associativity, at level 75) : cps_scope.
    Notation "x <- p ; e" := (Bind p (fun x => e))
      (right associativity, at level 76, p at next level) : cps_scope.
    Notation "! <- p ; e" := (Bind p (fun _ => e))
      (right associativity, at level 76, p at next level) : cps_scope.

    Notation "# v" := (Var v) (at level 70) : cps_scope.

    Notation "^ n" := (Const n) (at level 70) : cps_scope.
    Infix "+^" := Plus (left associativity, at level 79) : cps_scope.

    Notation "\ x , e" := (Abs (fun x => e)) (at level 78) : cps_scope.
    Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78) : cps_scope.

    Notation "[ x1 , x2 ]" := (Pair x1 x2) (at level 73) : cps_scope.
    Notation "#1 x" := (Fst x) (at level 72) : cps_scope.
    Notation "#2 x" := (Snd x) (at level 72) : cps_scope.

    Bind Scope cps_scope with prog primop.

    Open Scope cps_scope.

    Fixpoint typeDenote (t : type) : Set :=
      match t with
        | Nat => nat
        | t' ---> => typeDenote t' -> nat
        | Unit => unit
        | t1 ** t2 => (typeDenote t1 * typeDenote t2)%type
      end.

    Fixpoint progDenote (e : prog typeDenote) : nat :=
      match e with
        | PHalt n => n
        | App _ f x => f x
        | Bind _ p x => progDenote (x (primopDenote p))
      end

    with primopDenote t (p : primop typeDenote t) {struct p} : typeDenote t :=
      match p in (primop _ t) return (typeDenote t) with
        | Var _ v => v

        | Const n => n
        | Plus n1 n2 => n1 + n2

        | Abs _ e => fun x => progDenote (e x)

        | Pair _ _ v1 v2 => (v1, v2)
        | Fst _ _ v => fst v
        | Snd _ _ v => snd v
      end.

    Definition Prog := forall var, prog var.
    Definition Primop t := forall var, primop var t.
    Definition ProgDenote (E : Prog) := progDenote (E _).
    Definition PrimopDenote t (P : Primop t) := primopDenote (P _).
  End CPS.

  Import Source CPS.

  Fixpoint cpsType (t : Source.type) : CPS.type :=
    match t with
      | Nat => Nat%cps
      | t1 --> t2 => (cpsType t1 ** (cpsType t2 --->) --->)%cps
    end%source.

  Reserved Notation "x <-- e1 ; e2" (right associativity, at level 76, e1 at next level).

  Section cpsExp.
    Variable var : CPS.type -> Type.

    Import Source.
    Open Scope cps_scope.

    Fixpoint cpsExp t (e : exp (fun t => var (cpsType t)) t) {struct e}
      : (var (cpsType t) -> prog var) -> prog var :=
      match e in (exp _ t) return ((var (cpsType t) -> prog var) -> prog var) with
        | Var _ v => fun k => k v

        | Const n => fun k =>
          x <- ^n;
          k x
        | Plus e1 e2 => fun k =>
          x1 <-- e1;
          x2 <-- e2;
          x <- x1 +^ x2;
          k x

        | App _ _ e1 e2 => fun k =>
          f <-- e1;
          x <-- e2;
          kf <- \r, k r;
          p <- [x, kf];
          f @@ p
        | Abs _ _ e' => fun k =>
          f <- CPS.Abs (var := var) (fun p =>
            x <- #1 p;
            kf <- #2 p;
            r <-- e' x;
            kf @@ r);
          k f
      end

      where "x <-- e1 ; e2" := (cpsExp e1 (fun x => e2)).
  End cpsExp.

  Notation "x <-- e1 ; e2" := (cpsExp e1 (fun x => e2)) : cps_scope.
  Notation "! <-- e1 ; e2" := (cpsExp e1 (fun _ => e2))
    (right associativity, at level 76, e1 at next level) : cps_scope.

  Implicit Arguments cpsExp [var t].
  Definition CpsExp (E : Exp Nat) : Prog :=
    fun var => cpsExp (E _) (PHalt (var := _)).

  Eval compute in CpsExp zero.
  Eval compute in CpsExp one.
  Eval compute in CpsExp zpo.
  Eval compute in CpsExp app_ident.
  Eval compute in CpsExp app_ident'.

  Eval compute in ProgDenote (CpsExp zero).
  Eval compute in ProgDenote (CpsExp one).
  Eval compute in ProgDenote (CpsExp zpo).
  Eval compute in ProgDenote (CpsExp app_ident).
  Eval compute in ProgDenote (CpsExp app_ident').

End STLC.
