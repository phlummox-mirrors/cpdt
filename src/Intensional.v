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

Require Import Axioms Tactics DepList.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Intensional Transformations}% *)

(** TODO: Prose for this chapter *)


(** * Closure Conversion *)

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

  Section exp_equiv.
    Variables var1 var2 : type -> Type.

    Inductive exp_equiv : list { t : type & var1 t * var2 t }%type -> forall t, exp var1 t -> exp var2 t -> Prop :=
    | EqVar : forall G t (v1 : var1 t) v2,
      In (existT _ t (v1, v2)) G
      -> exp_equiv G (#v1) (#v2)

    | EqConst : forall G n,
      exp_equiv G (^n) (^n)
    | EqPlus : forall G x1 y1 x2 y2,
      exp_equiv G x1 x2
      -> exp_equiv G y1 y2
      -> exp_equiv G (x1 +^ y1) (x2 +^ y2)

    | EqApp : forall G t1 t2 (f1 : exp _ (t1 --> t2)) (x1 : exp _ t1) f2 x2,
      exp_equiv G f1 f2
      -> exp_equiv G x1 x2
      -> exp_equiv G (f1 @ x1) (f2 @ x2)
    | EqAbs : forall G t1 t2 (f1 : var1 t1 -> exp var1 t2) f2,
      (forall v1 v2, exp_equiv (existT _ t1 (v1, v2) :: G) (f1 v1) (f2 v2))
      -> exp_equiv G (Abs f1) (Abs f2).
  End exp_equiv.

  Axiom Exp_equiv : forall t (E : Exp t) var1 var2,
    exp_equiv nil (E var1) (E var2).
End Source.

Section Closed.
  Inductive type : Type :=
  | TNat : type
  | Arrow : type -> type -> type
  | Code : type -> type -> type -> type
  | Prod : type -> type -> type
  | TUnit : type.

  Notation "'Nat'" := TNat : cc_scope.
  Notation "'Unit'" := TUnit : cc_scope.
  Infix "-->" := Arrow (right associativity, at level 60) : cc_scope.
  Infix "**" := Prod (right associativity, at level 59) : cc_scope.
  Notation "env @@ dom ---> ran" := (Code env dom ran) (no associativity, at level 62, dom at next level) : cc_scope.

  Bind Scope cc_scope with type.
  Delimit Scope cc_scope with cc.

  Open Local Scope cc_scope.

  Section vars.
    Variable var : type -> Set.

    Inductive exp : type -> Type :=
    | Var : forall t,
      var t
      -> exp t

    | Const : nat -> exp Nat
    | Plus : exp Nat -> exp Nat -> exp Nat

    | App : forall dom ran,
      exp (dom --> ran)
      -> exp dom
      -> exp ran

    | Pack : forall env dom ran,
      exp (env @@ dom ---> ran)
      -> exp env
      -> exp (dom --> ran)

    | EUnit : exp Unit

    | Pair : forall t1 t2,
      exp t1
      -> exp t2
      -> exp (t1 ** t2)
    | Fst : forall t1 t2,
      exp (t1 ** t2)
      -> exp t1
    | Snd : forall t1 t2,
      exp (t1 ** t2)
      -> exp t2.

    Section funcs.
      Variable T : Type.

      Inductive funcs : Type :=
      | Main : T -> funcs
      | Abs : forall env dom ran,
        (var env -> var dom -> exp ran)
        -> (var (env @@ dom ---> ran) -> funcs)
        -> funcs.
    End funcs.

    Definition prog t := funcs (exp t).
  End vars.

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments EUnit [var].
  Implicit Arguments Fst [var t1 t2].
  Implicit Arguments Snd [var t1 t2].

  Implicit Arguments Main [var T].
  Implicit Arguments Abs [var T env dom ran].

  Notation "# v" := (Var v) (at level 70) : cc_scope.

  Notation "^ n" := (Const n) (at level 70) : cc_scope.
  Infix "+^" := Plus (left associativity, at level 79) : cc_scope.

  Infix "@@" := App (no associativity, at level 75) : cc_scope.
  Infix "##" := Pack (no associativity, at level 71) : cc_scope.

  Notation "()" := EUnit : cc_scope.

  Notation "[ x1 , x2 ]" := (Pair x1 x2) (at level 73) : cc_scope.
  Notation "#1 x" := (Fst x) (at level 72) : cc_scope.
  Notation "#2 x" := (Snd x) (at level 72) : cc_scope.

  Notation "f <= \\ x , y , e ; fs" :=
    (Abs (fun x y => e) (fun f => fs))
    (right associativity, at level 80, e at next level) : cc_scope.

  Bind Scope cc_scope with exp funcs prog.

  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | Unit => unit
      | dom --> ran => typeDenote dom -> typeDenote ran
      | t1 ** t2 => typeDenote t1 * typeDenote t2
      | env @@ dom ---> ran => typeDenote env -> typeDenote dom -> typeDenote ran
    end%type.

  Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
    match e in (exp _ t) return (typeDenote t) with
      | Var _ v => v

      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2

      | App _ _ f x => (expDenote f) (expDenote x)
      | Pack _ _ _ f env => (expDenote f) (expDenote env)

      | EUnit => tt

      | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
      | Fst _ _ e' => fst (expDenote e')
      | Snd _ _ e' => snd (expDenote e')
    end.

  Fixpoint funcsDenote T (fs : funcs typeDenote T) : T :=
    match fs with
      | Main v => v
      | Abs _ _ _ e fs =>
        funcsDenote (fs (fun env arg => expDenote (e env arg)))
    end.

  Definition progDenote t (p : prog typeDenote t) : typeDenote t :=
    expDenote (funcsDenote p).

  Definition Exp t := forall var, exp var t.
  Definition Prog t := forall var, prog var t.

  Definition ExpDenote t (E : Exp t) := expDenote (E _).
  Definition ProgDenote t (P : Prog t) := progDenote (P _).
End Closed.

