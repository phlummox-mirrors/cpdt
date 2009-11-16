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

Require Import Axioms Tactics DepList.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Extensional Transformations}% *)

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

(* begin thide *)
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
(* end thide *)
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

    Notation "[ x1 , x2 ]" := (Pair x1 x2) : cps_scope.
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

(* begin thide *)
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
(* end thide *)

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

(* begin thide *)
  Fixpoint lr (t : Source.type) : Source.typeDenote t -> CPS.typeDenote (cpsType t) -> Prop :=
    match t return (Source.typeDenote t -> CPS.typeDenote (cpsType t) -> Prop) with
      | Nat => fun n1 n2 => n1 = n2
      | t1 --> t2 => fun f1 f2 =>
        forall x1 x2, lr _ x1 x2
          -> forall k, exists r,
            f2 (x2, k) = k r
            /\ lr _ (f1 x1) r
    end%source.

  Lemma cpsExp_correct : forall G t (e1 : exp _ t) (e2 : exp _ t),
    exp_equiv G e1 e2
    -> (forall t v1 v2, In (existT _ t (v1, v2)) G -> lr t v1 v2)
    -> forall k, exists r,
      progDenote (cpsExp e2 k) = progDenote (k r)
      /\ lr t (expDenote e1) r.
    induction 1; crush; fold typeDenote in *;
      repeat (match goal with
                | [ H : forall k, exists r, progDenote (cpsExp ?E k) = _ /\ _
                  |- context[cpsExp ?E ?K] ] =>
                  generalize (H K); clear H
                | [ |- exists r, progDenote (_ ?R) = progDenote (_ r) /\ _ ] =>
                  exists R
                | [ t1 : Source.type |- _ ] =>
                  match goal with
                    | [ Hlr : lr t1 ?X1 ?X2, IH : forall v1 v2, _ |- _ ] =>
                      generalize (IH X1 X2); clear IH; intro IH;
                        match type of IH with
                          | ?P -> _ => assert P
                        end
                  end
              end; crush); eauto.
  Qed.

  Lemma vars_easy : forall (t : Source.type) (v1 : Source.typeDenote t)
    (v2 : typeDenote (cpsType t)),
    In
    (existT
      (fun t0 : Source.type =>
        (Source.typeDenote t0 * typeDenote (cpsType t0))%type) t
      (v1, v2)) nil -> lr t v1 v2.
    crush.
  Qed.

  Theorem CpsExp_correct : forall (E : Exp Nat),
    ProgDenote (CpsExp E) = ExpDenote E.
    unfold ProgDenote, CpsExp, ExpDenote; intros;
      generalize (cpsExp_correct (e1 := E _) (e2 := E _)
        (Exp_equiv _ _ _) vars_easy (PHalt (var := _))); crush.
  Qed.
(* end thide *)

End STLC.


(** * A Pattern Compiler *)

Module PatMatch.
  Module Source.
    Inductive type : Type :=
    | Unit : type
    | Arrow : type -> type -> type
    | Prod : type -> type -> type
    | Sum : type -> type -> type.

    Infix "-->" := Arrow (right associativity, at level 61).
    Infix "++" := Sum (right associativity, at level 60).
    Infix "**" := Prod (right associativity, at level 59).

    Inductive pat : type -> list type -> Type :=
    | PVar : forall t,
      pat t (t :: nil)
    | PPair : forall t1 t2 ts1 ts2,
      pat t1 ts1
      -> pat t2 ts2
      -> pat (t1 ** t2) (ts1 ++ ts2)
    | PInl : forall t1 t2 ts,
      pat t1 ts
      -> pat (t1 ++ t2) ts
    | PInr : forall t1 t2 ts,
      pat t2 ts
      -> pat (t1 ++ t2) ts.

    Implicit Arguments PVar [t].
    Implicit Arguments PInl [t1 t2 ts].
    Implicit Arguments PInr [t1 t2 ts].

    Notation "##" := PVar (at level 70) : pat_scope.
    Notation "[ p1 , p2 ]" := (PPair p1 p2) : pat_scope.
    Notation "'Inl' p" := (PInl p) (at level 71) : pat_scope.
    Notation "'Inr' p" := (PInr p) (at level 71) : pat_scope.

    Bind Scope pat_scope with pat.
    Delimit Scope pat_scope with pat.

    Section vars.
      Variable var : type -> Type.

      Inductive exp : type -> Type :=
      | Var : forall t,
        var t
        -> exp t

      | EUnit : exp Unit

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

      | EInl : forall t1 t2,
        exp t1
        -> exp (t1 ++ t2)
      | EInr : forall t1 t2,
        exp t2
        -> exp (t1 ++ t2)

      | Case : forall t1 t2 (tss : list (list type)),
        exp t1
        -> (forall ts, member ts tss -> pat t1 ts)
        -> (forall ts, member ts tss -> hlist var ts -> exp t2)
        -> exp t2
        -> exp t2.
    End vars.

    Definition Exp t := forall var, exp var t.

    Implicit Arguments Var [var t].
    Implicit Arguments EUnit [var].
    Implicit Arguments App [var t1 t2].
    Implicit Arguments Abs [var t1 t2].
    Implicit Arguments Pair [var t1 t2].
    Implicit Arguments EInl [var t1 t2].
    Implicit Arguments EInr [var t1 t2].
    Implicit Arguments Case [var t1 t2].

    Notation "# v" := (Var v) (at level 70) : source_scope.

    Notation "()" := EUnit : source_scope.

    Infix "@" := App (left associativity, at level 77) : source_scope.
    Notation "\ x , e" := (Abs (fun x => e)) (at level 78) : source_scope.

    Notation "[ x , y ]" := (Pair x y) : source_scope.

    Notation "'Inl' e" := (EInl e) (at level 71) : source_scope.
    Notation "'Inr' e" := (EInr e) (at level 71) : source_scope.

    Delimit Scope source_scope with source.
    Bind Scope source_scope with exp.

    Local Open Scope source_scope.

    Fixpoint typeDenote (t : type) : Set :=
      match t with
        | Unit => unit
        | t1 --> t2 => typeDenote t1 -> typeDenote t2
        | t1 ** t2 => (typeDenote t1 * typeDenote t2)%type
        | t1 ++ t2 => (typeDenote t1 + typeDenote t2)%type
      end.

    Fixpoint patDenote t ts (p : pat t ts) {struct p} : typeDenote t -> option (hlist typeDenote ts) :=
      match p in (pat t ts) return (typeDenote t -> option (hlist typeDenote ts)) with
        | PVar _ => fun v => Some (v ::: HNil)
        | PPair _ _ _ _ p1 p2 => fun v =>
          match patDenote p1 (fst v), patDenote p2 (snd v) with
            | Some tup1, Some tup2 => Some (happ tup1 tup2)
            | _, _ => None
          end
        | PInl _ _ _ p' => fun v =>
          match v with
            | inl v' => patDenote p' v'
            | _ => None
          end
        | PInr _ _ _ p' => fun v =>
          match v with
            | inr v' => patDenote p' v'
            | _ => None
          end
      end.

    Section matchesDenote.
      Variables t2 : type.
      Variable default : typeDenote t2.

      Fixpoint matchesDenote (tss : list (list type))
        : (forall ts, member ts tss -> option (hlist typeDenote ts))
        -> (forall ts, member ts tss -> hlist typeDenote ts -> typeDenote t2)
        -> typeDenote t2 :=
        match tss return (forall ts, member ts tss -> option (hlist typeDenote ts))
          -> (forall ts, member ts tss -> hlist typeDenote ts -> typeDenote t2)
          -> _ with
          | nil => fun _ _ =>
            default
          | ts :: tss' => fun (envs : forall ts', member ts' (ts :: tss') -> option (hlist typeDenote ts'))
            (bodies : forall ts', member ts' (ts :: tss') -> hlist typeDenote ts' -> typeDenote t2) =>
            match envs _ HFirst with
              | None => matchesDenote
                (fun _ mem => envs _ (HNext mem))
                (fun _ mem => bodies _ (HNext mem))
              | Some env => (bodies _ HFirst) env
            end
        end.
    End matchesDenote.

    Implicit Arguments matchesDenote [t2 tss].

    Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
      match e in (exp _ t) return (typeDenote t) with
        | Var _ v => v

        | EUnit => tt

        | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
        | Abs _ _ e' => fun x => expDenote (e' x)

        | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)

        | EInl _ _ e' => inl _ (expDenote e')
        | EInr _ _ e' => inr _ (expDenote e')

        | Case _ _ _ e ps es def =>
          matchesDenote (expDenote def)
          (fun _ mem => patDenote (ps _ mem) (expDenote e))
          (fun _ mem env => expDenote (es _ mem env))
      end.

    Definition ExpDenote t (E : Exp t) := expDenote (E _).
  End Source.

  Import Source.

  Module Elab.
    Section vars.
      Variable var : type -> Type.

      Inductive exp : type -> Type :=
      | Var : forall t,
        var t
        -> exp t

      | EUnit : exp Unit

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

      | EInl : forall t1 t2,
        exp t1
        -> exp (t1 ++ t2)
      | EInr : forall t1 t2,
        exp t2
        -> exp (t1 ++ t2)
      | Case : forall t1 t2 t,
        exp (t1 ++ t2)
        -> (var t1 -> exp t)
        -> (var t2 -> exp t)
        -> exp t.
    End vars.

    Definition Exp t := forall var, exp var t.

    Implicit Arguments Var [var t].
    Implicit Arguments EUnit [var].
    Implicit Arguments App [var t1 t2].
    Implicit Arguments Abs [var t1 t2].
    Implicit Arguments Pair [var t1 t2].
    Implicit Arguments Fst [var t1 t2].
    Implicit Arguments Snd [var t1 t2].
    Implicit Arguments EInl [var t1 t2].
    Implicit Arguments EInr [var t1 t2].
    Implicit Arguments Case [var t1 t2 t].


    Notation "# v" := (Var v) (at level 70) : elab_scope.

    Notation "()" := EUnit : elab_scope.

    Infix "@" := App (left associativity, at level 77) : elab_scope.
    Notation "\ x , e" := (Abs (fun x => e)) (at level 78) : elab_scope.
    Notation "\ ? , e" := (Abs (fun _ => e)) (at level 78) : elab_scope.

    Notation "[ x , y ]" := (Pair x y) : elab_scope.
    Notation "#1 e" := (Fst e) (at level 72) : elab_scope.
    Notation "#2 e" := (Snd e) (at level 72) : elab_scope.

    Notation "'Inl' e" := (EInl e) (at level 71) : elab_scope.
    Notation "'Inr' e" := (EInr e) (at level 71) : elab_scope.

    Bind Scope elab_scope with exp.
    Delimit Scope elab_scope with elab.

    Open Scope elab_scope.

    Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
      match e in (exp _ t) return (typeDenote t) with
        | Var _ v => v

        | EUnit => tt

        | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
        | Abs _ _ e' => fun x => expDenote (e' x)

        | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
        | Fst _ _ e' => fst (expDenote e')
        | Snd _ _ e' => snd (expDenote e')

        | EInl _ _ e' => inl _ (expDenote e')
        | EInr _ _ e' => inr _ (expDenote e')
        | Case _ _ _ e' e1 e2 =>
          match expDenote e' with
            | inl v => expDenote (e1 v)
            | inr v => expDenote (e2 v)
          end
      end.

    Definition ExpDenote t (E : Exp t) := expDenote (E _).
  End Elab.

  Import Elab.

  Notation "x <- e1 ; e2" := ((\x, e2) @ e1)%source
    (right associativity, at level 76, e1 at next level) : source_scope.
  Notation "x <- e1 ; e2" := ((\x, e2) @ e1)%elab
    (right associativity, at level 76, e1 at next level) : elab_scope.

  Section choice_tree.
    Open Scope source_scope.

    Fixpoint choice_tree var (t : type) (result : Type) : Type :=
      match t with
        | t1 ** t2 =>
          choice_tree var t1
          (choice_tree var t2
            result)
        | t1 ++ t2 =>
          choice_tree var t1 result
          * choice_tree var t2 result
        | t => exp var t -> result
      end%type.

    Fixpoint merge var t result {struct t}
      : (result -> result -> result)
      -> choice_tree var t result -> choice_tree var t result -> choice_tree var t result :=
      match t return ((result -> result -> result)
        -> choice_tree var t result -> choice_tree var t result -> choice_tree var t result) with
        | _ ** _ => fun mr ct1 ct2 =>
          merge _ _
          (merge _ _ mr)
          ct1 ct2

        | _ ++ _ => fun mr ct1 ct2 =>
          (merge var _ mr (fst ct1) (fst ct2),
            merge var _ mr (snd ct1) (snd ct2))

        | _ => fun mr ct1 ct2 e => mr (ct1 e) (ct2 e)
      end.

    Fixpoint everywhere var t result {struct t}
      : (exp var t -> result) -> choice_tree var t result :=
      match t return ((exp var t -> result) -> choice_tree var t result) with
        | t1 ** t2 => fun r =>
          everywhere (t := t1) (fun e1 =>
            everywhere (t := t2) (fun e2 =>
              r ([e1, e2])%elab))

        | _ ++ _ => fun r =>
          (everywhere (fun e => r (Inl e)%elab),
            everywhere (fun e => r (Inr e)%elab))

        | _ => fun r => r
      end.
  End choice_tree.

  Implicit Arguments merge [var t result].

  Section elaborate.
    Local Open Scope elab_scope.

    Fixpoint elaboratePat var t1 ts result (p : pat t1 ts) {struct p} :
      (hlist (exp var) ts -> result) -> result -> choice_tree var t1 result :=
      match p in (pat t1 ts) return ((hlist (exp var) ts -> result)
        -> result -> choice_tree var t1 result) with
        | PVar _ => fun succ fail =>
          everywhere (fun disc => succ (disc ::: HNil))

        | PPair _ _ _ _ p1 p2 => fun succ fail =>
          elaboratePat p1
          (fun tup1 =>
            elaboratePat p2
            (fun tup2 =>
              succ (happ tup1 tup2))
            fail)
          (everywhere (fun _ => fail))

        | PInl _ _ _ p' => fun succ fail =>
          (elaboratePat p' succ fail,
            everywhere (fun _ => fail))
        | PInr _ _ _ p' => fun succ fail =>
          (everywhere (fun _ => fail),
            elaboratePat p' succ fail)
      end.

    Implicit Arguments elaboratePat [var t1 ts result].

    Fixpoint letify var t ts {struct ts} : (hlist var ts -> exp var t)
      -> hlist (exp var) ts -> exp var t :=
      match ts return ((hlist var ts -> exp var t)
        -> hlist (exp var) ts -> exp var t) with
        | nil => fun f _ => f HNil
        | _ :: _ => fun f tup => letify (fun tup' => x <- hhd tup; f (x ::: tup')) (htl tup)
      end.

    Implicit Arguments letify [var t ts].

    Fixpoint expand var result t1 t2
      (out : result -> exp var t2) {struct t1}
      : forall ct : choice_tree var t1 result,
        exp var t1
        -> exp var t2 :=
        match t1 return (forall ct : choice_tree var t1 result, exp var t1
          -> exp var t2) with
          | (_ ** _)%source => fun ct disc =>
            expand
            (fun ct' => expand out ct' (#2 disc)%source)
            ct
            (#1 disc)
            
          | (_ ++ _)%source => fun ct disc =>
            Case disc
            (fun x => expand out (fst ct) (#x))
            (fun y => expand out (snd ct) (#y))
                  
          | _ => fun ct disc =>
            x <- disc; out (ct (#x))
        end.

    Definition mergeOpt A (o1 o2 : option A) :=
      match o1 with
        | None => o2
        | _ => o1
      end.

    Import Source.

    Fixpoint elaborateMatches var t1 t2
      (tss : list (list type)) {struct tss}
      : (forall ts, member ts tss -> pat t1 ts)
      -> (forall ts, member ts tss -> hlist var ts -> Elab.exp var t2)
      -> choice_tree var t1 (option (Elab.exp var t2)) :=
      match tss return (forall ts, member ts tss -> pat t1 ts)
        -> (forall ts, member ts tss -> _)
        -> _ with
        | nil => fun _ _ =>
          everywhere (fun _ => None)
        | ts :: tss' => fun (ps : forall ts', member ts' (ts :: tss') -> pat t1 ts')
          (es : forall ts', member ts' (ts :: tss') -> hlist var ts' -> Elab.exp var t2) =>
          merge (@mergeOpt _)
          (elaboratePat (ps _ HFirst)
            (fun ts => Some (letify
              (fun ts' => es _ HFirst ts')
              ts))
            None)
          (elaborateMatches
            (fun _ mem => ps _ (HNext mem))
            (fun _ mem => es _ (HNext mem)))
      end.

    Implicit Arguments elaborateMatches [var t1 t2 tss].

    Open Scope cps_scope.

    Fixpoint elaborate var t (e : Source.exp var t) {struct e} : Elab.exp var t :=
      match e in (Source.exp _ t) return (Elab.exp var t) with
        | Var _ v => #v

        | EUnit => ()

        | App _ _ e1 e2 => elaborate e1 @ elaborate e2
        | Abs _ _ e' => \x, elaborate (e' x) 

        | Pair _ _ e1 e2 => [elaborate e1, elaborate e2]
        | EInl _ _ e' => Inl (elaborate e')
        | EInr _ _ e' => Inr (elaborate e')

        | Case _ _ _ e' ps es def =>
          expand
          (fun eo => match eo with
                       | None => elaborate def
                       | Some e => e
                     end)
          (elaborateMatches ps (fun _ mem env => elaborate (es _ mem env)))
          (elaborate e')
      end.
  End elaborate.

  Definition Elaborate t (E : Source.Exp t) : Elab.Exp t :=
    fun _ => elaborate (E _).

  Fixpoint grab t result : choice_tree typeDenote t result -> typeDenote t -> result :=
    match t return (choice_tree typeDenote t result -> typeDenote t -> result) with
      | t1 ** t2 => fun ct v =>
        grab t2 _ (grab t1 _ ct (fst v)) (snd v)
      | t1 ++ t2 => fun ct v =>
        match v with
          | inl v' => grab t1 _ (fst ct) v'
          | inr v' => grab t2 _ (snd ct) v'
        end
      | t => fun ct v => ct (#v)%elab
    end%source%type.

  Implicit Arguments grab [t result].

  Ltac my_crush :=
    crush;
    repeat (match goal with
              | [ |- context[match ?E with inl _ => _ | inr _ => _ end] ] =>
                destruct E
            end; crush).

  Lemma expand_grab : forall t2 t1 result
    (out : result -> Elab.exp typeDenote t2)
    (ct : choice_tree typeDenote t1 result)
    (disc : Elab.exp typeDenote t1),
    Elab.expDenote (expand out ct disc) = Elab.expDenote (out (grab ct (Elab.expDenote disc))).
    induction t1; my_crush.
  Qed.

  Lemma recreate_pair : forall t1 t2
    (x : Elab.exp typeDenote t1)
    (x0 : Elab.exp typeDenote t2)
    (v : typeDenote (t1 ** t2)),
    expDenote x = fst v
    -> expDenote x0 = snd v
    -> @eq (typeDenote t1 * typeDenote t2) (expDenote [x, x0]) v.
    destruct v; crush.
  Qed.

  Lemma everywhere_correct : forall t1 result
    (succ : Elab.exp typeDenote t1 -> result) disc,
    exists disc', grab (everywhere succ) (Elab.expDenote disc) = succ disc'
      /\ Elab.expDenote disc' = Elab.expDenote disc.
    Hint Resolve recreate_pair.

    induction t1; my_crush; eauto; fold choice_tree;
      repeat (fold typeDenote in *; crush;
        match goal with
          | [ IH : forall result succ, _ |- context[grab (everywhere ?S) _] ] =>
            generalize (IH _ S); clear IH
          | [ e : exp typeDenote (?T ** _), IH : forall _ : exp typeDenote ?T, _ |- _ ] =>
            generalize (IH (#1 e)); clear IH
          | [ e : exp typeDenote (_ ** ?T), IH : forall _ : exp typeDenote ?T, _ |- _ ] =>
            generalize (IH (#2 e)); clear IH
          | [ e : typeDenote ?T, IH : forall _ : exp typeDenote ?T, _ |- _ ] =>
            generalize (IH (#e)); clear IH
        end; crush); eauto.
  Qed.

  Lemma merge_correct : forall t result
    (ct1 ct2 : choice_tree typeDenote t result)
    (mr : result -> result -> result) v,
    grab (merge mr ct1 ct2) v = mr (grab ct1 v) (grab ct2 v).
    induction t; crush.
  Qed.

  Lemma everywhere_fail : forall t result
    (fail : result) v,
    grab (everywhere (fun _ : Elab.exp typeDenote t => fail)) v = fail.
    induction t; crush.
  Qed.

  Lemma elaboratePat_correct : forall t1 ts (p : pat t1 ts)
    result (succ : hlist (Elab.exp typeDenote) ts -> result)
    (fail : result) v env,
    patDenote p v = Some env
    -> exists env', grab (elaboratePat p succ fail) v = succ env'
      /\ env = hmap Elab.expDenote env'.
    Hint Resolve hmap_happ.

    induction p; crush; fold choice_tree;
      repeat (match goal with
                | [ |- context[grab (everywhere ?succ) ?v] ] =>
                  generalize (everywhere_correct succ (#v)%elab)

                | [ H : forall result succ fail, _ |- context[grab (elaboratePat _ ?S ?F) ?V] ] =>
                  generalize (H _ S F V); clear H
                | [ H1 : context[match ?E with Some _ => _ | None => _ end],
                    H2 : forall env, ?E = Some env -> _ |- _ ] =>
                  destruct E
                | [ H : forall env, Some ?E = Some env -> _ |- _ ] =>
                  generalize (H _ (refl_equal _)); clear H
              end; crush); eauto.
  Qed.

  Lemma elaboratePat_fails : forall t1 ts (p : pat t1 ts)
    result (succ : hlist (Elab.exp typeDenote) ts -> result)
    (fail : result) v,
    patDenote p v = None
    -> grab (elaboratePat p succ fail) v = fail.
    Hint Resolve everywhere_fail.

    induction p; try solve [ crush ];
      simpl; fold choice_tree; intuition; simpl in *;
        repeat match goal with
                 | [ IH : forall result succ fail v, patDenote ?P v = _ -> _
                   |- context[grab (elaboratePat ?P ?S ?F) ?V] ] =>
                   generalize (IH _ S F V); clear IH; intro IH;
                     generalize (elaboratePat_correct P S F V); intros;
                       destruct (patDenote P V); try discriminate
                 | [ H : forall env, Some _ = Some env -> _ |- _ ] =>
                   destruct (H _ (refl_equal _)); clear H; intuition
                 | [ H : _ |- _ ] => rewrite H; intuition
                 | [ |- context[match ?v with inl _ => _ | inr _ => _ end] ] => destruct v; auto
               end.
  Qed.

  Implicit Arguments letify [var t ts].

  Lemma letify_correct : forall t ts (f : hlist typeDenote ts -> Elab.exp typeDenote t)
    (env : hlist (Elab.exp typeDenote) ts),
    Elab.expDenote (letify f env)
    = Elab.expDenote (f (hmap Elab.expDenote env)).
    induction ts; crush; dep_destruct env; crush.
  Qed.

  Theorem elaborate_correct : forall t (e : Source.exp typeDenote t),
    Elab.expDenote (elaborate e) = Source.expDenote e.
    Hint Rewrite expand_grab merge_correct letify_correct : cpdt.
    Hint Rewrite everywhere_fail elaboratePat_fails using assumption : cpdt.

    induction e; crush; try (ext_eq; crush);
      match goal with
        | [ tss : list (list type) |- _ ] =>
          induction tss; crush;
            match goal with
              | [ |- context[grab (elaboratePat ?P ?S ?F) ?V] ] =>
                case_eq (patDenote P V); [intros env Heq;
                  destruct (elaboratePat_correct P S F _ Heq); crush;
                    match goal with
                      | [ H : _ |- _ ] => rewrite <- H; crush
                    end
                  | crush ]
            end
      end.
  Qed.

  Theorem Elaborate_correct : forall t (E : Source.Exp t),
    Elab.ExpDenote (Elaborate E) = Source.ExpDenote E.
    unfold Elab.ExpDenote, Elaborate, Source.ExpDenote;
      intros; apply elaborate_correct.
  Qed.

End PatMatch.


(** * Exercises *)

(** %\begin{enumerate}%#<ol>#

%\item%#<li># When in the last chapter we implemented constant folding for simply-typed lambda calculus, it may have seemed natural to try applying beta reductions.  This would have been a lot more trouble than is apparent at first, because we would have needed to convince Coq that our normalizing function always terminated.

  It might also seem that beta reduction is a lost cause because we have no effective way of substituting in the [exp] type; we only managed to write a substitution function for the parametric [Exp] type.  This is not as big of a problem as it seems.  For instance, for the language we built by extending simply-typed lambda calculus with products and sums, it also appears that we need substitution for simplifying [case] expressions whose discriminees are known to be [inl] or [inr], but the function is still implementable.

  For this exercise, extend the products and sums constant folder from the last chapter so that it simplifies [case] expressions as well, by checking if the discriminee is a known [inl] or known [inr].  Also extend the correctness theorem to apply to your new definition.  You will probably want to assert an axiom relating to an expression equivalence relation like the one defined in this chapter.  Any such axiom should only mention syntax; it should not mention any compilation or denotation functions.  Following the format of the axiom from the last chapter is the safest bet to avoid proving a worthless theorem.
 #</li>#
   
#</ol>#%\end{enumerate}% *)
