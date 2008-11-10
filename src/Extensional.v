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

Require Import AxiomsImpred Tactics DepList.

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

    Section exp_equiv.
      Variables var1 var2 : type -> Type.

      Inductive exp_equiv : list { t : type & var1 t * var2 t }%type -> forall t, exp var1 t -> exp var2 t -> Prop :=
      | EqEVar : forall G t (v1 : var1 t) v2,
        In (existT _ t (v1, v2)) G
        -> exp_equiv G (#v1) (#v2)

      | EqEConst : forall G n,
        exp_equiv G (^n) (^n)
      | EqEPlus : forall G x1 y1 x2 y2,
        exp_equiv G x1 x2
        -> exp_equiv G y1 y2
        -> exp_equiv G (x1 +^ y1) (x2 +^ y2)

      | EqEApp : forall G t1 t2 (f1 : exp _ (t1 --> t2)) (x1 : exp _ t1) f2 x2,
        exp_equiv G f1 f2
        -> exp_equiv G x1 x2
        -> exp_equiv G (f1 @ x1) (f2 @ x2)
      | EqEAbs : forall G t1 t2 (f1 : var1 t1 -> exp var1 t2) f2,
        (forall v1 v2, exp_equiv (existT _ t1 (v1, v2) :: G) (f1 v1) (f2 v2))
        -> exp_equiv G (Abs f1) (Abs f2).
    End exp_equiv.

    Axiom Exp_equiv : forall t (E : Exp t) var1 var2,
      exp_equiv nil (E var1) (E var2).
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
    Notation "[ p1 , p2 ]" := (PPair p1 p2) (at level 72) : pat_scope.
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

    Notation "[ x , y ]" := (Pair x y) (at level 72) : source_scope.

    Notation "'Inl' e" := (EInl e) (at level 71) : source_scope.
    Notation "'Inr' e" := (EInr e) (at level 71) : source_scope.

    Bind Scope source_scope with exp.

    Open Local Scope source_scope.

    Fixpoint typeDenote (t : type) : Set :=
      match t with
        | Unit => unit
        | t1 --> t2 => typeDenote t1 -> typeDenote t2
        | t1 ** t2 => (typeDenote t1 * typeDenote t2)%type
        | t1 ++ t2 => (typeDenote t1 + typeDenote t2)%type
      end.

    Fixpoint patDenote t ts (p : pat t ts) {struct p} : typeDenote t -> option (hlist typeDenote ts) :=
      match p in (pat t ts) return (typeDenote t -> option (hlist typeDenote ts)) with
        | PVar _ => fun v => Some (v, tt)
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
        match tss return (forall ts, member ts tss -> _)
          -> (forall ts, member ts tss -> _)
          -> _ with
          | nil => fun _ _ =>
            default
          | ts :: tss' => fun (envs : forall ts', member ts' (ts :: tss') -> option (hlist typeDenote ts'))
            (bodies : forall ts', member ts' (ts :: tss') -> hlist typeDenote ts' -> typeDenote t2) =>
            match envs _ (hfirst (refl_equal _)) with
              | None => matchesDenote tss'
                (fun _ mem => envs _ (hnext mem))
                (fun _ mem => bodies _ (hnext mem))
              | Some env => (bodies _ (hfirst (refl_equal _))) env
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

  Section Elab.
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

    Notation "[ x , y ]" := (Pair x y) (at level 72) : elab_scope.
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

End PatMatch.
