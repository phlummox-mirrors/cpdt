(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Higher-Order Operational Semantics}% *)

(** * Closure Heaps *)

Section lookup.
  Variable A : Type.

  Fixpoint lookup (ls : list A) (n : nat) : option A :=
    match ls with
      | nil => None
      | v :: ls' => if eq_nat_dec n (length ls') then Some v else lookup ls' n
    end.

  Definition extends (ls1 ls2 : list A) := exists ls, ls2 = ls ++ ls1.

  Infix "##" := lookup (left associativity, at level 1).
  Infix "~>" := extends (no associativity, at level 80).

  Theorem lookup1 : forall x ls,
    (x :: ls) ## (length ls) = Some x.
    crush; match goal with
             | [ |- context[if ?E then _ else _] ] => destruct E
           end; crush.
  Qed.

  Theorem extends_refl : forall ls, ls ~> ls.
    exists nil; reflexivity.
  Qed.

  Theorem extends1 : forall v ls, ls ~> v :: ls.
    intros; exists (v :: nil); reflexivity.
  Qed.

  Theorem extends_trans : forall ls1 ls2 ls3,
    ls1 ~> ls2
    -> ls2 ~> ls3
    -> ls1 ~> ls3.
    intros ? ? ? [l1 ?] [l2 ?]; exists (l2 ++ l1); crush.
  Qed.

  Lemma lookup_contra : forall n v ls,
    ls ## n = Some v
    -> n >= length ls
    -> False.
    induction ls; crush;
      match goal with
        | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
      end; crush.
  Qed.

  Hint Resolve lookup_contra.

  Theorem extends_lookup : forall ls1 ls2 n v,
    ls1 ~> ls2
    -> ls1 ## n = Some v
    -> ls2 ## n = Some v.
    intros ? ? ? ? [l ?]; crush; induction l; crush;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; crush; elimtype False; eauto.
  Qed.
End lookup.

Infix "##" := lookup (left associativity, at level 1).
Infix "~>" := extends (no associativity, at level 80).

Hint Resolve lookup1 extends_refl extends1 extends_trans extends_lookup.


(** * Languages and Translation *)

Module Source.
  Section exp.
    Variable var : Type.

    Inductive exp : Type :=
    | Var : var -> exp
    | App : exp -> exp -> exp
    | Abs : (var -> exp) -> exp
    | Bool : bool -> exp.
  End exp.

  Implicit Arguments Bool [var].

  Definition Exp := forall var, exp var.

  Inductive val : Set :=
  | VFun : nat -> val
  | VBool : bool -> val.

  Definition closure := val -> exp val.
  Definition closures := list closure.

  Inductive eval : closures -> exp val -> closures -> val -> Prop :=
  | EvVar : forall cs v,
    eval cs (Var v) cs v

  | EvApp : forall cs1 e1 e2 cs2 v1 c cs3 v2 cs4 v3,
    eval cs1 e1 cs2 (VFun v1)
    -> eval cs2 e2 cs3 v2
    -> cs2 ## v1 = Some c
    -> eval cs3 (c v2) cs4 v3
    -> eval cs1 (App e1 e2) cs4 v3

  | EvAbs : forall cs c,
    eval cs (Abs c) (c :: cs) (VFun (length cs))

  | EvBool : forall cs b,
    eval cs (Bool b) cs (VBool b).

  Definition Eval (cs1 : closures) (E : Exp) (cs2 : closures) (v : val) := eval cs1 (E _) cs2 v.

  Section exp_equiv.
    Variables var1 var2 : Type.

    Inductive exp_equiv : list (var1 * var2) -> exp var1 -> exp var2 -> Prop :=
    | EqVar : forall G v1 v2,
      In (v1, v2) G
      -> exp_equiv G (Var v1) (Var v2)

    | EqApp : forall G f1 x1 f2 x2,
      exp_equiv G f1 f2
      -> exp_equiv G x1 x2
      -> exp_equiv G (App f1 x1) (App f2 x2)
    | EqAbs : forall G f1 f2,
      (forall v1 v2, exp_equiv ((v1, v2) :: G) (f1 v1) (f2 v2))
      -> exp_equiv G (Abs f1) (Abs f2)

    | EqBool : forall G b,
      exp_equiv G (Bool b) (Bool b).
  End exp_equiv.

  Definition Wf (E : Exp) := forall var1 var2, exp_equiv nil (E var1) (E var2).
End Source.

Module CPS.
  Section exp.
    Variable var : Type.

    Inductive prog : Type :=
    | Halt : var -> prog
    | App : var -> var -> prog
    | Bind : primop -> (var -> prog) -> prog

    with primop : Type :=
    | Abs : (var -> prog) -> primop

    | Bool : bool -> primop

    | Pair : var -> var -> primop
    | Fst : var -> primop
    | Snd : var -> primop.
  End exp.

  Implicit Arguments Bool [var].

  Notation "x <- p ; e" := (Bind p (fun x => e))
    (right associativity, at level 76, p at next level).

  Definition Prog := forall var, prog var.
  Definition Primop := forall var, primop var.

  Inductive val : Type :=
  | VFun : nat -> val
  | VBool : bool -> val
  | VPair : val -> val -> val.
  Definition closure := val -> prog val.
  Definition closures := list closure.

  Inductive eval : closures -> prog val -> val -> Prop :=
  | EvHalt : forall cs v,
    eval cs (Halt v) v

  | EvApp : forall cs n v2 c v3,
    cs ## n = Some c
    -> eval cs (c v2) v3
    -> eval cs (App (VFun n) v2) v3

  | EvBind : forall cs1 p e cs2 v1 v2,
    evalP cs1 p cs2 v1
    -> eval cs2 (e v1) v2
    -> eval cs1 (Bind p e) v2

  with evalP : closures -> primop val -> closures -> val -> Prop :=
  | EvAbs : forall cs c,
    evalP cs (Abs c) (c :: cs) (VFun (length cs))

  | EvPair : forall cs v1 v2,
    evalP cs (Pair v1 v2) cs (VPair v1 v2)
  | EvFst : forall cs v1 v2,
    evalP cs (Fst (VPair v1 v2)) cs v1
  | EvSnd : forall cs v1 v2,
    evalP cs (Snd (VPair v1 v2)) cs v2

  | EvBool : forall cs b,
    evalP cs (Bool b) cs (VBool b).

  Definition Eval (cs : closures) (P : Prog) (v : val) := eval cs (P _) v.
End CPS.

Import Source CPS.

Reserved Notation "x <-- e1 ; e2" (right associativity, at level 76, e1 at next level).

Section cpsExp.
  Variable var : Type.

  Import Source.

  Fixpoint cpsExp (e : exp var)
    : (var -> prog var) -> prog var :=
    match e with
      | Var v => fun k => k v

      | App e1 e2 => fun k =>
        f <-- e1;
        x <-- e2;
        kf <- CPS.Abs k;
        p <- Pair x kf;
        CPS.App f p
      | Abs e' => fun k =>
        f <- CPS.Abs (var := var) (fun p =>
          x <- Fst p;
          kf <- Snd p;
          r <-- e' x;
          CPS.App kf r);
        k f

      | Bool b => fun k =>
        x <- CPS.Bool b;
        k x
    end

    where "x <-- e1 ; e2" := (cpsExp e1 (fun x => e2)).
End cpsExp.

Notation "x <-- e1 ; e2" := (cpsExp e1 (fun x => e2)).

Definition CpsExp (E : Exp) : Prog := fun _ => cpsExp (E _) (Halt (var := _)).


(** * Correctness Proof *)

Definition cpsFunc var (e' : var -> Source.exp var) :=
  fun p : var =>
    x <- Fst p;
    kf <- Snd p;
    r <-- e' x;
    CPS.App kf r.

Section cr.
  Variable s1 : Source.closures.
  Variable s2 : CPS.closures.

  Import Source.

  Inductive cr : Source.val -> CPS.val -> Prop :=
  | CrFun : forall l1 l2 G f1 f2,
    (forall x1 x2, exp_equiv ((x1, x2) :: G) (f1 x1) (f2 x2))
    -> (forall x1 x2, In (x1, x2) G -> cr x1 x2)
    -> s1 ## l1 = Some f1
    -> s2 ## l2 = Some (cpsFunc f2)
    -> cr (Source.VFun l1) (CPS.VFun l2)

  | CrBool : forall b,
    cr (Source.VBool b) (CPS.VBool b).
End cr.

Notation "s1 & s2 |-- v1 ~~ v2" := (cr s1 s2 v1 v2) (no associativity, at level 70).

Hint Constructors cr.

Lemma eval_monotone : forall cs1 e cs2 v,
  Source.eval cs1 e cs2 v
  -> cs1 ~> cs2.
  induction 1; crush; eauto.
Qed.

Lemma cr_monotone : forall cs1 cs2 cs1' cs2',
  cs1 ~> cs1'
  -> cs2 ~> cs2'
  -> forall v1 v2, cs1 & cs2 |-- v1 ~~ v2
    -> cs1' & cs2' |-- v1 ~~ v2.
  induction 3; crush; eauto.
Qed.

Hint Resolve eval_monotone cr_monotone.

Lemma push : forall G s1 s2 v1' v2',
  (forall v1 v2, In (v1, v2) G -> s1 & s2 |-- v1 ~~ v2)
  -> s1 & s2 |-- v1' ~~ v2'
  -> (forall v1 v2, (v1', v2') = (v1, v2) \/ In (v1, v2) G -> s1 & s2 |-- v1 ~~ v2).
  crush.
Qed.

Hint Resolve push.

Ltac evalOne :=
  match goal with
    | [ |- CPS.eval ?cs ?e ?v ] =>
      let e := eval hnf in e in
        change (CPS.eval cs e v);
          econstructor; [ solve [ eauto ] | ]
  end.

Hint Constructors evalP.
Hint Extern 1 (CPS.eval _ _ _) => evalOne; repeat evalOne.

Lemma cpsExp_correct : forall s1 e1 s1' r1,
  Source.eval s1 e1 s1' r1
  -> forall G (e2 : exp CPS.val),
    exp_equiv G e1 e2
    -> forall s2,
      (forall v1 v2, In (v1, v2) G -> s1 & s2 |-- v1 ~~ v2)
      -> forall k, exists s2', exists r2,
        (forall r, CPS.eval s2' (k r2) r
          -> CPS.eval s2 (cpsExp e2 k) r)
        /\ s1' & s2' |-- r1 ~~ r2
        /\ s2 ~> s2'.
  induction 1; inversion 1; crush;
    repeat (match goal with
              | [ H : _ & _ |-- Source.VFun _ ~~ _ |- _ ] => inversion H; clear H
              | [ H1 : ?E = _, H2 : ?E = _ |- _ ] => rewrite H1 in H2; clear H1
              | [ H : forall G e2, exp_equiv G ?E e2 -> _ |- _ ] =>
                match goal with
                  | [ _ : Source.eval ?CS E _ _, _ : Source.eval _ ?E' ?CS _,
                      _ : forall G e2, exp_equiv G ?E' e2 -> _ |- _ ] => fail 1
                  | _ => match goal with
                           | [ k : val -> prog val, _ : _ & ?cs |-- _ ~~ _, _ : context[VFun] |- _ ] =>
                             guess (k :: cs) H
                           | _ => guess tt H
                         end
                end
            end; crush); eauto 13.
Qed.

Lemma CpsExp_correct : forall E cs b,
  Source.Eval nil E cs (Source.VBool b)
  -> Wf E
  -> CPS.Eval nil (CpsExp E) (CPS.VBool b).
  Hint Constructors CPS.eval.

  unfold Source.Eval, CPS.Eval, CpsExp; intros ? ? ? H1 H2;
    generalize (cpsExp_correct H1 (H2 _ _) (s2 := nil)
      (fun _ _ pf => match pf with end) (Halt (var := _))); crush;
    match goal with
      | [ H : _ & _ |-- _ ~~ _ |- _ ] => inversion H
    end; crush.
Qed.
