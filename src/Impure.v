(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List Omega.

Require Import Axioms Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Modeling Impure Languages}% *)

(** TODO: Prose for this chapter *)

Section var.
  Variable var : Type.

  Inductive term : Type :=
  | Var : var -> term
  | App : term -> term -> term
  | Abs : (var -> term) -> term
  | Unit : term.
End var.

Implicit Arguments Unit [var].

Notation "# v" := (Var v) (at level 70).
Notation "()" := Unit.

Infix "@" := App (left associativity, at level 72).
Notation "\ x , e" := (Abs (fun x => e)) (at level 73).
Notation "\ ? , e" := (Abs (fun _ => e)) (at level 73).

Definition Term := forall var, term var.

Definition ident : Term := fun _ => \x, #x.
Definition unite : Term := fun _ => ().
Definition ident_self : Term := fun _ => ident _ @ ident _.
Definition ident_unit : Term := fun _ => ident _ @ unite _.


Module impredicative.
  Inductive dynamic : Set :=
  | Dyn : forall (dynTy : Type), dynTy -> dynamic.

  Inductive computation (T : Type) : Set :=
  | Return : T -> computation T
  | Bind : forall (T' : Type),
    computation T' -> (T' -> computation T) -> computation T
  | Unpack : dynamic -> computation T.

  Inductive eval : forall T, computation T -> T -> Prop :=
  | EvalReturn : forall T (v : T),
    eval (Return v) v
  | EvalUnpack : forall T (v : T),
    eval (Unpack T (Dyn v)) v
  | EvalBind : forall T1 T2 (c1 : computation T1) (c2 : T1 -> computation T2) v1 v2,
    eval c1 v1
    -> eval (c2 v1) v2
    -> eval (Bind c1 c2) v2.

  Fixpoint termDenote (e : term dynamic) : computation dynamic :=
    match e with
      | Var v => Return v
      | App e1 e2 => Bind (termDenote e1) (fun f =>
        Bind (termDenote e2) (fun x =>
          Bind (Unpack (dynamic -> computation dynamic) f) (fun f' =>
            f' x)))
      | Abs e' => Return (Dyn (fun x => termDenote (e' x)))

      | Unit => Return (Dyn tt)
    end.

  Definition TermDenote (E : Term) := termDenote (E _).

  Eval compute in TermDenote ident.
  Eval compute in TermDenote unite.
  Eval compute in TermDenote ident_self.
  Eval compute in TermDenote ident_unit.

  Theorem eval_ident_unit : eval (TermDenote ident_unit) (Dyn tt).
    compute.
    repeat econstructor.
    simpl.
    constructor.
  Qed.

  Theorem invert_ident : forall (E : Term) d,
    eval (TermDenote (fun _ => ident _ @ E _)) d
    -> eval (TermDenote E) d.
    inversion 1.

    crush.

    Focus 3.
    crush.
    unfold TermDenote in H0.
    simpl in H0.
    (** [injection H0.] *)
  Abort.

End impredicative.


Module predicative.

  Inductive val : Type :=
  | Func : nat -> val
  | VUnit.

  Inductive computation : Type :=
  | Return : val -> computation
  | Bind : computation -> (val -> computation) -> computation
  | CAbs : (val -> computation) -> computation
  | CApp : val -> val -> computation.

  Definition func := val -> computation.

  Fixpoint get (n : nat) (ls : list func) {struct ls} : option func :=
    match ls with
      | nil => None
      | x :: ls' =>
        if eq_nat_dec n (length ls')
          then Some x
          else get n ls'
    end.

  Inductive eval : list func -> computation -> list func -> val -> Prop :=
  | EvalReturn : forall ds d,
    eval ds (Return d) ds d
  | EvalBind : forall ds c1 c2 ds' d1 ds'' d2,
    eval ds c1 ds' d1
    -> eval ds' (c2 d1) ds'' d2
    -> eval ds (Bind c1 c2) ds'' d2
  | EvalCAbs : forall ds f,
    eval ds (CAbs f) (f :: ds) (Func (length ds))
  | EvalCApp : forall ds i d2 f ds' d3,
    get i ds = Some f
    -> eval ds (f d2) ds' d3
    -> eval ds (CApp (Func i) d2) ds' d3.

  Fixpoint termDenote (e : term val) : computation :=
    match e with
      | Var v => Return v
      | App e1 e2 => Bind (termDenote e1) (fun f =>
        Bind (termDenote e2) (fun x =>
          CApp f x))
      | Abs e' => CAbs (fun x => termDenote (e' x))

      | Unit => Return VUnit
    end.

  Definition TermDenote (E : Term) := termDenote (E _).

  Eval compute in TermDenote ident.
  Eval compute in TermDenote unite.
  Eval compute in TermDenote ident_self.
  Eval compute in TermDenote ident_unit.

  Theorem eval_ident_unit : exists ds, eval nil (TermDenote ident_unit) ds VUnit.
    compute.
    repeat econstructor.
    simpl.
    rewrite (eta Return).
    reflexivity.
  Qed.

  Hint Constructors eval.

  Lemma app_nil_start : forall A (ls : list A),
    ls = nil ++ ls.
    reflexivity.
  Qed.

  Lemma app_cons : forall A (x : A) (ls : list A),
    x :: ls = (x :: nil) ++ ls.
    reflexivity.
  Qed.

  Theorem eval_monotone : forall ds c ds' d,
    eval ds c ds' d
    -> exists ds'', ds' = ds'' ++ ds.
    Hint Resolve app_nil_start app_ass app_cons.

    induction 1; firstorder; subst; eauto.
  Qed.

  Lemma length_app : forall A (ds2 ds1 : list A),
    length (ds1 ++ ds2) = length ds1 + length ds2.
    induction ds1; simpl; intuition.
  Qed.

  Lemma get_app : forall ds2 d ds1,
    get (length ds2) (ds1 ++ d :: ds2) = Some d.
    Hint Rewrite length_app : cpdt.

    induction ds1; crush;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; crush.
  Qed.

  Theorem invert_ident : forall (E : Term) ds ds' d,
    eval ds (TermDenote (fun _ => ident _ @ E _)) ds' d
    -> eval ((fun x => Return x) :: ds) (TermDenote E) ds' d.
    inversion 1; subst.
    clear H.
    inversion H3; clear H3; subst.
    inversion H6; clear H6; subst.
    generalize (eval_monotone H2); crush.
    inversion H5; clear H5; subst.
    rewrite get_app in H3.
    inversion H3; clear H3; subst.
    inversion H7; clear H7; subst.
    assumption.
  Qed.

End predicative.
