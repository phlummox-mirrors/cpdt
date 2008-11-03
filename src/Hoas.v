(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith Eqdep String List.

Require Import Axioms DepList Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Higher-Order Abstract Syntax}% *)

(** TODO: Prose for this chapter *)


(** * Parametric Higher-Order Abstract Syntax *)

Inductive type : Type :=
| Nat : type
| Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

Section exp.
  Variable var : type -> Type.

  Inductive exp : type -> Type :=
  | Const' : nat -> exp Nat
  | Plus' : exp Nat -> exp Nat -> exp Nat

  | Var : forall t, var t -> exp t
  | App' : forall dom ran, exp (dom --> ran) -> exp dom -> exp ran
  | Abs' : forall dom ran, (var dom -> exp ran) -> exp (dom --> ran).
End exp.

Implicit Arguments Const' [var].
Implicit Arguments Var [var t].
Implicit Arguments Abs' [var dom ran].

Definition Exp t := forall var, exp var t.
Definition Exp1 t1 t2 := forall var, var t1 -> exp var t2.

Definition Const (n : nat) : Exp Nat :=
  fun _ => Const' n.
Definition Plus (E1 E2 : Exp Nat) : Exp Nat :=
  fun _ => Plus' (E1 _) (E2 _).
Definition App dom ran (F : Exp (dom --> ran)) (X : Exp dom) : Exp ran :=
  fun _ => App' (F _) (X _).
Definition Abs dom ran (B : Exp1 dom ran) : Exp (dom --> ran) :=
  fun _ => Abs' (B _).

Section flatten.
  Variable var : type -> Type.

  Fixpoint flatten t (e : exp (exp var) t) {struct e} : exp var t :=
    match e in exp _ t return exp _ t with
      | Const' n => Const' n
      | Plus' e1 e2 => Plus' (flatten e1) (flatten e2)
      | Var _ e' => e'
      | App' _ _ e1 e2 => App' (flatten e1) (flatten e2)
      | Abs' _ _ e' => Abs' (fun x => flatten (e' (Var x)))
    end.
End flatten.

Definition Subst t1 t2 (E1 : Exp t1) (E2 : Exp1 t1 t2) : Exp t2 := fun _ =>
  flatten (E2 _ (E1 _)).


(** * A Type Soundness Proof *)

Reserved Notation "E1 ==> E2" (no associativity, at level 90).

Inductive Val : forall t, Exp t -> Prop :=
| VConst : forall n, Val (Const n)
| VAbs : forall dom ran (B : Exp1 dom ran), Val (Abs B).

Hint Constructors Val.

Inductive Step : forall t, Exp t -> Exp t -> Prop :=
| Beta : forall dom ran (B : Exp1 dom ran) (X : Exp dom),
  Val X
  -> App (Abs B) X ==> Subst X B
| AppCong1 : forall dom ran (F : Exp (dom --> ran)) (X : Exp dom) F',
  F ==> F'
  -> App F X ==> App F' X
| AppCong2 : forall dom ran (F : Exp (dom --> ran)) (X : Exp dom) X',
  Val F
  -> X ==> X'
  -> App F X ==> App F X'

| Sum : forall n1 n2,
  Plus (Const n1) (Const n2) ==> Const (n1 + n2)
| PlusCong1 : forall E1 E2 E1',
  E1 ==> E1'
  -> Plus E1 E2 ==> Plus E1' E2
| PlusCong2 : forall E1 E2 E2',
  Val E1
  -> E2 ==> E2'
  -> Plus E1 E2 ==> Plus E1 E2'

  where "E1 ==> E2" := (Step E1 E2).

Hint Constructors Step.

Inductive Closed : forall t, Exp t -> Prop :=
| CConst : forall b,
  Closed (Const b)
| CPlus : forall E1 E2,
  Closed E1
  -> Closed E2
  -> Closed (Plus E1 E2)
| CApp : forall dom ran (E1 : Exp (dom --> ran)) E2,
  Closed E1
  -> Closed E2
  -> Closed (App E1 E2)
| CAbs : forall dom ran (E1 : Exp1 dom ran),
  Closed (Abs E1).

Axiom closed : forall t (E : Exp t), Closed E.

Ltac my_crush' :=
  crush;
  repeat (match goal with
            | [ H : _ |- _ ] => generalize (inj_pairT2 _ _ _ _ _ H); clear H
          end; crush).

Ltac my_crush :=
  my_crush';
  try (match goal with
         | [ H : ?F = ?G |- _ ] =>
           match goal with
             | [ _ : F (fun _ => unit) = G (fun _ => unit) |- _ ] => fail 1
             | _ =>
               let H' := fresh "H'" in
                 assert (H' : F (fun _ => unit) = G (fun _ => unit)); [ congruence
                   | discriminate || injection H' ];
                 clear H'
           end
       end; my_crush');
  repeat match goal with
           | [ H : ?F = ?G, H2 : ?X (fun _ => unit) = ?Y (fun _ => unit) |- _ ] =>
             match X with
               | Y => fail 1
               | _ =>
                 assert (X = Y); [ unfold Exp; apply ext_eq; intro var;
                   let H' := fresh "H'" in
                     assert (H' : F var = G var); [ congruence
                       | match type of H' with
                           | ?X = ?Y =>
                             let X := eval hnf in X in
                               let Y := eval hnf in Y in
                                 change (X = Y) in H'
                         end; injection H'; clear H'; my_crush' ]
                   | my_crush'; clear H2 ]
             end
         end.

Lemma progress' : forall t (E : Exp t),
  Closed E
  -> Val E \/ exists E', E ==> E'.
  induction 1; crush;
    repeat match goal with
             | [ H : Val _ |- _ ] => inversion H; []; clear H; my_crush
           end; eauto.
Qed.

Theorem progress : forall t (E : Exp t),
  Val E \/ exists E', E ==> E'.
  intros; apply progress'; apply closed.
Qed.


(** * Big-Step Semantics *)

Reserved Notation "E1 ===> E2" (no associativity, at level 90).

Inductive BigStep : forall t, Exp t -> Exp t -> Prop :=
| SConst : forall n,
  Const n ===> Const n
| SPlus : forall E1 E2 n1 n2,
  E1 ===> Const n1
  -> E2 ===> Const n2
  -> Plus E1 E2 ===> Const (n1 + n2)

| SApp : forall dom ran (E1 : Exp (dom --> ran)) E2 B V2 V,
  E1 ===> Abs B
  -> E2 ===> V2
  -> Subst V2 B ===> V
  -> App E1 E2 ===> V
| SAbs : forall dom ran (B : Exp1 dom ran),
  Abs B ===> Abs B

  where "E1 ===> E2" := (BigStep E1 E2).

Hint Constructors BigStep.

Reserved Notation "E1 ==>* E2" (no associativity, at level 90).

Inductive MultiStep : forall t, Exp t -> Exp t -> Prop :=
| Done : forall t (E : Exp t), E ==>* E
| OneStep : forall t (E E' E'' : Exp t),
  E ==> E'
  -> E' ==>* E''
  -> E ==>* E''

  where "E1 ==>* E2" := (MultiStep E1 E2).

Hint Constructors MultiStep.

Theorem MultiStep_trans : forall t (E1 E2 E3 : Exp t),
  E1 ==>* E2
  -> E2 ==>* E3
  -> E1 ==>* E3.
  induction 1; eauto.
Qed.

Hint Resolve MultiStep_trans.

Theorem Big_Val : forall t (E V : Exp t),
  E ===> V
  -> Val V.
  induction 1; crush.
Qed.

Theorem Val_Big : forall t (V : Exp t),
  Val V
  -> V ===> V.
  destruct 1; crush.
Qed.

Hint Resolve Big_Val Val_Big.

Ltac uiper :=
  repeat match goal with
           | [ pf : _ = _ |- _ ] =>
             generalize pf; subst; intro;
               rewrite (UIP_refl _ _ pf); simpl;
                 repeat match goal with
                          | [ H : forall pf : ?X = ?X, _ |- _ ] =>
                            generalize (H (refl_equal _)); clear H; intro H
                        end
         end.

Lemma Multi_PlusCong1' : forall E2 t (pf : t = Nat) (E1 E1' : Exp t),
  E1 ==>* E1'
  -> Plus (match pf with refl_equal => E1 end) E2
  ==>* Plus (match pf with refl_equal => E1' end) E2.
  induction 1; crush; uiper; eauto.
Qed.

Lemma Multi_PlusCong1 : forall E1 E2 E1',
  E1 ==>* E1'
  -> Plus E1 E2 ==>* Plus E1' E2.
  intros; generalize (Multi_PlusCong1' E2 (refl_equal _)); auto.
Qed.

Lemma Multi_PlusCong2' : forall E1 (_ : Val E1) t (pf : t = Nat) (E2 E2' : Exp t),
  E2 ==>* E2'
  -> Plus E1 (match pf with refl_equal => E2 end)
  ==>* Plus E1 (match pf with refl_equal => E2' end).
  induction 2; crush; uiper; eauto.
Qed.

Lemma Multi_PlusCong2 : forall E1 E2 E2',
  Val E1
  -> E2 ==>* E2'
  -> Plus E1 E2 ==>* Plus E1 E2'.
  intros E1 E2 E2' H; generalize (Multi_PlusCong2' H (refl_equal _)); auto.
Qed.

Lemma Multi_AppCong1' : forall dom ran E2 t (pf : t = dom --> ran) (E1 E1' : Exp t),
  E1 ==>* E1'
  -> App (match pf in _ = t' return Exp t' with refl_equal => E1 end) E2
  ==>* App (match pf in _ = t' return Exp t' with refl_equal => E1' end) E2.
  induction 1; crush; uiper; eauto.
Qed.

Lemma Multi_AppCong1 : forall dom ran (E1 : Exp (dom --> ran)) E2 E1',
  E1 ==>* E1'
  -> App E1 E2 ==>* App E1' E2.
  intros; generalize (Multi_AppCong1' (ran := ran) E2 (refl_equal _)); auto.
Qed.

Lemma Multi_AppCong2 : forall dom ran (E1 : Exp (dom --> ran)) E2 E2',
  Val E1
  -> E2 ==>* E2'
  -> App E1 E2 ==>* App E1 E2'.
  induction 2; crush; eauto.
Qed.

Hint Resolve Multi_PlusCong1 Multi_PlusCong2 Multi_AppCong1 Multi_AppCong2.

Theorem Big_Multi : forall t (E V : Exp t),
  E ===> V
  -> E ==>* V.
  induction 1; crush; eauto 8.
Qed.

Lemma Big_Val' : forall t (V1 V2 : Exp t),
  Val V2
  -> V1 = V2
  -> V1 ===> V2.
  crush.
Qed.

Hint Resolve Big_Val'.

Lemma Multi_Big' : forall t (E E' : Exp t),
  E ==> E'
  -> forall E'', E' ===> E''
    -> E ===> E''.
  induction 1; crush; eauto;
    match goal with
      | [ H : _ ===> _ |- _ ] => inversion H; my_crush; eauto
    end.
Qed.

Hint Resolve Multi_Big'.

Theorem Multi_Big : forall t (E V : Exp t),
  E ==>* V
  -> Val V
  -> E ===> V.
  induction 1; crush; eauto.
Qed.


(** * Constant folding *)

Section cfold.
  Variable var : type -> Type.

  Fixpoint cfold t (e : exp var t) {struct e} : exp var t :=
    match e in exp _ t return exp _ t with
      | Const' n => Const' n
      | Plus' e1 e2 =>
        let e1' := cfold e1 in
        let e2' := cfold e2 in
          match e1', e2' with
            | Const' n1, Const' n2 => Const' (n1 + n2)
            | _, _ => Plus' e1' e2'
          end

      | Var _ x => Var x
      | App' _ _ e1 e2 => App' (cfold e1) (cfold e2)
      | Abs' _ _ e' => Abs' (fun x => cfold (e' x))
    end.
End cfold.

Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).


Definition ExpN (G : list type) (t : type) := forall var, hlist var G -> exp var t.

Definition ConstN G (n : nat) : ExpN G Nat :=
  fun _ _ => Const' n.
Definition PlusN G (E1 E2 : ExpN G Nat) : ExpN G Nat :=
  fun _ s => Plus' (E1 _ s) (E2 _ s).
Definition AppN G dom ran (F : ExpN G (dom --> ran)) (X : ExpN G dom) : ExpN G ran :=
  fun _ s => App' (F _ s) (X _ s).
Definition AbsN G dom ran (B : ExpN (dom :: G) ran) : ExpN G (dom --> ran) :=
  fun _ s => Abs' (fun x => B _ (x ::: s)).