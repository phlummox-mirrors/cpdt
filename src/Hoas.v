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

Definition zero := Const 0.
Definition one := Const 1.
Definition one_again := Plus zero one.
Definition ident : Exp (Nat --> Nat) := Abs (fun _ X => Var X).
Definition app_ident := App ident one_again.
Definition app : Exp ((Nat --> Nat) --> Nat --> Nat) := fun _ =>
  Abs' (fun f => Abs' (fun x => App' (Var f) (Var x))).
Definition app_ident' := App (App app ident) one_again.

Fixpoint countVars t (e : exp (fun _ => unit) t) {struct e} : nat :=
  match e with
    | Const' _ => 0
    | Plus' e1 e2 => countVars e1 + countVars e2
    | Var _ _ => 1
    | App' _ _ e1 e2 => countVars e1 + countVars e2
    | Abs' _ _ e' => countVars (e' tt)
  end.

Definition CountVars t (E : Exp t) : nat := countVars (E _).

Eval compute in CountVars zero.
Eval compute in CountVars one.
Eval compute in CountVars one_again.
Eval compute in CountVars ident.
Eval compute in CountVars app_ident.
Eval compute in CountVars app.
Eval compute in CountVars app_ident'.

Fixpoint countOne t (e : exp (fun _ => bool) t) {struct e} : nat :=
  match e with
    | Const' _ => 0
    | Plus' e1 e2 => countOne e1 + countOne e2
    | Var _ true => 1
    | Var _ false => 0
    | App' _ _ e1 e2 => countOne e1 + countOne e2
    | Abs' _ _ e' => countOne (e' false)
  end.

Definition CountOne t1 t2 (E : Exp1 t1 t2) : nat :=
  countOne (E _ true).

Definition ident1 : Exp1 Nat Nat := fun _ X => Var X.
Definition add_self : Exp1 Nat Nat := fun _ X => Plus' (Var X) (Var X).
Definition app_zero : Exp1 (Nat --> Nat) Nat := fun _ X => App' (Var X) (Const' 0).
Definition app_ident1 : Exp1 Nat Nat := fun _ X => App' (Abs' (fun Y => Var Y)) (Var X).

Eval compute in CountOne ident1.
Eval compute in CountOne add_self.
Eval compute in CountOne app_zero.
Eval compute in CountOne app_ident1.

Section ToString.
  Open Scope string_scope.

  Fixpoint natToString (n : nat) : string :=
    match n with
      | O => "O"
      | S n' => "S(" ++ natToString n' ++ ")"
    end.

  Fixpoint toString t (e : exp (fun _ => string) t) (cur : string) {struct e} : string * string :=
    match e with
      | Const' n => (cur, natToString n)
      | Plus' e1 e2 =>
        let (cur', s1) := toString e1 cur in
        let (cur'', s2) := toString e2 cur' in
        (cur'', "(" ++ s1 ++ ") + (" ++ s2 ++ ")")
      | Var _ s => (cur, s)
      | App' _ _ e1 e2 =>
        let (cur', s1) := toString e1 cur in
        let (cur'', s2) := toString e2 cur' in
        (cur'', "(" ++ s1 ++ ") (" ++ s2 ++ ")")
      | Abs' _ _ e' =>
        let (cur', s) := toString (e' cur) (cur ++ "'") in
        (cur', "(\" ++ cur ++ ", " ++ s ++ ")")
    end.

  Definition ToString t (E : Exp t) : string := snd (toString (E _) "x").
End ToString.

Eval compute in ToString zero.
Eval compute in ToString one.
Eval compute in ToString one_again.
Eval compute in ToString ident.
Eval compute in ToString app_ident.
Eval compute in ToString app.
Eval compute in ToString app_ident'.

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

Eval compute in Subst one ident1.
Eval compute in Subst one add_self.
Eval compute in Subst ident app_zero.
Eval compute in Subst one app_ident1.


(** * A Type Soundness Proof *)

Reserved Notation "E1 ==> E2" (no associativity, at level 90).

Inductive Val : forall t, Exp t -> Prop :=
| VConst : forall n, Val (Const n)
| VAbs : forall dom ran (B : Exp1 dom ran), Val (Abs B).

Hint Constructors Val.

Inductive Ctx : type -> type -> Type :=
| AppCong1 : forall (dom ran : type),
  Exp dom -> Ctx (dom --> ran) ran
| AppCong2 : forall (dom ran : type),
  Exp (dom --> ran) -> Ctx dom ran
| PlusCong1 : Exp Nat -> Ctx Nat Nat
| PlusCong2 : Exp Nat -> Ctx Nat Nat.

Inductive isCtx : forall t1 t2, Ctx t1 t2 -> Prop :=
| IsApp1 : forall dom ran (X : Exp dom), isCtx (AppCong1 ran X)
| IsApp2 : forall dom ran (F : Exp (dom --> ran)), Val F -> isCtx (AppCong2 F)
| IsPlus1 : forall E2, isCtx (PlusCong1 E2)
| IsPlus2 : forall E1, Val E1 -> isCtx (PlusCong2 E1).

Definition plug t1 t2 (C : Ctx t1 t2) : Exp t1 -> Exp t2 :=
  match C in Ctx t1 t2 return Exp t1 -> Exp t2 with
    | AppCong1 _ _ X => fun F => App F X
    | AppCong2 _ _ F => fun X => App F X
    | PlusCong1 E2 => fun E1 => Plus E1 E2
    | PlusCong2 E1 => fun E2 => Plus E1 E2
  end.

Infix "@" := plug (no associativity, at level 60).

Inductive Step : forall t, Exp t -> Exp t -> Prop :=
| Beta : forall dom ran (B : Exp1 dom ran) (X : Exp dom),
  Val X
  -> App (Abs B) X ==> Subst X B
| Sum : forall n1 n2,
  Plus (Const n1) (Const n2) ==> Const (n1 + n2)
| Cong : forall t t' (C : Ctx t t') E E' E1,
  isCtx C
  -> E1 = C @ E
  -> E ==> E'
  -> E1 ==> C @ E'

  where "E1 ==> E2" := (Step E1 E2).

Hint Constructors isCtx Step.

Inductive Closed : forall t, Exp t -> Prop :=
| CConst : forall n,
  Closed (Const n)
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

Hint Extern 1 (_ = _ @ _) => simpl.

Lemma progress' : forall t (E : Exp t),
  Closed E
  -> Val E \/ exists E', E ==> E'.
  induction 1; crush;
    repeat match goal with
             | [ H : Val _ |- _ ] => inversion H; []; clear H; my_crush'
           end; eauto 6.
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

Lemma Multi_Cong : forall t t' (C : Ctx t t'),
  isCtx C
  -> forall E E', E ==>* E'
    -> C @ E ==>* C @ E'.
  induction 2; crush; eauto.
Qed.

Lemma Multi_Cong' : forall t t' (C : Ctx t t') E1 E2 E E',
  isCtx C
  -> E1 = C @ E
  -> E2 = C @ E'
  -> E ==>* E'
  -> E1 ==>* E2.
  crush; apply Multi_Cong; auto.
Qed.

Hint Resolve Multi_Cong'.

Ltac mtrans E :=
  match goal with
    | [ |- E ==>* _ ] => fail 1
    | _ => apply MultiStep_trans with E; [ solve [ eauto ] | eauto ]
  end.

Theorem Big_Multi : forall t (E V : Exp t),
  E ===> V
  -> E ==>* V.
  induction 1; crush; eauto;
    repeat match goal with
             | [ n1 : _, E2 : _ |- _ ] => mtrans (Plus (Const n1) E2)
             | [ n1 : _, n2 : _ |- _ ] => mtrans (Plus (Const n1) (Const n2))
             | [ B : _, E2 : _ |- _ ] => mtrans (App (Abs B) E2)
           end.
Qed.

Lemma Big_Val' : forall t (V1 V2 : Exp t),
  Val V2
  -> V1 = V2
  -> V1 ===> V2.
  crush.
Qed.

Hint Resolve Big_Val'.

Ltac equate_conj F G :=
  match constr:(F, G) with
    | (_ ?x1, _ ?x2) => constr:(x1 = x2)
    | (_ ?x1 ?y1, _ ?x2 ?y2) => constr:(x1 = x2 /\ y1 = y2)
    | (_ ?x1 ?y1 ?z1, _ ?x2 ?y2 ?z2) => constr:(x1 = x2 /\ y1 = y2 /\ z1 = z2)
    | (_ ?x1 ?y1 ?z1 ?u1, _ ?x2 ?y2 ?z2 ?u2) => constr:(x1 = x2 /\ y1 = y2 /\ z1 = z2 /\ u1 = u2)
    | (_ ?x1 ?y1 ?z1 ?u1 ?v1, _ ?x2 ?y2 ?z2 ?u2 ?v2) => constr:(x1 = x2 /\ y1 = y2 /\ z1 = z2 /\ u1 = u2 /\ v1 = v2)
  end.

Ltac my_crush :=
  my_crush';
  repeat (match goal with
            | [ H : ?F = ?G |- _ ] =>
              (let H' := fresh "H'" in
                assert (H' : F (fun _ => unit) = G (fun _ => unit)); [ congruence
                  | discriminate || injection H'; clear H' ];
                my_crush';
                repeat match goal with
                         | [ H : context[fun _ => unit] |- _ ] => clear H
                       end;
                match type of H with
                  | ?F = ?G =>
                    let ec := equate_conj F G in
                      let var := fresh "var" in
                        assert ec; [ intuition; unfold Exp; apply ext_eq; intro var;
                          assert (H' : F var = G var); try congruence;
                            match type of H' with
                              | ?X = ?Y =>
                                let X := eval hnf in X in
                                  let Y := eval hnf in Y in
                                    change (X = Y) in H'
                            end; injection H'; my_crush'; tauto
                          | intuition; subst ]
                end);
              clear H
          end; my_crush');
  my_crush'.

Lemma Multi_Big' : forall t (E E' : Exp t),
  E ==> E'
  -> forall E'', E' ===> E''
    -> E ===> E''.
  induction 1; crush; eauto;
    match goal with
      | [ H : _ ===> _ |- _ ] => inversion H; my_crush; eauto
    end;
    match goal with
      | [ H : isCtx _ |- _ ] => inversion H; my_crush; eauto
    end.
Qed.

Hint Resolve Multi_Big'.

Theorem Multi_Big : forall t (E V : Exp t),
  E ==>* V
  -> Val V
  -> E ===> V.
  induction 1; crush; eauto.
Qed.
