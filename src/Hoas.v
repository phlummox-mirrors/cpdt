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

Ltac my_subst :=
  repeat match goal with
           | [ x : type |- _ ] => subst x
         end.

Ltac my_crush' :=
  crush; my_subst;
  repeat (match goal with
            | [ H : _ |- _ ] => generalize (inj_pairT2 _ _ _ _ _ H); clear H
          end; crush; my_subst).

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

Hint Extern 1 (_ = _ @ _) => simpl.

Lemma progress' : forall t (E : Exp t),
  Closed E
  -> Val E \/ exists E', E ==> E'.
  induction 1; crush;
    repeat match goal with
             | [ H : Val _ |- _ ] => inversion H; []; clear H; my_crush
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
Definition Cfold1 t1 t2 (E : Exp1 t1 t2) : Exp1 t1 t2 := fun _ x => cfold (E _ x).

Lemma fold_Cfold : forall t (E : Exp t),
  (fun _ => cfold (E _)) = Cfold E.
  reflexivity.
Qed.

Hint Rewrite fold_Cfold : fold.

Lemma fold_Cfold1 : forall t1 t2 (E : Exp1 t1 t2),
  (fun _ x => cfold (E _ x)) = Cfold1 E.
  reflexivity.
Qed.

Hint Rewrite fold_Cfold1 : fold.

Lemma fold_Subst_Cfold1 : forall t1 t2 (E : Exp1 t1 t2) (V : Exp t1),
  (fun _ => flatten (cfold (E _ (V _))))
  = Subst V (Cfold1 E).
  reflexivity.
Qed.

Axiom cheat : forall T, T.


Lemma fold_Const : forall n, (fun _ => Const' n) = Const n.
  reflexivity.
Qed.
Lemma fold_Plus : forall (E1 E2 : Exp _), (fun _ => Plus' (E1 _) (E2 _)) = Plus E1 E2.
  reflexivity.
Qed.
Lemma fold_App : forall dom ran (F : Exp (dom --> ran)) (X : Exp dom),
  (fun _ => App' (F _) (X _)) = App F X.
  reflexivity.
Qed.
Lemma fold_Abs : forall dom ran (B : Exp1 dom ran),
  (fun _ => Abs' (B _)) = Abs B.
  reflexivity.
Qed.

Hint Rewrite fold_Const fold_Plus fold_App fold_Abs : fold.

Lemma fold_Subst : forall t1 t2 (E1 : Exp1 t1 t2) (V : Exp t1),
  (fun _ => flatten (E1 _ (V _))) = Subst V E1.
  reflexivity.
Qed.

Hint Rewrite fold_Subst : fold.

Section Closed1.
  Variable xt : type.

  Definition Const1 (n : nat) : Exp1 xt Nat :=
    fun _ _ => Const' n.
  Definition Var1 : Exp1 xt xt := fun _ x => Var x.
  Definition Plus1 (E1 E2 : Exp1 xt Nat) : Exp1 xt Nat :=
    fun _ s => Plus' (E1 _ s) (E2 _ s).
  Definition App1 dom ran (F : Exp1 xt (dom --> ran)) (X : Exp1 xt dom) : Exp1 xt ran :=
    fun _ s => App' (F _ s) (X _ s).
  Definition Abs1 dom ran (B : forall var, var dom -> Exp1 xt ran) : Exp1 xt (dom --> ran) :=
    fun _ s => Abs' (fun x => B _ x _ s).

  Inductive Closed1 : forall t, Exp1 xt t -> Prop :=
  | CConst1 : forall n,
    Closed1 (Const1 n)
  | CPlus1 : forall E1 E2,
    Closed1 E1
    -> Closed1 E2
    -> Closed1 (Plus1 E1 E2)
  | CApp1 : forall dom ran (E1 : Exp1 _ (dom --> ran)) E2,
    Closed1 E1
    -> Closed1 E2
    -> Closed1 (App1 E1 E2)
  | CAbs1 : forall dom ran (E1 : forall var, var dom -> Exp1 _ ran),
    Closed1 (Abs1 E1).

  Axiom closed1 : forall t (E : Exp1 xt t), Closed1 E.
End Closed1.

Hint Resolve closed1.

Ltac ssimp := unfold Subst, Cfold in *; simpl in *; autorewrite with fold in *;
  repeat match goal with
           | [ xt : type |- _ ] =>
             rewrite (@fold_Subst xt) in *
         end;
  autorewrite with fold in *.

Lemma cfold_thorough : forall var t (e : exp var t),
  cfold (cfold e) = cfold e.
  induction e; crush; try (f_equal; ext_eq; eauto);
    match goal with
      | [ e1 : exp _ Nat, e2 : exp _ Nat |- _ ] =>
        dep_destruct (cfold e1); crush;
        dep_destruct (cfold e2); crush
    end.
Qed.

Lemma Cfold_thorough : forall t (E : Exp t),
  Cfold (Cfold E) = Cfold E.
  intros; unfold Cfold, Exp; ext_eq;
    apply cfold_thorough.
Qed.

Hint Resolve Cfold_thorough.

Section eq_arg.
  Variable A : Type.
  Variable B : A -> Type.

  Variable x : A.

  Variables f g : forall x, B x.
  Hypothesis Heq : f = g.

  Theorem eq_arg : f x = g x.
    congruence.
  Qed.
End eq_arg.

Implicit Arguments eq_arg [A B f g].

Lemma Cfold_Subst_thorough : forall t1 (V : Exp t1) t2 (B : Exp1 t1 t2),
  Subst (Cfold V) (Cfold1 B) = Cfold (Subst (Cfold V) (Cfold1 B)).

Lemma Cfold_Step_thorough' : forall t (E V : Exp t),
  E ===> V
  -> forall E', E = Cfold E'
    -> Cfold V = V.
  induction 1; crush.
  apply IHBigStep3 with (Subst V2 B).
  
  generalize (closed E'); inversion 1; my_crush.

  generalize (eq_arg (fun _ => Set) H2); ssimp.
  dep_destruct (cfold (E0 (fun _ => Set))); try discriminate;
    dep_destruct (cfold (E3 (fun _ => Set))); discriminate.

  ssimp; my_crush.

  rewrite <- (IHBigStep2 _ (refl_equal _)).
  generalize (IHBigStep1 _ (refl_equal _)).
  my_crush.
  ssimp.
  assert (B = Cfold1 B).
  generalize H2; clear_all; my_crush.
  unfold Exp1; ext_eq.
  generalize (eq_arg x H2); injection 1; my_crush.

  rewrite H8.
  

  my_crush.

Lemma Cfold_thorough : forall t (E V : Exp t),
  Cfold E ===> V
  -> V = Cfold V.

Lemma Cfold_Subst' : forall t (E V : Exp t),
  E ===> V
  -> forall t' B (V' : Exp t') V'', E = Cfold (Subst V' B)
    -> V = Cfold V'' 
    -> Closed1 B
    -> Subst (Cfold V') (Cfold1 B) ===> Cfold V''.
  induction 1; inversion 3; my_crush; ssimp; my_crush.

  rewrite <- H0; auto.

  apply cheat.
  apply cheat.
  apply cheat.

  repeat rewrite (@fold_Subst_Cfold1 t') in *.
  repeat rewrite fold_Cfold in *.
  apply SApp with (Cfold1 B) V2.

  unfold Abs, Subst, Cfold, Cfold1 in *.
  match goal with
    | [ |- _ ===> ?F ] =>
      replace F with (fun var => cfold (Abs' (fun x : var _ => B var x)))
  end.
  apply IHBigStep1; auto.
  ssimp.
  apply cheat.
  reflexivity.

  replace V2 with (Cfold V2).
  unfold Cfold, Subst.
  apply IHBigStep2; auto.
  apply cheat.
  apply cheat.

  replace V2 with (Cfold V2).
  unfold Subst, Cfold.
  apply IHBigStep3; auto.
  apply cheat.
  apply cheat.

  apply cheat.  
Qed.

Theorem Cfold_Subst : forall t1 t2 (V : Exp t1) B (V' : Exp t2),
  Subst (Cfold V) (Cfold1 B) ===> Cfold V'
  -> Subst (Cfold V) (Cfold1 B) ===> Cfold V'.
  Hint Resolve Cfold_Subst'.

  eauto.
Qed.

Hint Resolve Cfold_Subst.

Theorem Cfold_correct : forall t (E V : Exp t),
  E ===> V
  -> Cfold E ===> Cfold V.
  induction 1; crush; ssimp; eauto.

  change ((fun H1 : type -> Type =>
    match Cfold E1 H1 with
      | Const' n3 =>
        match Cfold E2 H1 with
          | Const' n4 => Const' (var:=H1) (n3 + n4)
          | Plus' _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
          | Var _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
          | App' _ _ _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
          | Abs' _ _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
        end
      | Plus' _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
      | Var _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
      | App' _ _ _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
      | Abs' _ _ _ => Plus' (cfold (E1 H1)) (cfold (E2 H1))
    end) ===> Const (n1 + n2)).

  Ltac simp :=
    repeat match goal with
             | [ H : _ = Cfold _ |- _ ] => rewrite <- H in *
             | [ H : Const _ ===> Const _ |- _ ] =>
               inversion H; clear H; my_crush
           end.

  generalize (closed (Cfold E1)); inversion 1; my_crush; simp;
    try solve [ ssimp; simp; eauto ];
      generalize (closed (Cfold E2)); inversion 1; my_crush; simp; ssimp; simp; eauto.
Qed.
