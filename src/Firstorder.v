(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith String List.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\part{Formalizing Programming Languages and Compilers}

   \chapter{First-Order Abstract Syntax}% *)

(** TODO: Prose for this chapter *)


(** * Concrete Binding *)

Module Concrete.

  Definition var := string.
  Definition var_eq := string_dec.

  Inductive exp : Set :=
  | Const : bool -> exp
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : var -> exp -> exp.

  Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

  Definition ctx := list (var * type).

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  Inductive lookup : ctx -> var -> type -> Prop :=
  | First : forall x t G,
    (x, t) :: G |-v x : t
  | Next : forall x t x' t' G,
    x <> x'
    -> G |-v x : t
    -> (x', t') :: G |-v x : t

    where "G |-v x : t" := (lookup G x t).

  Hint Constructors lookup.

  Reserved Notation "G |-e e : t" (no associativity, at level 90, e at next level).

  Inductive hasType : ctx -> exp -> type -> Prop :=
  | TConst : forall G b,
    G |-e Const b : Bool
  | TVar : forall G v t,
    G |-v v : t
    -> G |-e Var v : t
  | TApp : forall G e1 e2 dom ran,
    G |-e e1 : dom --> ran
    -> G |-e e2 : dom
    -> G |-e App e1 e2 : ran
  | TAbs : forall G x e' dom ran,
    (x, dom) :: G |-e e' : ran
    -> G |-e Abs x e' : dom --> ran

    where "G |-e e : t" := (hasType G e t).

  Hint Constructors hasType.

  Lemma weaken_lookup : forall x t G' G1,
    G1 |-v x : t
    -> G1 ++ G' |-v x : t.
    induction G1 as [ | [x' t'] tl ]; crush;
      match goal with
        | [ H : _ |-v _ : _ |- _ ] => inversion H; crush
      end.
  Qed.

  Hint Resolve weaken_lookup.

  Theorem weaken_hasType' : forall G' G e t,
    G |-e e : t
    -> G ++ G' |-e e : t.
    induction 1; crush; eauto.
  Qed.

  Theorem weaken_hasType : forall e t,
    nil |-e e : t
    -> forall G', G' |-e e : t.
    intros; change G' with (nil ++ G');
      eapply weaken_hasType'; eauto.
  Qed.

  Hint Resolve weaken_hasType.

  Section subst.
    Variable x : var.
    Variable e1 : exp.

    Fixpoint subst (e2 : exp) : exp :=
      match e2 with
        | Const b => Const b
        | Var x' =>
          if var_eq x' x
            then e1
            else Var x'
        | App e1 e2 => App (subst e1) (subst e2)
        | Abs x' e' =>
          Abs x' (if var_eq x' x
            then e'
            else subst e')
      end.

    Variable xt : type.
    Hypothesis Ht' : nil |-e e1 : xt.

    Notation "x # G" := (forall t' : type, In (x, t') G -> False) (no associativity, at level 90).

    Lemma subst_lookup' : forall x' t,
      x <> x'
      -> forall G1, G1 ++ (x, xt) :: nil |-v x' : t
        -> G1 |-v x' : t.
      induction G1 as [ | [x'' t'] tl ]; crush;
        match goal with
          | [ H : _ |-v _ : _ |- _ ] => inversion H
        end; crush.
    Qed.

    Hint Resolve subst_lookup'.

    Lemma subst_lookup : forall x' t G1,
      x' # G1
      -> G1 ++ (x, xt) :: nil |-v x' : t
      -> t = xt.
      induction G1 as [ | [x'' t'] tl ]; crush; eauto;
        match goal with
          | [ H : _ |-v _ : _ |- _ ] => inversion H
        end; crush; elimtype False; eauto;
        match goal with
          | [ H : nil |-v _ : _ |- _ ] => inversion H
        end.
    Qed.

    Implicit Arguments subst_lookup [x' t G1].

    Lemma shadow_lookup : forall v t t' G1,
      G1 |-v x : t'
      -> G1 ++ (x, xt) :: nil |-v v : t
      -> G1 |-v v : t.
      induction G1 as [ | [x'' t''] tl ]; crush;
        match goal with
          | [ H : nil |-v _ : _ |- _ ] => inversion H
          | [ H1 : _ |-v _ : _, H2 : _ |-v _ : _ |- _ ] =>
            inversion H1; crush; inversion H2; crush
        end.
    Qed.

    Lemma shadow_hasType' : forall G e t,
      G |-e e : t
      -> forall G1, G = G1 ++ (x, xt) :: nil
        -> forall t'', G1 |-v x : t''
          -> G1 |-e e : t.
      Hint Resolve shadow_lookup.

      induction 1; crush; eauto;
        match goal with
          | [ H : (?x0, _) :: _ ++ (x, _) :: _ |-e _ : _ |- _ ] =>
            destruct (var_eq x0 x); subst; eauto
        end.
    Qed.

    Lemma shadow_hasType : forall G1 e t t'',
      G1 ++ (x, xt) :: nil |-e e : t
      -> G1 |-v x : t''
      -> G1 |-e e : t.
      intros; eapply shadow_hasType'; eauto.
    Qed.

    Hint Resolve shadow_hasType.

    Lemma disjoint_cons : forall x x' t (G : ctx),
      x # G
      -> x' <> x
      -> x # (x', t) :: G.
      firstorder;
        match goal with
          | [ H : (_, _) = (_, _) |- _ ] => injection H
        end; crush.
    Qed.

    Hint Resolve disjoint_cons.

    Theorem subst_hasType : forall G e2 t,
      G |-e e2 : t
        -> forall G1, G = G1 ++ (x, xt) :: nil
          -> x # G1
          -> G1 |-e subst e2 : t.
      induction 1; crush;
        try match goal with
              | [ |- context[if ?E then _ else _] ] => destruct E
            end; crush; eauto 6;
        match goal with
          | [ H1 : x # _, H2 : _ |-v x : _ |- _ ] =>
            rewrite (subst_lookup H1 H2)
        end; crush.
    Qed.

    Theorem subst_hasType_closed : forall e2 t,
      (x, xt) :: nil |-e e2 : t
      -> nil |-e subst e2 : t.
      intros; eapply subst_hasType; eauto.
    Qed.
  End subst.

  Hint Resolve subst_hasType_closed.

  Notation "[ x ~> e1 ] e2" := (subst x e1 e2) (no associativity, at level 80).

  Inductive val : exp -> Prop :=
  | VConst : forall b, val (Const b)
  | VAbs : forall x e, val (Abs x e).

  Hint Constructors val.

  Reserved Notation "e1 ==> e2" (no associativity, at level 90).

  Inductive step : exp -> exp -> Prop :=
  | Beta : forall x e1 e2,
    val e2
    -> App (Abs x e1) e2 ==> [x ~> e2] e1
  | Cong1 : forall e1 e2 e1',
    e1 ==> e1'
    -> App e1 e2 ==> App e1' e2
  | Cong2 : forall e1 e2 e2',
    val e1
    -> e2 ==> e2'
    -> App e1 e2 ==> App e1 e2'

    where "e1 ==> e2" := (step e1 e2).

  Hint Constructors step.

  Lemma progress' : forall G e t, G |-e e : t
    -> G = nil
    -> val e \/ exists e', e ==> e'.
    induction 1; crush; eauto;
      try match goal with
            | [ H : _ |-e _ : _ --> _ |- _ ] => inversion H
          end;
      repeat match goal with
               | [ H : _ |- _ ] => solve [ inversion H; crush; eauto ]
             end.
  Qed.

  Theorem progress : forall e t, nil |-e e : t
    -> val e \/ exists e', e ==> e'.
    intros; eapply progress'; eauto.
  Qed.

  Lemma preservation' : forall G e t, G |-e e : t
    -> G = nil
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    induction 1; inversion 2; crush; eauto;
      match goal with
        | [ H : _ |-e Abs _ _ : _ |- _ ] => inversion H
      end; eauto.
  Qed.

  Theorem preservation : forall e t, nil |-e e : t
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    intros; eapply preservation'; eauto.
  Qed.

End Concrete.


(** * De Bruijn Indices *)

Module DeBruijn.

  Definition var := nat.
  Definition var_eq := eq_nat_dec.

  Inductive exp : Set :=
  | Const : bool -> exp
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : exp -> exp.

  Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

  Definition ctx := list type.

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  Inductive lookup : ctx -> var -> type -> Prop :=
  | First : forall t G,
    t :: G |-v O : t
  | Next : forall x t t' G,
    G |-v x : t
    -> t' :: G |-v S x : t

    where "G |-v x : t" := (lookup G x t).

  Hint Constructors lookup.

  Reserved Notation "G |-e e : t" (no associativity, at level 90, e at next level).

  Inductive hasType : ctx -> exp -> type -> Prop :=
  | TConst : forall G b,
    G |-e Const b : Bool
  | TVar : forall G v t,
    G |-v v : t
    -> G |-e Var v : t
  | TApp : forall G e1 e2 dom ran,
    G |-e e1 : dom --> ran
    -> G |-e e2 : dom
    -> G |-e App e1 e2 : ran
  | TAbs : forall G e' dom ran,
    dom :: G |-e e' : ran
    -> G |-e Abs e' : dom --> ran

    where "G |-e e : t" := (hasType G e t).

  Hint Constructors hasType.

  Lemma weaken_lookup : forall G' v t G,
    G |-v v : t
    -> G ++ G' |-v v : t.
    induction 1; crush.
  Qed.

  Hint Resolve weaken_lookup.

  Theorem weaken_hasType' : forall G' G e t,
    G |-e e : t
    -> G ++ G' |-e e : t.
    induction 1; crush; eauto.
  Qed.

  Theorem weaken_hasType : forall e t,
    nil |-e e : t
    -> forall G', G' |-e e : t.
    intros; change G' with (nil ++ G');
      eapply weaken_hasType'; eauto.
  Qed.

  Hint Resolve weaken_hasType.

  Section subst.
    Variable e1 : exp.

    Fixpoint subst (x : var) (e2 : exp) : exp :=
      match e2 with
        | Const b => Const b
        | Var x' =>
          if var_eq x' x
            then e1
            else Var x'
        | App e1 e2 => App (subst x e1) (subst x e2)
        | Abs e' => Abs (subst (S x) e')
      end.

    Variable xt : type.

    Lemma subst_eq : forall t G1,
      G1 ++ xt :: nil |-v length G1 : t
      -> t = xt.
      induction G1; inversion 1; crush.
    Qed.

    Implicit Arguments subst_eq [t G1].

    Lemma subst_eq' : forall t G1 x,
      G1 ++ xt :: nil |-v x : t
      -> x <> length G1
      -> G1 |-v x : t.
      induction G1; inversion 1; crush;
        match goal with
          | [ H : nil |-v _ : _ |- _ ] => inversion H
        end.
    Qed.

    Hint Resolve subst_eq'.

    Lemma subst_neq : forall v t G1,
      G1 ++ xt :: nil |-v v : t
      -> v <> length G1
      -> G1 |-e Var v : t.
      induction G1; inversion 1; crush.
    Qed.

    Hint Resolve subst_neq.

    Hypothesis Ht' : nil |-e e1 : xt.

    Lemma hasType_push : forall dom G1 e' ran,
      dom :: G1 |-e subst (length (dom :: G1)) e' : ran
      -> dom :: G1 |-e subst (S (length G1)) e' : ran.
      trivial.
    Qed.

    Hint Resolve hasType_push.

    Theorem subst_hasType : forall G e2 t,
      G |-e e2 : t
        -> forall G1, G = G1 ++ xt :: nil
          -> G1 |-e subst (length G1) e2 : t.
      induction 1; crush;
        try match goal with
              | [ |- context[if ?E then _ else _] ] => destruct E
            end; crush; eauto 6;
        try match goal with
              | [ H : _ |-v _ : _ |- _ ] =>
                rewrite (subst_eq H)
            end; crush.
    Qed.

    Theorem subst_hasType_closed : forall e2 t,
      xt :: nil |-e e2 : t
      -> nil |-e subst O e2 : t.
      intros; change O with (length (@nil type)); eapply subst_hasType; eauto.
    Qed.
  End subst.

  Hint Resolve subst_hasType_closed.

  Notation "[ x ~> e1 ] e2" := (subst e1 x e2) (no associativity, at level 80).

  Inductive val : exp -> Prop :=
  | VConst : forall b, val (Const b)
  | VAbs : forall e, val (Abs e).

  Hint Constructors val.

  Reserved Notation "e1 ==> e2" (no associativity, at level 90).

  Inductive step : exp -> exp -> Prop :=
  | Beta : forall e1 e2,
    val e2
    -> App (Abs e1) e2 ==> [O ~> e2] e1
  | Cong1 : forall e1 e2 e1',
    e1 ==> e1'
    -> App e1 e2 ==> App e1' e2
  | Cong2 : forall e1 e2 e2',
    val e1
    -> e2 ==> e2'
    -> App e1 e2 ==> App e1 e2'

    where "e1 ==> e2" := (step e1 e2).

  Hint Constructors step.

  Lemma progress' : forall G e t, G |-e e : t
    -> G = nil
    -> val e \/ exists e', e ==> e'.
    induction 1; crush; eauto;
      try match goal with
            | [ H : _ |-e _ : _ --> _ |- _ ] => inversion H
          end;
      repeat match goal with
               | [ H : _ |- _ ] => solve [ inversion H; crush; eauto ]
             end.
  Qed.

  Theorem progress : forall e t, nil |-e e : t
    -> val e \/ exists e', e ==> e'.
    intros; eapply progress'; eauto.
  Qed.

  Lemma preservation' : forall G e t, G |-e e : t
    -> G = nil
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    induction 1; inversion 2; crush; eauto;
      match goal with
        | [ H : _ |-e Abs _ : _ |- _ ] => inversion H
      end; eauto.
  Qed.

  Theorem preservation : forall e t, nil |-e e : t
    -> forall e', e ==> e'
      -> nil |-e e' : t.
    intros; eapply preservation'; eauto.
  Qed.

End DeBruijn.
