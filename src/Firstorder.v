(* Copyright (c) 2008-2009, Adam Chlipala
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

(** Many people interested in interactive theorem-proving want to prove theorems about programming languages.  That domain also provides a good setting for demonstrating how to apply the ideas from the earlier parts of this book.  This part introduces some techniques for encoding the syntax and semantics of programming languages, along with some example proofs designed to be as practical as possible, rather than to illustrate basic Coq technique.

   To prove anything about a language, we must first formalize the language's syntax.  We have a broad design space to choose from, and it makes sense to start with the simplest options, so-called %\textit{%#<i>#first-order#</i>#%}% syntax encodings that do not use dependent types.  These encodings are first-order because they do not use Coq function types in a critical way.  In this chapter, we consider the most popular first-order encodings, using each to prove a basic type soundness theorem. *)


(** * Concrete Binding *)

(** The most obvious encoding of the syntax of programming languages follows usual context-free grammars literally.  We represent variables as strings and include a variable in our AST definition wherever a variable appears in the informal grammar.  Concrete binding turns out to involve a surprisingly large amount of menial bookkeeping, especially when we encode higher-order languages with nested binder scopes.  This section's example should give a flavor of what is required. *)

Module Concrete.

  (** We need our variable type and its decidable equality operation. *)

  Definition var := string.
  Definition var_eq := string_dec.

  (** We will formalize basic simply-typed lambda calculus.  The syntax of expressions and types follows what we would write in a context-free grammar. *)

  Inductive exp : Set :=
  | Const : bool -> exp
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : var -> exp -> exp.

  Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

  (** It is useful to define a syntax extension that lets us write function types in more standard notation. *)

  Infix "-->" := Arrow (right associativity, at level 60).

  (** Now we turn to a typing judgment.  We will need to define it in terms of typing contexts, which we represent as lists of pairs of variables and types. *)

  Definition ctx := list (var * type).

  (** The definitions of our judgments will be prettier if we write them using mixfix syntax.  To define a judgment for looking up the type of a variable in a context, we first %\textit{%#</i>#reserve#</i>#%}% a notation for the judgment.  Reserved notations enable mutually-recursive definition of a judgment and its notation; in this sense, the reservation is like a forward declaration in C. *)

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  (** Now we define the judgment itself, using a [where] clause to associate a notation definition. *)

  Inductive lookup : ctx -> var -> type -> Prop :=
  | First : forall x t G,
    (x, t) :: G |-v x : t
  | Next : forall x t x' t' G,
    x <> x'
    -> G |-v x : t
    -> (x', t') :: G |-v x : t

    where "G |-v x : t" := (lookup G x t).

  Hint Constructors lookup.

  (** The same technique applies to defining the main typing judgment.  We use an [at next level] clause to cause the argument [e] of the notation to be parsed at a low enough precedence level. *)

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

  (** It is useful to know that variable lookup results are unchanged by adding extra bindings to the end of a context. *)

  Lemma weaken_lookup : forall x t G' G1,
    G1 |-v x : t
    -> G1 ++ G' |-v x : t.
    induction G1 as [ | [? ?] ? ]; crush;
      match goal with
        | [ H : _ |-v _ : _ |- _ ] => inversion H; crush
      end.
  Qed.

  Hint Resolve weaken_lookup.

  (** The same property extends to the full typing judgment. *)

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

  (** Much of the inconvenience of first-order encodings comes from the need to treat capture-avoiding substitution explicitly.  We must start by defining a substitution function. *)

  Section subst.
    Variable x : var.
    Variable e1 : exp.

    (** We are substituting expression [e1] for every free occurrence of [x].  Note that this definition is specialized to the case where [e1] is closed; substitution is substantially more complicated otherwise, potentially involving explicit alpha-variation.  Luckily, our example of type safety for a call-by-value semantics only requires this restricted variety of substitution. *)

    Fixpoint subst (e2 : exp) : exp :=
      match e2 with
        | Const _ => e2
        | Var x' => if var_eq x' x then e1 else e2
        | App e1 e2 => App (subst e1) (subst e2)
        | Abs x' e' => Abs x' (if var_eq x' x then e' else subst e')
      end.

    (** We can prove a few theorems about substitution in well-typed terms, where we assume that [e1] is closed and has type [xt]. *)

    Variable xt : type.
    Hypothesis Ht' : nil |-e e1 : xt.

    (** It is helpful to establish a notation asserting the freshness of a particular variable in a context. *)

    Notation "x # G" := (forall t' : type, In (x, t') G -> False) (no associativity, at level 90).

    (** To prove type preservation, we will need lemmas proving consequences of variable lookup proofs. *)

    Lemma subst_lookup' : forall x' t,
      x <> x'
      -> forall G1, G1 ++ (x, xt) :: nil |-v x' : t
        -> G1 |-v x' : t.
      induction G1 as [ | [? ?] ? ]; crush;
        match goal with
          | [ H : _ |-v _ : _ |- _ ] => inversion H
        end; crush.
    Qed.

    Hint Resolve subst_lookup'.

    Lemma subst_lookup : forall x' t G1,
      x' # G1
      -> G1 ++ (x, xt) :: nil |-v x' : t
      -> t = xt.
      induction G1 as [ | [? ?] ? ]; crush; eauto;
        match goal with
          | [ H : _ |-v _ : _ |- _ ] => inversion H
        end; crush; (elimtype False; eauto;
          match goal with
            | [ H : nil |-v _ : _ |- _ ] => inversion H
          end)
        || match goal with
             | [ H : _ |- _ ] => apply H; crush; eauto
           end.
    Qed.

    Implicit Arguments subst_lookup [x' t G1].

    (** Another set of lemmas allows us to remove provably unused variables from the ends of typing contexts. *)

    Lemma shadow_lookup : forall v t t' G1,
      G1 |-v x : t'
      -> G1 ++ (x, xt) :: nil |-v v : t
      -> G1 |-v v : t.
      induction G1 as [ | [? ?] ? ]; crush;
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
          | [ H : (?x0, _) :: _ ++ (?x, _) :: _ |-e _ : _ |- _ ] =>
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

    (** Disjointness facts may be extended to larger contexts when the appropriate obligations are met. *)

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

    (** Finally, we arrive at the main theorem about substitution: it preserves typing. *)

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

    (** We wrap the last theorem into an easier-to-apply form specialized to closed expressions. *)

    Theorem subst_hasType_closed : forall e2 t,
      (x, xt) :: nil |-e e2 : t
      -> nil |-e subst e2 : t.
      intros; eapply subst_hasType; eauto.
    Qed.
  End subst.

  Hint Resolve subst_hasType_closed.

  (** A notation for substitution will make the operational semantics easier to read. *)

  Notation "[ x ~> e1 ] e2" := (subst x e1 e2) (no associativity, at level 80).

  (** To define a call-by-value small-step semantics, we rely on a standard judgment characterizing which expressions are values. *)

  Inductive val : exp -> Prop :=
  | VConst : forall b, val (Const b)
  | VAbs : forall x e, val (Abs x e).

  Hint Constructors val.

  (** Now the step relation is easy to define. *)

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

  (** The progress theorem says that any well-typed expression can take a step.  To deal with limitations of the [induction] tactic, we put most of the proof in a lemma whose statement uses the usual trick of introducing extra equality hypotheses. *)

  Lemma progress' : forall G e t, G |-e e : t
    -> G = nil
    -> val e \/ exists e', e ==> e'.
    induction 1; crush; eauto;
      try match goal with
            | [ H : _ |-e _ : _ --> _ |- _ ] => inversion H
          end;
      match goal with
        | [ H : _ |- _ ] => solve [ inversion H; crush; eauto ]
      end.
  Qed.

  Theorem progress : forall e t, nil |-e e : t
    -> val e \/ exists e', e ==> e'.
    intros; eapply progress'; eauto.
  Qed.

  (** A similar pattern works for the preservation theorem, which says that any step of execution preserves an expression's type. *)

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

(** This was a relatively simple example, giving only a taste of the proof burden associated with concrete syntax.  We were helped by the fact that, with call-by-value semantics, we only need to reason about substitution in closed expressions.  There was also no need to alpha-vary an expression. *)


(** * De Bruijn Indices *)

(** De Bruijn indices are much more popular than concrete syntax.  This technique provides a %\textit{%#<i>#canonical#</i>#%}% representation of syntax, where any two alpha-equivalent expressions have syntactically equal encodings, removing the need for explicit reasoning about alpha conversion.  Variables are represented as natural numbers, where variable [n] denotes a reference to the [n]th closest enclosing binder.  Because variable references in effect point to binders, there is no need to label binders, such as function abstraction, with variables. *)

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

  (** The definition of typing proceeds much the same as in the last section.  Since variables are numbers, contexts can be simple lists of types.  This makes it possible to write the lookup judgment without mentioning inequality of variables. *)

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

  (** In the [hasType] case for function abstraction, there is no need to choose a variable name.  We simply push the function domain type onto the context [G]. *)

  Hint Constructors hasType.

  (** We prove roughly the same weakening theorems as before. *)

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

    (** Substitution is easier to define than with concrete syntax.  While our old definition needed to use two comparisons for equality of variables, the de Bruijn substitution only needs one comparison. *)

    Fixpoint subst (x : var) (e2 : exp) : exp :=
      match e2 with
        | Const _ => e2
        | Var x' => if var_eq x' x then e1 else e2
        | App e1 e2 => App (subst x e1) (subst x e2)
        | Abs e' => Abs (subst (S x) e')
      end.

    Variable xt : type.

    (** We prove similar theorems about inversion of variable lookup. *)

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

    (** The next lemma is included solely to guide [eauto], which will not apply computational equivalences automatically. *)

    Lemma hasType_push : forall dom G1 e' ran,
      dom :: G1 |-e subst (length (dom :: G1)) e' : ran
      -> dom :: G1 |-e subst (S (length G1)) e' : ran.
      trivial.
    Qed.

    Hint Resolve hasType_push.

    (** Finally, we are ready for the main theorem about substitution and typing. *)

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

  (** We define the operational semantics much as before. *)

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

  (** Since we have added the right hints, the progress and preservation theorem statements and proofs are exactly the same as in the concrete encoding example. *)

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


(** * Locally Nameless Syntax *)

Module LocallyNameless.

  Definition free_var := string.
  Definition bound_var := nat.

  Inductive exp : Set :=
  | Const : bool -> exp
  | FreeVar : free_var -> exp
  | BoundVar : bound_var -> exp
  | App : exp -> exp -> exp
  | Abs : exp -> exp.

  Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

  Definition ctx := list (free_var * type).

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

  Inductive lookup : ctx -> free_var -> type -> Prop :=
  | First : forall x t G,
    (x, t) :: G |-v x : t
  | Next : forall x t x' t' G,
    x <> x'
    -> G |-v x : t
    -> (x', t') :: G |-v x : t

    where "G |-v x : t" := (lookup G x t).

  Hint Constructors lookup.

  Reserved Notation "G |-e e : t" (no associativity, at level 90, e at next level).

  Section open.
    Variable x : free_var.

    Fixpoint open (n : bound_var) (e : exp) : exp :=
      match e with
        | Const _ => e
        | FreeVar _ => e
        | BoundVar n' =>
          if eq_nat_dec n' n
            then FreeVar x
            else if le_lt_dec n' n
              then e
              else BoundVar (pred n')
        | App e1 e2 => App (open n e1) (open n e2)
        | Abs e1 => Abs (open (S n) e1)
      end.
  End open.

  Inductive notFreeIn (x : free_var) : exp -> Prop :=
  | NfConst : forall c, notFreeIn x (Const c)
  | NfFreeVar : forall y, y <> x -> notFreeIn x (FreeVar y)
  | NfBoundVar : forall y, notFreeIn x (BoundVar y)
  | NfApp : forall e1 e2, notFreeIn x e1 -> notFreeIn x e2 -> notFreeIn x (App e1 e2)
  | NfAbs : forall e1, (forall y, y <> x -> notFreeIn x (open y O e1)) -> notFreeIn x (Abs e1).

  Hint Constructors notFreeIn.

  Inductive hasType : ctx -> exp -> type -> Prop :=
  | TConst : forall G b,
    G |-e Const b : Bool
  | TFreeVar : forall G v t,
    G |-v v : t
    -> G |-e FreeVar v : t
  | TApp : forall G e1 e2 dom ran,
    G |-e e1 : dom --> ran
    -> G |-e e2 : dom
    -> G |-e App e1 e2 : ran
  | TAbs : forall G e' dom ran,
    (forall x, notFreeIn x e' -> (x, dom) :: G |-e open x O e' : ran)
    -> G |-e Abs e' : dom --> ran

    where "G |-e e : t" := (hasType G e t).

  Hint Constructors hasType.

  (** We prove roughly the same weakening theorems as before. *)

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
    Variable x : free_var.
    Variable e1 : exp.

    Fixpoint subst (e2 : exp) : exp :=
      match e2 with
        | Const _ => e2
        | FreeVar x' => if string_dec x' x then e1 else e2
        | BoundVar _ => e2
        | App e1 e2 => App (subst e1) (subst e2)
        | Abs e' => Abs (subst e')
      end.
  End subst.


  Notation "[ x ~> e1 ] e2" := (subst x e1 e2) (no associativity, at level 80).

  Inductive val : exp -> Prop :=
  | VConst : forall b, val (Const b)
  | VAbs : forall e, val (Abs e).

  Hint Constructors val.

  Reserved Notation "e1 ==> e2" (no associativity, at level 90).

  Inductive step : exp -> exp -> Prop :=
  | Beta : forall x e1 e2,
    val e2
    -> notFreeIn x e1
    -> App (Abs e1) e2 ==> [x ~> e2] (open x O e1)
  | Cong1 : forall e1 e2 e1',
    e1 ==> e1'
    -> App e1 e2 ==> App e1' e2
  | Cong2 : forall e1 e2 e2',
    val e1
    -> e2 ==> e2'
    -> App e1 e2 ==> App e1 e2'

    where "e1 ==> e2" := (step e1 e2).

  Hint Constructors step.

  Open Scope string_scope.

  Fixpoint vlen (e : exp) : nat :=
    match e with
      | Const _ => 0
      | FreeVar x => String.length x
      | BoundVar _ => 0
      | App e1 e2 => vlen e1 + vlen e2
      | Abs e1 => vlen e1
    end.

  Opaque le_lt_dec.

  Hint Extern 1 (@eq exp _ _) => f_equal.

  Lemma open_comm : forall x1 x2 e n1 n2,
    open x1 n1 (open x2 (S n2 + n1) e)
    = open x2 (n2 + n1) (open x1 n1 e).
    induction e; crush;
      repeat (match goal with
                | [ |- context[if ?E then _ else _] ] => destruct E
              end; crush).

    replace (S (n2 + n1)) with (n2 + S n1); auto.
  Qed.

  Hint Rewrite plus_0_r : cpdt.

  Lemma open_comm0 : forall x1 x2 e n,
    open x1 0 (open x2 (S n) e)
    = open x2 n (open x1 0 e).
    intros; generalize (open_comm x1 x2 e 0 n); crush.
  Qed.    

  Hint Extern 1 (notFreeIn _ (open _ 0 (open _ (S _) _))) => rewrite open_comm0.

  Lemma notFreeIn_open : forall x y,
    x <> y
    -> forall e,
      notFreeIn x e
      -> forall n, notFreeIn x (open y n e).
    induction 2; crush;
      repeat (match goal with
                | [ |- context[if ?E then _ else _] ] => destruct E
              end; crush).
  Qed.    

  Hint Resolve notFreeIn_open.

  Lemma infVar : forall x y, String.length x > String.length y
    -> y <> x.
    intros; destruct (string_dec x y); intros; subst; crush.
  Qed.

  Hint Resolve infVar.

  Lemma inf' : forall x e, String.length x > vlen e -> notFreeIn x e.
    induction e; crush; eauto.
  Qed.

  Fixpoint primes (n : nat) : string :=
    match n with
      | O => "x"
      | S n' => primes n' ++ "'"
    end.

  Lemma length_app : forall s2 s1, String.length (s1 ++ s2) = String.length s1 + String.length s2.
    induction s1; crush.
  Qed.

  Hint Rewrite length_app : cpdt.

  Lemma length_primes : forall n, String.length (primes n) = S n.
    induction n; crush.
  Qed.

  Hint Rewrite length_primes : cpdt.

  Lemma inf : forall e, exists x, notFreeIn x e.
    intro; exists (primes (vlen e)); apply inf'; crush.
  Qed.

  Lemma progress_Abs : forall e1 e2,
    val e2
    -> exists e', App (Abs e1) e2 ==> e'.
    intros; destruct (inf e1); eauto.
  Qed.

  Hint Resolve progress_Abs.

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

  (*Lemma preservation' : forall G e t, G |-e e : t
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
  Qed.*)

End LocallyNameless.
