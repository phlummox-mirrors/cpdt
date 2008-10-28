(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import List.

Require Import Tactics MoreSpecif.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Proof by Reflection}% *)

(** The last chapter highlighted a very heuristic approach to proving.  In this chapter, we will study an alternative technique, %\textit{%#<i>#proof by reflection#</i>#%}%.  We will write, in Gallina, decision procedures with proofs of correctness, and we will appeal to these procedures in writing very short proofs.  Such a proof is checked by running the decision procedure.  The term %\textit{%#<i>#reflection#</i>#%}% applies because we will need to translate Gallina propositions into values of inductive types representing syntax, so that Gallina programs may analyze them. *)


(** * Proving Evenness *)

(** Proving that particular natural number constants are even is certainly something we would rather have happen automatically.  The Ltac-programming techniques that we learned in the last chapter make it easy to implement such a procedure. *)

Inductive isEven : nat -> Prop :=
| Even_O : isEven O
| Even_SS : forall n, isEven n -> isEven (S (S n)).

Ltac prove_even := repeat constructor.

Theorem even_256 : isEven 256.
  prove_even.
Qed.

Print even_256.
(** [[

even_256 = 
Even_SS
  (Even_SS
     (Even_SS
        (Even_SS
    ]]

    ...and so on.  This procedure always works (at least on machines with infinite resources), but it has a serious drawback, which we see when we print the proof it generates that 256 is even.  The final proof term has length linear in the input value.  This seems like a shame, since we could write a trivial and trustworthy program to verify evenness of constants.  The proof checker could simply call our program where needed.

    It is also unfortunate not to have static typing guarantees that our tactic always behaves appropriately.  Other invocations of similar tactics might fail with dynamic type errors, and we would not know about the bugs behind these errors until we happened to attempt to prove complex enough goals.

    The techniques of proof by reflection address both complaints.  We will be able to write proofs like this with constant size overhead beyond the size of the input, and we will do it with verified decision procedures written in Gallina.

    For this example, we begin by using a type from the [MoreSpecif] module to write a certified evenness checker. *)

Print partial.
(** [[

Inductive partial (P : Prop) : Set :=  Proved : P -> [P] | Uncertain : [P]
    ]] *)

(** A [partial P] value is an optional proof of [P]. The notation [[P]] stands for [partial P]. *)

Open Local Scope partial_scope.

(** We bring into scope some notations for the [partial] type.  These overlap with some of the notations we have seen previously for specification types, so they were placed in a separate scope that needs separate opening. *)

Definition check_even (n : nat) : [isEven n].
  Hint Constructors isEven.

  refine (fix F (n : nat) : [isEven n] :=
    match n return [isEven n] with
      | 0 => Yes
      | 1 => No
      | S (S n') => Reduce (F n')
    end); auto.
Defined.

(** We can use dependent pattern-matching to write a function that performs a surprising feat.  When given a [partial P], this function [partialOut] returns a proof of [P] if the [partial] value contains a proof, and it returns a (useless) proof of [True] otherwise.  From the standpoint of ML and Haskell programming, it seems impossible to write such a type, but it is trivial with a [return] annotation. *)

Definition partialOut (P : Prop) (x : [P]) :=
  match x return (match x with
                    | Proved _ => P
                    | Uncertain => True
                  end) with
    | Proved pf => pf
    | Uncertain => I
  end.

(** It may seem strange to define a function like this.  However, it turns out to be very useful in writing a reflective verison of our earlier [prove_even] tactic: *)

Ltac prove_even_reflective :=
  match goal with
    | [ |- isEven ?N] => exact (partialOut (check_even N))
  end.

(** We identify which natural number we are considering, and we "prove" its evenness by pulling the proof out of the appropriate [check_even] call. *)

Theorem even_256' : isEven 256.
  prove_even_reflective.
Qed.

Print even_256'.
(** [[

even_256' = partialOut (check_even 256)
     : isEven 256
    ]]

    We can see a constant wrapper around the object of the proof.  For any even number, this form of proof will suffice.  What happens if we try the tactic with an odd number? *)

Theorem even_255 : isEven 255.
  (** [[

  prove_even_reflective.

  [[

User error: No matching clauses for match goal
  ]]

  Thankfully, the tactic fails.  To see more precisely what goes wrong, we can run manually the body of the [match].

  [[

  exact (partialOut (check_even 255)).

  [[

  Error: The term "partialOut (check_even 255)" has type
 "match check_even 255 with
  | Yes => isEven 255
  | No => True
  end" while it is expected to have type "isEven 255"
  ]]

  As usual, the type-checker performs no reductions to simplify error messages.  If we reduced the first term ourselves, we would see that [check_even 255] reduces to a [No], so that the first term is equivalent to [True], which certainly does not unify with [isEven 255]. *)
Abort.


(** * Reflecting the Syntax of a Trivial Tautology Language *)

(** We might also like to have reflective proofs of trivial tautologies like this one: *)

Theorem true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
  tauto.
Qed.

Print true_galore.

(** [[

true_galore = 
fun H : True /\ True =>
and_ind (fun _ _ : True => or_introl (True /\ (True -> True)) I) H
     : True /\ True -> True \/ True /\ (True -> True)
    ]]

    As we might expect, the proof that [tauto] builds contains explicit applications of natural deduction rules.  For large formulas, this can add a linear amount of proof size overhead, beyond the size of the input.

   To write a reflective procedure for this class of goals, we will need to get into the actual "reflection" part of "proof by reflection."  It is impossible to case-analyze a [Prop] in any way in Gallina.  We must %\textit{%#<i>#reflect#</i>#%}% [Prop] into some type that we %\textit{%#<i>#can#</i>#%}% analyze.  This inductive type is a good candidate: *)

Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut -> taut -> taut
| TautOr : taut -> taut -> taut
| TautImp : taut -> taut -> taut.

(** We write a recursive function to "unreflect" this syntax back to [Prop]. *)

Fixpoint tautDenote (t : taut) : Prop :=
  match t with
    | TautTrue => True
    | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
    | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
    | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.

(** It is easy to prove that every formula in the range of [tautDenote] is true. *)

Theorem tautTrue : forall t, tautDenote t.
  induction t; crush.
Qed.

(** To use [tautTrue] to prove particular formulas, we need to implement the syntax reflection process.  A recursive Ltac function does the job. *)

Ltac tautReflect P :=
  match P with
    | True => TautTrue
    | ?P1 /\ ?P2 =>
      let t1 := tautReflect P1 in
      let t2 := tautReflect P2 in
        constr:(TautAnd t1 t2)
    | ?P1 \/ ?P2 =>
      let t1 := tautReflect P1 in
      let t2 := tautReflect P2 in
        constr:(TautOr t1 t2)
    | ?P1 -> ?P2 =>
      let t1 := tautReflect P1 in
      let t2 := tautReflect P2 in
        constr:(TautImp t1 t2)
  end.

(** With [tautReflect] available, it is easy to finish our reflective tactic.  We look at the goal formula, reflect it, and apply [tautTrue] to the reflected formula. *)

Ltac obvious :=
  match goal with
    | [ |- ?P ] =>
      let t := tautReflect P in
        exact (tautTrue t)
  end.

(** We can verify that [obvious] solves our original example, with a proof term that does not mention details of the proof. *)

Theorem true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
  obvious.
Qed.

Print true_galore'.

(** [[

true_galore' = 
tautTrue
  (TautImp (TautAnd TautTrue TautTrue)
     (TautOr TautTrue (TautAnd TautTrue (TautImp TautTrue TautTrue))))
     : True /\ True -> True \/ True /\ (True -> True)

    ]]

    It is worth considering how the reflective tactic improves on a pure-Ltac implementation.  The formula reflection process is just as ad-hoc as before, so we gain little there.  In general, proofs will be more complicated than formula translation, and the "generic proof rule" that we apply here %\textit{%#<i>#is#</i>#%}% on much better formal footing than a recursive Ltac function.  The dependent type of the proof guarantees that it "works" on any input formula.  This is all in addition to the proof-size improvement that we have already seen. *)


(** * A Monoid Expression Simplifier *)

(** Proof by reflection does not require encoding of all of the syntax in a goal.  We can insert "variables" in our syntax types to allow injection of arbitrary pieces, even if we cannot apply specialized reasoning to them.  In this section, we explore that possibility by writing a tactic for normalizing monoid equations. *)

Section monoid.
  Variable A : Set.
  Variable e : A.
  Variable f : A -> A -> A.

  Infix "+" := f.

  Hypothesis assoc : forall a b c, (a + b) + c = a + (b + c).
  Hypothesis identl : forall a, e + a = a.
  Hypothesis identr : forall a, a + e = a.

  (** We add variables and hypotheses characterizing an arbitrary instance of the algebraic structure of monoids.  We have an associative binary operator and an identity element for it.

     It is easy to define an expression tree type for monoid expressions.  A [Var] constructor is a "catch-all" case for subexpressions that we cannot model.  These subexpressions could be actual Gallina variables, or they could just use functions that our tactic is unable to understand. *)

  Inductive mexp : Set :=
  | Ident : mexp
  | Var : A -> mexp
  | Op : mexp -> mexp -> mexp.

  (** Next, we write an "un-reflect" function. *)

  Fixpoint mdenote (me : mexp) : A :=
    match me with
      | Ident => e
      | Var v => v
      | Op me1 me2 => mdenote me1 + mdenote me2
    end.

  (** We will normalize expressions by flattening them into lists, via associativity, so it is helpful to have a denotation function for lists of monoid values. *)

  Fixpoint mldenote (ls : list A) : A :=
    match ls with
      | nil => e
      | x :: ls' => x + mldenote ls'
    end.

  (** The flattening function itself is easy to implement. *)

  Fixpoint flatten (me : mexp) : list A :=
    match me with
      | Ident => nil
      | Var x => x :: nil
      | Op me1 me2 => flatten me1 ++ flatten me2
    end.

  (** [flatten] has a straightforward correctness proof in terms of our [denote] functions. *)

  Lemma flatten_correct' : forall ml2 ml1,
    mldenote ml1 + mldenote ml2 = mldenote (ml1 ++ ml2).
    induction ml1; crush.
  Qed.

  Theorem flatten_correct : forall me, mdenote me = mldenote (flatten me).
    Hint Resolve flatten_correct'.

    induction me; crush.
  Qed.

  (** Now it is easy to prove a theorem that will be the main tool behind our simplification tactic. *)

  Theorem monoid_reflect : forall me1 me2,
    mldenote (flatten me1) = mldenote (flatten me2)
    -> mdenote me1 = mdenote me2.
    intros; repeat rewrite flatten_correct; assumption.
  Qed.

  (** We implement reflection into the [mexp] type. *)

  Ltac reflect me :=
    match me with
      | e => Ident
      | ?me1 + ?me2 =>
        let r1 := reflect me1 in
        let r2 := reflect me2 in
          constr:(Op r1 r2)
      | _ => constr:(Var me)
    end.

  (** The final [monoid] tactic works on goals that equate two monoid terms.  We reflect each and change the goal to refer to the reflected versions, finishing off by applying [monoid_reflect] and simplifying uses of [mldenote]. *)

  Ltac monoid :=
    match goal with
      | [ |- ?me1 = ?me2 ] =>
        let r1 := reflect me1 in
        let r2 := reflect me2 in
          change (mdenote r1 = mdenote r2);
            apply monoid_reflect; simpl mldenote
    end.

  (** We can make short work of theorems like this one: *)

  Theorem t1 : forall a b c d, a + b + c + d = a + (b + c) + d.
    intros; monoid.
    (** [[

  ============================
   a + (b + (c + (d + e))) = a + (b + (c + (d + e)))
        ]]

        [monoid] has canonicalized both sides of the equality, such that we can finish the proof by reflexivity. *)

    reflexivity.
  Qed.

  (** It is interesting to look at the form of the proof. *)

  Print t1.
  (** [[

t1 = 
fun a b c d : A =>
monoid_reflect (Op (Op (Op (Var a) (Var b)) (Var c)) (Var d))
  (Op (Op (Var a) (Op (Var b) (Var c))) (Var d))
  (refl_equal (a + (b + (c + (d + e)))))
     : forall a b c d : A, a + b + c + d = a + (b + c) + d
      ]]

      The proof term contains only restatements of the equality operands in reflected form, followed by a use of reflexivity on the shared canonical form. *)
End monoid.

(** Extensions of this basic approach are used in the implementations of the [ring] and [field] tactics that come packaged with Coq. *)


(** * A Smarter Tautology Solver *)

Require Import Quote.

Inductive formula : Set :=
| Atomic : index -> formula
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula.

Definition asgn := varmap Prop.

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).

Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
  match f with
    | Atomic v => varmap_find False v atomics
    | Truth => True
    | Falsehood => False
    | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
    | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
    | Imp f1 f2 => formulaDenote atomics f1 --> formulaDenote atomics f2
  end.

Section my_tauto.
  Variable atomics : asgn.

  Definition holds (v : index) := varmap_find False v atomics.

  Require Import ListSet.

  Definition index_eq : forall x y : index, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition add (s : set index) (v : index) := set_add index_eq v s.
  Definition In_dec : forall v (s : set index), {In v s} + {~In v s}.
    Open Local Scope specif_scope.

    intro; refine (fix F (s : set index) : {In v s} + {~In v s} :=
      match s return {In v s} + {~In v s} with
        | nil => No
        | v' :: s' => index_eq v' v || F s'
      end); crush.
  Defined.

  Fixpoint allTrue (s : set index) : Prop :=
    match s with
      | nil => True
      | v :: s' => holds v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s,
    allTrue s
    -> holds v
    -> allTrue (add s v).
    induction s; crush;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; crush.
  Qed.

  Theorem allTrue_In : forall v s,
    allTrue s
    -> set_In v s
    -> varmap_find False v atomics.
    induction s; crush.
  Qed.

  Hint Resolve allTrue_add allTrue_In.

  Open Local Scope partial_scope.

  Definition forward (f : formula) (known : set index) (hyp : formula)
    (cont : forall known', [allTrue known' -> formulaDenote atomics f])
    : [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f].
    refine (fix F (f : formula) (known : set index) (hyp : formula)
      (cont : forall known', [allTrue known' -> formulaDenote atomics f]){struct hyp}
      : [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f] :=
      match hyp return [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f] with
        | Atomic v => Reduce (cont (add known v))
        | Truth => Reduce (cont known)
        | Falsehood => Yes
        | And h1 h2 =>
          Reduce (F (Imp h2 f) known h1 (fun known' =>
            Reduce (F f known' h2 cont)))
        | Or h1 h2 => F f known h1 cont && F f known h2 cont
        | Imp _ _ => Reduce (cont known)
      end); crush.
  Defined.

  Definition backward (known : set index) (f : formula) : [allTrue known -> formulaDenote atomics f].
    refine (fix F (known : set index) (f : formula) : [allTrue known -> formulaDenote atomics f] :=
      match f return [allTrue known -> formulaDenote atomics f] with
        | Atomic v => Reduce (In_dec v known)
        | Truth => Yes
        | Falsehood => No
        | And f1 f2 => F known f1 && F known f2
        | Or f1 f2 => F known f1 || F known f2
        | Imp f1 f2 => forward f2 known f1 (fun known' => F known' f2)
      end); crush; eauto.
  Defined.

  Definition my_tauto (f : formula) : [formulaDenote atomics f].
    intro; refine (Reduce (backward nil f)); crush.
  Defined.
End my_tauto.

Ltac my_tauto :=
  repeat match goal with
           | [ |- forall x : ?P, _ ] =>
             match type of P with
               | Prop => fail 1
               | _ => intro
             end
         end;
  quote formulaDenote;
  match goal with
    | [ |- formulaDenote ?m ?f ] => exact (partialOut (my_tauto m f))
  end.

Theorem mt1 : True.
  my_tauto.
Qed.

Print mt1.

Theorem mt2 : forall x y : nat, x = y --> x = y.
  my_tauto.
Qed.

Print mt2.

Theorem mt3 : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  --> y > z /\ (x < y \/ x < S y).
  my_tauto.
Qed.

Print mt3.

Theorem mt4 : True /\ True /\ True /\ True /\ True /\ True /\ False --> False.
  my_tauto.
Qed.

Print mt4.

Theorem mt4' : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
  tauto.
Qed.

Print mt4'.
