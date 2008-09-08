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

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Inductive Types}% *)

(** In a sense, CIC is built from just two relatively straightforward features: function types and inductive types.  From this modest foundation, we can prove effectively all of the theorems of math and carry out effectively all program verifications, with enough effort expended.  This chapter introduces induction and recursion in Coq and shares some "design patterns" for overcoming common pitfalls with them. *)


(** * Enumerations *)

(** Coq inductive types generalize the algebraic datatypes found in Haskell and ML.  Confusingly enough, inductive types also generalize generalized algebraic datatypes (GADTs), by adding the possibility for type dependency.  Even so, it is worth backing up from the examples of the last chapter and going over basic, algebraic datatype uses of inductive datatypes, because the chance to prove things about the values of these types adds new wrinkles beyond usual practice in Haskell and ML.

The singleton type [unit] is an inductive type: *)

Inductive unit : Set :=
  | tt.

(** This vernacular command defines a new inductive type [unit] whose only value is [tt], as we can see by checking the types of the two identifiers: *)

Check unit.
(** [[

  unit : Set
]] *)
Check tt.
(** [[

  tt : unit
]] *)

(** We can prove that [unit] is a genuine singleton type. *)

Theorem unit_singleton : forall x : unit, x = tt.
(** The important thing about an inductive type is, unsurprisingly, that you can do induction over its values, and induction is the key to proving this theorem.  We ask to proceed by induction on the variable [x]. *)
  induction x.
(** The goal changes to: [[

 tt = tt
]] *)
  (** ...which we can discharge trivially. *)
  reflexivity.
Qed.

(** It seems kind of odd to write a proof by induction with no inductive hypotheses.  We could have arrived at the same result by beginning the proof with: [[

  destruct x.
...which corresponds to "proof by case analysis" in classical math.  For non-recursive inductive types, the two tactics will always have identical behavior.  Often case analysis is sufficient, even in proofs about recursive types, and it is nice to avoid introducing unneeded induction hypotheses.

What exactly %\textit{%#<i>#is#</i>#%}% the induction principle for [unit]?  We can ask Coq: *)

Check unit_ind.
(** [[

unit_ind : forall P : unit -> Prop, P tt -> forall u : unit, P u
]]

Every [Inductive] command defining a type [T] also defines an induction principle named [T_ind].  Coq follows the Curry-Howard correspondence and includes the ingredients of programming and proving in the same single syntactic class.  Thus, our type, operations over it, and principles for reasoning about it all live in the same language and are described by the same type system.  The key to telling what is a program and what is a proof lies in the distinction between the type [Prop], which appears in our induction principle; and the type [Set], which we have seen a few times already.

The convention goes like this: [Set] is the type of normal types, and the values of such types are programs.  [Prop] is the type of logical propositions, and the values of such types are proofs.  Thus, an induction principle has a type that shows us that it is a function for building proofs.

Specifically, [unit_ind] quantifies over a predicate [P] over [unit] values.  If we can present a proof that [P] holds of [tt], then we are rewarded with a proof that [P] holds for any value [u] of type [unit].  In our last proof, the predicate was [(fun u : unit => u = tt)].

%\medskip%

We can define an inductive type even simpler than [unit]: *)

Inductive Empty_set : Set := .

(** [Empty_set] has no elements.  We can prove fun theorems about it: *)

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
  destruct 1.
Qed.

(** Because [Empty_set] has no elements, the fact of having an element of this type implies anything.  We use [destruct 1] instead of [destruct x] in the proof because unused quantified variables are relegated to being referred to by number.  (There is a good reason for this, related to the unity of quantifiers and dependent function types.)

We can see the induction principle that made this proof so easy: *)

Check Empty_set_ind.
(** [[

Empty_set_ind : forall (P : Empty_set -> Prop) (e : Empty_set), P e
]]

In other words, any predicate over values from the empty set holds vacuously of every such element.  In the last proof, we chose the predicate [(fun _ : Empty_set => 2 + 2 = 5)].

We can also apply this get-out-of-jail-free card programmatically.  Here is a lazy way of converting values of [Empty_set] to values of [unit]: *)

Definition e2u (e : Empty_set) : unit := match e with end.

(** We employ [match] pattern matching as in the last chapter.  Since we match on a value whose type has no constructors, there is no need to provide any branches.

%\medskip%

Moving up the ladder of complexity, we can define the booleans: *)

Inductive bool : Set :=
| true
| false.

(** We can use less vacuous pattern matching to define boolean negation. *)

Definition not (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

(** An alternative definition desugars to the above: *)

Definition not' (b : bool) : bool :=
  if b then false else true.

(** We might want to prove that [not] is its own inverse operation. *)

Theorem not_inverse : forall b : bool, not (not b) = b.
  destruct b.

  (** After we case analyze on [b], we are left with one subgoal for each constructor of [bool].

[[

2 subgoals
  
  ============================
   not (not true) = true
]]

[[
subgoal 2 is:
 not (not false) = false
]]

The first subgoal follows by Coq's rules of computation, so we can dispatch it easily: *)

  reflexivity.

(** Likewise for the second subgoal, so we can restart the proof and give a very compact justification. *)

Restart.
  destruct b; reflexivity.
Qed.

(** Another theorem about booleans illustrates another useful tactic. *)

Theorem not_ineq : forall b : bool, not b <> b.
  destruct b; discriminate.
Qed.

(** [discriminate] is used to prove that two values of an inductive type are not equal, whenever the values are formed with different constructors.  In this case, the different constructors are [true] and [false].

At this point, it is probably not hard to guess what the underlying induction principle for [bool] is. *)

Check bool_ind.
(** [[

bool_ind : forall P : bool -> Prop, P true -> P false -> forall b : bool, P b
]] *)


(** * Simple Recursive Types *)

(** The natural numbers are the simplest common example of an inductive type that actually deserves the name. *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(** [O] is zero, and [S] is the successor function, so that [0] is syntactic sugar for [O], [1] for [S O], [2] for [S (S O)], and so on.

Pattern matching works as we demonstrated in the last chapter: *)

Definition isZero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** We can prove theorems by case analysis: *)

Theorem S_isZero : forall n : nat, isZero (pred (S (S n))) = false.
  destruct n; reflexivity.
Qed.

(** We can also now get into genuine inductive theorems.  First, we will need a recursive function, to make things interesting. *)

Fixpoint plus (n m : nat) {struct n} : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Recall that [Fixpoint] is Coq's mechanism for recursive function definitions, and that the [{struct n}] annotation is noting which function argument decreases structurally at recursive calls.

Some theorems about [plus] can be proved without induction. *)

Theorem O_plus_n : forall n : nat, plus O n = n.
  intro; reflexivity.
Qed.

(** Coq's computation rules automatically simplify the application of [plus].  If we just reverse the order of the arguments, though, this no longer works, and we need induction. *)

Theorem n_plus_O : forall n : nat, plus n O = n.
  induction n.

(** Our first subgoal is [plus O O = O], which %\textit{%#<i>#is#</i>#%}% trivial by computation. *)

  reflexivity.

(** Our second subgoal is more work and also demonstrates our first inductive hypothesis.

[[

  n : nat
  IHn : plus n O = n
  ============================
   plus (S n) O = S n
]]

We can start out by using computation to simplify the goal as far as we can. *)

  simpl.

(** Now the conclusion is [S (plus n O) = S n].  Using our inductive hypothesis: *)

  rewrite IHn.

(** ...we get a trivial conclusion [S n = S n]. *)

  reflexivity.

(** Not much really went on in this proof, so the [crush] tactic from the [Tactics] module can prove this theorem automatically. *)

Restart.
  induction n; crush.
Qed.

(** We can check out the induction principle at work here: *)

Check nat_ind.
(** [[

nat_ind : forall P : nat -> Prop,
          P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

Each of the two cases of our last proof came from the type of one of the arguments to [nat_ind].  We chose [P] to be [(fun n : nat => plus n O = n)].  The first proof case corresponded to [P O], and the second case to [(forall n : nat, P n -> P (S n))].  The free variable [n] and inductive hypothesis [IHn] came from the argument types given here.

Since [nat] has a constructor that takes an argument, we may sometimes need to know that that constructor is injective. *)

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
  injection 1; trivial.
Qed.

(** [injection] refers to a premise by number, adding new equalities between the corresponding arguments of equated terms that are formed with the same constructor.  We end up needing to prove [n = m -> n = m], so it is unsurprising that a tactic named [trivial] is able to finish the proof.

There is also a very useful tactic called [congruence] that can prove this theorem immediately.  [congruence] generalizes [discriminate] and [injection], and it also adds reasoning about the general properties of equality, such as that a function returns equal results on equal arguments.  That is, [congruence] is a %\textit{%#<i>#complete decision procedure for the theory of equality and uninterpreted functions#</i>#%}%, plus some smarts about inductive types.

%\medskip%

We can define a type of lists of natural numbers. *)

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

(** Recursive definitions are straightforward extensions of what we have seen before. *)

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
    | NNil => O
    | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) {struct ls1} : nat_list :=
  match ls1 with
    | NNil => ls2
    | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

(** Inductive theorem proving can again be automated quite effectively. *)

Theorem nlength_napp : forall ls1 ls2 : nat_list, nlength (napp ls1 ls2)
  = plus (nlength ls1) (nlength ls2).
  induction ls1; crush.
Qed.

Check nat_list_ind.
(** [[

nat_list_ind
     : forall P : nat_list -> Prop,
       P NNil ->
       (forall (n : nat) (n0 : nat_list), P n0 -> P (NCons n n0)) ->
       forall n : nat_list, P n
]]

%\medskip%

In general, we can implement any "tree" types as inductive types.  For example, here are binary trees of naturals. *)

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
    | NLeaf => O
    | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) {struct tr1} : nat_btree :=
  match tr1 with
    | NLeaf => tr2
    | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
  induction n1; crush.
Qed.

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2)
  = plus (nsize tr2) (nsize tr1).
  Hint Rewrite n_plus_O plus_assoc : cpdt.

  induction tr1; crush.
Qed.

Check nat_btree_ind.
(** [[

nat_btree_ind
     : forall P : nat_btree -> Prop,
       P NLeaf ->
       (forall n : nat_btree,
        P n -> forall (n0 : nat) (n1 : nat_btree), P n1 -> P (NNode n n0 n1)) ->
       forall n : nat_btree, P n
]] *)
