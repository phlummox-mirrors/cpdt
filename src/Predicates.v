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


(** %\chapter{Inductive Predicates}% *)

(** The so-called "Curry-Howard Correspondence" states a formal connection between functional programs and mathematical proofs.  In the last chapter, we snuck in a first introduction to this subject in Coq.  Witness the close similarity between the types [unit] and [True] from the standard library: *)

Print unit.
(** [[

Inductive unit : Set :=  tt : unit
]] *)

Print True.
(** [[

Inductive True : Prop :=  I : True
]] *)

(** Recall that [unit] is the type with only one value, and [True] is the proposition that always holds.  Despite this superficial difference between the two concepts, in both cases we can use the same inductive definition mechanism.  The connection goes further than this.  We see that we arrive at the definition of [True] by replacing [unit] by [True], [tt] by [I], and [Set] by [Prop].  The first two of these differences are superficial changes of names, while the third difference is the crucial one for separating programs from proofs.  A term [T] of type [Set] is a type of programs, and a term of type [T] is a program.  A term [T] of type [Prop] is a logical proposition, and its proofs are of type [T].

[unit] has one value, [tt].  [True] has one proof, [I].  Why distinguish between these two types?  Many people who have read about Curry-Howard in an abstract context and not put it to use in proof engineering answer that the two types in fact %\textit{%#<i>#should not#</i>#%}% be distinguished.  There is a certain aesthetic appeal to this point of view, but I want to argue that it is best to treat Curry-Howard very loosely in practical proving.  There are Coq-specific reasons for preferring the distinction, involving efficient compilation and avoidance of paradoxes in the presence of classical math, but I will argue that there is a more general principle that should lead us to avoid conflating programming and proving.

The essence of the argument is roughly this: to an engineer, not all functions of type [A -> B] are created equal, but all proofs of a proposition [P -> Q] are.  This idea is known as %\textit{%#<i>#proof irrelevance#</i>#%}%, and its formalizations in logics prevent us from distinguishing between alternate proofs of the same proposition.  Proof irrelevance is compatible with, but not derivable in, Gallina.  Apart from this theoretical concern, I will argue that it is most effective to do engineering with Coq by employing different techniques for programs versus proofs.  Most of this book is organized around that distinction, describing how to program, by applying standard functional programming techniques in the presence of dependent types; and how to prove, by writing custom Ltac decision procedures.

With that perspective in mind, this chapter is sort of a mirror image of the last chapter, introducing how to define predicates with inductive definitions.  We will point out similarities in places, but much of the effective Coq user's bag of tricks is disjoint for predicates versus "datatypes."  This chapter is also a covert introduction to dependent types, which are the foundation on which interesting inductive predicates are built, though we will rely on tactics to build dependently-typed proof terms for us for now.  A future chapter introduces more manual application of dependent types. *)


(** * Propositional Logic *)

(** Let us begin with a brief tour through the definitions of the connectives for propositional logic.  We will work within a Coq section that provides us with a set of propositional variables.  In Coq parlance, these are just terms of type [Prop.] *)

Section Propositional.
  Variables P Q R : Prop.

  (** In Coq, the most basic propositional connective is implication, written [->], which we have already used in almost every proof.  Rather than being defined inductively, implication is built into Coq as the function type constructor.

We have also already seen the definition of [True].  For a demonstration of a lower-level way of establishing proofs of inductive predicates, we turn to this trivial theorem. *)
  
  Theorem obvious : True.
    apply I.
  Qed.

  (** We may always use the [apply] tactic to take a proof step based on applying a particular constructor of the inductive predicate that we are trying to establish.  Sometimes there is only one constructor that could possibly apply, in which case a shortcut is available: *)

  Theorem obvious' : True.
    constructor.
  Qed.

  (** There is also a predicate [False], which is the Curry-Howard mirror image of [Empty_set] from the last chapter. *)

  Print False.
  (** [[

Inductive False : Prop :=
]] *)

  (** We can conclude anything from [False], doing case analysis on a proof of [False] in the same way we might do case analysis on, say, a natural number.  Since there are no cases to consider, any such case analysis succeeds immediately in proving the goal. *)

  Theorem False_imp : False -> 2 + 2 = 5.
    destruct 1.
  Qed.

  (** In a consistent context, we can never build a proof of [False].  In inconsistent contexts that appear in the courses of proofs, it is usually easiest to proceed by demonstrating that inconsistency with an explicit proof of [False]. *)

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro.

    (** At this point, we have an inconsistent hypothesis [2 + 2 = 5], so the specific conclusion is not important.  We use the [elimtype] tactic to state a proposition, telling Coq that we wish to construct a proof of the new proposition and then prove the original goal by case analysis on the structure of the new auxiliary proof.  Since [False] has no constructors, [elimtype False] simply leaves us with the obligation to prove [False]. *)

    elimtype False.
    (** [[

  H : 2 + 2 = 5
  ============================
   False
]] *)

    (** For now, we will leave the details of this proof about arithmetic to [crush]. *)

    crush.
  Qed.

  (** A related notion to [False] is logical negation. *)

  Print not.
  (** [[

not = fun A : Prop => A -> False
     : Prop -> Prop
     ]] *)

  (** We see that [not] is just shorthand for implication of [False].  We can use that fact explicitly in proofs.  The syntax [~P] expands to [not P]. *)

  Theorem arith_neq' : ~ (2 + 2 = 5).
    unfold not.

    (** [[

  ============================
   2 + 2 = 5 -> False
   ]] *)

    crush.
  Qed.

  (** We also have conjunction, which we introduced in the last chapter. *)

  Print and.
  (** [[

Inductive and (A : Prop) (B : Prop) : Prop :=  conj : A -> B -> A /\ B
]] *)

  (** The interested reader can check that [and] has a Curry-Howard doppleganger called [prod], the type of pairs.  However, it is generally most convenient to reason about conjunction using tactics.  An explicit proof of commutativity of [and] illustrates the usual suspects for such tasks.  [/\] is an infix shorthand for [and]. *)

  Theorem and_comm : P /\ Q -> Q /\ P.
    (** We start by case analysis on the proof of [P /\ Q]. *)

    destruct 1.
    (** [[

  H : P
  H0 : Q
  ============================
   Q /\ P
   ]] *)

    (** Every proof of a conjunction provides proofs for both conjuncts, so we get a single subgoal reflecting that.  We can proceed by splitting this subgoal into a case for each conjunct of [Q /\ P]. *)

    split.
    (** [[
2 subgoals
  
  H : P
  H0 : Q
  ============================
   Q

subgoal 2 is:
 P
 ]] *)

    (** In each case, the conclusion is among our hypotheses, so the [assumption] tactic finishes the process. *)

    assumption.
    assumption.
  Qed.

  (** Coq disjunction is called [or] and abbreviated with the infix operator [\/]. *)

  Print or.
  (** [[

Inductive or (A : Prop) (B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B
]] *)

  (** We see that there are two ways to prove a disjunction: prove the first disjunct or prove the second.  The Curry-Howard analogue of this is the Coq [sum] type.  We can demonstrate the main tactics here with another proof of commutativity. *)

  Theorem or_comm : P \/ Q -> Q \/ P.
    (** As in the proof for [and], we begin with case analysis, though this time we are met by two cases instead of one. *)
    destruct 1.
(** [[

2 subgoals
  
  H : P
  ============================
   Q \/ P

subgoal 2 is:
 Q \/ P
]] *)

    (** We can see that, in the first subgoal, we want to prove the disjunction by proving its second disjunct.  The [right] tactic telegraphs this intent. *)

    right; assumption.

    (** The second subgoal has a symmetric proof.

       [[

1 subgoal
  
  H : Q
  ============================
   Q \/ P
   ]] *)

    left; assumption.
  Qed.


(* begin hide *)
(* In-class exercises *)

  Theorem contra : P -> ~P -> R.
  Admitted.

  Theorem and_assoc : (P /\ Q) /\ R -> P /\ (Q /\ R).
  Admitted.

  Theorem or_assoc : (P \/ Q) \/ R -> P \/ (Q \/ R).
  Admitted.

(* end hide *)


  (** It would be a shame to have to plod manually through all proofs about propositional logic.  Luckily, there is no need.  One of the most basic Coq automation tactics is [tauto], which is a complete decision procedure for constructive propositional logic.  (More on what "constructive" means in the next section.)  We can use [tauto] to dispatch all of the purely propositional theorems we have proved so far. *)

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  (** Sometimes propositional reasoning forms important plumbing for the proof of a theorem, but we still need to apply some other smarts about, say, arithmetic.  [intuition] is a generalization of [tauto] that proves everything it can using propositional reasoning.  When some goals remain, it uses propositional laws to simplify them as far as possible.  Consider this example, which uses the list concatenation operator [++] from the standard library. *)

  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    intuition.

    (** A lot of the proof structure has been generated for us by [intuition], but the final proof depends on a fact about lists.  The remaining subgoal hints at what cleverness we need to inject. *)

    (** [[

  ls1 : list nat
  ls2 : list nat
  H0 : length ls1 + length ls2 = 6
  ============================
   length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2
   ]] *)

    (** We can see that we need a theorem about lengths of concatenated lists, which we proved last chapter and is also in the standard library. *)

    rewrite app_length.
    (** [[

  ls1 : list nat
  ls2 : list nat
  H0 : length ls1 + length ls2 = 6
  ============================
   length ls1 + length ls2 = 6 \/ length ls1 = length ls2
   ]] *)

    (** Now the subgoal follows by purely propositional reasoning.  That is, we could replace [length ls1 + length ls2 = 6] with [P] and [length ls1 = length ls2] with [Q] and arrive at a tautology of propositional logic. *)

    tauto.
  Qed.

  (** [intuition] is one of the main bits of glue in the implementation of [crush], so, with a little help, we can get a short automated proof of the theorem. *)

  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length : cpdt.

    crush.
  Qed.

End Propositional.


(** * What Does It Mean to Be Constructive? *)

(** One potential point of confusion in the presentation so far is the distinction between [bool] and [Prop].  [bool] is a datatype whose two values are [true] and [false], while [Prop] is a more primitive type that includes among its members [True] and [False].  Why not collapse these two concepts into one, and why must there be more than two states of mathematical truth?

The answer comes from the fact that Coq implements %\textit{%#<i>#constructive#</i>#%}% or %\textit{%#<i>#intuitionistic#</i>#%}% logic, in contrast to the %\textit{%#<i>#classical#</i>#%}% logic that you may be more familiar with.  In constructive logic, classical tautologies like [~ ~P -> P] and [P \/ ~P] do not always hold.  In general, we can only prove these tautologies when [P] is %\textit{%#<i>#decidable#</i>#%}%, in the sense of computability theory.  The Curry-Howard encoding that Coq uses for [or] allows us to extract either a proof of [P] or a proof of [~P] from any proof of [P \/ ~P].  Since our proofs are just functional programs which we can run, this would give us a decision procedure for the halting problem, where the instantiations of [P] would be formulas like "this particular Turing machine halts."

Hence the distinction between [bool] and [Prop].  Programs of type [bool] are computational by construction; we can always run them to determine their results.  Many [Prop]s are undecidable, and so we can write more expressive formulas with [Prop]s than with [bool]s, but the inevitable consequence is that we cannot simply "run a [Prop] to determine its truth."

Constructive logic lets us define all of the logical connectives in an aesthetically-appealing way, with orthogonal inductive definitions.  That is, each connective is defined independently using a simple, shared mechanism.  Constructivity also enables a trick called %\textit{%#<i>#program extraction#</i>#%}%, where we write programs by phrasing them as theorems to be proved.  Since our proofs are just functional programs, we can extract executable programs from our final proofs, which we could not do as naturally with classical proofs.

We will see more about Coq's program extraction facility in a later chapter.  However, I think it is worth interjecting another warning at this point, following up on the prior warning about taking the Curry-Howard correspondence too literally.  It is possible to write programs by theorem-proving methods in Coq, but hardly anyone does it.  It is almost always most useful to maintain the distinction between programs and proofs.  If you write a program by proving a theorem, you are likely to run into algorithmic inefficiencies that you introduced in your proof to make it easier to prove.  It is a shame to have to worry about such situations while proving tricky theorems, and it is a happy state of affairs that you almost certainly will not need to, with the ideal of extracting programs from proofs being confined mostly to theoretical studies. *)


(** * First-Order Logic *)

(** The [forall] connective of first-order logic, which we have seen in many examples so far, is built into Coq.  Getting ahead of ourselves a bit, we can see it as the dependent function type constructor.  In fact, implication and universal quantification are just different syntactic shorthands for the same Coq mechanism.  A formula [P -> Q] is equivalent to [forall x : P, Q], where [x] does not appear in [Q].  That is, the "real" type of the implication says "for every proof of [P], there exists a proof of [Q]."

Existential quantification is defined in the standard library. *)

Print ex.
(** [[

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
    ]] *)

(** [ex] is parameterized by the type [A] that we quantify over, and by a predicate [P] over [A]s.  We prove an existential by exhibiting some [x] of type [A], along with a proof of [P x].  As usual, there are tactics that save us from worrying about the low-level details most of the time. *)

Theorem exist1 : exists x : nat, x + 1 = 2.
  (** remove printing exists*)
  (** We can start this proof with a tactic [exists], which should not be confused with the formula constructor shorthand of the same name.  (In the PDF version of this document, the reverse 'E' appears instead of the text "exists.") *)
  exists 1.

  (** The conclusion is replaced with a version using the existential witness that we announced. *)

  (** [[

  ============================
   1 + 1 = 2
   ]] *)

  reflexivity.
Qed.

(** printing exists $\exists$ *)

(** We can also use tactics to reason about existential hypotheses. *)

Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
  (** We start by case analysis on the proof of the existential fact. *)
  destruct 1.
  (** [[

  n : nat
  m : nat
  x : nat
  H : n + x = m
  ============================
   n <= m
   ]] *)

  (** The goal has been replaced by a form where there is a new free variable [x], and where we have a new hypothesis that the body of the existential holds with [x] substituted for the old bound variable.  From here, the proof is just about arithmetic and is easy to automate. *)

  crush.
Qed.


(* begin hide *)
(* In-class exercises *)

Theorem forall_exists_commute : forall (A B : Type) (P : A -> B -> Prop),
  (exists x : A, forall y : B, P x y) -> (forall y : B, exists x : A, P x y).
Admitted.

(* end hide *)


(** The tactic [intuition] has a first-order cousin called [firstorder].  [firstorder] proves many formulas when only first-order reasoning is needed, and it tries to perform first-order simplifications in any case.  First-order reasoning is much harder than propositional reasoning, so [firstorder] is much more likely than [intuition] to get stuck in a way that makes it run for long enough to be useless. *)


(** * Predicates with Implicit Equality *)

(** We start our exploration of a more complicated class of predicates with a simple example: an alternative way of characterizing when a natural number is zero. *)

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

(** We can call [isZero] a %\textit{%#<i>#judgment#</i>#%}%, in the sense often used in the semantics of programming languages.  Judgments are typically defined in the style of %\textit{%#<i>#natural deduction#</i>#%}%, where we write a number of %\textit{%#<i>#inference rules#</i>#%}% with premises appearing above a solid line and a conclusion appearing below the line.  In this example, the sole constructor [IsZero] of [isZero] can be thought of as the single inference rule for deducing [isZero], with nothing above the line and [isZero 0] below it.  The proof of [isZero_zero] demonstrates how we can apply an inference rule.

The definition of [isZero] differs in an important way from all of the other inductive definitions that we have seen in this and the previous chapter.  Instead of writing just [Set] or [Prop] after the colon, here we write [nat -> Prop].  We saw examples of parameterized types like [list], but there the parameters appeared with names %\textit{%#<i>#before#</i>#%}% the colon.  Every constructor of a parameterized inductive type must have a range type that uses the same parameter, whereas the form we use here enables us to use different arguments to the type for different constructors.

For instance, [isZero] forces its argument to be [0].  We can see that the concept of equality is somehow implicit in the inductive definition mechanism.  The way this is accomplished is similar to the way that logic variables are used in Prolog, and it is a very powerful mechanism that forms a foundation for formalizing all of mathematics.  In fact, though it is natural to think of inductive types as folding in the functionality of equality, in Coq, the true situation is reversed, with equality defined as just another inductive type! *)

Print eq.
(** [[

Inductive eq (A : Type) (x : A) : A -> Prop :=  refl_equal : x = x
]] *)

(** [eq] is the type we get behind the scenes when uses of infix [=] are expanded.  We see that [eq] has both a parameter [x] that is fixed and an extra unnamed argument of the same type.  It is crucial that the second argument is untied to the parameter in the type of [eq]; otherwise, we would have to prove that two values are equal even to be able to state the possibility of equality, which would more or less defeat the purpose of having an equality proposition.  However, examining the type of equality's sole constructor [refl_equal], we see that we can only %\textit{%#<i>#prove#</i>#%}% equality when its two arguments are syntactically equal.  This definition turns out to capture all of the basic properties of equality, and the equality-manipulating tactics that we have seen so far, like [reflexivity] and [rewrite], are implemented treating [eq] as just another inductive type with a well-chosen definition.

Returning to the example of [isZero], we can see how to make use of hypotheses that use this predicate. *)

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
  (** We want to proceed by cases on the proof of the assumption about [isZero]. *)
  destruct 1.
  (** [[

  n : nat
  ============================
   n + 0 = n
   ]] *)

  (** Since [isZero] has only one constructor, we are presented with only one subgoal.  The argument [m] to [isZero] is replaced with that type's argument from the single constructor [IsZero].  From this point, the proof is trivial. *)

  crush.
Qed.

(** Another example seems at first like it should admit an analogous proof, but in fact provides a demonstration of one of the most basic gotchas of Coq proving. *)

Theorem isZero_contra : isZero 1 -> False.
  (** Let us try a proof by cases on the assumption, as in the last proof. *)
  destruct 1.
  (** [[

  ============================
   False
   ]] *)

  (** It seems that case analysis has not helped us much at all!  Our sole hypothesis disappears, leaving us, if anything, worse off than we were before.  What went wrong?  We have met an important restriction in tactics like [destruct] and [induction] when applied to types with arguments.  If the arguments are not already free variables, they will be replaced by new free variables internally before doing the case analysis or induction.  Since the argument [1] to [isZero] is replaced by a fresh variable, we lose the crucial fact that it is not equal to [0].

     Why does Coq use this restriction?  We will discuss the issue in detail in a future chapter, when we see the dependently-typed programming techniques that would allow us to write this proof term manually.  For now, we just say that the algorithmic problem of "logically complete case analysis" is undecidable when phrased in Coq's logic.  A few tactics and design patterns that we will present in this chapter suffice in almost all cases.  For the current example, what we want is a tactic called [inversion], which corresponds to the concept of inversion that is frequently used with natural deduction proof systems. *)

  Undo.
  inversion 1.
Qed.

(** What does [inversion] do?  Think of it as a version of [destruct] that does its best to take advantage of the structure of arguments to inductive types.  In this case, [inversion] completed the proof immediately, because it was able to detect that we were using [isZero] with an impossible argument.

Sometimes using [destruct] when you should have used [inversion] can lead to confusing results.  To illustrate, consider an alternate proof attempt for the last theorem. *)

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  destruct 1.
  (** [[

  ============================
   1 + 1 = 4
   ]] *)

  (** What on earth happened here?  Internally, [destruct] replaced [1] with a fresh variable, and, trying to be helpful, it also replaced the occurrence of [1] within the unary representation of each number in the goal.  This has the net effect of decrementing each of these numbers.  If you are doing a proof and encounter a strange transmutation like this, there is a good chance that you should go back and replace a use of [destruct] with [inversion]. *)
Abort.


(* begin hide *)
(* In-class exercises *)

(* EX: Define an inductive type capturing when a list has exactly two elements.  Prove that your predicate does not hold of the empty list, and prove that, whenever it holds of a list, the length of that list is two. *)

(* end hide *)

