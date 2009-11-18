(* Copyright (c) 2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import DepList.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Universes and Axioms}% *)

(** Many traditional theorems can be proved in Coq without special knowledge of CIC, the logic behind the prover.  A development just seems to be using a particular ASCII notation for standard formulas based on set theory.  Nonetheless, as we saw in Chapter 4, CIC differs from set theory in making it possible to define the usual logical connectives as derived notions.  The foundation of it all is a dependently-typed functional programming language, based on dependent function types and inductive type families.  By using the facilities of this language directly, we can accomplish some things much more easily than in mainstream math.

   Gallina, which adds features to the more theoretical CIC, is the logic implemented in Coq.  It has a relatively simple foundation that can be defined rigorously in a page or two of formal proof rules.  Still, there are some important subtleties that have practical ramifications.  This chapter focuses on those subtleties, avoiding formal metatheory in favor of example code. *)


(** * The [Type] Hierarchy *)

(** Every object in Gallina has a type. *)

Check 0.
(** %\vspace{-.15in}% [[
  0
     : nat
 
     ]]

  It is natural enough that zero be considered as a natural number. *)

Check nat.
(** %\vspace{-.15in}% [[
  nat
     : Set
 
     ]]

  From a set theory perspective, it is unsurprising to consider the natural numbers as a "set." *)

Check Set.
(** %\vspace{-.15in}% [[
  Set
     : Type
 
     ]]

  The type [Set] may be considered as the set of all sets, a concept that set theory handles in terms of %\textit{%#<i>#classes#</i>#%}%.  In Coq, this more general notion is [Type]. *)

Check Type.
(** %\vspace{-.15in}% [[
  Type
     : Type
 
     ]]

  Strangely enough, [Type] appears to be its own type.  It is known that polymorphic languages with this property are inconsistent.  That is, using such a language to encode proofs is unwise, because it is possible to "prove" any theorem.  What is really going on here?

  Let us repeat some of our queries after toggling a flag related to Coq's printing behavior. *)

Set Printing Universes.

Check nat.
(** %\vspace{-.15in}% [[
  nat
     : Set
     ]] *)

(** printing $ %({}*% #(<a/>*# *)
(** printing ^ %*{})% #*<a/>)# *)

Check Set.
(** %\vspace{-.15in}% [[
  Set
     : Type $ (0)+1 ^

     ]] *)

Check Type.
(** %\vspace{-.15in}% [[
  Type $ Top.3 ^
     : Type $ (Top.3)+1 ^
 
     ]]

  Occurrences of [Type] are annotated with some additional information, inside comments.  These annotations have to do with the secret behind [Type]: it really stands for an infinite hierarchy of types.  The type of [Set] is [Type0], the type of [Type0] is [Type1], the type of [Type1] is [Type2], and so on.  This is how we avoid the "[Type : Type]" paradox.  As a convenience, the universe hierarchy drives Coq's one variety of subtyping.  Any term whose type is [Type] at level [i] is automatically also described by [Type] at level [j] when [j > i].

  In the outputs of our first [Check] query, we see that the type level of [Set]'s type is [(0)+1]. Here [0] stands for the level of [Set], and we increment it to arrive at the level that %\textit{%#<i>#classifies#</i>#%}% [Set].

  In the second query's output, we see that the occurrence of [Type] that we check is assigned a fresh %\textit{%#<i>#universe variable#</i>#%}% [Top.3].  The output type increments [Top.3] to move up a level in the universe hierarchy.  As we write code that uses definitions whose types mention universe variables, unification may refine the values of those variables.  Luckily, the user rarely has to worry about the details.

  Another crucial concept in CIC is %\textit{%#<i>#predicativity#</i>#%}%.  Consider these queries. *)

Check forall T : nat, fin T.
(** %\vspace{-.15in}% [[
  forall T : nat, fin T
     : Set
     ]] *)

Check forall T : Set, T.
(** %\vspace{-.15in}% [[
  forall T : Set, T
     : Type $ max(0, (0)+1) ^
     ]] *)

Check forall T : Type, T.
(** %\vspace{-.15in}% [[
  forall T : Type $ Top.9 ^ , T
     : Type $ max(Top.9, (Top.9)+1) ^
 
     ]]

  These outputs demonstrate the rule for determining which universe a [forall] type lives in.  In particular, for a type [forall x : T1, T2], we take the maximum of the universes of [T1] and [T2].  In the first example query, both [T1] ([nat]) and [T2] ([fin T]) are in [Set], so the [forall] type is in [Set], too.  In the second query, [T1] is [Set], which is at level [(0)+1]; and [T2] is [T], which is at level [0].  Thus, the [forall] exists at the maximum of these two levels.  The third example illustrates the same outcome, where we replace [Set] with an occurrence of [Type] that is assigned universe variable [Top.9].  This universe variable appears in the places where [0] appeared in the previous query.

  The behind-the-scenes manipulation of universe variables gives us predicativity.  Consider this simple definition of a polymorphic identity function. *)

Definition id (T : Set) (x : T) : T := x.

Check id 0.
(** %\vspace{-.15in}% [[
  id 0
     : nat
 
Check id Set.

Error: Illegal application (Type Error):
...
The 1st term has type "Type (* (Top.15)+1 *)" which should be coercible to "Set".
 
  ]]

  The parameter [T] of [id] must be instantiated with a [Set].  [nat] is a [Set], but [Set] is not.  We can try fixing the problem by generalizing our definition of [id]. *)

Reset id.
Definition id (T : Type) (x : T) : T := x.
Check id 0.
(** %\vspace{-.15in}% [[
  id 0
     : nat
     ]] *)

Check id Set.
(** %\vspace{-.15in}% [[
  id Set
     : Type $ Top.17 ^
  ]] *)

Check id Type.
(** %\vspace{-.15in}% [[
  id Type $ Top.18 ^
     : Type $ Top.19 ^
  ]] *)

(** So far so good.  As we apply [id] to different [T] values, the inferred index for [T]'s [Type] occurrence automatically moves higher up the type hierarchy.

   [[
Check id id.

Error: Universe inconsistency (cannot enforce Top.16 < Top.16).
 
   ]]

  This error message reminds us that the universe variable for [T] still exists, even though it is usually hidden.  To apply [id] to itself, that variable would need to be less than itself in the type hierarchy.  Universe inconsistency error messages announce cases like this one where a term could only type-check by violating an implied constraint over universe variables.  Such errors demonstrate that [Type] is %\textit{%#<i>#predicative#</i>#%}%, where this word has a CIC meaning closely related to its usual mathematical meaning.  A predicative system enforces the constraint that, for any object of quantified type, none of those quantifiers may never be instantiated with the object itself.  Impredicativity is associated with popular paradoxes in set theory, involving inconsistent constructions like "the set of all sets that do not contain themselves."  Similar paradoxes result from uncontrolled impredicativity in Coq. *)


(** ** Inductive Definitions *)

(** Predicativity restrictions also apply to inductive definitions.  As an example, let us consider a type of expression trees that allows injection of any native Coq value.  The idea is that an [exp T] stands for a reflected expression of type [T].

   [[
Inductive exp : Set -> Set :=
| Const : forall T : Set, T -> exp T
| Pair : forall T1 T2, exp T1 -> exp T2 -> exp (T1 * T2)
| Eq : forall T, exp T -> exp T -> exp bool.

Error: Large non-propositional inductive types must be in Type.
 
   ]]

   This definition is %\textit{%#<i>#large#</i>#%}% in the sense that at least one of its constructors takes an argument whose type has type [Type].  Coq would be inconsistent if we allowed definitions like this one in their full generality.  Instead, we must change [exp] to live in [Type].  We will go even further and move [exp]'s index to [Type] as well. *)

Inductive exp : Type -> Type :=
| Const : forall T, T -> exp T
| Pair : forall T1 T2, exp T1 -> exp T2 -> exp (T1 * T2)
| Eq : forall T, exp T -> exp T -> exp bool.

(** This definition is accepted.  We can build some sample expressions. *)

Check Const 0.
(** %\vspace{-.15in}% [[
  Const 0
     : exp nat
     ]] *)

Check Pair (Const 0) (Const tt).
(** %\vspace{-.15in}% [[
  Pair (Const 0) (Const tt)
     : exp (nat * unit)
     ]] *)

Check Eq (Const Set) (Const Type).
(** %\vspace{-.15in}% [[
  Eq (Const Set) (Const Type (* Top.59 *))
     : exp bool
 
     ]]

  We can check many expressions, including fancy expressions that include types.  However, it is not hard to hit a type-checking wall.

  [[
Check Const (Const O).

Error: Universe inconsistency (cannot enforce Top.42 < Top.42).
 
  ]]

  We are unable to instantiate the parameter [T] of [Const] with an [exp] type.  To see why, it is helpful to print the annotated version of [exp]'s inductive definition. *)

Print exp.
(** %\vspace{-.15in}% [[
Inductive exp
              : Type $ Top.8 ^ ->
                Type
                $ max(0, (Top.11)+1, (Top.14)+1, (Top.15)+1, (Top.19)+1) ^ :=
    Const : forall T : Type $ Top.11 ^ , T -> exp T
  | Pair : forall (T1 : Type $ Top.14 ^ ) (T2 : Type $ Top.15 ^ ),
           exp T1 -> exp T2 -> exp (T1 * T2)
  | Eq : forall T : Type $ Top.19 ^ , exp T -> exp T -> exp bool
 
  ]]

  We see that the index type of [exp] has been assigned to universe level [Top.8].  In addition, each of the four occurrences of [Type] in the types of the constructors gets its own universe variable.  Each of these variables appears explicitly in the type of [exp].  In particular, any type [exp T] lives at a universe level found by incrementing by one the maximum of the four argument variables.  A consequence of this is that [exp] %\textit{%#<i>#must#</i>#%}% live at a higher universe level than any type which may be passed to one of its constructors.  This consequence led to the universe inconsistency.

  Strangely, the universe variable [Top.8] only appears in one place.  Is there no restriction imposed on which types are valid arguments to [exp]?  In fact, there is a restriction, but it only appears in a global set of universe constraints that are maintained "off to the side," not appearing explicitly in types.  We can print the current database. *)

Print Universes.
(** %\vspace{-.15in}% [[
Top.19 < Top.9 <= Top.8
Top.15 < Top.9 <= Top.8 <= Coq.Init.Datatypes.38
Top.14 < Top.9 <= Top.8 <= Coq.Init.Datatypes.37
Top.11 < Top.9 <= Top.8
 
]]

[Print Universes] outputs many more constraints, but we have collected only those that mention [Top] variables.  We see one constraint for each universe variable associated with a constructor argument from [exp]'s definition.  [Top.19] is the type argument to [Eq].  The constraint for [Top.19] effectively says that [Top.19] must be less than [Top.8], the universe of [exp]'s indices; an intermediate variable [Top.9] appears as an artifact of the way the constraint was generated.

The next constraint, for [Top.15], is more complicated.  This is the universe of the second argument to the [Pair] constructor.  Not only must [Top.15] be less than [Top.8], but it also comes out that [Top.8] must be less than [Coq.Init.Datatypes.38].  What is this new universe variable?  It is from the definition of the [prod] inductive family, to which types of the form [A * B] are desugared. *)

Print prod.
(** %\vspace{-.15in}% [[
Inductive prod (A : Type $ Coq.Init.Datatypes.37 ^ )
          (B : Type $ Coq.Init.Datatypes.38 ^ )
            : Type $ max(Coq.Init.Datatypes.37, Coq.Init.Datatypes.38) ^ :=
    pair : A -> B -> A * B
 
    ]]

  We see that the constraint is enforcing that indices to [exp] must not live in a higher universe level than [B]-indices to [prod].  The next constraint above establishes a symmetric condition for [A].

  Thus it is apparent that Coq maintains a tortuous set of universe variable inequalities behind the scenes.  It may look like some functions are polymorphic in the universe levels of their arguments, but what is really happening is imperative updating of a system of constraints, such that all uses of a function are consistent with a global set of universe levels.  When the constraint system may not be evolved soundly, we get a universe inconsistency error.

  %\medskip%

  Something interesting is revealed in the annotated definition of [prod].  A type [prod A B] lives at a universe that is the maximum of the universes of [A] and [B].  From our earlier experiments, we might expect that [prod]'s universe would in fact need to be %\textit{%#<i>#one higher#</i>#%}% than the maximum.  The critical difference is that, in the definition of [prod], [A] and [B] are defined as %\textit{%#<i>#parameters#</i>#%}%; that is, they appear named to the left of the main colon, rather than appearing (possibly unnamed) to the right.

  Parameters are not as flexible as normal inductive type arguments.  The range types of all of the constructors of a parameterized type must share the same indices.  Nonetheless, when it is possible to define a polymorphic type in this way, we gain the ability to use the new type family in more ways, without triggering universe inconsistencies.  For instance, nested pairs of types are perfectly legal. *)

Check (nat, (Type, Set)).
(** %\vspace{-.15in}% [[
  (nat, (Type $ Top.44 ^ , Set))
     : Set * (Type $ Top.45 ^ * Type $ Top.46 ^ )
 
  ]]

  The same cannot be done with a counterpart to [prod] that does not use parameters. *)

Inductive prod' : Type -> Type -> Type :=
| pair' : forall A B : Type, A -> B -> prod' A B.

(** [[
Check (pair' nat (pair' Type Set)).

Error: Universe inconsistency (cannot enforce Top.51 < Top.51).
 
]]

The key benefit parameters bring us is the ability to avoid quantifying over types in the types of constructors.  Such quantification induces less-than constraints, while parameters only introduce less-than-or-equal-to constraints. *)
