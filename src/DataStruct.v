(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List.

Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Dependent Data Structures}% *)

(** Our red-black tree example from the last chapter illustrated how dependent types enable static enforcement of data structure invariants.  To find interesting uses of dependent data structures, however, we need not look to the favorite examples of data structures and algorithms textbooks.  More basic examples like length-indexed and heterogeneous lists come up again and again as the building blocks of dependent programs.  There is a surprisingly large design space for this class of data structure, and we will spend this chapter exploring it. *)


(** * More Length-Indexed Lists *)

(** We begin with a deeper look at the length-indexed lists that began the last chapter. *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  (** We might like to have a certified function for selecting an element of an [ilist] by position.  We could do this using subset types and explicit manipulation of proofs, but dependent types let us do it more directly.  It is helpful to define a type family [index], where [index n] is isomorphic to [{m : nat | m < n}].  Such a type family is also often called [Fin] or similar, standing for "finite." *)

  (* EX: Define a function [get] for extracting an [ilist] element by position. *)

(* begin thide *)
  Inductive index : nat -> Set :=
  | First : forall n, index (S n)
  | Next : forall n, index n -> index (S n).

  (** [index] essentially makes a more richly-typed copy of the natural numbers.  Every element is a [First] iterated through applying [Next] a number of times that indicates which number is being selected.

     Now it is easy to pick a [Prop]-free type for a selection function.  As usual, our first implementation attempt will not convince the type checker, and we will attack the deficiencies one at a time.

     [[
  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx => ?
      | Cons _ x ls' => fun idx =>
        match idx with
          | First _ => x
          | Next _ idx' => get ls' idx'
        end
    end.

    We apply the usual wisdom of delaying arguments in [Fixpoint]s so that they may be included in [return] clauses.  This still leaves us with a quandary in each of the [match] cases.  First, we need to figure out how to take advantage of the contradiction in the [Nil] case.  Every [index] has a type of the form [S n], which cannot unify with the [O] value that we learn for [n] in the [Nil] case.  The solution we adopt is another case of [match]-within-[return].

    [[
  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx =>
        match idx in index n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | Cons _ x ls' => fun idx =>
        match idx with
          | First _ => x
          | Next _ idx' => get ls' idx'
        end
    end.

    Now the first [match] case type-checks, and we see that the problem with the [Cons] case is that the pattern-bound variable [idx'] does not have an apparent type compatible with [ls'].  We need to use [match] annotations to make the relationship explicit.  Unfortunately, the usual trick of postponing argument binding will not help us here.  We need to match on both [ls] and [idx]; one or the other must be matched first.  To get around this, we apply a trick that we will call "the convoy pattern," introducing a new function and applying it immediately, to satisfy the type checker.

    [[
  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx =>
        match idx in index n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | Cons _ x ls' => fun idx =>
        match idx in index n' return ilist (pred n') -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun ls' => get ls' idx'
        end ls'
    end.

    There is just one problem left with this implementation.  Though we know that the local [ls'] in the [Next] case is equal to the original [ls'], the type-checker is not satisfied that the recursive call to [get] does not introduce non-termination.  We solve the problem by convoy-binding the partial application of [get] to [ls'], rather than [ls'] by itself. *)

  Fixpoint get n (ls : ilist n) {struct ls} : index n -> A :=
    match ls in ilist n return index n -> A with
      | Nil => fun idx =>
        match idx in index n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | Cons _ x ls' => fun idx =>
        match idx in index n' return (index (pred n') -> A) -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun get_ls' => get_ls' idx'
        end (get ls')
    end.
(* end thide *)
End ilist.

Implicit Arguments Nil [A].
(* begin thide *)
Implicit Arguments First [n].
(* end thide *)

(** A few examples show how to make use of these definitions. *)

Check Cons 0 (Cons 1 (Cons 2 Nil)).
(** [[

Cons 0 (Cons 1 (Cons 2 Nil))
     : ilist nat 3
]] *)
(* begin thide *)
Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) First.
(** [[

     = 0
     : nat
]] *)
Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next First).
(** [[

     = 1
     : nat
]] *)
Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next (Next First)).
(** [[

     = 2
     : nat
]] *)
(* end thide *)

(** Our [get] function is also quite easy to reason about.  We show how with a short example about an analogue to the list [map] function. *)

Section ilist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Fixpoint imap n (ls : ilist A n) {struct ls} : ilist B n :=
    match ls in ilist _ n return ilist B n with
      | Nil => Nil
      | Cons _ x ls' => Cons (f x) (imap ls')
    end.

  (** It is easy to prove that [get] "distributes over" [imap] calls.  The only tricky bit is remembering to use the [dep_destruct] tactic in place of plain [destruct] when faced with a baffling tactic error message. *)

  Theorem get_imap : forall n (idx : index n) (ls : ilist A n),
    get (imap ls) idx = f (get ls idx).
(* begin thide *)
    induction ls; dep_destruct idx; crush.
  Qed.
(* end thide *)
End ilist_map.


(** * Heterogeneous Lists *)

(** Programmers who move to statically-typed functional languages from "scripting languages" often complain about the requirement that every element of a list have the same type.  With fancy type systems, we can partially lift this requirement.  We can index a list type with a "type-level" list that explains what type each element of the list should have.  This has been done in a variety of ways in Haskell using type classes, and it we can do it much more cleanly and directly in Coq. *)

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  (* EX: Define a type [hlist] indexed by a [list A], where the type of each element is determined by running [B] on the corresponding element of the index list. *)

  (** We parameterize our heterogeneous lists by a type [A] and an [A]-indexed type [B]. *)

(* begin thide *)
  Inductive hlist : list A -> Type :=
  | MNil : hlist nil
  | MCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  (** We can implement a variant of the last section's [get] function for [hlist]s.  To get the dependent typing to work out, we will need to index our element selectors by the types of data that they point to. *)

(* end thide *)
  (* EX: Define an analogue to [get] for [hlist]s. *)

(* begin thide *)
  Variable elm : A.

  Inductive member : list A -> Type :=
  | MFirst : forall ls, member (elm :: ls)
  | MNext : forall x ls, member ls -> member (x :: ls).

  (** Because the element [elm] that we are "searching for" in a list does not change across the constructors of [member], we simplify our definitions by making [elm] a local variable.  In the definition of [member], we say that [elm] is found in any list that begins with [elm], and, if removing the first element of a list leaves [elm] present, then [elm] is present in the original list, too.  The form looks much like a predicate for list membership, but we purposely define [member] in [Type] so that we may decompose its values to guide computations.

     We can use [member] to adapt our definition of [get] to [hlists].  The same basic [match] tricks apply.  In the [MCons] case, we form a two-element convoy, passing both the data element [x] and the recursor for the sublist [mls'] to the result of the inner [match].  We did not need to do that in [get]'s definition because the types of list elements were not dependent there. *)

  Fixpoint hget ls (mls : hlist ls) {struct mls} : member ls -> B elm :=
    match mls in hlist ls return member ls -> B elm with
      | MNil => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => B elm
                                          | _ :: _ => unit
                                        end) with
          | MFirst _ => tt
          | MNext _ _ _ => tt
        end
      | MCons _ _ x mls' => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => Empty_set
                                          | x' :: ls'' =>
                                            B x' -> (member ls'' -> B elm) -> B elm
                                        end) with
          | MFirst _ => fun x _ => x
          | MNext _ _ mem' => fun _ get_mls' => get_mls' mem'
        end x (hget mls')
    end.
(* end thide *)
End hlist.

(* begin thide *)
Implicit Arguments MNil [A B].
Implicit Arguments MCons [A B x ls].

Implicit Arguments MFirst [A elm ls].
Implicit Arguments MNext [A elm x ls].
(* end thide *)

(** By putting the parameters [A] and [B] in [Type], we allow some very higher-order uses.  For instance, one use of [hlist] is for the simple heterogeneous lists that we referred to earlier. *)

Definition someTypes : list Set := nat :: bool :: nil.

(* begin thide *)

Example someValues : hlist (fun T : Set => T) someTypes :=
  MCons 5 (MCons true MNil).

Eval simpl in hget someValues MFirst.
(** [[

     = 5
     : (fun T : Set => T) nat
]] *)
Eval simpl in hget someValues (MNext MFirst).
(** [[

     = true
     : (fun T : Set => T) bool
]] *)

(** We can also build indexed lists of pairs in this way. *)

Example somePairs : hlist (fun T : Set => T * T)%type someTypes :=
  MCons (1, 2) (MCons (true, false) MNil).

(* end thide *)


(** ** A Lambda Calculus Interpreter *)

(** Heterogeneous lists are very useful in implementing interpreters for functional programming languages.  Using the types and operations we have already defined, it is trivial to write an interpreter for simply-typed lambda calculus.  Our interpreter can alternatively be thought of as a denotational semantics.

   We start with an algebraic datatype for types. *)

Inductive type : Set :=
| Unit : type
| Arrow : type -> type -> type.

(** Now we can define a type family for expressions.  An [exp ts t] will stand for an expression that has type [t] and whose free variables have types in the list [ts].  We effectively use the de Bruijn variable representation, which we will discuss in more detail in later chapters.  Variables are represented as [member] values; that is, a variable is more or less a constructive proof that a particular type is found in the type environment. *)

Inductive exp : list type -> type -> Set :=
| Const : forall ts, exp ts Unit

(* begin thide *)
| Var : forall ts t, member t ts -> exp ts t
| App : forall ts dom ran, exp ts (Arrow dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (Arrow dom ran).
(* end thide *)

Implicit Arguments Const [ts].

(** We write a simple recursive function to translate [type]s into [Set]s. *)

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Unit => unit
    | Arrow t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(** Now it is straightforward to write an expression interpreter.  The type of the function, [expDenote], tells us that we translate expressions into functions from properly-typed environments to final values.  An environment for a free variable list [ts] is simply a [hlist typeDenote ts].  That is, for each free variable, the heterogeneous list that is the environment must have a value of the variable's associated type.  We use [hget] to implement the [Var] case, and we use [MCons] to extend the environment in the [Abs] case. *)

(* EX: Define an interpreter for [exp]s. *)

(* begin thide *)
Fixpoint expDenote ts t (e : exp ts t) {struct e} : hlist typeDenote ts -> typeDenote t :=
  match e in exp ts t return hlist typeDenote ts -> typeDenote t with
    | Const _ => fun _ => tt

    | Var _ _ mem => fun s => hget s mem
    | App _ _ _ e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
    | Abs _ _ _ e' => fun s => fun x => expDenote e' (MCons x s)
  end.

(** Like for previous examples, our interpreter is easy to run with [simpl]. *)

Eval simpl in expDenote Const MNil.
(** [[

    = tt
     : typeDenote Unit
]] *)
Eval simpl in expDenote (Abs (dom := Unit) (Var MFirst)) MNil.
(** [[

     = fun x : unit => x
     : typeDenote (Arrow Unit Unit)
]] *)
Eval simpl in expDenote (Abs (dom := Unit)
  (Abs (dom := Unit) (Var (MNext MFirst)))) MNil.
(** [[

     = fun x _ : unit => x
     : typeDenote (Arrow Unit (Arrow Unit Unit))
]] *)
Eval simpl in expDenote (Abs (dom := Unit) (Abs (dom := Unit) (Var MFirst))) MNil.
(** [[

     = fun _ x0 : unit => x0
     : typeDenote (Arrow Unit (Arrow Unit Unit))
]] *)
Eval simpl in expDenote (App (Abs (Var MFirst)) Const) MNil.
(** [[

     = tt
     : typeDenote Unit
]] *)

(* end thide *)

(** We are starting to develop the tools behind dependent typing's amazing advantage over alternative approaches in several important areas.  Here, we have implemented complete syntax, typing rules, and evaluation semantics for simply-typed lambda calculus without even needing to define a syntactic substitution operation.  We did it all without a single line of proof, and our implementation is manifestly executable.  In a later chapter, we will meet other, more common approaches to language formalization.  Such approaches often state and prove explicit theorems about type safety of languages.  In the above example, we got type safety, termination, and other meta-theorems for free, by reduction to CIC, which we know has those properties. *)


(** * Recursive Type Definitions *)

(** There is another style of datatype definition that leads to much simpler definitions of the [get] and [hget] definitions above.  Because Coq supports "type-level computation," we can redo our inductive definitions as %\textit{%#<i>#recursive#</i>#%}% definitions. *)

(* EX: Come up with an alternate [ilist] definition that makes it easier to write [get]. *)

Section filist.
  Variable A : Set.

(* begin thide *)
  Fixpoint filist (n : nat) : Set :=
    match n with
      | O => unit
      | S n' => A * filist n'
    end%type.

  (** We say that a list of length 0 has no contents, and a list of length [S n'] is a pair of a data value and a list of length [n']. *)

  Fixpoint findex (n : nat) : Set :=
    match n with
      | O => Empty_set
      | S n' => option (findex n')
    end.

  (** We express that there are no index values when [n = O], by defining such indices as type [Empty_set]; and we express that, at [n = S n'], there is a choice between picking the first element of the list (represented as [None]) or choosing a later element (represented by [Some idx], where [idx] is an index into the list tail). *)

  Fixpoint fget (n : nat) : filist n -> findex n -> A :=
    match n return filist n -> findex n -> A with
      | O => fun _ idx => match idx with end
      | S n' => fun ls idx =>
        match idx with
          | None => fst ls
          | Some idx' => fget n' (snd ls) idx'
        end
    end.

  (** Our new [get] implementation needs only one dependent [match], which just copies the stated return type of the function.  Our choices of data structure implementations lead to just the right typing behavior for this new definition to work out. *)
(* end thide *)
End filist.

(** Heterogeneous lists are a little trickier to define with recursion, but we then reap similar benefits in simplicity of use. *)

(* EX: Come up with an alternate [hlist] definition that makes it easier to write [hget]. *)

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

(* begin thide *)
  Fixpoint fhlist (ls : list A) : Type :=
    match ls with
      | nil => unit
      | x :: ls' => B x * fhlist ls'
    end%type.

  (** The definition of [fhlist] follows the definition of [filist], with the added wrinkle of dependently-typed data elements. *)

  Variable elm : A.

  Fixpoint fmember (ls : list A) : Type :=
    match ls with
      | nil => Empty_set
      | x :: ls' => (x = elm) + fmember ls'
    end%type.

  (** The definition of [fmember] follows the definition of [findex].  Empty lists have no members, and member types for nonempty lists are built by adding one new option to the type of members of the list tail.  While for [index] we needed no new information associated with the option that we add, here we need to know that the head of the list equals the element we are searching for.  We express that with a sum type whose left branch is the appropriate equality proposition.  Since we define [fmember] to live in [Type], we can insert [Prop] types as needed, because [Prop] is a subtype of [Type].

     We know all of the tricks needed to write a first attempt at a [get] function for [fhlist]s.

     [[

  Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
    match ls return fhlist ls -> fmember ls -> B elm with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx =>
        match idx with
          | inl _ => fst mls
          | inr idx' => fhget ls' (snd mls) idx'
        end
    end.

    Only one problem remains.  The expression [fst mls] is not known to have the proper type.  To demonstrate that it does, we need to use the proof available in the [inl] case of the inner [match]. *)

  Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
    match ls return fhlist ls -> fmember ls -> B elm with
      | nil => fun _ idx => match idx with end
      | _ :: ls' => fun mls idx =>
        match idx with
          | inl pf => match pf with
                        | refl_equal => fst mls
                      end
          | inr idx' => fhget ls' (snd mls) idx'
        end
    end.

  (** By pattern-matching on the equality proof [pf], we make that equality known to the type-checker.  Exactly why this works can be seen by studying the definition of equality. *)

  Print eq.
  (** [[

Inductive eq (A : Type) (x : A) : A -> Prop :=  refl_equal : x = x
]]

In a proposition [x = y], we see that [x] is a parameter and [y] is a regular argument.  The type of the constructor [refl_equal] shows that [y] can only ever be instantiated to [x].  Thus, within a pattern-match with [refl_equal], occurrences of [y] can be replaced with occurrences of [x] for typing purposes.  All examples of similar dependent pattern matching that we have seen before require explicit annotations, but Coq implements a special case of annotation inference for matches on equality proofs. *)
(* end thide *)
End fhlist.

Implicit Arguments fhget [A B elm ls].


(** * Data Structures as Index Functions *)

(** Indexed lists can be useful in defining other inductive types with constructors that take variable numbers of arguments.  In this section, we consider parameterized trees with arbitrary branching factor. *)

Section tree.
  Variable A : Set.

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, ilist tree n -> tree.
End tree.

(** Every [Node] of a [tree] has a natural number argument, which gives the number of child trees in the second argument, typed with [ilist].  We can define two operations on trees of naturals: summing their elements and incrementing their elements.  It is useful to define a generic fold function on [ilist]s first. *)

Section ifoldr.
  Variables A B : Set.
  Variable f : A -> B -> B.
  Variable i : B.

  Fixpoint ifoldr n (ls : ilist A n) {struct ls} : B :=
    match ls with
      | Nil => i
      | Cons _ x ls' => f x (ifoldr ls')
    end.
End ifoldr.

Fixpoint sum (t : tree nat) : nat :=
  match t with
    | Leaf n => n
    | Node _ ls => ifoldr (fun t' n => sum t' + n) O ls
  end.

Fixpoint inc (t : tree nat) : tree nat :=
  match t with
    | Leaf n => Leaf (S n)
    | Node _ ls => Node (imap inc ls)
  end.

(** Now we might like to prove that [inc] does not decrease a tree's [sum]. *)

Theorem sum_inc : forall t, sum (inc t) >= sum t.
(* begin thide *)
  induction t; crush.
  (** [[

  n : nat
  i : ilist (tree nat) n
  ============================
   ifoldr (fun (t' : tree nat) (n0 : nat) => sum t' + n0) 0 (imap inc i) >=
   ifoldr (fun (t' : tree nat) (n0 : nat) => sum t' + n0) 0 i
   ]]

   We are left with a single subgoal which does not seem provable directly.  This is the same problem that we met in Chapter 3 with other nested inductive types. *)

  Check tree_ind.
  (** [[

tree_ind
     : forall (A : Set) (P : tree A -> Prop),
       (forall a : A, P (Leaf a)) ->
       (forall (n : nat) (i : ilist (tree A) n), P (Node i)) ->
       forall t : tree A, P t
]]

The automatically-generated induction principle is too weak.  For the [Node] case, it gives us no inductive hypothesis.  We could write our own induction principle, as we did in Chapter 3, but there is an easier way, if we are willing to alter the definition of [tree]. *)
Abort.

Reset tree.

(** First, let us try using our recursive definition of [ilist]s instead of the inductive version. *)

Section tree.
  Variable A : Set.

  (** [[

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, filist tree n -> tree.

[[

Error: Non strictly positive occurrence of "tree" in
 "forall n : nat, filist tree n -> tree"
]]

  The special-case rule for nested datatypes only works with nested uses of other inductive types, which could be replaced with uses of new mutually-inductive types.  We defined [filist] recursively, so it may not be used for nested recursion.

  Our final solution uses yet another of the inductive definition techniques introduced in Chapter 3, reflexive types.  Instead of merely using [index] to get elements out of [ilist], we can %\textit{%#<i>#define#</i>#%}% [ilist] in terms of [index].  For the reasons outlined above, it turns out to be easier to work with [findex] in place of [index]. *)

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, (findex n -> tree) -> tree.

  (** A [Node] is indexed by a natural number [n], and the node's [n] children are represented as a function from [findex n] to trees, which is isomorphic to the [ilist]-based representation that we used above. *)
End tree.

Implicit Arguments Node [A n].

(** We can redefine [sum] and [inc] for our new [tree] type.  Again, it is useful to define a generic fold function first.  This time, it takes in a function whose range is some [findex] type, and it folds another function over the results of calling the first function at every possible [findex] value. *)

Section rifoldr.
  Variables A B : Set.
  Variable f : A -> B -> B.
  Variable i : B.

  Fixpoint rifoldr (n : nat) : (findex n -> A) -> B :=
    match n return (findex n -> A) -> B with
      | O => fun _ => i
      | S n' => fun get => f (get None) (rifoldr n' (fun idx => get (Some idx)))
    end.
End rifoldr.

Implicit Arguments rifoldr [A B n].

Fixpoint sum (t : tree nat) : nat :=
  match t with
    | Leaf n => n
    | Node _ f => rifoldr plus O (fun idx => sum (f idx))
  end.

Fixpoint inc (t : tree nat) : tree nat :=
  match t with
    | Leaf n => Leaf (S n)
    | Node _ f => Node (fun idx => inc (f idx))
  end.

(** Now we are ready to prove the theorem where we got stuck before.  We will not need to define any new induction principle, but it %\textit{%#<i>#will#</i>#%}% be helpful to prove some lemmas. *)

Lemma plus_ge : forall x1 y1 x2 y2,
  x1 >= x2
  -> y1 >= y2
  -> x1 + y1 >= x2 + y2.
  crush.
Qed.

Lemma sum_inc' : forall n (f1 f2 : findex n -> nat),
  (forall idx, f1 idx >= f2 idx)
  -> rifoldr plus 0 f1 >= rifoldr plus 0 f2.
  Hint Resolve plus_ge.

  induction n; crush.
Qed.

Theorem sum_inc : forall t, sum (inc t) >= sum t.
  Hint Resolve sum_inc'.

  induction t; crush.
Qed.

(* end thide *)

(** Even if Coq would generate complete induction principles automatically for nested inductive definitions like the one we started with, there would still be advantages to using this style of reflexive encoding.  We see one of those advantages in the definition of [inc], where we did not need to use any kind of auxiliary function.  In general, reflexive encodings often admit direct implementations of operations that would require recursion if performed with more traditional inductive data structures. *)

(** ** Another Interpreter Example *)

(** We develop another example of variable-arity constructors, in the form of optimization of a small expression language with a construct like Scheme's %\texttt{%#<tt>#cond#</tt>#%}%.  Each of our conditional expressions takes a list of pairs of boolean tests and bodies.  The value of the conditional comes from the body of the first test in the list to evaluate to [true].  To simplify the interpreter we will write, we force each conditional to include a final, default case. *)

Inductive type' : Type := Nat | Bool.

Inductive exp' : type' -> Type :=
| NConst : nat -> exp' Nat
| Plus : exp' Nat -> exp' Nat -> exp' Nat
| Eq : exp' Nat -> exp' Nat -> exp' Bool

| BConst : bool -> exp' Bool
(* begin thide *)
| Cond : forall n t, (findex n -> exp' Bool)
  -> (findex n -> exp' t) -> exp' t -> exp' t.
(* end thide *)

(** A [Cond] is parameterized by a natural [n], which tells us how many cases this conditional has.  The test expressions are represented with a function of type [findex n -> exp' Bool], and the bodies are represented with a function of type [findex n -> exp' t], where [t] is the overall type.  The final [exp' t] argument is the default case.

We start implementing our interpreter with a standard type denotation function. *)

Definition type'Denote (t : type') : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(** To implement the expression interpreter, it is useful to have the following function that implements the functionality of [Cond] without involving any syntax. *)

(* begin thide *)
Section cond.
  Variable A : Set.
  Variable default : A.

  Fixpoint cond (n : nat) : (findex n -> bool) -> (findex n -> A) -> A :=
    match n return (findex n -> bool) -> (findex n -> A) -> A with
      | O => fun _ _ => default
      | S n' => fun tests bodies =>
        if tests None
          then bodies None
          else cond n'
            (fun idx => tests (Some idx))
            (fun idx => bodies (Some idx))
    end.
End cond.

Implicit Arguments cond [A n].
(* end thide *)

(** Now the expression interpreter is straightforward to write. *)

Fixpoint exp'Denote t (e : exp' t) {struct e} : type'Denote t :=
  match e in exp' t return type'Denote t with
    | NConst n =>
      n
    | Plus e1 e2 =>
      exp'Denote e1 + exp'Denote e2
    | Eq e1 e2 =>
      if eq_nat_dec (exp'Denote e1) (exp'Denote e2) then true else false

    | BConst b =>
      b
    | Cond _ _ tests bodies default =>
(* begin thide *)
      cond
      (exp'Denote default)
      (fun idx => exp'Denote (tests idx))
      (fun idx => exp'Denote (bodies idx))
(* end thide *)
  end.

(** We will implement a constant-folding function that optimizes conditionals, removing cases with known-[false] tests and cases that come after known-[true] tests.  A function [cfoldCond] implements the heart of this logic.  The convoy pattern is used again near the end of the implementation. *)

(* begin thide *)
Section cfoldCond.
  Variable t : type'.
  Variable default : exp' t.

  Fixpoint cfoldCond (n : nat)
    : (findex n -> exp' Bool) -> (findex n -> exp' t) -> exp' t :=
    match n return (findex n -> exp' Bool) -> (findex n -> exp' t) -> exp' t with
      | O => fun _ _ => default
      | S n' => fun tests bodies =>
        match tests None with
          | BConst true => bodies None
          | BConst false => cfoldCond n'
            (fun idx => tests (Some idx))
            (fun idx => bodies (Some idx))
          | _ =>
            let e := cfoldCond n'
              (fun idx => tests (Some idx))
              (fun idx => bodies (Some idx)) in
            match e in exp' t return exp' t -> exp' t with
              | Cond n _ tests' bodies' default' => fun body =>
                Cond
                (S n)
                (fun idx => match idx with
                              | None => tests None
                              | Some idx => tests' idx
                            end)
                (fun idx => match idx with
                              | None => body
                              | Some idx => bodies' idx
                            end)
                default'
              | e => fun body =>
                Cond
                1
                (fun _ => tests None)
                (fun _ => body)
                e
            end (bodies None)
        end
    end.
End cfoldCond.

Implicit Arguments cfoldCond [t n].
(* end thide *)

(** Like for the interpreters, most of the action was in this helper function, and [cfold] itself is easy to write. *)

Fixpoint cfold t (e : exp' t) {struct e} : exp' t :=
  match e in exp' t return exp' t with
    | NConst n => NConst n
    | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | NConst n1, NConst n2 => NConst (n1 + n2)
        | _, _ => Plus e1' e2'
      end
    | Eq e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | NConst n1, NConst n2 => BConst (if eq_nat_dec n1 n2 then true else false)
        | _, _ => Eq e1' e2'
      end

    | BConst b => BConst b
    | Cond _ _ tests bodies default =>
(* begin thide *)
      cfoldCond
      (cfold default)
      (fun idx => cfold (tests idx))
      (fun idx => cfold (bodies idx))
(* end thide *)
  end.

(* begin thide *)
(** To prove our final correctness theorem, it is useful to know that [cfoldCond] preserves expression meanings.  This lemma formalizes that property.  The proof is a standard mostly-automated one, with the only wrinkle being a guided instantation of the quantifiers in the induction hypothesis. *)

Lemma cfoldCond_correct : forall t (default : exp' t)
  n (tests : findex n -> exp' Bool) (bodies : findex n -> exp' t),
  exp'Denote (cfoldCond default tests bodies)
  = exp'Denote (Cond n tests bodies default).
  induction n; crush;
    match goal with
      | [ IHn : forall tests bodies, _, tests : _ -> _, bodies : _ -> _ |- _ ] =>
        generalize (IHn (fun idx => tests (Some idx)) (fun idx => bodies (Some idx)));
          clear IHn; intro IHn
    end;
    repeat (match goal with
              | [ |- context[match ?E with
                               | NConst _ => _
                               | Plus _ _ => _
                               | Eq _ _ => _
                               | BConst _ => _
                               | Cond _ _ _ _ _ => _
                             end] ] => dep_destruct E
              | [ |- context[if ?B then _ else _] ] => destruct B
            end; crush).
Qed.

(** It is also useful to know that the result of a call to [cond] is not changed by substituting new tests and bodies functions, so long as the new functions have the same input-output behavior as the old.  It turns out that, in Coq, it is not possible to prove in general that functions related in this way are equal.  We treat this issue with our discussion of axioms in a later chapter.  For now, it suffices to prove that the particular function [cond] is %\textit{%#<i>#extensional#</i>#%}%; that is, it is unaffected by substitution of functions with input-output equivalents. *)

Lemma cond_ext : forall (A : Set) (default : A) n (tests tests' : findex n -> bool)
  (bodies bodies' : findex n -> A),
  (forall idx, tests idx = tests' idx)
  -> (forall idx, bodies idx = bodies' idx)
  -> cond default tests bodies
  = cond default tests' bodies'.
  induction n; crush;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; crush.
Qed.

(** Now the final theorem is easy to prove.  We add our two lemmas as hints and perform standard automation with pattern-matching of subterms to destruct. *)
(* end thide *)

Theorem cfold_correct : forall t (e : exp' t),
  exp'Denote (cfold e) = exp'Denote e.
(* begin thide *)
  Hint Rewrite cfoldCond_correct : cpdt.
  Hint Resolve cond_ext.

  induction e; crush;
    repeat (match goal with
              | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
            end; crush).
Qed.
(* end thide *)


(** * Exercises *)

(** remove printing * *)

(** Some of the type family definitions from this chapter are duplicated in the [DepList] module of the book source.  Only the recursive versions of length-indexed and heterogeneous lists are included, and they are renamed without the [f] prefixes, e.g., [ilist] in place of [filist].

%\begin{enumerate}%#<ol>#

%\item%#<li># Define a tree analogue of [hlist].  That is, define a parameterized type of binary trees with data at their leaves, and define a type family [htree] indexed by trees.  The structure of an [htree] mirrors its index tree, with the type of each data element (which only occur at leaves) determined by applying a type function to the corresponding element of the index tree.  Define a type standing for all possible paths from the root of a tree to leaves and use it to implement a function [tget] for extracting an element of an [htree] by path.  Define a function [htmap2] for "mapping over two trees in parallel."  That is, [htmap2] takes in two [htree]s with the same index tree, and it forms a new [htree] with the same index by applying a binary function pointwise.

  Repeat this process so that you implement each definition for each of the three definition styles covered in this chapter: inductive, recursive, and index function.#</li>#

%\item%#<li># Write a dependently-typed interpreter for a simple programming language with ML-style pattern-matching.  The language is defined informally by this grammar:

  [[
t ::= bool | t + t
p ::= x | b | inl p | inr p
e ::= x | b | inl e | inr e | case e of [p => e]* | _ => e
]]

  [x] stands for a variable, and [b] stands for a boolean constant.  The production for [case] expressions means that a pattern-match includes zero or more pairs of patterns and expressions, along with a default case.

  Your interpreter should be implemented in the style demonstrated in this chapter.  That is, your definition of expressions should use dependent types and de Bruijn indices to combine syntax and typing rules, such that the type of an expression tells the types of variables that are in scope.  You should implement a simple recursive function translating types [t] to [Set], and your interpreter should produce values in the image of this translation.#</li>#

#</ol>#%\end{enumerate}% *)
