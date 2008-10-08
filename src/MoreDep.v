(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith Bool List.

Require Import Tactics MoreSpecif.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{More Dependent Types}% *)

(** Subset types and their relatives help us integrate verification with programming.  Though they reorganize the certified programmer's workflow, they tend not to have deep effects on proofs.  We write largely the same proofs as we would for classical verification, with some of the structure moved into the programs themselves.  It turns out that, when we use dependent types to their full potential, we warp the development and proving process even more than that, picking up "free theorems" to the extent that often a certified program is hardly more complex than its uncertified counterpart in Haskell or ML.

   In particular, we have only scratched the tip of the iceberg that is Coq's inductive definition mechanism.  The inductive types we have seen so far have their counterparts in the other proof assistants that we surveyed in Chapter 1.  This chapter explores the strange new world of dependent inductive datatypes (that is, dependent inductive types outside [Prop]), a possibility which sets Coq apart from all of the competition not based on type theory. *)


(** * Length-Indexed Lists *)

(** Many introductions to dependent types start out by showing how to use them to eliminate array bounds checks.  When the type of an array tells you how many elements it has, your compiler can detect out-of-bounds dereferences statically.  Since we are working in a pure functional language, the next best thing is length-indexed lists, which the following code defines. *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

(** We see that, within its section, [ilist] is given type [nat -> Set].  Previously, every inductive type we have seen has either had plain [Set] as its type or has been a predicate with some type ending in [Prop].  The full generality of inductive definitions lets us integrate the expressivity of predicates directly into our normal programming.

   The [nat] argument to [ilist] tells us the length of the list.  The types of [ilist]'s constructors tell us that a [Nil] list has length [O] and that a [Cons] list has length one greater than the length of its sublist.  We may apply [ilist] to any natural number, even natural numbers that are only known at runtime.  It is this breaking of the %\textit{%#<i>#phase distinction#</i>#%}% that characterizes [ilist] as %\textit{%#<i>#dependently typed#</i>#%}%.

   In expositions of list types, we usually see the length function defined first, but here that would not be a very productive function to code.  Instead, let us implement list concatenation.

   [[
Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) {struct ls1} : ilist (n1 + n2) :=
  match ls1 with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app ls1' ls2)
  end.

  Coq is not happy with this definition:

[[
The term "ls2" has type "ilist n2" while it is expected to have type
 "ilist (?14 + n2)"
]]

  We see the return of a problem we have considered before.  Without explicit annotations, Coq does not enrich our typing assumptions in the branches of a [match] expression.  It is clear that the unification variable [?14] should be resolved to 0 in this context, so that we have [0 + n2] reducing to [n2], but Coq does not realize that.  We cannot fix the problem using just the simple [return] clauses we applied in the last chapter.  We need to combine a [return] clause with a new kind of annotation, an [in] clause. *)

Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) {struct ls1} : ilist (n1 + n2) :=
  match ls1 in (ilist n1) return (ilist (n1 + n2)) with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app ls1' ls2)
  end.

(** This version of [app] passes the type checker.  Using [return] alone allowed us to express a dependency of the [match] result type on the %\textit{%#<i>#value#</i>#%}% of the discriminee.  What [in] adds to our arsenal is a way of expressing a dependency on the %\textit{%#<i>#type#</i>#%}% of the discriminee.  Specifically, the [n1] in the [in] clause above is a %\textit{%#<i>#binding occurrence#</i>#%}% whose scope is the [return] clause.

We may use [in] clauses only to bind names for the arguments of an inductive type family.  That is, each [in] clause must be an inductive type family name applied to a sequence of underscores and variable names of the proper length.  The positions for %\textit{%#<i>#parameters#</i>#%}% to the type family must all be underscores.  Parameters are those arguments declared with section variables or with entries to the left of the first colon in an inductive definition.  They cannot vary depending on which constructor was used to build the discriminee, so Coq prohibits pointless matches on them.  It is those arguments defined in the type to the right of the colon that we may name with [in] clauses.

Our [app] function could be typed in so-called %\textit{%#<i>#stratified#</i>#%}% type systems, which avoid true dependency.  We could consider the length indices to lists to live in a separate, compile-time-only universe from the lists themselves.  Our next example would be harder to implement in a stratified system.  We write an injection function from regular lists to length-indexed lists.  A stratified implementation would need to duplicate the definition of lists across compile-time and run-time versions, and the run-time versions would need to be indexed by the compile-time versions. *)

Fixpoint inject (ls : list A) : ilist (length ls) :=
  match ls return (ilist (length ls)) with
    | nil => Nil
    | h :: t => Cons h (inject t)
  end.

(** We can define an inverse conversion and prove that it really is an inverse. *)

Fixpoint unject n (ls : ilist n) {struct ls} : list A :=
  match ls with
    | Nil => nil
    | Cons _ h t => h :: unject t
  end.

Theorem inject_inverse : forall ls, unject (inject ls) = ls.
  induction ls; crush.
Qed.

(** Now let us attempt a function that is surprisingly tricky to write.  In ML, the list head function raises an exception when passed an empty list.  With length-indexed lists, we can rule out such invalid calls statically, and here is a first attempt at doing so.

[[
Definition hd n (ls : ilist (S n)) : A :=
  match ls with
    | Nil => ???
    | Cons _ h _ => h
  end.

It is not clear what to write for the [Nil] case, so we are stuck before we even turn our function over to the type checker.  We could try omitting the [Nil] case:

[[
Definition hd n (ls : ilist (S n)) : A :=
  match ls with
    | Cons _ h _ => h
  end.

[[
Error: Non exhaustive pattern-matching: no clause found for pattern Nil
]]

Unlike in ML, we cannot use inexhaustive pattern matching, becuase there is no conception of a %\texttt{%#<tt>#Match#</tt>#%}% exception to be thrown.  We might try using an [in] clause somehow.

[[
Definition hd n (ls : ilist (S n)) : A :=
  match ls in (ilist (S n)) with
    | Cons _ h _ => h
  end.

[[
Error: The reference n was not found in the current environment
]]

In this and other cases, we feel like we want [in] clauses with type family arguments that are not variables.  Unfortunately, Coq only supports variables in those positions.  A completely general mechanism could only be supported with a solution to the problem of higher-order unification, which is undecidable.  There %\textit{%#<i>#are#</i>#%}% useful heuristics for handling non-variable indices which are gradually making their way into Coq, but we will spend some time in this and the next few chapters on effective pattern matching on dependent types using only the primitive [match] annotations.

Our final, working attempt at [hd] uses an auxiliary function and a surprising [return] annotation. *)

Definition hd' n (ls : ilist n) :=
  match ls in (ilist n) return (match n with O => unit | S _ => A end) with
    | Nil => tt
    | Cons _ h _ => h
  end.

Definition hd n (ls : ilist (S n)) : A := hd' ls.

(** We annotate our main [match] with a type that is itself a [match].  We write that the function [hd'] returns [unit] when the list is empty and returns the carried type [A] in all other cases.  In the definition of [hd], we just call [hd'].  Because the index of [ls] is known to be nonzero, the type checker reduces the [match] in the type of [hd'] to [A]. *)

End ilist.


(** * A Tagless Interpreter *)

(** A favorite example for motivating the power of functional programming is implementation of a simple expression language interpreter.  In ML and Haskell, such interpreters are often implemented using an algebraic datatype of values, where at many points it is checked that a value was built with the right constructor of the value type.  With dependent types, we can implement a %\textit{%#<i>#tagless#</i>#%}% interpreter that both removes this source of runtime ineffiency and gives us more confidence that our implementation is correct. *)

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool

| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall t, exp Bool -> exp t -> exp t -> exp t

| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
| Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2.

(** We have a standard algebraic datatype [type], defining a type language of naturals, booleans, and product (pair) types.  Then we have the indexed inductive type [exp], where the argument to [exp] tells us the encoded type of an expression.  In effect, we are defining the typing rules for expressions simultaneously with the syntax.

   We can give types and expressions semantics in a new style, based critically on the chance for %\textit{%#<i>#type-level computation#</i>#%}%. *)

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end%type.

(** [typeDenote] compiles types of our object language into "native" Coq types.  It is deceptively easy to implement.  The only new thing we see is the [%type] annotation, which tells Coq to parse the [match] expression using the notations associated with types.  Without this annotation, the [*] would be interpreted as multiplication on naturals, rather than as the product type constructor.  [type] is one example of an identifer bound to a %\textit{%#<i>#notation scope#</i>#%}%.  We will deal more explicitly with notations and notation scopes in later chapters.

   We can define a function [expDenote] that is typed in terms of [typeDenote]. *)

Fixpoint expDenote t (e : exp t) {struct e} : typeDenote t :=
  match e in (exp t) return (typeDenote t) with
    | NConst n => n
    | Plus e1 e2 => expDenote e1 + expDenote e2
    | Eq e1 e2 => if eq_nat_dec (expDenote e1) (expDenote e2) then true else false

    | BConst b => b
    | And e1 e2 => expDenote e1 && expDenote e2
    | If _ e' e1 e2 => if expDenote e' then expDenote e1 else expDenote e2

    | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
    | Fst _ _ e' => fst (expDenote e')
    | Snd _ _ e' => snd (expDenote e')
  end.

(** Again we find that an [in] annotation is essential for type-checking a function.  Besides that, the definition is routine.  In fact, it is less complicated than what we would write in ML or Haskell 98, since we do not need to worry about pushing final values in and out of an algebraic datatype.  The only unusual thing is the use of an expression of the form [if E then true else false] in the [Eq] case.  Remember that [eq_nat_dec] has a rich dependent type, rather than a simple boolean type.  Coq's native [if] is overloaded to work on a test of any two-constructor type, so we can use [if] to build a simple boolean from the [sumbool] that [eq_nat_dec] returns.

   We can implement our old favorite, a constant folding function, and prove it correct.  It will be useful to write a function [pairOut] that checks if an [exp] of [Prod] type is a pair, returning its two components if so.  Unsurprisingly, a first attempt leads to a type error.

[[
Definition pairOut t1 t2 (e : exp (Prod t1 t2)) : option (exp t1 * exp t2) :=
  match e in (exp (Prod t1 t2)) return option (exp t1 * exp t2) with
    | Pair _ _ e1 e2 => Some (e1, e2)
    | _ => None
  end.

[[
Error: The reference t2 was not found in the current environment
]]

We run again into the problem of not being able to specify non-variable arguments in [in] clauses.  The problem would just be hopeless without a use of an [in] clause, though, since the result type of the [match] depends on an argument to [exp].  Our solution will be to use a more general type, as we did for [hd].  First, we define a type-valued function to use in assigning a type to [pairOut]. *)

Definition pairOutType (t : type) :=
  match t with
    | Prod t1 t2 => option (exp t1 * exp t2)
    | _ => unit
  end.

(** When passed a type that is a product, [pairOutType] returns our final desired type.  On any other input type, [pairOutType] returns [unit], since we do not care about extracting components of non-pairs.  Now we can write another helper function to provide the default behavior of [pairOut], which we will apply for inputs that are not literal pairs. *)

Definition pairOutDefault (t : type) :=
  match t return (pairOutType t) with
    | Prod _ _ => None
    | _ => tt
  end.

(** Now [pairOut] is deceptively easy to write. *)

Definition pairOut t (e : exp t) :=
  match e in (exp t) return (pairOutType t) with
    | Pair _ _ e1 e2 => Some (e1, e2)
    | _ => pairOutDefault _
  end.

(** There is one important subtlety in this definition.  Coq allows us to use convenient ML-style pattern matching notation, but, internally and in proofs, we see that patterns are expanded out completely, matching one level of inductive structure at a time.  Thus, the default case in the [match] above expands out to one case for each constructor of [exp] besides [Pair], and the underscore in [pairOutDefault _] is resolved differently in each case.  From an ML or Haskell programmer's perspective, what we have here is type inference determining which code is run (returning either [None] or [tt]), which goes beyond what is possible with type inference guiding parametric polymorphism in Hindley-Milner languages, but is similar to what goes on with Haskell type classes.

With [pairOut] available, we can write [cfold] in a straightforward way.  There are really no surprises beyond that Coq verifies that this code has such an expressive type, given the small annotation burden. *)

Fixpoint cfold t (e : exp t) {struct e} : exp t :=
  match e in (exp t) return (exp t) with
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
    | And e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | BConst b1, BConst b2 => BConst (b1 && b2)
        | _, _ => And e1' e2'
      end
    | If _ e e1 e2 =>
      let e' := cfold e in
      match e' with
        | BConst true => cfold e1
        | BConst false => cfold e2
        | _ => If e' (cfold e1) (cfold e2)
      end

    | Pair _ _ e1 e2 => Pair (cfold e1) (cfold e2)
    | Fst _ _ e =>
      let e' := cfold e in
      match pairOut e' with
        | Some p => fst p
        | None => Fst e'
      end
    | Snd _ _ e =>
      let e' := cfold e in
      match pairOut e' with
        | Some p => snd p
        | None => Snd e'
      end
  end.

(** The correctness theorem for [cfold] turns out to be easy to prove, once we get over one serious hurdle. *)

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
  induction e; crush.

(** The first remaining subgoal is:

   [[

  expDenote (cfold e1) + expDenote (cfold e2) =
   expDenote
     match cfold e1 with
     | NConst n1 =>
         match cfold e2 with
         | NConst n2 => NConst (n1 + n2)
         | Plus _ _ => Plus (cfold e1) (cfold e2)
         | Eq _ _ => Plus (cfold e1) (cfold e2)
         | BConst _ => Plus (cfold e1) (cfold e2)
         | And _ _ => Plus (cfold e1) (cfold e2)
         | If _ _ _ _ => Plus (cfold e1) (cfold e2)
         | Pair _ _ _ _ => Plus (cfold e1) (cfold e2)
         | Fst _ _ _ => Plus (cfold e1) (cfold e2)
         | Snd _ _ _ => Plus (cfold e1) (cfold e2)
         end
     | Plus _ _ => Plus (cfold e1) (cfold e2)
     | Eq _ _ => Plus (cfold e1) (cfold e2)
     | BConst _ => Plus (cfold e1) (cfold e2)
     | And _ _ => Plus (cfold e1) (cfold e2)
     | If _ _ _ _ => Plus (cfold e1) (cfold e2)
     | Pair _ _ _ _ => Plus (cfold e1) (cfold e2)
     | Fst _ _ _ => Plus (cfold e1) (cfold e2)
     | Snd _ _ _ => Plus (cfold e1) (cfold e2)
     end
     ]]

     We would like to do a case analysis on [cfold e1], and we attempt that in the way that has worked so far.

     [[
  destruct (cfold e1).

  [[
User error: e1 is used in hypothesis e
]]

    Coq gives us another cryptic error message.  Like so many others, this one basically means that Coq is not able to build some proof about dependent types.  It is hard to generate helpful and specific error messages for problems like this, since that would require some kind of understanding of the dependency structure of a piece of code.  We will encounter many examples of case-specific tricks for recovering from errors like this one.

    For our current proof, we can use a tactic [dep_destruct] defined in the book [Tactics] module.  General elimination/inversion of dependently-typed hypotheses is undecidable, since it must be implemented with [match] expressions that have the restriction on [in] clauses that we have already discussed.  [dep_destruct] makes a best effort to handle some common cases.  In a future chapter, we will learn about the explicit manipulation of equality proofs that is behind [dep_destruct]'s implementation in Ltac, but for now, we treat it as a useful black box. *)
  
  dep_destruct (cfold e1).

  (** This successfully breaks the subgoal into 5 new subgoals, one for each constructor of [exp] that could produce an [exp Nat].  Note that [dep_destruct] is successful in ruling out the other cases automatically, in effect automating some of the work that we have done manually in implementing functions like [hd] and [pairOut].

     This is the only new trick we need to learn to complete the proof.  We can back up and give a short, automated proof. *)

  Restart.

  induction e; crush;
    repeat (match goal with
              | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
              | [ |- (if ?E then _ else _) = _ ] => destruct E
            end; crush).
Qed.


(** Dependently-Typed Red-Black Trees *)

Inductive color : Set := Red | Black.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat-> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).

Require Import Max Min.

Section depth.
  Variable f : nat -> nat -> nat.

  Fixpoint depth c n (t : rbtree c n) {struct t} : nat :=
    match t with
      | Leaf => 0
      | RedNode _ t1 _ t2 => S (f (depth t1) (depth t2))
      | BlackNode _ _ _ t1 _ t2 => S (f (depth t1) (depth t2))
    end.
End depth.

Theorem depth_min : forall c n (t : rbtree c n), depth min t >= n.
  induction t; crush;
    match goal with
      | [ |- context[min ?X ?Y] ] => destruct (min_dec X Y)
    end; crush.
Qed.

Lemma depth_max' : forall c n (t : rbtree c n), match c with
                                                  | Red => depth max t <= 2 * n + 1
                                                  | Black => depth max t <= 2 * n
                                                end.
  induction t; crush;
    match goal with
      | [ |- context[max ?X ?Y] ] => destruct (max_dec X Y)
    end; crush.

  destruct c1; crush.
  destruct c2; crush.
Qed.

Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 2 * n + 1.
  intros; generalize (depth_max' t); destruct c; crush.
Qed.

Theorem balanced : forall c n (t : rbtree c n), 2 * depth min t + 1 >= depth max t.
  intros; generalize (depth_min t); generalize (depth_max t); crush.
Qed.


Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.

Notation "{< x >}" := (existT _ _ x).

Definition balance1 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n -> { c : color & rbtree c (S n) } with
    | RedNode' _ _ _ t1 y t2 =>
      match t1 in rbtree c n return rbtree _ n -> rbtree c2 n -> { c : color & rbtree c (S n) } with
        | RedNode _ a x b => fun c d => {<RedNode (BlackNode a x b) y (BlackNode c data d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree _ n -> rbtree c2 n -> { c : color & rbtree c (S n) } with
            | RedNode _ b x c => fun a d => {<RedNode (BlackNode a y b) x (BlackNode c data d)>}
            | b => fun a t => {<BlackNode (RedNode a y b) data t>}
          end t1'
      end t2
  end.

Definition balance2 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n -> { c : color & rbtree c (S n) } with
    | RedNode' _ _ _ t1 z t2 =>
      match t1 in rbtree c n return rbtree _ n -> rbtree c2 n -> { c : color & rbtree c (S n) } with
        | RedNode _ b y c => fun d a => {<RedNode (BlackNode a data b) y (BlackNode c z d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree _ n -> rbtree c2 n -> { c : color & rbtree c (S n) } with
            | RedNode _ c z' d => fun b a => {<RedNode (BlackNode a data b) z (BlackNode c z' d)>}
            | b => fun a t => {<BlackNode t data (RedNode a z b)>}
          end t1'
      end t2
  end.

Section present.
  Variable x : nat.

  Fixpoint present c n (t : rbtree c n) {struct t} : Prop :=
    match t with
      | Leaf => False
      | RedNode _ a y b => present a \/ x = y \/ present b
      | BlackNode _ _ _ a y b => present a \/ x = y \/ present b
    end.

  Definition rpresent n (t : rtree n) : Prop :=
    match t with
      | RedNode' _ _ _ a y b => present a \/ x = y \/ present b
    end.
End present.

Section insert.
  Variable x : nat.

  Definition insResult c n :=
    match c with
      | Red => rtree n
      | Black => { c' : color & rbtree c' n }
    end.

  Fixpoint ins c n (t : rbtree c n) {struct t} : insResult c n :=
    match t in (rbtree c n) return (insResult c n) with
      | Leaf => {< RedNode Leaf x Leaf >}
      | RedNode _ a y b =>
        if le_lt_dec x y
          then RedNode' (projT2 (ins a)) y b
          else RedNode' a y (projT2 (ins b))
      | BlackNode c1 c2 _ a y b =>
        if le_lt_dec x y
          then
            match c1 return insResult c1 _ -> _ with
              | Red => fun ins_a => balance1 ins_a y b
              | _ => fun ins_a => {< BlackNode (projT2 ins_a) y b >}
            end (ins a)
          else
            match c2 return insResult c2 _ -> _ with
              | Red => fun ins_b => balance2 ins_b y a
              | _ => fun ins_b => {< BlackNode a y (projT2 ins_b) >}
            end (ins b)
    end.

  Definition insertResult c n :=
    match c with
      | Red => rbtree Black (S n)
      | Black => { c' : color & rbtree c' n }
    end.

  Definition makeBlack c n : insResult c n -> insertResult c n :=
    match c return insResult c n -> insertResult c n with
      | Red => fun r =>
        match r in rtree n return insertResult Red n with
          | RedNode' _ _ _ a x b => BlackNode a x b
        end
      | Black => fun r => r
    end.

  Implicit Arguments makeBlack [c n].

  Definition insert c n (t : rbtree c n) : insertResult c n :=
    makeBlack (ins t).

  Record rbtree' : Set := Rbtree' {
    rtC : color;
    rtN : nat;
    rtT : rbtree rtC rtN
  }.

  Section present.
    Variable z : nat.

    Lemma present_balance1 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n) ,
      present z (projT2 (balance1 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
      destruct a; crush;
        repeat match goal with
                 | [ H : context[match ?T with
                                   | Leaf => _
                                   | RedNode _ _ _ _ => _
                                   | BlackNode _ _ _ _ _ _ => _
                                 end] |- _ ] => pose T; dep_destruct T; crush
                 | [ |- context[match ?T with
                                  | Leaf => _
                                  | RedNode _ _ _ _ => _
                                  | BlackNode _ _ _ _ _ _ => _
                                end] ] => pose T; dep_destruct T; crush
               end.
    Qed.

    Lemma present_balance2 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n) ,
      present z (projT2 (balance2 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
      destruct a; crush;
        repeat match goal with
                 | [ H : context[match ?T with
                                   | Leaf => _
                                   | RedNode _ _ _ _ => _
                                   | BlackNode _ _ _ _ _ _ => _
                                 end] |- _ ] => pose T; dep_destruct T; crush
                 | [ |- context[match ?T with
                                  | Leaf => _
                                  | RedNode _ _ _ _ => _
                                  | BlackNode _ _ _ _ _ _ => _
                                end] ] => pose T; dep_destruct T; crush
               end.
    Qed.

    Definition present_insResult c n :=
      match c return (rbtree c n -> insResult c n -> Prop) with
        | Red => fun t r => rpresent z r <-> z = x \/ present z t
        | Black => fun t r => present z (projT2 r) <-> z = x \/ present z t
      end.

    Theorem present_ins : forall c n (t : rbtree c n),
      present_insResult t (ins t).
      induction t; crush;
        repeat (match goal with
                  | [ H : context[if ?E then _ else _] |- _ ] => destruct E
                  | [ |- context[if ?E then _ else _] ] => destruct E
                  | [ H : context[match ?C with Red => _ | Black => _ end] |- _ ] => destruct C
                end; crush);
        try match goal with
              | [ H : context[balance1 ?A ?B ?C] |- _ ] =>
                generalize (present_balance1 A B C)
            end;
        try match goal with
              | [ H : context[balance2 ?A ?B ?C] |- _ ] =>
                generalize (present_balance2 A B C)
            end;
        try match goal with
              | [ |- context[balance1 ?A ?B ?C] ] =>
                generalize (present_balance1 A B C)
            end;
        try match goal with
              | [ |- context[balance2 ?A ?B ?C] ] =>
                generalize (present_balance2 A B C)
            end;
        intuition;
          match goal with
            | [ z : nat, x : nat |- _ ] =>
              match goal with
                | [ H : z = x |- _ ] => rewrite H in *; clear H
              end
          end;
          tauto.
    Qed.

    Theorem present_insert_Red : forall n (t : rbtree Red n),
      present z (insert t)
      <-> (z = x \/ present z t).
      unfold insert; inversion t;
        generalize (present_ins t); simpl;
          dep_destruct (ins t); tauto.
    Qed.

    Theorem present_insert_Black : forall n (t : rbtree Black n),
      present z (projT2 (insert t))
      <-> (z = x \/ present z t).
      unfold insert; inversion t;
        generalize (present_ins t); simpl;
          dep_destruct (ins t); tauto.
    Qed.
  End present.
End insert.


(** * A Certified Regular Expression Matcher *)

(** Another interesting example is regular expressions with dependent types that express which predicates over strings particular regexps implement.  We can then assign a dependent type to a regular expression matching function, guaranteeing that it always decides the string property that we expect it to decide.

   Before defining the syntax of expressions, it is helpful to define an inductive type capturing the meaning of the Kleene star.  We use Coq's string support, which comes through a combination of the [Strings] library and some parsing notations built into Coq.  Operators like [++] and functions like [length] that we know from lists are defined again for strings.  Notation scopes help us control which versions we want to use in particular contexts. *)

Require Import Ascii String.
Open Scope string_scope.

Section star.
  Variable P : string -> Prop.

  Inductive star : string -> Prop :=
  | Empty : star ""
  | Iter : forall s1 s2,
    P s1
    -> star s2
    -> star (s1 ++ s2).
End star.

(** Now we can make our first attempt at defining a [regexp] type that is indexed by predicates on strings.  Here is a reasonable-looking definition that is restricted to constant characters and concatenation.

[[
Inductive regexp : (string -> Prop) -> Set :=
| Char : forall ch : ascii,
  regexp (fun s => s = String ch "")
| Concat : forall (P1 P2 : string -> Prop) (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2).

[[
User error: Large non-propositional inductive types must be in Type
]]

What is a large inductive type?  In Coq, it is an inductive type that has a constructor which quantifies over some type of type [Type].  We have not worked with [Type] very much to this point.  Every term of CIC has a type, including [Set] and [Prop], which are assigned type [Type].  The type [string -> Prop] from the failed definition also has type [Type].

It turns out that allowing large inductive types in [Set] leads to contradictions when combined with certain kinds of classical logic reasoning.  Thus, by default, such types are ruled out.  There is a simple fix for our [regexp] definition, which is to place our new type in [Type].  While fixing the problem, we also expand the list of constructors to cover the remaining regular expression operators. *)

Inductive regexp : (string -> Prop) -> Type :=
| Char : forall ch : ascii,
  regexp (fun s => s = String ch "")
| Concat : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2)
| Or : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => P1 s \/ P2 s)
| Star : forall P (r : regexp P),
  regexp (star P).

(** Many theorems about strings are useful for implementing a certified regexp matcher, and few of them are in the [Strings] library.  The book source includes statements, proofs, and hint commands for a handful of such omittted theorems.  Since they are orthogonal to our use of dependent types, we hide them in the rendered versions of this book. *)

(* begin hide *)
Open Scope specif_scope.

Lemma length_emp : length "" <= 0.
  crush.
Qed.

Lemma append_emp : forall s, s = "" ++ s.
  crush.
Qed.

Ltac substring :=
  crush;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] => destruct N; crush
         end.

Lemma substring_le : forall s n m,
  length (substring n m s) <= m.
  induction s; substring.
Qed.

Lemma substring_all : forall s,
  substring 0 (length s) s = s.
  induction s; substring.
Qed.

Lemma substring_none : forall s n,
  substring n 0 s = "".
  induction s; substring.
Qed.

Hint Rewrite substring_all substring_none : cpdt.

Lemma substring_split : forall s m,
  substring 0 m s ++ substring m (length s - m) s = s.
  induction s; substring.
Qed.

Lemma length_app1 : forall s1 s2,
  length s1 <= length (s1 ++ s2).
  induction s1; crush.
Qed.

Hint Resolve length_emp append_emp substring_le substring_split length_app1.

Lemma substring_app_fst : forall s2 s1 n,
  length s1 = n
  -> substring 0 n (s1 ++ s2) = s1.
  induction s1; crush.
Qed.

Lemma substring_app_snd : forall s2 s1 n,
  length s1 = n
  -> substring n (length (s1 ++ s2) - n) (s1 ++ s2) = s2.
  Hint Rewrite <- minus_n_O : cpdt.

  induction s1; crush.
Qed.

Hint Rewrite substring_app_fst substring_app_snd using (trivial; fail) : cpdt.
(* end hide *)

(** A few auxiliary functions help us in our final matcher definition.  The function [split] will be used to implement the regexp concatenation case. *)

Section split.
  Variables P1 P2 : string -> Prop.
  Variable P1_dec : forall s, {P1 s} + { ~P1 s}.
  Variable P2_dec : forall s, {P2 s} + { ~P2 s}.
  (** We require a choice of two arbitrary string predicates and functions for deciding them. *)

  Variable s : string.
  (** Our computation will take place relative to a single fixed string, so it is easiest to make it a [Variable], rather than an explicit argument to our functions. *)

  (** [split'] is the workhorse behind [split].  It searches through the possible ways of splitting [s] into two pieces, checking the two predicates against each such pair.  [split'] progresses right-to-left, from splitting all of [s] into the first piece to splitting all of [s] into the second piece.  It takes an extra argument, [n], which specifies how far along we are in this search process. *)

  Definition split' (n : nat) : n <= length s
    -> {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2}
    + {forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> ~P1 s1 \/ ~P2 s2}.
    refine (fix F (n : nat) : n <= length s
      -> {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2}
      + {forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> ~P1 s1 \/ ~P2 s2} :=
      match n return n <= length s
        -> {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2}
        + {forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> ~P1 s1 \/ ~P2 s2} with
        | O => fun _ => Reduce (P1_dec "" && P2_dec s)
        | S n' => fun _ => (P1_dec (substring 0 (S n') s)
            && P2_dec (substring (S n') (length s - S n') s))
          || F n' _
      end); clear F; crush; eauto 7;
    match goal with
      | [ _ : length ?S <= 0 |- _ ] => destruct S
      | [ _ : length ?S' <= S ?N |- _ ] =>
        generalize (eq_nat_dec (length S') (S N)); destruct 1
    end; crush.
  Defined.

  (** There is one subtle point in the [split'] code that is worth mentioning.  The main body of the function is a [match] on [n].  In the case where [n] is known to be [S n'], we write [S n'] in several places where we might be tempted to write [n].  However, without further work to craft proper [match] annotations, the type-checker does not use the equality between [n] and [S n'].  Thus, it is common to see patterns repeated in [match] case bodies in dependently-typed Coq code.  We can at least use a [let] expression to avoid copying the pattern more than once, replacing the first case body with:

     [[

        | S n' => fun _ => let n := S n' in
          (P1_dec (substring 0 n s)
            && P2_dec (substring n (length s - n) s))
          || F n' _
     ]]

     [split] itself is trivial to implement in terms of [split'].  We just ask [split'] to begin its search with [n = length s]. *)

  Definition split : {exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2}
    + {forall s1 s2, s = s1 ++ s2 -> ~P1 s1 \/ ~P2 s2}.
    refine (Reduce (split' (n := length s) _)); crush; eauto.
  Defined.
End split.

Implicit Arguments split [P1 P2].

(* begin hide *)
Lemma app_empty_end : forall s, s ++ "" = s.
  induction s; crush.
Qed.

Hint Rewrite app_empty_end : cpdt.

Lemma substring_self : forall s n,
  n <= 0
  -> substring n (length s - n) s = s.
  induction s; substring.
Qed.

Lemma substring_empty : forall s n m,
  m <= 0
  -> substring n m s = "".
  induction s; substring.
Qed.

Hint Rewrite substring_self substring_empty using omega : cpdt.

Lemma substring_split' : forall s n m,
  substring n m s ++ substring (n + m) (length s - (n + m)) s
  = substring n (length s - n) s.
  Hint Rewrite substring_split : cpdt.

  induction s; substring.
Qed.

Lemma substring_stack : forall s n2 m1 m2,
  m1 <= m2
  -> substring 0 m1 (substring n2 m2 s)
  = substring n2 m1 s.
  induction s; substring.
Qed.

Ltac substring' :=
  crush;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] => case_eq N; crush
         end.

Lemma substring_stack' : forall s n1 n2 m1 m2,
  n1 + m1 <= m2
  -> substring n1 m1 (substring n2 m2 s)
  = substring (n1 + n2) m1 s.
  induction s; substring';
    match goal with
      | [ |- substring ?N1 _ _ = substring ?N2 _ _ ] =>
        replace N1 with N2; crush
    end.
Qed.

Lemma substring_suffix : forall s n,
  n <= length s
  -> length (substring n (length s - n) s) = length s - n.
  induction s; substring.
Qed.

Lemma substring_suffix_emp' : forall s n m,
  substring n (S m) s = ""
  -> n >= length s.
  induction s; crush;
    match goal with
      | [ |- ?N >= _ ] => destruct N; crush
    end;
    match goal with
      [ |- S ?N >= S ?E ] => assert (N >= E); [ eauto | omega ]
    end.
Qed.

Lemma substring_suffix_emp : forall s n m,
  substring n m s = ""
  -> m > 0
  -> n >= length s.
  destruct m as [| m]; [crush | intros; apply substring_suffix_emp' with m; assumption].
Qed.

Hint Rewrite substring_stack substring_stack' substring_suffix
  using omega : cpdt.

Lemma minus_minus : forall n m1 m2,
  m1 + m2 <= n
  -> n - m1 - m2 = n - (m1 + m2).
  intros; omega.
Qed.

Lemma plus_n_Sm' : forall n m : nat, S (n + m) = m + S n.
  intros; omega.
Qed.

Hint Rewrite minus_minus using omega : cpdt.
(* end hide *)

(** One more helper function will come in handy: [dec_star], for implementing another linear search through ways of splitting a string, this time for implementing the Kleene star. *)

Section dec_star.
  Variable P : string -> Prop.
  Variable P_dec : forall s, {P s} + { ~P s}.

  (** Some new lemmas and hints about the [star] type family are useful here.  We omit them here; they are included in the book source at this point. *)

  (* begin hide *)
  Hint Constructors star.

  Lemma star_empty : forall s,
    length s = 0
    -> star P s.
    destruct s; crush.
  Qed.

  Lemma star_singleton : forall s, P s -> star P s.
    intros; rewrite <- (app_empty_end s); auto.
  Qed.

  Lemma star_app : forall s n m,
    P (substring n m s)
    -> star P (substring (n + m) (length s - (n + m)) s)
    -> star P (substring n (length s - n) s).
    induction n; substring;
      match goal with
        | [ H : P (substring ?N ?M ?S) |- _ ] =>
          solve [ rewrite <- (substring_split S M); auto
            | rewrite <- (substring_split' S N M); auto ]
      end.
  Qed.

  Hint Resolve star_empty star_singleton star_app.

  Variable s : string.

  Lemma star_inv : forall s,
    star P s
    -> s = ""
    \/ exists i, i < length s
      /\ P (substring 0 (S i) s)
      /\ star P (substring (S i) (length s - S i) s).
    Hint Extern 1 (exists i : nat, _) =>
      match goal with
        | [ H : P (String _ ?S) |- _ ] => exists (length S); crush
      end.

    induction 1; [
      crush
      | match goal with
          | [ _ : P ?S |- _ ] => destruct S; crush
        end
    ].
  Qed.    

  Lemma star_substring_inv : forall n,
    n <= length s
    -> star P (substring n (length s - n) s)
    -> substring n (length s - n) s = ""
    \/ exists l, l < length s - n
      /\ P (substring n (S l) s)
      /\ star P (substring (n + S l) (length s - (n + S l)) s).
    Hint Rewrite plus_n_Sm' : cpdt.

    intros;
      match goal with
        | [ H : star _ _ |- _ ] => generalize (star_inv H); do 3 crush; eauto
      end.
  Qed.
  (* end hide *)

  (** The function [dec_star''] implements a single iteration of the star.  That is, it tries to find a string prefix matching [P], and it calls a parameter function on the remainder of the string. *)

  Section dec_star''.
    Variable n : nat.
    (** [n] is the length of the prefix of [s] that we have already processed. *)

    Variable P' : string -> Prop.
    Variable P'_dec : forall n' : nat, n' > n
      -> {P' (substring n' (length s - n') s)}
      + { ~P' (substring n' (length s - n') s)}.
    (** When we use [dec_star''], we will instantiate [P'_dec] with a function for continuing the search for more instances of [P] in [s]. *)

    (** Now we come to [dec_star''] itself.  It takes as an input a natural [l] that records how much of the string has been searched so far, as we did for [split'].  The return type expresses that [dec_star''] is looking for an index into [s] that splits [s] into a nonempty prefix and a suffix, such that the prefix satisfies [P] and the suffix satisfies [P']. *)

    Definition dec_star'' (l : nat)
      : {exists l', S l' <= l
        /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)}
      + {forall l', S l' <= l
        -> ~P (substring n (S l') s)
        \/ ~P' (substring (n + S l') (length s - (n + S l')) s)}.
      refine (fix F (l : nat) : {exists l', S l' <= l
        /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)}
      + {forall l', S l' <= l
        -> ~P (substring n (S l') s)
        \/ ~P' (substring (n + S l') (length s - (n + S l')) s)} :=
      match l return {exists l', S l' <= l
        /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)}
      + {forall l', S l' <= l ->
        ~P (substring n (S l') s)
        \/ ~P' (substring (n + S l') (length s - (n + S l')) s)} with
        | O => _
        | S l' =>
          (P_dec (substring n (S l') s) && P'_dec (n' := n + S l') _)
          || F l'
      end); clear F; crush; eauto 7;
      match goal with
        | [ H : ?X <= S ?Y |- _ ] => destruct (eq_nat_dec X (S Y)); crush
      end.
    Defined.
  End dec_star''.

  (* begin hide *)
  Lemma star_length_contra : forall n,
    length s > n
    -> n >= length s
    -> False.
    crush.
  Qed.

  Lemma star_length_flip : forall n n',
    length s - n <= S n'
    -> length s > n
    -> length s - n > 0.
    crush.
  Qed.

  Hint Resolve star_length_contra star_length_flip substring_suffix_emp.
  (* end hide *)

  (** The work of [dec_star''] is nested inside another linear search by [dec_star'], which provides the final functionality we need, but for arbitrary suffixes of [s], rather than just for [s] overall. *)
  
  Definition dec_star' (n n' : nat) : length s - n' <= n
    -> {star P (substring n' (length s - n') s)}
    + { ~star P (substring n' (length s - n') s)}.
    refine (fix F (n n' : nat) {struct n} : length s - n' <= n
      -> {star P (substring n' (length s - n') s)}
      + { ~star P (substring n' (length s - n') s)} :=
      match n return length s - n' <= n
        -> {star P (substring n' (length s - n') s)}
        + { ~star P (substring n' (length s - n') s)} with
        | O => fun _ => Yes
        | S n'' => fun _ =>
          le_gt_dec (length s) n'
          || dec_star'' (n := n') (star P) (fun n0 _ => Reduce (F n'' n0 _)) (length s - n')
      end); clear F; crush; eauto;
    match goal with
      | [ H : star _ _ |- _ ] => apply star_substring_inv in H; crush; eauto
    end;
    match goal with
      | [ H1 : _ < _ - _, H2 : forall l' : nat, _ <= _ - _ -> _ |- _ ] =>
        generalize (H2 _ (lt_le_S _ _ H1)); tauto
    end.
  Defined.

  (** Finally, we have [dec_star].  It has a straightforward implementation.  We introduce a spurious match on [s] so that [simpl] will know to reduce calls to [dec_star].  The heuristic that [simpl] uses is only to unfold identifier definitions when doing so would simplify some [match] expression. *)

  Definition dec_star : {star P s} + { ~star P s}.
    refine (match s with
              | "" => Reduce (dec_star' (n := length s) 0 _)
              | _ => Reduce (dec_star' (n := length s) 0 _)
            end); crush.
  Defined.
End dec_star.

(* begin hide *)
Lemma app_cong : forall x1 y1 x2 y2,
  x1 = x2
  -> y1 = y2
  -> x1 ++ y1 = x2 ++ y2.
  congruence.
Qed.

Hint Resolve app_cong.
(* end hide *)

(** With these helper functions completed, the implementation of our [matches] function is refreshingly straightforward.  We only need one small piece of specific tactic work beyond what [crush] does for us. *)

Definition matches P (r : regexp P) s : {P s} + { ~P s}.
  refine (fix F P (r : regexp P) s : {P s} + { ~P s} :=
    match r with
      | Char ch => string_dec s (String ch "")
      | Concat _ _ r1 r2 => Reduce (split (F _ r1) (F _ r2) s)
      | Or _ _ r1 r2 => F _ r1 s || F _ r2 s
      | Star _ r => dec_star _ _ _
    end); crush;
  match goal with
    | [ H : _ |- _ ] => generalize (H _ _ (refl_equal _))
  end; tauto.
Defined.

(* begin hide *)
Example hi := Concat (Char "h"%char) (Char "i"%char).
Eval simpl in matches hi "hi".
Eval simpl in matches hi "bye".

Example a_b := Or (Char "a"%char) (Char "b"%char).
Eval simpl in matches a_b "".
Eval simpl in matches a_b "a".
Eval simpl in matches a_b "aa".
Eval simpl in matches a_b "b".

Example a_star := Star (Char "a"%char).
Eval simpl in matches a_star "".
Eval simpl in matches a_star "a".
Eval simpl in matches a_star "b".
Eval simpl in matches a_star "aa".
(* end hide *)
