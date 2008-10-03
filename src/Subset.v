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


(** %\chapter{Subset Types and Variations}% *)

(** So far, we have seen many examples of what we might call "classical program verification."  We write programs, write their specifications, and then prove that the programs satisfy their specifications.  The programs that we have written in Coq have been normal functional programs that we could just as well have written in Haskell or ML.  In this chapter, we start investigating uses of %\textit{%#<i>#dependent types#</i>#%}% to integrate programming, specification, and proving into a single phase. *)


(** * Introducing Subset Types *)

(** Let us consider several ways of implementing the natural number predecessor function.  We start by displaying the definition from the standard library: *)

Print pred.
(** [[

pred = fun n : nat => match n with
                      | 0 => 0
                      | S u => u
                      end
     : nat -> nat
]] *)

(** We can use a new command, [Extraction], to produce an OCaml version of this function. *)

Extraction pred.

(** %\begin{verbatim}
(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u
\end{verbatim}%

#<pre>
(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u
</pre># *)

(** Returning 0 as the predecessor of 0 can come across as somewhat of a hack.  In some situations, we might like to be sure that we never try to take the predecessor of 0.  We can enforce this by giving [pred] a stronger, dependent type. *)

Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n return (n > 0 -> nat) with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

(** We expand the type of [pred] to include a %\textit{%#<i>#proof#</i>#%}% that its argument [n] is greater than 0.  When [n] is 0, we use the proof to derive a contradiction, which we can use to build a value of any type via a vacuous pattern match.  When [n] is a successor, we have no need for the proof and just return the answer.  The proof argument can be said to have a %\textit{%#<i>#dependent#</i>#%}% type, because its type depends on the %\textit{%#<i>#value#</i>#%}% of the argument [n].

There are two aspects of the definition of [pred_strong1] that may be surprising.  First, we took advantage of [Definition]'s syntactic sugar for defining function arguments in the case of [n], but we bound the proofs later with explicit [fun] expressions.  Second, there is the [return] clause for the [match], which we saw briefly in Chapter 2.  Let us see what happens if we write this function in the way that at first seems most natural. *)

(** [[
Definition pred_strong1' (n : nat) (pf : n > 0) : nat :=
  match n with
    | O => match zgtz pf with end
    | S n' => n'
  end.

  [[
Error: In environment
n : nat
pf : n > 0
The term "pf" has type "n > 0" while it is expected to have type 
"0 > 0"
]]

The term [zgtz pf] fails to type-check.  Somehow the type checker has failed to take into account information that follows from which [match] branch that term appears in.  The problem is that, by default, [match] does not let us use such implied information.  To get refined typing, we must always add special [match] annotations.

In this case, we must use a [return] annotation to declare the relationship between the %\textit{%#<i>#value#</i>#%}% of the [match] discriminee and the %\textit{%#<i>#type#</i>#%}% of the result.  There is no annotation that lets us declare a relationship between the discriminee and the type of a variable that is already in scope; hence, we delay the binding of [pf], so that we can use the [return] annotation to express the needed relationship.

Why does Coq not infer this relationship for us?  Certainly, it is not hard to imagine heuristics that would handle this particular case and many others.  In general, however, the inference problem is undecidable.  The known undecidable problem of %\textit{%#<i>#higher-order unification#</i>#%}% reduces to the [match] type inference problem.  Over time, Coq is enhanced with more and more heuristics to get around this problem, but there must always exist [match]es whose types Coq cannot infer without annotations.

Let us now take a look at the OCaml code Coq generates for [pred_strong1]. *)

Extraction pred_strong1.

(** %\begin{verbatim}
(** val pred_strong1 : nat -> nat **)

let pred_strong1 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
\end{verbatim}%

#<pre>
(** val pred_strong1 : nat -> nat **)

let pred_strong1 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
</pre># *)

(** The proof argument has disappeared!  We get exactly the OCaml code we would have written manually.  This is our first demonstration of the main technically interesting feature of Coq program extraction: program components of type [Prop] are erased systematically.

We can reimplement our dependently-typed [pred] based on %\textit{%#<i>#subset types#</i>#%}%, defined in the standard library with the type family [sig]. *)

Print sig.
(** [[

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P
For sig: Argument A is implicit
For exist: Argument A is implicit
]]

[sig] is a Curry-Howard twin of [ex], except that [sig] is in [Type], while [ex] is in [Prop].  That means that [sig] values can survive extraction, while [ex] proofs will always be erased.  The actual details of extraction of [sig]s are more subtle, as we will see shortly.

We rewrite [pred_strong1], using some syntactic sugar for subset types. *)

Locate "{ _ : _ | _ }".
(** [[

Notation            Scope     
"{ x : A  |  P }" := sig (fun x : A => P)
                      : type_scope
                      (default interpretation)
 ]] *)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist O pf => match zgtz pf with end
    | exist (S n') _ => n'
  end.

Extraction pred_strong2.

(** %\begin{verbatim}
(** val pred_strong2 : nat -> nat **)

let pred_strong2 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
\end{verbatim}%

#<pre>
(** val pred_strong2 : nat -> nat **)

let pred_strong2 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
</pre>#

We arrive at the same OCaml code as was extracted from [pred_strong1], which may seem surprising at first.  The reason is that a value of [sig] is a pair of two pieces, a value and a proof about it.  Extraction erases the proof, which reduces the constructor [exist] of [sig] to taking just a single argument.  An optimization eliminates uses of datatypes with single constructors taking single arguments, and we arrive back where we started.

We can continue on in the process of refining [pred]'s type.  Let us change its result type to capture that the output is really the predecessor of the input. *)

Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
    | exist 0 pf => match zgtz pf with end
    | exist (S n') _ => exist _ n' (refl_equal _)
  end.

(** The function [proj1_sig] extracts the base value from a subset type.  Besides the use of that function, the only other new thing is the use of the [exist] constructor to build a new [sig] value, and the details of how to do that follow from the output of our earlier [Print] command.

By now, the reader is probably ready to believe that the new [pred_strong] leads to the same OCaml code as we have seen several times so far, and Coq does not disappoint. *)

Extraction pred_strong3.

(** %\begin{verbatim}
(** val pred_strong3 : nat -> nat **)

let pred_strong3 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
\end{verbatim}%

#<pre>
(** val pred_strong3 : nat -> nat **)

let pred_strong3 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
</pre>#

We have managed to reach a type that is, in a formal sense, the most expressive possible for [pred].  Any other implementation of the same type must have the same input-output behavior.  However, there is still room for improvement in making this kind of code easier to write.  Here is a version that takes advantage of tactic-based theorem proving.  We switch back to passing a separate proof argument instead of using a subset type for the function's input, because this leads to cleaner code. *)

Definition pred_strong4 (n : nat) : n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n return (n > 0 -> {m : nat | n = S m}) with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end).

  (** We build [pred_strong4] using tactic-based proving, beginning with a [Definition] command that ends in a period before a definition is given.  Such a command enters the interactive proving mode, with the type given for the new identifier as our proof goal.  We do most of the work with the [refine] tactic, to which we pass a partial "proof" of the type we are trying to prove.  There may be some pieces left to fill in, indicated by underscores.  Any underscore that Coq cannot reconstruct with type inference is added as a proof subgoal.  In this case, we have two subgoals:

     [[

2 subgoals
  
  n : nat
  _ : 0 > 0
  ============================
   False
]]

[[

subgoal 2 is:
 S n' = S n'
 ]]

We can see that the first subgoal comes from the second underscore passed to [False_rec], and the second subgoal comes from the second underscore passed to [exist].  In the first case, we see that, though we bound the proof variable with an underscore, it is still available in our proof context.  It is hard to refer to underscore-named variables in manual proofs, but automation makes short work of them.  Both subgoals are easy to discharge that way, so let us back up and ask to prove all subgoals automatically. *)

  Undo.
  refine (fun n =>
    match n return (n > 0 -> {m : nat | n = S m}) with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end); crush.
Defined.

(** We end the "proof" with [Defined] instead of [Qed], so that the definition we constructed remains visible.  This contrasts to the case of ending a proof with [Qed], where the details of the proof are hidden afterward.  Let us see what our prooof script constructed. *)

Print pred_strong4.
(** [[

pred_strong4 = 
fun n : nat =>
match n as n0 return (n0 > 0 -> {m : nat | n0 = S m}) with
| 0 =>
    fun _ : 0 > 0 =>
    False_rec {m : nat | 0 = S m}
      (Bool.diff_false_true
         (Bool.absurd_eq_true false
            (Bool.diff_false_true
               (Bool.absurd_eq_true false (pred_strong4_subproof n _)))))
| S n' =>
    fun _ : S n' > 0 =>
    exist (fun m : nat => S n' = S m) n' (refl_equal (S n'))
end
     : forall n : nat, n > 0 -> {m : nat | n = S m}
]]

We see the code we entered, with some proofs filled in.  The first proof obligation, the second argument to [False_rec], is filled in with a nasty-looking proof term that we can be glad we did not enter by hand.  The second proof obligation is a simple reflexivity proof.

We are almost done with the ideal implementation of dependent predecessor.  We can use Coq's syntax extension facility to arrive at code with almost no complexity beyond a Haskell or ML program with a complete specification in a comment. *)

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_strong5 (n : nat) : n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n return (n > 0 -> {m : nat | n = S m}) with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end); crush.
Defined.


(** * Decidable Proposition Types *)

(** There is another type in the standard library which captures the idea of program values that indicate which of two propositions is true. *)

Print sumbool.
(** [[

Inductive sumbool (A : Prop) (B : Prop) : Set :=
    left : A -> {A} + {B} | right : B -> {A} + {B}
For left: Argument A is implicit
For right: Argument B is implicit
]] *)

(** We can define some notations to make working with [sumbool] more convenient. *)

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

(** The [Reduce] notation is notable because it demonstrates how [if] is overloaded in Coq.  The [if] form actually works when the test expression has any two-constructor inductive type.  Moreover, in the [then] and [else] branches, the appropriate constructor arguments are bound.  This is important when working with [sumbool]s, when we want to have the proof stored in the test expression available when proving the proof obligations generated in the appropriate branch.

Now we can write [eq_nat_dec], which compares two natural numbers, returning either a proof of their equality or a proof of their inequality. *)

Definition eq_nat_dec (n m : nat) : {n = m} + {n <> m}.
  refine (fix f (n m : nat) {struct n} : {n = m} + {n <> m} :=
    match n, m return {n = m} + {n <> m} with
      | O, O => Yes
      | S n', S m' => Reduce (f n' m')
      | _, _ => No
    end); congruence.
Defined.

(** Our definition extracts to reasonable OCaml code. *)

Extraction eq_nat_dec.

(** %\begin{verbatim}
(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S n0 -> Right)
    | S n' -> (match m with
                 | O -> Right
                 | S m' -> eq_nat_dec n' m')
\end{verbatim}%

#<pre>
(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S n0 -> Right)
    | S n' -> (match m with
                 | O -> Right
                 | S m' -> eq_nat_dec n' m')
</pre>#

Proving this kind of decidable equality result is so common that Coq comes with a tactic for automating it. *)

Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
  decide equality.
Defined.

(** Curious readers can verify that the [decide equality] version extracts to the same OCaml code as our more manual version does.  That OCaml code had one undesirable property, which is that it uses %\texttt{%#<tt>#Left#</tt>#%}% and %\texttt{%#<tt>#Right#</tt>#%}% constructors instead of the boolean values built into OCaml.  We can fix this, by using Coq's facility for mapping Coq inductive types to OCaml variant types. *)

Extract Inductive sumbool => "bool" ["true" "false"].
Extraction eq_nat_dec'.

(** %\begin{verbatim}
(** val eq_nat_dec' : nat -> nat -> bool **)

let rec eq_nat_dec' n m0 =
  match n with
    | O -> (match m0 with
              | O -> true
              | S n0 -> false)
    | S n0 -> (match m0 with
                 | O -> false
                 | S n1 -> eq_nat_dec' n0 n1)
\end{verbatim}%

#<pre>
(** val eq_nat_dec' : nat -> nat -> bool **)

let rec eq_nat_dec' n m0 =
  match n with
    | O -> (match m0 with
              | O -> true
              | S n0 -> false)
    | S n0 -> (match m0 with
                 | O -> false
                 | S n1 -> eq_nat_dec' n0 n1)
</pre># *)

(** %\smallskip%

We can build "smart" versions of the usual boolean operators and put them to good use in certified programming.  For instance, here is a [sumbool] version of boolean "or." *)

Notation "x || y" := (if x then Yes else Reduce y) (at level 50).

(** Let us use it for building a function that decides list membership.  We need to assume the existence of an equality decision procedure for the type of list elements. *)

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** The final function is easy to write using the techniques we have developed so far. *)

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + { ~In x ls}.
    refine (fix f (x : A) (ls : list A) {struct ls}
      : {In x ls} + { ~In x ls} :=
      match ls return {In x ls} + { ~In x ls} with
	| nil => No
	| x' :: ls' => A_eq_dec x x' || f x ls'
      end); crush.
  Qed.
End In_dec.

(** [In_dec] has a reasonable extraction to OCaml. *)

Extraction In_dec.

(** %\begin{verbatim}
(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec a_eq_dec x = function
  | Nil -> false
  | Cons (x', ls') ->
      (match a_eq_dec x x' with
         | true -> true
         | false -> in_dec a_eq_dec x ls')
\end{verbatim}%

#<pre>
(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec a_eq_dec x = function
  | Nil -> false
  | Cons (x', ls') ->
      (match a_eq_dec x x' with
         | true -> true
         | false -> in_dec a_eq_dec x ls')
</pre># *)


(** * Partial Subset Types *)

Inductive maybe (A : Type) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[[ x ]]" := (Found _ x _).

Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).


(** * A Type-Checking Example *)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

Inductive type : Set := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

Definition eq_type_dec : forall (t1 t2 : type), {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

Definition typeCheck (e : exp) : {{t | hasType e t}}.
  Hint Constructors hasType.

  refine (fix F (e : exp) : {{t | hasType e t}} :=
    match e return {{t | hasType e t}} with
      | Nat _ => [[TNat]]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;;
        eq_type_dec t2 TNat;;
        [[TNat]]
      | Bool _ => [[TBool]]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [[TBool]]
    end); crush.
Defined.

Eval simpl in typeCheck (Nat 0).
Eval simpl in typeCheck (Plus (Nat 1) (Nat 2)).
Eval simpl in typeCheck (Plus (Nat 1) (Bool false)).
