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


(** I will start off by jumping right in to a fully-worked set of examples, building certified compilers from increasingly complicated source languages to stack machines.  We will meet a few useful tactics and see how they can be used in manual proofs, and we will also see how easily these proofs can be automated instead.  I assume that you have installed Coq and Proof General.

As always, you can step through the source file %\texttt{%#<tt>#StackMachine.v#</tt>#%}% for this chapter interactively in Proof General.  Alternatively, to get a feel for the whole lifecycle of creating a Coq development, you can enter the pieces of source code in this chapter in a new %\texttt{%#<tt>#.v#</tt>#%}% file in an Emacs buffer.  If you do the latter, include a line [Require Import List Tactics] at the start of the file, to match some code hidden from the chapter source, and be sure to run the Coq binary %\texttt{%#<tt>#coqtop#</tt>#%}% with the command-line argument %\texttt{%#<tt>#-I SRC#</tt>#%}%, where %\texttt{%#<tt>#SRC#</tt>#%}% is the path to a directory containing the source for this book.  In either case, if you have installed Proof General properly, it should start automatically when you visit a %\texttt{%#<tt>#.v#</tt>#%}% buffer in Emacs.

With Proof General, the portion of a buffer that Coq has processed is highlighted in some way, like being given a blue background.  You step through Coq source files by positioning the point at the position you want Coq to run to and pressing C-C C-RET.  This can be used both for normal step-by-step coding, by placing the point inside some command past the end of the highlighted region; and for undoing, by placing the point inside the highlighted region. *)


(** * Arithmetic expressions over natural numbers *)

(** We will begin with that staple of compiler textbooks, arithemtic expressions over a single type of numbers. *)

(** ** Source language *)

(** We begin with the syntax of the source language. *)

Inductive binop : Set := Plus | Times.

(** Our first line of Coq code should be unsurprising to ML and Haskell programmers.  We define an algebraic datatype [binop] to stand for the binary operators of our source language.  There are just two wrinkles compared to ML and Haskell.  First, we use the keyword [Inductive], in place of %\texttt{%#<tt>#data#</tt>#%}%, %\texttt{%#<tt>#datatype#</tt>#%}%, or %\texttt{%#<tt>#type#</tt>#%}%.  This is not just a trivial surface syntax difference; inductive types in Coq are much more expressive than garden variety algebraic datatypes, essentially enabling us to encode all of mathematics, though we begin humbly in this chapter.  Second, there is the [: Set] fragment, which declares that we are defining a datatype that should be thought of as a constituent of programs.  Later, we will see other options for defining datatypes in the universe of proofs or in an infinite hierarchy of universes, encompassing both programs and proofs, that is useful in higher-order constructions. *)

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

(** Now we define the type of arithmetic expressions.  We write that a constant may be built from one argument, a natural number; and a binary operation may be built from a choice of operator and two operand expressions.

A note for readers following along in the PDF version: coqdoc supports pretty-printing of tokens in LaTeX or HTML.  Where you see a right arrow character, the source contains the ASCII text %\texttt{%#<tt>#->#</tt>#%}%.  Other examples of this substitution appearing in this chapter are a double right arrow for %\texttt{%#<tt>#=>#</tt>#%}% and the inverted 'A' symbol for %\texttt{%#<tt>#forall#</tt>#%}%.  When in doubt about the ASCII version of a symbol, you can consult the chapter source code.

%\medskip%

Now we are ready to say what these programs mean.  We will do this by writing an interpreter that can be thought of as a trivial operational or denotational semantics.  (If you are not familiar with these semantic techniques, no need to worry; we will stick to "common sense" constructions.) *)

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

(** The meaning of a binary operator is a binary function over naturals, defined with pattern-matching notation analogous to the %\texttt{%#<tt>#case#</tt>#%}% and %\texttt{%#<tt>#match#</tt>#%}% of ML and Haskell, and referring to the functions [plus] and [mult] from the Coq standard library.  The keyword [Definition] is Coq's all-purpose notation for binding a term of the programming language to a name, with some associated syntactic sugar, like the notation we see here for defining a function.  That sugar could be expanded to yield this definition:

[[
Definition binopDenote : binop -> nat -> nat -> nat := fun (b : binop) =>
  match b with
    | Plus => plus
    | Times => mult
  end.

In this example, we could also omit all of the type annotations, arriving at:

[[
Definition binopDenote := fun b =>
  match b with
    | Plus => plus
    | Times => mult
  end.

Languages like Haskell and ML have a convenient %\textit{%#<i>#principal typing#</i>#%}% property, which gives us strong guarantees about how effective type inference will be.  Unfortunately, Coq's type system is so expressive that any kind of "complete" type inference is impossible, and the task even seems to be hard heuristically in practice.  Nonetheless, Coq includes some very helpful heuristics, many of them copying the workings of Haskell and ML type-checkers for programs that fall in simple fragments of Coq's language.

This is as good a time as any to mention the preponderance of different languages associated with Coq.  The theoretical foundation of Coq is a formal system called the %\textit{%#<i>#Calculus of Inductive Constructions (CIC)#</i>#%}%, which is an extension of the older %\textit{%#<i>#Calculus of Constructions (CoC)#</i>#%}%.  CIC is quite a spartan foundation, which is helpful for proving metatheory but not so helpful for real development.  Still, it is nice to know that it has been proved that CIC enjoys properties like %\textit{%#<i>#strong normalization#</i>#%}%, meaning that every program (and, more importantly, every proof term) terminates; and %\textit{%#<i>#relative consistency#</i>#%}% with systems like versions of Zermelo Fraenkel set theory, which roughly means that you can believe that Coq proofs mean that the corresponding propositions are "really true," if you believe in set theory.

Coq is actually based on an extension of CIC called %\textit{%#<i>#Gallina#</i>#%}%.  The text after the [:=] and before the period in the last code example is a term of Gallina.  Gallina adds many useful features that are not compiled internalluy to more primitive CIC features.  The important metatheorems about CIC have not been extended to the full breadth of these features, but most Coq users do not seem to lose much sleep over this omission.

Commands like [Inductive] and [Definition] are part of %\textit{%#<i>#the vernacular#</i>#%}%, which includes all sorts of useful queries and requests to the Coq system.

Finally, there is %\textit{%#<i>#Ltac#</i>#%}%, Coq's domain-specific language for writing proofs and decision procedures. We will see some basic examples of Ltac later in this chapter, and much of this book is devoted to more involved Ltac examples.

%\medskip%

We can give a simple definition of the meaning of an expression: *)

Fixpoint expDenote (e : exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(** We declare explicitly that this is a recursive definition, using the keyword [Fixpoint].  The rest should be old hat for functional programmers. *)


(** ** Target language *)

(** We will compile our source programs onto a simple stack machine, whose syntax is: *)

Inductive instr : Set :=
| IConst : nat -> instr
| IBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(** An instruction either pushes a constant onto the stack or pops two arguments, applies a binary operator to them, and pushes the result onto the stack.  A program is a list of instructions, and a stack is a list of natural numbers.

We can give instructions meanings as functions from stacks to optional stacks, where running an instruction results in [None] in case of a stack underflow and results in [Some s'] when the result of execution is the new stack [s'].  [::] is the "list cons" operator from the Coq standard library. *)

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | IConst n => Some (n :: s)
    | IBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
      end
  end.

(** With [instrDenote] defined, it is easy to define a function [progDenote], which iterates application of [instrDenote] through a whole program. *)

Fixpoint progDenote (p : prog) (s : stack) {struct p} : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

(** There is one interesting difference compared to our previous example of a [Fixpoint].  This recursive function takes two arguments, [p] and [s].  It is critical for the soundness of Coq that every program terminate, so a shallow syntactic termination check is imposed on every recursive function definition.  One of the function parameters must be designated to decrease monotonically across recursive calls.  That is, every recursive call must use a version of that argument that has been pulled out of the current argument by some number of [match] expressions.  [expDenote] has only one argument, so we did not need to specify which of its arguments decreases.  For [progDenote], we resolve the ambiguity by writing [{struct p}] to indicate that argument [p] decreases structurally. *)


(** ** Translation *)

(** Our compiler itself is now unsurprising.  [++] is the list concatenation operator from the Coq standard library. *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => IConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ IBinop b :: nil
  end.


(** ** Translation correctness *)

(** We are ready to prove that our compiler is implemented correctly.  We can use a new vernacular command [Theorem] to start a correctness proof, in terms of the semantics we defined earlier: *)

Theorem compileCorrect : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
(* begin hide *)
Abort.
(* end hide *)

(** Though a pencil-and-paper proof might clock out at this point, writing "by a routine induction on [e]," it turns out not to make sense to attack this proof directly.  We need to use the standard trick of %\textit{%#<i>#strengthening the induction hypothesis#</i>#%}%.  We do that by proving an auxiliary lemma:
*)

Lemma compileCorrect' : forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

(** After the period in the [Lemma] command, we are in %\textit{%#<i>#the interactive proof-editing mode#</i>#%}%.  We find ourselves staring at this ominous screen of text:

[[
1 subgoal
  
 ============================
  forall (e : exp) (p : list instr) (s : stack),
   progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)  
]]

Coq seems to be restating the lemma for us.  What we are seeing is a limited case of a more general protocol for describing where we are in a proof.  We are told that we have a single subgoal.  In general, during a proof, we can have many pending subgoals, each of which is a logical proposition to prove.  Subgoals can be proved in any order, but it usually works best to prove them in the order that Coq chooses.

Next in the output, we see our single subgoal described in full detail.  There is a double-dashed line, above which would be our free variables and hypotheses, if we had any.  Below the line is the conclusion, which, in general, is to be proved from the hypotheses.

We manipulate the proof state by running commands called %\textit{%#<i>#tactics#</i>#%}%.  Let us start out by running one of the most important tactics:
*)

  induction e.

(** We declare that this proof will proceed by induction on the structure of the expression [e].  This swaps out our initial subgoal for two new subgoals, one for each case of the inductive proof:

[[
2 subgoals
  
 n : nat
 ============================
 forall (s : stack) (p : list instr),
   progDenote (compile (Const n) ++ p) s =
   progDenote p (expDenote (Const n) :: s)
]]
[[
 subgoal 2 is:
  forall (s : stack) (p : list instr),
    progDenote (compile (Binop b e1 e2) ++ p) s =
    progDenote p (expDenote (Binop b e1 e2) :: s)
]]

The first and current subgoal is displayed with the double-dashed line below free variables and hypotheses, while later subgoals are only summarized with their conclusions.  We see an example of a free variable in the first subgoal; [n] is a free variable of type [nat].  The conclusion is the original theorem statement where [e] has been replaced by [Const n].  In a similar manner, the second case has [e] replaced by a generalized invocation of the [Binop] expression constructor.  We can see that proving both cases corresponds to a standard proof by structural induction.

We begin the first case with another very common tactic.
*)

  intros.

(** The current subgoal changes to:
[[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote (compile (Const n) ++ p) s =
 progDenote p (expDenote (Const n) :: s)
]]

We see that [intros] changes [forall]-bound variables at the beginning of a goal into free variables.

To progress further, we need to use the definitions of some of the functions appearing in the goal.  The [unfold] tactic replaces an identifier with its definition.
*)

  unfold compile.

(** [[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote ((IConst n :: nil) ++ p) s =
 progDenote p (expDenote (Const n) :: s)
]] *)

  unfold expDenote.

(** [[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote ((IConst n :: nil) ++ p) s = progDenote p (n :: s)
]]

We only need to unfold the first occurrence of [progDenote] to prove the goal: *)

  unfold progDenote at 1.

(** [[

 n : nat
 s : stack
 p : list instr
 ============================
  (fix progDenote (p0 : prog) (s0 : stack) {struct p0} : 
    option stack :=
      match p0 with
      | nil => Some s0
      | i :: p' =>
          match instrDenote i s0 with
          | Some s' => progDenote p' s'
          | None => None (A:=stack)
          end
      end) ((IConst n :: nil) ++ p) s =
   progDenote p (n :: s)
]]

This last [unfold] has left us with an anonymous fixpoint version of [progDenote], which will generally happen when unfolding recursive definitions.  Fortunately, in this case, we can eliminate such complications right away, since the structure of the argument [(IConst n :: nil) ++ p] is known, allowing us to simplify the internal pattern match with the [simpl] tactic:
*)

  simpl.

(** [[

 n : nat
 s : stack
 p : list instr
 ============================
 (fix progDenote (p0 : prog) (s0 : stack) {struct p0} : 
  option stack :=
    match p0 with
    | nil => Some s0
    | i :: p' =>
        match instrDenote i s0 with
        | Some s' => progDenote p' s'
        | None => None (A:=stack)
        end
    end) p (n :: s) = progDenote p (n :: s)
]]

Now we can unexpand the definition of [progDenote]:
*)

  fold progDenote.

(** [[

 n : nat
 s : stack
 p : list instr
 ============================
 progDenote p (n :: s) = progDenote p (n :: s)
]]

It looks like we are at the end of this case, since we have a trivial equality.  Indeed, a single tactic finishes us off:
*)

  reflexivity.

(** On to the second inductive case:

[[

  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  ============================
   forall (s : stack) (p : list instr),
   progDenote (compile (Binop b e1 e2) ++ p) s =
   progDenote p (expDenote (Binop b e1 e2) :: s)
]]

We see our first example of hypotheses above the double-dashed line.  They are the inductive hypotheses [IHe1] and [IHe2] corresponding to the subterms [e1] and [e2], respectively.

We start out the same way as before, introducing new free variables and unfolding and folding the appropriate definitions.  The seemingly frivolous [unfold]/[fold] pairs are actually accomplishing useful work, because [unfold] will sometimes perform easy simplifications. *)

  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.

(** Now we arrive at a point where the tactics we have seen so far are insufficient:

[[

  b : binop
  e1 : exp
  IHe1 : forall (s : stack) (p : list instr),
         progDenote (compile e1 ++ p) s = progDenote p (expDenote e1 :: s)
  e2 : exp
  IHe2 : forall (s : stack) (p : list instr),
         progDenote (compile e2 ++ p) s = progDenote p (expDenote e2 :: s)
  s : stack
  p : list instr
  ============================
   progDenote ((compile e2 ++ compile e1 ++ IBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

What we need is the associative law of list concatenation, available as a theorem [app_ass] in the standard library. *)

Check app_ass.

(** [[

app_ass
     : forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n
]]

We use it to perform a rewrite: *)

  rewrite app_ass.

(** changing the conclusion to: [[

   progDenote (compile e2 ++ (compile e1 ++ IBinop b :: nil) ++ p) s =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

Now we can notice that the lefthand side of the equality matches the lefthand side of the second inductive hypothesis, so we can rewrite with that hypothesis, too: *)

  rewrite IHe2.

(** [[

   progDenote ((compile e1 ++ IBinop b :: nil) ++ p) (expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

The same process lets us apply the remaining hypothesis. *)

  rewrite app_ass.
  rewrite IHe1.

(** [[

   progDenote ((IBinop b :: nil) ++ p) (expDenote e1 :: expDenote e2 :: s) =
   progDenote p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

Now we can apply a similar sequence of tactics to that that ended the proof of the first case.
*)

  unfold progDenote at 1.
  simpl.
  fold progDenote.
  reflexivity.

(** And the proof is completed, as indicated by the message:

[[
Proof completed.

And there lies our first proof.  Already, even for simple theorems like this, the final proof script is unstructured and not very enlightening to readers.  If we extend this approach to more serious theorems, we arrive at the unreadable proof scripts that are the favorite complaints of opponents of tactic-based proving.  Fortunately, Coq has rich support for scripted automation, and we can take advantage of such a scripted tactic (defined elsewhere) to make short work of this lemma.  We abort the old proof attempt and start again.
*)

Abort.

Lemma compileCorrect' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

(** We need only to state the basic inductive proof scheme and call a tactic that automates the tedious reasoning in between.  In contrast to the period tactic terminator from our last proof, the semicolon tactic separator supports structured, compositional proofs.  The tactic [t1; t2] has the effect of running [t1] and then running [t2] on each remaining subgoal.  The semicolon is one of the most fundamental building blocks of effective proof automation.  The period terminator is very useful for exploratory proving, where you need to see intermediate proof states, but final proofs of any serious complexity should have just one period, terminating a single compound tactic that probably uses semicolons.

The proof of our main theorem is now easy.  We prove it with four period-terminated tactics, though separating them with semicolons would work as well; the version here is easier to step through. *)

Theorem compileCorrect : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros.

(** [[

  e : exp
  ============================
   progDenote (compile e) nil = Some (expDenote e :: nil)
]]

At this point, we want to massage the lefthand side to match the statement of [compileCorrect'].  A theorem from the standard library is useful: *)

Check app_nil_end.

(** [[

app_nil_end
     : forall (A : Type) (l : list A), l = l ++ nil
]] *)

  rewrite (app_nil_end (compile e)).

(** This time, we explicitly specify the value of the variable [l] from the theorem statement, since multiple expressions of list type appear in the conclusion.  [rewrite] might choose the wrong place to rewrite if we did not specify which we want.

[[

  e : exp
  ============================
   progDenote (compile e ++ nil) nil = Some (expDenote e :: nil)
]]

Now we can apply the lemma. *)

  rewrite compileCorrect'.

(** [[

  e : exp
  ============================
   progDenote nil (expDenote e :: nil) = Some (expDenote e :: nil)
]]

We are almost done.  The lefthand and righthand sides can be seen to match by simple symbolic evaluation.  That means we are in luck, because Coq identifies any pair of terms as equal whenever they normalize to the same result by symbolic evaluation.  By the definition of [progDenote], that is the case here, but we do not need to worry about such details.  A simple invocation of [reflexivity] does the normalization and checks that the two results are syntactically equal. *)

  reflexivity.
Qed.


(** * Typed expressions *)

(** In this section, we will build on the initial example by adding additional expression forms that depend on static typing of terms for safety. *)

(** ** Source language *)

(** We define a trivial language of types to classify our expressions: *)

Inductive type : Set := Nat | Bool.

(** Now we define an expanded set of binary operators. *)

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

(** The definition of [tbinop] is different from [binop] in an important way.  Where we declared that [binop] has type [Set], here we declare that [tbinop] has type [type -> type -> type -> Set].  We define [tbinop] as an %\textit{%#<i>#indexed type family#</i>#%}%.  Indexed inductive types are at the heart of Coq's expressive power; almost everything else of interest is defined in terms of them.

ML and Haskell have indexed algebraic datatypes.  For instance, their list types are indexed by the type of data that the list carries.  However, compared to Coq, ML and Haskell 98 place two important restrictions on datatype definitions.

First, the indices of the range of each data constructor must be type variables bound at the top level of the datatype definition.  There is no way to do what we did here, where we, for instance, say that [TPlus] is a constructor building a [tbinop] whose indices are all fixed at [Nat].  %\textit{%#<i>#Generalized algebraic datatypes (GADTs)#</i>#%}% are a popular feature in GHC Haskell and other languages that removes this first restriction.

The second restriction is not lifted by GADTs.  In ML and Haskell, indices of types must be types and may not be %\textit{%#<i>#expressions#</i>#%}%.  In Coq, types may be indiced by arbitrary Gallina terms.  Type indices can live in the same universe as programs, and we can compute with them just like regular programs.  Haskell supports a hobbled form of computation in type indices based on multi-parameter type classes, and recent extensions like type functions bring Haskell programming even closer to "real" functional programming with types, but, without dependent typing, there must always be a gap between how one programs with types and how one programs normally.
*)

(** We can define a similar type family for typed expressions. *)

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall arg1 arg2 res, tbinop arg1 arg2 res -> texp arg1 -> texp arg2 -> texp res.

(** Thanks to our use of dependent types, every well-typed [texp] represents a well-typed source expression, by construction.  This turns out to be very convenient for many things we might want to do with expressions.  For instance, it is easy to adapt our interpreter approach to defining semantics.  We start by defining a function mapping the types of our languages into Coq types: *)

Definition typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(** It can take a few moments to come to terms with the fact that [Set], the type of types of programs, is itself a first-class type, and that we can write functions that return [Set]s.  Past that wrinkle, the definition of [typeDenote] is trivial, relying on the [nat] and [bool] types from the Coq standard library.

We need to define a few auxiliary functions, implementing our boolean binary operators that do not appear with the right types in the standard library.  They are entirely standard and ML-like, with the one caveat being that the Coq [nat] type uses a unary representation, where [O] is zero and [S n] is the successor of [n].
*)

Definition eq_bool (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => true
    | false, false => true
    | _, _ => false
  end.

Fixpoint eq_nat (n1 n2 : nat) {struct n1} : bool :=
  match n1, n2 with
    | O, O => true
    | S n1', S n2' => eq_nat n1' n2'
    | _, _ => false
  end.

Fixpoint lt (n1 n2 : nat) {struct n1} : bool :=
  match n1, n2 with
    | O, S _ => true
    | S n1', S n2' => lt n1' n2'
    | _, _ => false
  end.

(** Now we can interpret binary operators: *)

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b in (tbinop arg1 arg2 res) return (typeDenote arg1 -> typeDenote arg2 -> typeDenote res) with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => eq_nat
    | TEq Bool => eq_bool
    | TLt => lt
  end.

(** This function has just a few differences from the denotation functions we saw earlier.  First, [tbinop] is an indexed type, so its indices become additional arguments to [tbinopDenote].  Second, we need to perform a genuine %\textit{%#<i>#dependent pattern match#</i>#%}% to come up with a definition of this function that type-checks.  In each branch of the [match], we need to use branch-specific information about the indices to [tbinop].  General type inference that takes such information into account is undecidable, and Coq avoids pursuing special heuristics for the problem, instead asking users to write annotations, like we see above on the line with [match].

The [in] annotation restates the type of the term being case-analyzed.  Though we use the same names for the indices as we use in the type of the original argument binder, these are actually fresh variables, and they are %\textit{%#<i>#binding occcurrences#</i>#%}%.  Their scope is the [return] clause.  That is, [arg1], [arg2], and [arg3] are new bound variables bound only within the return clause [typeDenote arg1 -> typeDenote arg2 -> typeDenote res].  By being explicit about the functional relationship between the type indices and the match result, we regain decidable type inference.

The same tricks suffice to define an expression denotation function in an unsurprising way:
*)

Fixpoint texpDenote t (e : texp t) {struct e} : typeDenote t :=
  match e in (texp t) return (typeDenote t) with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.


(** ** Target language *)

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
| TINConst : forall s, nat -> tinstr s (Nat :: s)
| TIBConst : forall s, bool -> tinstr s (Bool :: s)
| TIBinop : forall arg1 arg2 res s,
  tbinop arg1 arg2 res
  -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i in (tinstr ts ts') return (vstack ts -> vstack ts') with
    | TINConst _ n => fun s => (n, s)
    | TIBConst _ b => fun s => (b, s)
    | TIBinop _ _ _ _ b => fun s =>
      match s with
        (arg1, (arg2, s')) => ((tbinopDenote b) arg1 arg2, s')
      end
  end.

Fixpoint tprogDenote ts ts' (p : tprog ts ts') {struct p} : vstack ts -> vstack ts' :=
  match p in (tprog ts ts') return (vstack ts -> vstack ts') with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.


(** ** Translation *)

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') {struct p} : tprog ts' ts'' -> tprog ts ts'' :=
  match p in (tprog ts ts') return (tprog ts' ts'' -> tprog ts ts'') with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e : texp t) (ts : tstack) {struct e} : tprog ts (t :: ts) :=
  match e in (texp t) return (tprog ts (t :: ts)) with
    | TNConst n => TCons (TINConst _ n) (TNil _)
    | TBConst b => TCons (TIBConst _ b) (TNil _)
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
      (tconcat (tcompile e1 _) (TCons (TIBinop _ b) (TNil _)))
  end.

Print tcompile.


(** ** Translation correctness *)

Lemma tcompileCorrect' : forall t (e : texp t)
  ts (s : vstack ts),
  tprogDenote (tcompile e ts) s
  = (texpDenote e, s).
  induction e; crush.
Abort.

Lemma tconcatCorrect : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'')
  (s : vstack ts),
  tprogDenote (tconcat p p') s
  = tprogDenote p' (tprogDenote p s).
  induction p; crush.
Qed.

Hint Rewrite tconcatCorrect : cpdt.

Lemma tcompileCorrect' : forall t (e : texp t)
  ts (s : vstack ts),
  tprogDenote (tcompile e ts) s
  = (texpDenote e, s).
  induction e; crush.
Qed.

Hint Rewrite tcompileCorrect' : cpdt.

Theorem tcompileCorrect : forall t (e : texp t), tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.
