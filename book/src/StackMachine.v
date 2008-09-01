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
(* end hide *)


(** I will start off by jumping right in to a fully-worked set of examples, building certified compilers from increasingly complicated source languages to stack machines.  We will meet a few useful tactics and see how they can be used in manual proofs, and we will also see how easily these proofs can be automated instead.  I assume that you have installed Coq and Proof General.

As always, you can step through the source file %\texttt{%#<tt>#StackMachine.v#</tt>#%}% for this chapter interactively in Proof General.  Alternatively, to get a feel for the whole lifecycle of creating a Coq development, you can enter the pieces of source code in this chapter in a new %\texttt{%#<tt>#.v#</tt>#%}% file in an Emacs buffer.  If you do the latter, include a line [Require Import List Tactics] at the start of the file, to match some code hidden from the chapter source, and be sure to run the Coq binary %\texttt{%#<tt>#coqtop#</tt>#%}% with the command-line argument %\texttt{%#<tt>#-I SRC#</tt>#%}%, where %\texttt{%#<tt>#SRC#</tt>#%}% is the path to a directory containing the source for this book.  In either case, if you have installed Proof General properly, it should start automatically when you visit a %\texttt{%#<tt>#.v#</tt>#%}% buffer in Emacs. *)


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

Lemma compileCorrect' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e.

  intros.
  unfold compile.
  unfold expDenote.
  simpl.
  reflexivity.

  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.
  rewrite app_ass.
  rewrite IHe2.
  rewrite app_ass.
  rewrite IHe1.
  simpl.
  reflexivity.
Abort.

Lemma compileCorrect' : forall e s p, progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

Theorem compileCorrect : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intro.
  rewrite (app_nil_end (compile e)).
  rewrite compileCorrect'.
  reflexivity.
Qed.
