(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(**

This work is licensed under a
Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
Unported License.
The license text is available at:
%\begin{center} \url{http://creativecommons.org/licenses/by-nc-nd/3.0/} \end{center}%
#<a href="http://creativecommons.org/licenses/by-nc-nd/3.0/">http://creativecommons.org/licenses/by-nc-nd/3.0/</a>#

*)


(** * Whence This Book? *)

(**

We would all like to have programs check that our programs are correct.  Due in no small part to some bold but unfulfilled promises in the history of computer science, today most people who write software, practitioners and academics alike, assume that the costs of formal program verification outweigh the associated benefits.  The purpose of this book is to convince you that the technology of program verification is mature enough today that it makes sense to use it in a support role in many kinds of research projects in computer science.  Beyond the convincing, I also want to provide a handbook on practical engineering of certified programs with the Coq proof assistant.

There are a good number of (though definitely not "many") tools that are in wide use today for building machine-checked mathematical proofs and machine-certified programs.  This is my attempt at an exhaustive list of interactive "proof assistants" satisfying a few criteria.  First, the authors of each tool must intend for it to be put to use for software-related applications.  Second, there must have been enough engineering effort put into the tool that someone not doing research on the tool itself would feel his time was well spent using it.  A third criterion is more of an empirical validation of the second: the tool must have a significant user community outside of its own development team.

%
\begin{tabular}{rl}
\textbf{ACL2} & \url{http://www.cs.utexas.edu/users/moore/acl2/} \\
\textbf{Coq} & \url{http://coq.inria.fr/} \\
\textbf{Isabelle/HOL} & \url{http://isabelle.in.tum.de/} \\
\textbf{PVS} & \url{http://pvs.csl.sri.com/} \\
\textbf{Twelf} & \url{http://www.twelf.org/} \\
\end{tabular}
%
#
<table align="center">
<tr><td align="right"><b>ACL2</b></td> <td><a href="http://www.cs.utexas.edu/users/moore/acl2/">http://www.cs.utexas.edu/users/moore/acl2/</a></td></tr>
<tr><td align="right"><b>Coq</b></td> <td><a href="http://coq.inria.fr/">http://coq.inria.fr/</a></td></tr>
<tr><td align="right"><b>Isabelle/HOL</b></td> <td><a href="http://isabelle.in.tum.de/">http://isabelle.in.tum.de/</a></td></tr>
<tr><td align="right"><b>PVS</b></td> <td><a href="http://pvs.csl.sri.com/">http://pvs.csl.sri.com/</a></td></tr>
<tr><td align="right"><b>Twelf</b></td> <td><a href="http://www.twelf.org/">http://www.twelf.org/</a></td></tr>
</table>
#

Isabelle/HOL, implemented with the "proof assistant development framework" Isabelle, is the most popular proof assistant for the HOL logic.  The other implementations of HOL can be considered equivalent for purposes of the discussion here.

*)


(** * Why Coq? *)

(**
This book is going to be about certified programming using Coq, and I am convinced that it is the best tool for the job.  Coq has a number of very attractive properties, which I will summarize here, mentioning which of the other candidate tools lack each property.
*)


(** ** Based on a Higher-Order Functional Programming Language *)

(**
There is no reason to give up the familiar comforts of functional programming when you start writing certified programs.  All of the tools I listed are based on functional programming languages, which means you can use them without their proof-related aspects to write and run regular programs.

ACL2 is notable in this field for having only a %\textit{%#<i>#first-order#</i>#%}% language at its foundation.  That is, you cannot work with functions over functions and all those other treats that functional programmers love.  By giving up this facility, ACL2 can make broader assumptions about how well its proof automation will work, but we can generally recover the same advantages in other proof assistants when we happen to be programming in first-order fragments.
*)


(** ** Dependent Types *)

(**
A language of %\textit{%#<i>#dependent types#</i>#%}% may include references to programs inside of types.  For instance, the type of an array might include a program expression giving the size of the array, making it possible to verify lack of out-of-bounds accesses statically.  Dependent types can go even further than this, effectively capturing any correctness property in a type.  For instance, later in this book, we will see how to give a Mini-ML compiler a type that guarantees that it maps well-typed source programs to well-typed target programs.

ACL2 and HOL lack dependent types outright.  PVS and Twelf each supports a different strict subset of Coq's dependent type language.  Twelf's type language is restricted to a bare-bones, monomorphic lambda calculus, which places serious restrictions on how complicated %\textit{%#<i>#computations inside types#</i>#%}% can be.  This restriction is important for the soundness argument behind Twelf's approach to representing and checking proofs.

In contrast, PVS's dependent types are much more general, but they are squeezed inside the single mechanism of %\textit{%#<i>#subset types#</i>#%}%, where a normal type is refined by attaching a predicate over its elements.  Each member of the subset type is an element of the base type that satisfies the predicate.

Dependent types are not just useful because they help you express correctness properties in types.  Dependent types also often let you write certified programs %\textit{%#<i>#without writing anything that looks like a proof#</i>#%}%.  Even with subset types, which for many contexts can be used to express any relevant property with enough acrobatics, the human driving the proof assistant usually has to build some proofs explicitly.  Writing formal proofs is hard, so we want to avoid it as far as possible, so dependent types are invaluable.

*)

(** ** An Easy-to-Check Kernel Proof Language *)

(**
Scores of automated decision procedures are useful in practical theorem proving, but it is unfortunate to have to trust in the correct implementation of each procedure.  Proof assistants satisfying the "de Bruijn criterion" may use complicated and extensible procedures to seek out proofs, but in the end they produce %\textit{%#<i>#proof terms#</i>#%}% in kernel languages.  These core languages have feature complexity on par with what you find in proposals for formal foundations for mathematics.  To believe a proof, we can ignore the possibility of bugs during %\textit{%#<i>#search#</i>#%}% and just rely on a (relatively small) proof-checking kernel that we apply to the %\textit{%#<i>#result#</i>#%}% of the search.

ACL2 and PVS do not meet the de Bruijn criterion, employing fancy decision procedures that produce no "evidence trails" justifying their results.
*)

(** ** Convenient Programmable Proof Automation *)

(**
A commitment to a kernel proof language opens up wide possibilities for user extension of proof automation systems, without allowing user mistakes to trick the overall system into accepting invalid proofs.  Almost any interesting verification problem is undecidable, so it is important to help users build their own procedures for solving the restricted problems that they encounter in particular implementations.

Twelf features no proof automation marked as a bonafide part of the latest release; there is some code included for testing purposes.  The Twelf style is based on writing out all proofs in full detail.  Because Twelf is specialized to the domain of syntactic metatheory proofs about programming languages and logics, it is feasible to use it to write those kinds of proofs manually.  Outside that domain, the lack of automation can be a serious obstacle to productivity.  Most kinds of program verification fall outside Twelf's forte.

Of the remaining tools, all can support user extension with new decision procedures by hacking directly in the tool's implementation language (such as OCaml for Coq).  Since ACL2 and PVS do not satisfy the de Bruijn criterion, overall correctness is at the mercy of the authors of new procedures.

Isabelle/HOL and Coq both support coding new proof manipulations in ML in ways that cannot lead to the acceptance of invalid proofs.  Additionally, Coq includes a domain-specific language for coding decision procedures in normal Coq source code, with no need to break out into ML.  This language is called Ltac, and I think of it as the unsung hero of the proof assistant world.  Not only does Ltac prevent you from making fatal mistakes, it also includes a number of novel programming constructs which combine to make a "proof by decision procedure" style very pleasant.  We will meet these features in the chapters to come.
*)

(** ** Proof by Reflection *)

(**
A surprising wealth of benefits follow from choosing a proof language that integrates a rich notion of computation.  Coq includes programs and proof terms in the same syntactic class.  This makes it easy to write programs that compute proofs.  With rich enough dependent types, such programs are %\textit{%#<i>#certified decision procedures#</i>#%}%.  In such cases, these certified procedures can be put to good use %\textit{%#<i>#without ever running them#</i>#%}%!  Their types guarantee that, if we did bother to run them, we would receive proper "ground" proofs.

The critical ingredient for this technique, many of whose instances are referred to as %\textit{%#<i>#proof by reflection#</i>#%}%, is a way of inducing non-trivial computation inside of logical propositions during proof checking.  Further, most of these instances require dependent types to make it possible to state the appropriate theorems.  Of the proof assistants I listed, only Coq really provides this support.
*)


(** * Engineering with a Proof Assistant *)

(**
In comparisons with its competitors, Coq is often derided for promoting unreadable proofs.  It is very easy to write proof scripts that manipulate proof goals imperatively, with no structure to aid readers.  Such developments are nightmares to maintain, and they certainly do not manage to convey "why the theorem is true" to anyone but the original author.  One additional (and not insignificant) purpose of this book is to show why it is unfair and unproductive to dismiss Coq based on the existence of such developments.

I will go out on a limb and guess that the reader is a dedicated fan of some functional programming language or another, and that he may even have been involved in teaching that language to undergraduates.  I want to propose an analogy between two attitudes: coming to a negative conclusion about Coq after reading common Coq developments in the wild, and coming to a negative conclusion about Your Favorite Language after looking at the programs undergraduates write in it in the first week of class.  The pragmatics of mechanized proving and program verification have been under serious study for much less time than the pragmatics of programming have been.  The computer theorem proving community is still developing the key insights that correspond to those that functional programming texts and instructors impart to their students, to help those students get over that critical hump where using the language stops being more trouble than it is worth.  Most of the insights for Coq are barely even disseminated among the experts, let alone set down in a tutorial form.  I hope to use this book to go a long way towards remedying that.

If I do that job well, then this book should be of interest even to people who have participated in classes or tutorials specifically about Coq.  The book should even be useful to people who have been using Coq for years but who are mystified when their Coq developments prove impenetrable by colleagues.  The crucial angle in this book is that there are "design patterns" for reliably avoiding the really grungy parts of theorem proving, and consistent use of these patterns can get you over the hump to the point where it is worth your while to use Coq to prove your theorems and certify your programs, even if formal verification is not your main concern in a project.  We will follow this theme by pursuing two main methods for replacing manual proofs with more understandable artifacts: dependently-typed functions and custom Ltac decision procedures.
*)


(** * Prerequisites for This Book *)

(**
I try to keep the required background knowledge to a minimum in this book.  I will assume familiarity with the material from usual discrete math and logic courses taken by all undergraduate computer science majors, and I will assume that readers have significant experience programming in one of the ML dialects, in Haskell, or in some other, closely-related language.  Experience with only dynamically-typed functional languages might lead to befuddlement in some places, but a reader who has come to grok Scheme deeply will probably be fine.

A good portion of the book is about how to formalize programming languages, compilers, and proofs about them.  I depart significantly from today's most popular methodology for pencil-and-paper formalism among programming languages researchers.  There is no need to be familiar with operational semantics, preservation and progress theorems, or any of the material found in courses on programming language semantics but not in basic discrete math and logic courses.  I will use operational semantics very sparingly, and there will be no preservation or progress proofs.  Instead, I will use a style that seems to work much better in Coq, which can be given the fancy-sounding name %\textit{%#<i>#foundational type-theoretic semantics#</i>#%}% or the more populist name %\textit{%#<i>#semantics by definitional compilers#</i>#%}%.
*)
