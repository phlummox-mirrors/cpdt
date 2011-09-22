(* Copyright (c) 2011, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)

Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.

(* end hide *)

(** %\part{Proof Engineering}

   \chapter{Proof Search by Logic Programming}% *)

(** Exciting new chapter that is missing prose for the new content!  Some content was moved from the next chapter, and it may not seem entirely to fit here yet. *)


(** * Introducing Logic Programming *)

Print plus.

Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r
  -> plusR (S n) m (S r).

(* begin thide *)
Hint Constructors plusR.
(* end thide *)

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
(* begin thide *)
  induction n; crush.
Qed.
(* end thide *)

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
(* begin thide *)
  induction 1; crush.
Qed.
(* end thide *)

Example four_plus_three : 4 + 3 = 7.
(* begin thide *)
  reflexivity.
Qed.
(* end thide *)

Example four_plus_three' : plusR 4 3 7.
(* begin thide *)
  auto.
Qed.
(* end thide *)

Example five_plus_three' : plusR 5 3 8.
(* begin thide *)
  auto 6.
Restart.
  info auto 6.
Qed.
(* end thide *)

(* begin thide *)
Hint Constructors ex.
(* end thide *)

Example seven_minus_three : exists x, x + 3 = 7.
(* begin thide *)
  eauto 6.
Abort.
(* end thide *)

Example seven_minus_three' : exists x, plusR x 3 7.
(* begin thide *)
  info eauto 6.
Qed.
(* end thide *)

Example seven_minus_four' : exists x, plusR 4 x 7.
(* begin thide *)
  info eauto 6.
Qed.
(* end thide *)

(* begin thide *)
SearchRewrite (O + _).

Hint Immediate plus_O_n.

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
  crush.
Qed.

Hint Resolve plusS.
(* end thide *)

Example seven_minus_three : exists x, x + 3 = 7.
(* begin thide *)
  info eauto 6.
Qed.
(* end thide *)

Example seven_minus_four : exists x, 4 + x = 7.
(* begin thide *)
  info eauto 6.
Qed.
(* end thide *)

Example hundred_minus_hundred : exists x, 4 + x + 0 = 7.
(* begin thide *)
  eauto 6.
Abort.
(* end thide *)

(* begin thide *)
Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
  crush.
Qed.

Hint Resolve plusO.
(* end thide *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
(* begin thide *)
  info eauto 7.
Qed.
(* end thide *)

Check eq_trans.

Section slow.
  Hint Resolve eq_trans.

  Example three_minus_four_zero : exists x, 1 + x = 0.
    Time eauto 1.
    Time eauto 2.
    Time eauto 3.
    Time eauto 4.
    Time eauto 5.
    debug eauto 3.
  Abort.
End slow.

(* begin thide *)
Hint Resolve eq_trans : slow.
(* end thide *)

Example three_minus_four_zero : exists x, 1 + x = 0.
(* begin thide *)
  eauto.
Abort.
(* end thide *)

Example seven_minus_three_again : exists x, x + 3 = 7.
(* begin thide *)
  eauto 6.
Qed.
(* end thide *)

Example needs_trans : forall x y, 1 + x = y
  -> y = 2
  -> exists z, z + x = 3.
(* begin thide *)
  info eauto with slow.
Qed.
(* end thide *)


(** * Searching for Underconstrained Values *)

Print length.

Example length_1_2 : length (1 :: 2 :: nil) = 2.
  auto.
Qed.

Print length_1_2.

(* begin thide *)
Theorem length_O : forall A, length (nil (A := A)) = O.
  crush.
Qed.

Theorem length_S : forall A (h : A) t n,
  length t = n
  -> length (h :: t) = S n.
  crush.
Qed.

Hint Resolve length_O length_S.
(* end thide *)

Example length_is_2 : exists ls : list nat, length ls = 2.
(* begin thide *)
  eauto.

  Show Proof.
Abort.
(* end thide *)

Print Forall.

Example length_is_2 : exists ls : list nat, length ls = 2
  /\ Forall (fun n => n >= 1) ls.
(* begin thide *)
  eauto 9.
Qed.
(* end thide *)

Definition sum := fold_right plus O.

(* begin thide *)
Lemma plusO' : forall n m,
  n = m
  -> 0 + n = m.
  crush.
Qed.

Hint Resolve plusO'.

Hint Extern 1 (sum _ = _) => simpl.
(* end thide *)

Example length_and_sum : exists ls : list nat, length ls = 2
  /\ sum ls = O.
(* begin thide *)
  eauto 7.
Qed.
(* end thide *)

Print length_and_sum.

Example length_and_sum' : exists ls : list nat, length ls = 5
  /\ sum ls = 42.
(* begin thide *)
  eauto 15.
Qed.
(* end thide *)

Print length_and_sum'.

Example length_and_sum'' : exists ls : list nat, length ls = 2
  /\ sum ls = 3
  /\ Forall (fun n => n <> 0) ls.
(* begin thide *)
  eauto 11.
Qed.
(* end thide *)

Print length_and_sum''.


(** * Synthesizing Programs *)

Inductive exp : Set :=
| Const : nat -> exp
| Var : exp
| Plus : exp -> exp -> exp.

Inductive eval (var : nat) : exp -> nat -> Prop :=
| EvalConst : forall n, eval var (Const n) n
| EvalVar : eval var Var var
| EvalPlus : forall e1 e2 n1 n2, eval var e1 n1
  -> eval var e2 n2
  -> eval var (Plus e1 e2) (n1 + n2).

(* begin thide *)
Hint Constructors eval.
(* end thide *)

Example eval1 : forall var, eval var (Plus Var (Plus (Const 8) Var)) (var + (8 + var)).
(* begin thide *)
  auto.
Qed.
(* end thide *)

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
(* begin thide *)
  eauto.
Abort.
(* end thide *)

(* begin thide *)
Theorem EvalPlus' : forall var e1 e2 n1 n2 n, eval var e1 n1
  -> eval var e2 n2
  -> n1 + n2 = n
  -> eval var (Plus e1 e2) n.
  crush.
Qed.

Hint Resolve EvalPlus'.

Hint Extern 1 (_ = _) => abstract omega.
(* end thide *)

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

Print eval1'.

Example synthesize1 : exists e, forall var, eval var e (var + 7).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

Print synthesize1.

Example synthesize2 : exists e, forall var, eval var e (2 * var + 8).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

Print synthesize2.

Example synthesize3 : exists e, forall var, eval var e (3 * var + 42).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

Print synthesize3.

(* begin thide *)
Theorem EvalConst' : forall var n m, n = m
  -> eval var (Const n) m.
  crush.
Qed.

Hint Resolve EvalConst'.

Theorem zero_times : forall n m r,
  r = m
  -> r = 0 * n + m.
  crush.
Qed.

Hint Resolve zero_times.

Theorem EvalVar' : forall var n,
  var = n
  -> eval var Var n.
  crush.
Qed.

Hint Resolve EvalVar'.

Theorem plus_0 : forall n r,
  r = n
  -> r = n + 0.
  crush.
Qed.

Theorem times_1 : forall n, n = 1 * n.
  crush.
Qed.

Hint Resolve plus_0 times_1.

Require Import Arith Ring.

Theorem combine : forall x k1 k2 n1 n2,
  (k1 * x + n1) + (k2 * x + n2) = (k1 + k2) * x + (n1 + n2).
  intros; ring.
Qed.

Hint Resolve combine.

Theorem linear : forall e, exists k, exists n,
  forall var, eval var e (k * var + n).
  induction e; crush; eauto.
Qed.

Print linear.
(* end thide *)


(** * More on [auto] Hints *)

(** Another class of built-in tactics includes [auto], [eauto], and [autorewrite].  These are based on %\textit{%#<i>#hint databases#</i>#%}%, which we have seen extended in many examples so far.  These tactics are important, because, in Ltac programming, we cannot create %``%#"#global variables#"#%''% whose values can be extended seamlessly by different modules in different source files.  We have seen the advantages of hints so far, where [crush] can be defined once and for all, while still automatically applying the hints we add throughout developments.

The basic hints for [auto] and [eauto] are [Hint Immediate lemma], asking to try solving a goal immediately by applying a lemma and discharging any hypotheses with a single proof step each; [Resolve lemma], which does the same but may add new premises that are themselves to be subjects of nested proof search; [Constructors type], which acts like [Resolve] applied to every constructor of an inductive type; and [Unfold ident], which tries unfolding [ident] when it appears at the head of a proof goal.  Each of these [Hint] commands may be used with a suffix, as in [Hint Resolve lemma : my_db].  This adds the hint only to the specified database, so that it would only be used by, for instance, [auto with my_db].  An additional argument to [auto] specifies the maximum depth of proof trees to search in depth-first order, as in [auto 8] or [auto 8 with my_db].  The default depth is 5.

All of these [Hint] commands can be issued alternatively with a more primitive hint kind, [Extern].  A few examples should do best to explain how [Hint Extern] works. *)

Theorem bool_neq : true <> false.
(* begin thide *)
  auto.

  (** [crush] would have discharged this goal, but the default hint database for [auto] contains no hint that applies. *)

Abort.

(** It is hard to come up with a [bool]-specific hint that is not just a restatement of the theorem we mean to prove.  Luckily, a simpler form suffices. *)

Hint Extern 1 (_ <> _) => congruence.

Theorem bool_neq : true <> false.
  auto.
Qed.
(* end thide *)

(** Our hint says: %``%#"#whenever the conclusion matches the pattern [_ <> _], try applying [congruence].#"#%''%  The [1] is a cost for this rule.  During proof search, whenever multiple rules apply, rules are tried in increasing cost order, so it pays to assign high costs to relatively expensive [Extern] hints.

[Extern] hints may be implemented with the full Ltac language.  This example shows a case where a hint uses a [match]. *)

Section forall_and.
  Variable A : Set.
  Variables P Q : A -> Prop.

  Hypothesis both : forall x, P x /\ Q x.

  Theorem forall_and : forall z, P z.
(* begin thide *)
    crush.

    (** [crush] makes no progress beyond what [intros] would have accomplished.  [auto] will not apply the hypothesis [both] to prove the goal, because the conclusion of [both] does not unify with the conclusion of the goal.  However, we can teach [auto] to handle this kind of goal. *)

    Hint Extern 1 (P ?X) =>
      match goal with
        | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
      end.

    auto.
  Qed.
(* end thide *)

  (** We see that an [Extern] pattern may bind unification variables that we use in the associated tactic.  [proj1] is a function from the standard library for extracting a proof of [R] from a proof of [R /\ S]. *)

End forall_and.

(** After our success on this example, we might get more ambitious and seek to generalize the hint to all possible predicates [P].

   [[
  Hint Extern 1 (?P ?X) =>
    match goal with
      | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
    end.

User error: Bound head variable
 
   ]]

   Coq's [auto] hint databases work as tables mapping %\textit{%#<i>#head symbols#</i>#%}% to lists of tactics to try.  Because of this, the constant head of an [Extern] pattern must be determinable statically.  In our first [Extern] hint, the head symbol was [not], since [x <> y] desugars to [not (eq x y)]; and, in the second example, the head symbol was [P].

   This restriction on [Extern] hints is the main limitation of the [auto] mechanism, preventing us from using it for general context simplifications that are not keyed off of the form of the conclusion.  This is perhaps just as well, since we can often code more efficient tactics with specialized Ltac programs, and we will see how in the next chapter. *)


(** * Rewrite Hints *)

   (** We have used [Hint Rewrite] in many examples so far.  [crush] uses these hints by calling [autorewrite].  Our rewrite hints have taken the form [Hint Rewrite lemma : cpdt], adding them to the [cpdt] rewrite database.  This is because, in contrast to [auto], [autorewrite] has no default database.  Thus, we set the convention that [crush] uses the [cpdt] database.

   This example shows a direct use of [autorewrite]. *)

Section autorewrite.
  Variable A : Set.
  Variable f : A -> A.

  Hypothesis f_f : forall x, f (f x) = f x.

  Hint Rewrite f_f : my_db.

  Lemma f_f_f : forall x, f (f (f x)) = f x.
    intros; autorewrite with my_db; reflexivity.
  Qed.

  (** There are a few ways in which [autorewrite] can lead to trouble when insufficient care is taken in choosing hints.  First, the set of hints may define a nonterminating rewrite system, in which case invocations to [autorewrite] may not terminate.  Second, we may add hints that %``%#"#lead [autorewrite] down the wrong path.#"#%''%  For instance: *)

  Section garden_path.
    Variable g : A -> A.
    Hypothesis f_g : forall x, f x = g x.
    Hint Rewrite f_g : my_db.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with my_db.
      (** [[
============================
 g (g (g x)) = g x
          ]]
          *)

    Abort.

    (** Our new hint was used to rewrite the goal into a form where the old hint could no longer be applied.  This %``%#"#non-monotonicity#"#%''% of rewrite hints contrasts with the situation for [auto], where new hints may slow down proof search but can never %``%#"#break#"#%''% old proofs.  The key difference is that [auto] either solves a goal or makes no changes to it, while [autorewrite] may change goals without solving them.  The situation for [eauto] is slightly more complicated, as changes to hint databases may change the proof found for a particular goal, and that proof may influence the settings of unification variables that appear elsewhere in the proof state. *)

  Reset garden_path.

  (** [autorewrite] also works with quantified equalities that include additional premises, but we must be careful to avoid similar incorrect rewritings. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
    Hint Rewrite f_g : my_db.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with my_db.
      (** [[

  ============================
   g (g (g x)) = g x

subgoal 2 is:
 P x
subgoal 3 is:
 P (f x)
subgoal 4 is:
 P (f x)
          ]]
          *)

    Abort.

    (** The inappropriate rule fired the same three times as before, even though we know we will not be able to prove the premises. *)

  Reset garden_path.

  (** Our final, successful, attempt uses an extra argument to [Hint Rewrite] that specifies a tactic to apply to generated premises.  Such a hint is only used when the tactic succeeds for all premises, possibly leaving further subgoals for some premises. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
(* begin thide *)
    Hint Rewrite f_g using assumption : my_db.
(* end thide *)

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
(* begin thide *)
      intros; autorewrite with my_db; reflexivity.
    Qed.
(* end thide *)

    (** [autorewrite] will still use [f_g] when the generated premise is among our assumptions. *)

    Lemma f_f_f_g : forall x, P x -> f (f x) = g x.
(* begin thide *)
      intros; autorewrite with my_db; reflexivity.
(* end thide *)
    Qed.
  End garden_path.

  (** remove printing * *)

  (** It can also be useful to use the [autorewrite with db in *] form, which does rewriting in hypotheses, as well as in the conclusion. *)

  (** printing * $*$ *)

  Lemma in_star : forall x y, f (f (f (f x))) = f (f y)
    -> f x = f (f (f y)).
(* begin thide *)
    intros; autorewrite with my_db in *; assumption.
(* end thide *)
  Qed.

End autorewrite.


(** * Exercises *)

(** printing * $\cdot$ *)

(** %\begin{enumerate}%#<ol>#

%\item%#<li># I did a Google search for group theory and found #<a href="http://dogschool.tripod.com/housekeeping.html">#a page that proves some standard theorems#</a>#%\footnote{\url{http://dogschool.tripod.com/housekeeping.html}}%.  This exercise is about proving all of the theorems on that page automatically.

  For the purposes of this exercise, a group is a set [G], a binary function [f] over [G], an identity element [e] of [G], and a unary inverse function [i] for [G].  The following laws define correct choices of these parameters.  We follow standard practice in algebra, where all variables that we mention are quantified universally implicitly at the start of a fact.  We write infix [*] for [f], and you can set up the same sort of notation in your code with a command like [Infix "*" := f.].

  %\begin{itemize}%#<ul>#
    %\item%#<li># %\textbf{%#<b>#Associativity#</b>#%}%: [(a * b) * c = a * (b * c)]#</li>#
    %\item%#<li># %\textbf{%#<b>#Right Identity#</b>#%}%: [a * e = a]#</li>#
    %\item%#<li># %\textbf{%#<b>#Right Inverse#</b>#%}%: [a * i a = e]#</li>#
  #</ul> </li>#%\end{itemize}%

  The task in this exercise is to prove each of the following theorems for all groups, where we define a group exactly as above.  There is a wrinkle: every theorem or lemma must be proved by either a single call to [crush] or a single call to [eauto]!  It is allowed to pass numeric arguments to [eauto], where appropriate.  Recall that a numeric argument sets the depth of proof search, where 5 is the default.  Lower values can speed up execution when a proof exists within the bound.  Higher values may be necessary to find more involved proofs.

  %\begin{itemize}%#<ul>#
    %\item%#<li># %\textbf{%#<b>#Characterizing Identity#</b>#%}%: [a * a = a -> a = e]#</li>#
    %\item%#<li># %\textbf{%#<b>#Left Inverse#</b>#%}%: [i a * a = e]#</li>#
    %\item%#<li># %\textbf{%#<b>#Left Identity#</b>#%}%: [e * a = a]#</li>#
    %\item%#<li># %\textbf{%#<b>#Uniqueness of Left Identity#</b>#%}%: [p * a = a -> p = e]#</li>#
    %\item%#<li># %\textbf{%#<b>#Uniqueness of Right Inverse#</b>#%}%: [a * b = e -> b = i a]#</li>#
    %\item%#<li># %\textbf{%#<b>#Uniqueness of Left Inverse#</b>#%}%: [a * b = e -> a = i b]#</li>#
    %\item%#<li># %\textbf{%#<b>#Right Cancellation#</b>#%}%: [a * x = b * x -> a = b]#</li>#
    %\item%#<li># %\textbf{%#<b>#Left Cancellation#</b>#%}%: [x * a = x * b -> a = b]#</li>#
    %\item%#<li># %\textbf{%#<b>#Distributivity of Inverse#</b>#%}%: [i (a * b) = i b * i a]#</li>#
    %\item%#<li># %\textbf{%#<b>#Double Inverse#</b>#%}%: [i (i a) = a]#</li>#
    %\item%#<li># %\textbf{%#<b>#Identity Inverse#</b>#%}%: [i e = e]#</li>#
  #</ul> </li>#%\end{itemize}%

  One more use of tactics is allowed in this problem.  The following lemma captures one common pattern of reasoning in algebra proofs: *)

(* begin hide *)
Variable G : Set.
Variable f : G -> G -> G.
Infix "*" := f.
(* end hide *)

Lemma mult_both : forall a b c d1 d2,
  a * c = d1
  -> b * c = d2
  -> a = b
  -> d1 = d2.
  crush.
Qed.

(** That is, we know some equality [a = b], which is the third hypothesis above.  We derive a further equality by multiplying both sides by [c], to yield [a * c = b * c].  Next, we do algebraic simplification on both sides of this new equality, represented by the first two hypotheses above.  The final result is a new theorem of algebra.

   The next chapter introduces more details of programming in Ltac, but here is a quick teaser that will be useful in this problem.  Include the following hint command before you start proving the main theorems of this exercise: *)

Hint Extern 100 (_ = _) =>
  match goal with
    | [ _ : True |- _ ] => fail 1
    | _ => assert True by constructor; eapply mult_both
  end.

(** This hint has the effect of applying [mult_both] %\emph{%#<i>#at most once#</i>#%}% during a proof.  After the next chapter, it should be clear why the hint has that effect, but for now treat it as a useful black box.  Simply using [Hint Resolve mult_both] would increase proof search time unacceptably, because there are just too many ways to use [mult_both] repeatedly within a proof.

   The order of the theorems above is itself a meta-level hint, since I found that order to work well for allowing the use of earlier theorems as hints in the proofs of later theorems.

   The key to this problem is coming up with further lemmas like [mult_both] that formalize common patterns of reasoning in algebraic proofs.  These lemmas need to be more than sound: they must also fit well with the way that [eauto] does proof search.  For instance, if we had given [mult_both] a traditional statement, we probably would have avoided %``%#"#pointless#"#%''% equalities like [a = b], which could be avoided simply by replacing all occurrences of [b] with [a].  However, the resulting theorem would not work as well with automated proof search!  Every additional hint you come up with should be registered with [Hint Resolve], so that the lemma statement needs to be in a form that [eauto] understands %``%#"#natively.#"#%''%

   I recommend testing a few simple rules corresponding to common steps in algebraic proofs.  You can apply them manually with any tactics you like (e.g., [apply] or [eapply]) to figure out what approaches work, and then switch to [eauto] once you have the full set of hints.

   I also proved a few hint lemmas tailored to particular theorems, but which do not give common algebraic simplification rules.  You will probably want to use some, too, in cases where [eauto] does not find a proof within a reasonable amount of time.  In total, beside the main theorems to be proved, my sample solution includes 6 lemmas, with a mix of the two kinds of lemmas.  You may use more in your solution, but I suggest trying to minimize the number.

#</ol>#%\end{enumerate}% *)
