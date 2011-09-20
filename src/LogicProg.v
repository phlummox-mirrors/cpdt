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
