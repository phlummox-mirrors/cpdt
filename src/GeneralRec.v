(* Copyright (c) 2006, 2011, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List.

Require Import CpdtTactics Coinductive.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{General Recursion}% *)

(** Termination of all programs is a crucial property of Gallina.  Non-terminating programs introduce logical inconsistency, where any theorem can be proved with an infinite loop.  Coq uses a small set of conservative, syntactic criteria to check termination of all recursive definitions.  These criteria are insufficient to support the natural encodings of a variety of important programming idioms.  Further, since Coq makes it so convenient to encode mathematics computationally, with functional programs, we may find ourselves wanting to employ more complicated recursion in mathematical definitions.

   What exactly are the conservative criteria that we run up against?  For %\emph{%#<i>#recursive#</i>#%}% definitions, recursive calls are only allowed on %\emph{%#<i>#syntactic subterms#</i>#%}% of the original primary argument, a restriction known as %\index{primitive recursion}\emph{%#<i>#primitive recursion#</i>#%}%.  In fact, Coq's handling of reflexive inductive types (those defined in terms of functions returning the same type) gives a bit more flexibility than in traditional primitive recursion, but the term is still applied commonly.  In Chapter 5, we saw how %\emph{%#<i>#co-recursive#</i>#%}% definitions are checked against a syntactic guardness condition that guarantees productivity.

   Many natural recursion patterns satisfy neither condition.  For instance, there is our simple running example in this chapter, merge sort.  We will study three different approaches to more flexible recursion, and the latter two of the approaches will even support definitions that may fail to terminate on certain inputs, without any up-front characterization of which inputs those may be.

   Before proceeding, it is important to note that the problem here is not as fundamental as it may appear.  The final example of Chapter 5 demonstrated what is called a %\index{deep embedding}\emph{%#<i>#deep embedding#</i>#%}% of the syntax and semantics of a programming language.  That is, we gave a mathematical definition of a language of programs and their meanings.  This language clearly admitted non-termination, and we could think of writing all our sophisticated recursive functions with such explicit syntax types.  However, in doing so, we forfeit our chance to take advantage of Coq's very good built-in support for reasoning about Gallina programs.  We would rather use a %\index{shallow embedding}\emph{%#<i>#shallow embedding#</i>#%}%, where we model informal constructs by encoding them as normal Gallina programs.  Each of the three techniques of this chapter follows that style. *)


(** * Well-Founded Recursion *)

(** The essence of terminating recursion is that there are no infinite chains of nested recursive calls.  This intuition is commonly mapped to the mathematical idea of a %\index{well-founded relation}\emph{%#<i>#well-founded relation#</i>#%}%, and the associated standard technique in Coq is %\index{well-founded recursion}\emph{%#<i>#well-founded recursion#</i>#%}%.  The syntactic-subterm relation that Coq applies by default is well-founded, but many cases demand alternate well-founded relations.  To demonstrate, let us see where we get stuck on attempting a standard merge sort implementation. *)

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.
  (** We have a set equipped with some %``%#"#less-than-or-equal-to#"#%''% test. *)

  (** A standard function inserts an element into a sorted list, preserving sortedness. *)

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
	if le x h
	  then x :: ls
	  else h :: insert x ls'
    end.

  (** We will also need a function to merge two sorted lists.  (We use a less efficient implementation than usual, because the more efficient implementation already forces us to think about well-founded recursion, while here we are only interested in setting up the example of merge sort.) *)

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

  (** The last helper function for classic merge sort is the one that follows, to partition a list arbitrarily into two pieces of approximately equal length. *)

  Fixpoint partition (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
	let (ls1, ls2) := partition ls' in
	  (h1 :: ls1, h2 :: ls2)
    end.

  (** Now, let us try to write the final sorting function, using a natural number %``%#"#[<=]#"#%''% test [leb] from the standard library.
[[
  Fixpoint mergeSort (ls : list A) : list A :=
    if leb (length ls) 2
      then ls
      else let lss := partition ls in
	merge (mergeSort (fst lss)) (mergeSort (snd lss)).
]]

<<
Recursive call to mergeSort has principal argument equal to
"fst (partition ls)" instead of a subterm of "ls".
>>

The definition is rejected for not following the simple primitive recursion criterion.  In particular, it is not apparent that recursive calls to [mergeSort] are syntactic subterms of the original argument [ls]; indeed, they are not, yet we know this is a well-founded recursive definition.

To produce an acceptable definition, we need to choose a well-founded relation and prove that [mergeSort] respects it.  A good starting point is an examination of how well-foundedness is formalized in the Coq standard library. *)

  Print well_founded.
  (** %\vspace{-.15in}% [[
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
]]

The bulk of the definitional work devolves to the %\index{accessibility relation}\index{Gallina terms!Acc}\emph{%#<i>#accessibility#</i>#%}% relation [Acc], whose definition we may also examine. *)

  Print Acc.
(** %\vspace{-.15in}% [[
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
]]

In prose, an element [x] is accessible for a relation [R] if every element %``%#"#less than#"#%''% [x] according to [R] is also accessible.  Since [Acc] is defined inductively, we know that any accessibility proof involves a finite chain of invocations, in a certain sense which we can make formal.  Building on Chapter 5's examples, let us define a co-inductive relation that is closer to the usual informal notion of %``%#"#absence of infinite decreasing chains.#"#%''% *)

  CoInductive isChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s, isChain R (Cons y s)
    -> R y x
    -> isChain R (Cons x (Cons y s)).

(** We can now prove that any accessible element cannot be the beginning of any infinite decreasing chain. *)

(* begin thide *)
  Lemma noChains' : forall A (R : A -> A -> Prop) x, Acc R x
    -> forall s, ~isChain R (Cons x s).
    induction 1; crush;
      match goal with
        | [ H : isChain _ _ |- _ ] => inversion H; eauto
      end.
  Qed.

(** From here, the absence of infinite decreasing chains in well-founded sets is immediate. *)

  Theorem noChains : forall A (R : A -> A -> Prop), well_founded R
    -> forall s, ~isChain R s.
    destruct s; apply noChains'; auto.
  Qed.
(* end thide *)

(** Absence of infinite decreasing chains implies absence of infinitely nested recursive calls, for any recursive definition that respects the well-founded relation.  The [Fix] combinator from the standard library formalizes that intuition: *)

  Check Fix.
(** %\vspace{-.15in}%[[
Fix
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall x : A, P x
]]

A call to %\index{Gallina terms!Fix}%[Fix] must present a relation [R] and a proof of its well-foundedness.  The next argument, [P], is the possibly dependent range type of the function we build; the domain [A] of [R] is the function's domain.  The following argument has this type:

[[
       forall x : A, (forall y : A, R y x -> P y) -> P x
]]

This is an encoding of the function body.  The input [x] stands for the function argument, and the next input stands for the function we are defining.  Recursive calls are encoded as calls to the second argument, whose type tells us it expects a value [y] and a proof that [y] is %``%#"#less than#"#%''% [x], according to [R].  In this way, we enforce the well-foundedness restriction on recursive calls.

The rest of [Fix]'s type tells us that it returns a function of exactly the type we expect, so we are now ready to use it to implement [mergeSort].  Careful readers may have noticed that [Fix] has a dependent type of the sort we met in the previous chapter.

Before writing [mergeSort], we need to settle on a well-founded relation.  The right one for this example is based on lengths of lists. *)

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  (** We must prove that the relation is truly well-founded.  To save some space in the rest of this chapter, we skip right to nice, automated proof scripts, though we postpone introducing the principles behind such scripts to Part III of the book.  Curious readers may still replace semicolons with periods and newlines to step through these scripts interactively. *)

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red; intro; eapply lengthOrder_wf'; eauto.
  Defined.

  (** Notice that we end these proofs with %\index{Vernacular commands!Defined}%[Defined], not [Qed].  Recall that [Defined] marks the theorems as %\emph{transparent}%, so that the details of their proofs may be used during program execution.  Why could such details possibly matter for computation?  It turns out that [Fix] satisfies the primitive recursion restriction by declaring itself as %\emph{%#<i>#recursive in the structure of [Acc] proofs#</i>#%}%.  This is possible because [Acc] proofs follow a predictable inductive structure.  We must do work, as in the last theorem's proof, to establish that all elements of a type belong to [Acc], but the automatic unwinding of those proofs during recursion is straightforward.  If we ended the proof with [Qed], the proof details would be hidden from computation, in which case the unwinding process would get stuck.

     To justify our two recursive [mergeSort] calls, we will also need to prove that [partition] respects the [lengthOrder] relation.  These proofs, too, must be kept transparent, to avoid stuckness of [Fix] evaluation. *)

  Lemma partition_wf : forall len ls, 2 <= length ls <= len
    -> let (ls1, ls2) := partition ls in
      lengthOrder ls1 ls /\ lengthOrder ls2 ls.
    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (length ls));
        repeat (match goal with
                  | [ _ : length ?E < 2 |- _ ] => destruct E
                  | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                  | [ IH : _ |- context[partition ?L] ] =>
                    specialize (IH L); destruct (partition L); destruct IH
                end; crush).
  Defined.

  Ltac partition := intros ls ?; intros; generalize (@partition_wf (length ls) ls);
    destruct (partition ls); destruct 1; crush.

  Lemma partition_wf1 : forall ls, 2 <= length ls
    -> lengthOrder (fst (partition ls)) ls.
    partition.
  Defined.

  Lemma partition_wf2 : forall ls, 2 <= length ls
    -> lengthOrder (snd (partition ls)) ls.
    partition.
  Defined.

  Hint Resolve partition_wf1 partition_wf2.

  (** To write the function definition itself, we use the %\index{tactics!refine}%[refine] tactic as a convenient way to write a program that needs to manipulate proofs, without writing out those proofs manually.  We also use a replacement [le_lt_dec] for [leb] that has a more interesting dependent type. *)

  Definition mergeSort : list A -> list A.
(* begin thide *)
    refine (Fix lengthOrder_wf (fun _ => list A)
      (fun (ls : list A)
        (mergeSort : forall ls' : list A, lengthOrder ls' ls -> list A) =>
        if le_lt_dec 2 (length ls)
	  then let lss := partition ls in
            merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
	  else ls)); subst lss; eauto.
  Defined.
(* end thide *)
End mergeSort.

(** The important thing is that it is now easy to evaluate calls to [mergeSort]. *)

Eval compute in mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).
(** [= 1 :: 2 :: 8 :: 19 :: 36 :: nil] *)

(** Since the subject of this chapter is merely how to define functions with unusual recursion structure, we will not prove any further correctness theorems about [mergeSort]. Instead, we stop at proving that [mergeSort] has the expected computational behavior, for all inputs, not merely the one we just tested. *)

(* begin thide *)
Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls,
  mergeSort le ls = if le_lt_dec 2 (length ls)
    then let lss := partition ls in
      merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
    else ls.
  intros; apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)); intros.

  (** The library theorem [Fix_eq] imposes one more strange subgoal upon us.  We must prove that the function body is unable to distinguish between %``%#"#self#"#%''% arguments that map equal inputs to equal outputs.  One might think this should be true of any Gallina code, but in fact this general %\index{extensionality}\emph{%#<i>#function extensionality#</i>#%}% property is neither provable nor disprovable within Coq.  The type of [Fix_eq] makes clear what we must show manually: *)

  Check Fix_eq.
(** %\vspace{-.15in}%[[
Fix_eq
     : forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
         (P : A -> Type)
         (F : forall x : A, (forall y : A, R y x -> P y) -> P x),
       (forall (x : A) (f g : forall y : A, R y x -> P y),
        (forall (y : A) (p : R y x), f y p = g y p) -> F x f = F x g) ->
       forall x : A,
       Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y)
]]

  Most such obligations are dischargable with straightforward proof automation, and this example is no exception. *)

  match goal with
    | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
  end; simpl; f_equal; auto.
Qed.
(* end thide *)

(** As a final test of our definition's suitability, we can extract to OCaml. *)

Extraction mergeSort.

(** <<
let rec mergeSort le x =
  match le_lt_dec (S (S O)) (length x) with
  | Left ->
    let lss = partition x in
    merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
  | Right -> x
>>

  We see almost precisely the same definition we would have written manually in OCaml!  It might be a good exercise for the reader to use the commands we saw in the previous chapter to clean up some remaining differences from idiomatic OCaml.

  One more piece of the full picture is missing.  To go on and prove correctness of [mergeSort], we would need more than a way of unfolding its definition.  We also need an appropriate induction principle matched to the well-founded relation.  Such a principle is available in the standard library, though we will say no more about its details here. *)

Check well_founded_induction.
(** %\vspace{-.15in}%[[
well_founded_induction
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Set,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall a : A, P a
]]

  Some more recent Coq features provide more convenient syntax for defining recursive functions.  Interested readers can consult the Coq manual about the commands %\index{Function}%[Function] and %\index{Program Fixpoint}%[Program Fixpoint]. *)


(** * A Non-Termination Monad *)

Section computation.
  Variable A : Type.

  Definition computation :=
    {f : nat -> option A
      | forall (n : nat) (v : A),
	f n = Some v
	-> forall (n' : nat), n' >= n
	  -> f n' = Some v}.

  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
End computation.

Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N); try rewrite (H _ (refl_equal _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] => rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run'; repeat (match goal with
                            | [ H : forall n v, ?E n = Some v -> _
                                |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
                              specialize (H N); destruct (E N); try rewrite (H _ (refl_equal _)) by auto; try discriminate
                          end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
  exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.

Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    exists (fun _ : nat => @None A); abstract run.
  Defined.

  Theorem run_Bottom : forall v, ~run Bottom v.
    run.
  Qed.
End Bottom.

Section Return.
  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
    intros; exists (fun _ : nat => Some v); abstract run.
  Defined.

  Theorem run_Return : run Return v.
    run.
  Qed.

  Theorem run_Return_inv : forall x, run Return x -> x = v.
    run.
  Qed.
End Return.

Hint Resolve run_Return.

Section Bind.
  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
    exists (fun n =>
      let (f1, Hf1) := m1 in
      match f1 n with
	| None => None
	| Some v =>
	  let (f2, Hf2) := m2 v in
	    f2 n
      end); abstract run.
  Defined.

  Require Import Max.

  Theorem run_Bind : forall (v1 : A) (v2 : B),
    run m1 v1
    -> run (m2 v1) v2
    -> run Bind v2.
    run; match goal with
           | [ x : nat, y : nat |- _ ] => exists (max x y)
         end; run.
  Qed.

  Theorem run_Bind_inv : forall (v2 : B),
    run Bind v2
    -> exists v1 : A,
      run m1 v1
      /\ run (m2 v1) v2.
    run.
  Qed.
End Bind.

Hint Resolve run_Bind.

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

Definition meq A (m1 m2 : computation A) := forall n, proj1_sig m1 n = proj1_sig m2 n.

Theorem left_identity : forall A B (a : A) (f : A -> computation B),
  meq (Bind (Return a) f) (f a).
  run.
Qed.

Theorem right_identity : forall A (m : computation A),
  meq (Bind m (@Return _)) m.
  run.
Qed.

Theorem associativity : forall A B C (m : computation A) (f : A -> computation B) (g : B -> computation C),
  meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
  run.
Qed.

Section monotone_runTo.
  Variable A : Type.
  Variable c : computation A.
  Variable v : A.

  Theorem monotone_runTo : forall (n1 : nat),
    runTo c n1 v
    -> forall n2, n2 >= n1
      -> runTo c n2 v.
    run.
  Qed.
End monotone_runTo.

Hint Resolve monotone_runTo.

Section lattice.
  Variable A : Type.

  Definition leq (x y : option A) :=
    forall v, x = Some v -> y = Some v.
End lattice.

Hint Unfold leq.

Section Fix.
  Variables A B : Type.
  Variable f : (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous : forall n v v1 x,
    runTo (f v1 x) n v
    -> forall (v2 : A -> computation B),
      (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n))
      -> runTo (f v2 x) n v.

  Fixpoint Fix' (n : nat) (x : A) : computation B :=
    match n with
      | O => Bottom _
      | S n' => f (Fix' n') x
    end.

  Hint Extern 1 (_ >= _) => omega.
  Hint Unfold leq.

  Lemma Fix'_ok : forall steps n x v, proj1_sig (Fix' n x) steps = Some v
    -> forall n', n' >= n
      -> proj1_sig (Fix' n' x) steps = Some v.
    unfold runTo in *; induction n; crush;
      match goal with
        | [ H : _ >= _ |- _ ] => inversion H; crush; eauto
      end.
  Qed.

  Hint Resolve Fix'_ok.

  Hint Extern 1 (proj1_sig _ _ = _) => simpl;
    match goal with
      | [ |- proj1_sig ?E _ = _ ] => eapply (proj2_sig E)
    end.

  Definition Fix : A -> computation B.
    intro x; exists (fun n => proj1_sig (Fix' n x) n); abstract run.
  Defined.

  Definition extensional (f : (A -> computation B) -> (A -> computation B)) := 
    forall g1 g2 n,
      (forall x, proj1_sig (g1 x) n = proj1_sig (g2 x) n)
      -> forall x, proj1_sig (f g1 x) n = proj1_sig (f g2 x) n.

  Hypothesis f_extensional : extensional f.

  Theorem run_Fix : forall x v,
    run (f Fix x) v
    -> run (Fix x) v.
    run; match goal with
           | [ n : nat |- _ ] => exists (S n); eauto
         end.
  Qed.
End Fix.

Hint Resolve run_Fix.

Lemma leq_Some : forall A (x y : A), leq (Some x) (Some y)
  -> x = y.
  intros ? ? ? H; generalize (H _ (refl_equal _)); crush.
Qed.

Lemma leq_None : forall A (x y : A), leq (Some x) None
  -> False.
  intros ? ? ? H; generalize (H _ (refl_equal _)); crush.
Qed.

Definition mergeSort' : forall A, (A -> A -> bool) -> list A -> computation (list A).
  refine (fun A le => Fix
    (fun (mergeSort : list A -> computation (list A))
      (ls : list A) =>
      if le_lt_dec 2 (length ls)
	then let lss := partition ls in
          ls1 <- mergeSort (fst lss);
          ls2 <- mergeSort (snd lss);
          Return (merge le ls1 ls2)
	else Return ls) _); abstract (run;
          repeat (match goal with
                    | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
                  end; run);
          repeat match goal with
                   | [ H : forall x, leq (proj1_sig (?f x) _) (proj1_sig (?g x) _) |- _ ] =>
                     match goal with
                       | [ H1 : f ?arg = _, H2 : g ?arg = _ |- _ ] =>
                         generalize (H arg); rewrite H1; rewrite H2; clear H1 H2; simpl; intro
                     end
                 end; run; repeat match goal with
                                    | [ H : _ |- _ ] => (apply leq_None in H; tauto) || (apply leq_Some in H; subst)
                                  end; auto).
Defined.

Print mergeSort'.

Lemma test_mergeSort' : run (mergeSort' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  exists 4; reflexivity.
Qed.

Definition looper : bool -> computation unit.
  refine (Fix (fun looper (b : bool) =>
    if b then Return tt else looper b) _);
  abstract (unfold leq in *; run;
    repeat match goal with
             | [ x : unit |- _ ] => destruct x
             | [ x : bool |- _ ] => destruct x
           end; auto).
Defined.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.
