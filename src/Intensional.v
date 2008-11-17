(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith Bool String List Eqdep JMeq.

Require Import Axioms Tactics DepList.

Set Implicit Arguments.

Infix "==" := JMeq (at level 70, no associativity).
(* end hide *)




(** %\chapter{Intensional Transformations}% *)

(** TODO: Prose for this chapter *)


(** * Closure Conversion *)

Module Source.
  Inductive type : Type :=
  | TNat : type
  | Arrow : type -> type -> type.

  Notation "'Nat'" := TNat : source_scope.
  Infix "-->" := Arrow (right associativity, at level 60) : source_scope.

  Open Scope source_scope.
  Bind Scope source_scope with type.
  Delimit Scope source_scope with source.

  Section vars.
    Variable var : type -> Type.

    Inductive exp : type -> Type :=
    | Var : forall t,
      var t
      -> exp t

    | Const : nat -> exp Nat
    | Plus : exp Nat -> exp Nat -> exp Nat

    | App : forall t1 t2,
      exp (t1 --> t2)
      -> exp t1
      -> exp t2
    | Abs : forall t1 t2,
      (var t1 -> exp t2)
      -> exp (t1 --> t2).
  End vars.

  Definition Exp t := forall var, exp var t.

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments Plus [var].
  Implicit Arguments App [var t1 t2].
  Implicit Arguments Abs [var t1 t2].

  Notation "# v" := (Var v) (at level 70) : source_scope.

  Notation "^ n" := (Const n) (at level 70) : source_scope.
  Infix "+^" := Plus (left associativity, at level 79) : source_scope.

  Infix "@" := App (left associativity, at level 77) : source_scope.
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78) : source_scope.
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78) : source_scope.

  Bind Scope source_scope with exp.

  Definition zero : Exp Nat := fun _ => ^0.
  Definition one : Exp Nat := fun _ => ^1.
  Definition zpo : Exp Nat := fun _ => zero _ +^ one _.
  Definition ident : Exp (Nat --> Nat) := fun _ => \x, #x.
  Definition app_ident : Exp Nat := fun _ => ident _ @ zpo _.
  Definition app : Exp ((Nat --> Nat) --> Nat --> Nat) := fun _ =>
    \f, \x, #f @ #x.
  Definition app_ident' : Exp Nat := fun _ => app _ @ ident _ @ zpo _.

  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
    end.

  Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
    match e in (exp _ t) return (typeDenote t) with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).

  Section exp_equiv.
    Variables var1 var2 : type -> Type.

    Inductive exp_equiv : list { t : type & var1 t * var2 t }%type -> forall t, exp var1 t -> exp var2 t -> Prop :=
    | EqVar : forall G t (v1 : var1 t) v2,
      In (existT _ t (v1, v2)) G
      -> exp_equiv G (#v1) (#v2)

    | EqConst : forall G n,
      exp_equiv G (^n) (^n)
    | EqPlus : forall G x1 y1 x2 y2,
      exp_equiv G x1 x2
      -> exp_equiv G y1 y2
      -> exp_equiv G (x1 +^ y1) (x2 +^ y2)

    | EqApp : forall G t1 t2 (f1 : exp _ (t1 --> t2)) (x1 : exp _ t1) f2 x2,
      exp_equiv G f1 f2
      -> exp_equiv G x1 x2
      -> exp_equiv G (f1 @ x1) (f2 @ x2)
    | EqAbs : forall G t1 t2 (f1 : var1 t1 -> exp var1 t2) f2,
      (forall v1 v2, exp_equiv (existT _ t1 (v1, v2) :: G) (f1 v1) (f2 v2))
      -> exp_equiv G (Abs f1) (Abs f2).
  End exp_equiv.

  Axiom Exp_equiv : forall t (E : Exp t) var1 var2,
    exp_equiv nil (E var1) (E var2).
End Source.

Module Closed.
  Inductive type : Type :=
  | TNat : type
  | Arrow : type -> type -> type
  | Code : type -> type -> type -> type
  | Prod : type -> type -> type
  | TUnit : type.

  Notation "'Nat'" := TNat : cc_scope.
  Notation "'Unit'" := TUnit : cc_scope.
  Infix "-->" := Arrow (right associativity, at level 60) : cc_scope.
  Infix "**" := Prod (right associativity, at level 59) : cc_scope.
  Notation "env @@ dom ---> ran" := (Code env dom ran) (no associativity, at level 62, dom at next level) : cc_scope.

  Bind Scope cc_scope with type.
  Delimit Scope cc_scope with cc.

  Open Local Scope cc_scope.

  Section vars.
    Variable var : type -> Set.

    Inductive exp : type -> Type :=
    | Var : forall t,
      var t
      -> exp t

    | Const : nat -> exp Nat
    | Plus : exp Nat -> exp Nat -> exp Nat

    | App : forall dom ran,
      exp (dom --> ran)
      -> exp dom
      -> exp ran

    | Pack : forall env dom ran,
      exp (env @@ dom ---> ran)
      -> exp env
      -> exp (dom --> ran)

    | EUnit : exp Unit

    | Pair : forall t1 t2,
      exp t1
      -> exp t2
      -> exp (t1 ** t2)
    | Fst : forall t1 t2,
      exp (t1 ** t2)
      -> exp t1
    | Snd : forall t1 t2,
      exp (t1 ** t2)
      -> exp t2

    | Let : forall t1 t2,
      exp t1
      -> (var t1 -> exp t2)
      -> exp t2.

    Section funcs.
      Variable T : Type.

      Inductive funcs : Type :=
      | Main : T -> funcs
      | Abs : forall env dom ran,
        (var env -> var dom -> exp ran)
        -> (var (env @@ dom ---> ran) -> funcs)
        -> funcs.
    End funcs.

    Definition prog t := funcs (exp t).
  End vars.

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments EUnit [var].
  Implicit Arguments Fst [var t1 t2].
  Implicit Arguments Snd [var t1 t2].

  Implicit Arguments Main [var T].
  Implicit Arguments Abs [var T env dom ran].

  Notation "# v" := (Var v) (at level 70) : cc_scope.

  Notation "^ n" := (Const n) (at level 70) : cc_scope.
  Infix "+^" := Plus (left associativity, at level 79) : cc_scope.

  Infix "@" := App (left associativity, at level 77) : cc_scope.
  Infix "##" := Pack (no associativity, at level 71) : cc_scope.

  Notation "()" := EUnit : cc_scope.

  Notation "[ x1 , x2 ]" := (Pair x1 x2) (at level 73) : cc_scope.
  Notation "#1 x" := (Fst x) (at level 72) : cc_scope.
  Notation "#2 x" := (Snd x) (at level 72) : cc_scope.

  Notation "f <== \\ x , y , e ; fs" :=
    (Abs (fun x y => e) (fun f => fs))
    (right associativity, at level 80, e at next level) : cc_scope.
  Notation "f <== \\ ! , y , e ; fs" :=
    (Abs (fun _ y => e) (fun f => fs))
    (right associativity, at level 80, e at next level) : cc_scope.
  Notation "f <== \\ x , ! , e ; fs" :=
    (Abs (fun x _ => e) (fun f => fs))
    (right associativity, at level 80, e at next level) : cc_scope.
  Notation "f <== \\ ! , ! , e ; fs" :=
    (Abs (fun _ _ => e) (fun f => fs))
    (right associativity, at level 80, e at next level) : cc_scope.

  Notation "x <- e1 ; e2" := (Let e1 (fun x => e2))
    (right associativity, at level 80, e1 at next level) : cc_scope.

  Bind Scope cc_scope with exp funcs prog.

  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | Unit => unit
      | dom --> ran => typeDenote dom -> typeDenote ran
      | t1 ** t2 => typeDenote t1 * typeDenote t2
      | env @@ dom ---> ran => typeDenote env -> typeDenote dom -> typeDenote ran
    end%type.

  Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
    match e in (exp _ t) return (typeDenote t) with
      | Var _ v => v

      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2

      | App _ _ f x => (expDenote f) (expDenote x)
      | Pack _ _ _ f env => (expDenote f) (expDenote env)

      | EUnit => tt

      | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
      | Fst _ _ e' => fst (expDenote e')
      | Snd _ _ e' => snd (expDenote e')

      | Let _ _ e1 e2 => expDenote (e2 (expDenote e1))
    end.

  Fixpoint funcsDenote T (fs : funcs typeDenote T) : T :=
    match fs with
      | Main v => v
      | Abs _ _ _ e fs =>
        funcsDenote (fs (fun env arg => expDenote (e env arg)))
    end.

  Definition progDenote t (p : prog typeDenote t) : typeDenote t :=
    expDenote (funcsDenote p).

  Definition Exp t := forall var, exp var t.
  Definition Prog t := forall var, prog var t.

  Definition ExpDenote t (E : Exp t) := expDenote (E _).
  Definition ProgDenote t (P : Prog t) := progDenote (P _).
End Closed.

Import Source Closed.

Section splice.
  Open Local Scope cc_scope.

  Fixpoint spliceFuncs var T1 (fs : funcs var T1)
    T2 (f : T1 -> funcs var T2) {struct fs} : funcs var T2 :=
    match fs with
      | Main v => f v
      | Abs _ _ _ e fs' => Abs e (fun x => spliceFuncs (fs' x) f)
    end.
End splice.

Notation "x <-- e1 ; e2" := (spliceFuncs e1 (fun x => e2))
  (right associativity, at level 80, e1 at next level) : cc_scope.

Definition natvar (_ : Source.type) := nat.
Definition isfree := hlist (fun (_ : Source.type) => bool).

Ltac maybe_destruct E :=
  match goal with
    | [ x : _ |- _ ] =>
      match E with
        | x => idtac
      end
    | _ =>
      match E with
        | eq_nat_dec _ _ => idtac
      end
  end; destruct E.

Ltac my_crush :=
  crush; repeat (match goal with
                   | [ x : (_ * _)%type |- _ ] => destruct x
                   | [ |- context[if ?B then _ else _] ] => maybe_destruct B
                   | [ _ : context[if ?B then _ else _] |- _ ] => maybe_destruct B
                 end; crush).

Section isfree.
  Import Source.
  Open Local Scope source_scope.

  Fixpoint lookup_type (envT : list Source.type) (n : nat) {struct envT}
    : isfree envT -> option Source.type :=
    match envT return (isfree envT -> _) with
      | nil => fun _ => None
      | first :: rest => fun fvs =>
        if eq_nat_dec n (length rest)
          then match fvs with
                 | (true, _) => Some first
                 | (false, _) => None
               end
          else lookup_type rest n (snd fvs)
    end.
  
  Implicit Arguments lookup_type [envT].

  Notation ok := (fun (envT : list Source.type) (fvs : isfree envT)
    (n : nat) (t : Source.type)
    => lookup_type n fvs = Some t).

  Fixpoint wfExp (envT : list Source.type) (fvs : isfree envT)
    t (e : Source.exp natvar t) {struct e} : Prop :=
    match e with
      | Var t v => ok envT fvs v t

      | Const _ => True
      | Plus e1 e2 => wfExp envT fvs e1 /\ wfExp envT fvs e2

      | App _ _ e1 e2 => wfExp envT fvs e1 /\ wfExp envT fvs e2
      | Abs dom _ e' => wfExp (dom :: envT) (true ::: fvs) (e' (length envT))
    end.

  Implicit Arguments wfExp [envT t].

  Theorem wfExp_weaken : forall t (e : exp natvar t) envT (fvs fvs' : isfree envT),
    wfExp fvs e
    -> (forall n t, ok _ fvs n t -> ok _ fvs' n t)
    -> wfExp fvs' e.
    Hint Extern 1 (lookup_type (envT := _ :: _) _ _ = Some _) =>
      simpl in *; my_crush.

    induction e; my_crush; eauto.
  Defined.

  Fixpoint isfree_none (envT : list Source.type) : isfree envT :=
    match envT return (isfree envT) with
      | nil => tt
      | _ :: _ => (false, isfree_none _)
    end.

  Implicit Arguments isfree_none [envT].

  Fixpoint isfree_one (envT : list Source.type) (n : nat) {struct envT} : isfree envT :=
    match envT return (isfree envT) with
      | nil => tt
      | _ :: rest =>
        if eq_nat_dec n (length rest)
          then (true, isfree_none)
          else (false, isfree_one _ n)
    end.

  Implicit Arguments isfree_one [envT].

  Fixpoint isfree_merge (envT : list Source.type) : isfree envT -> isfree envT -> isfree envT :=
    match envT return (isfree envT -> isfree envT -> isfree envT) with
      | nil => fun _ _ => tt
      | _ :: _ => fun fv1 fv2 => (fst fv1 || fst fv2, isfree_merge _ (snd fv1) (snd fv2))
    end.

  Implicit Arguments isfree_merge [envT].

  Fixpoint fvsExp t (e : exp natvar t)
    (envT : list Source.type) {struct e} : isfree envT :=
    match e with
      | Var _ n => isfree_one n

      | Const _ => isfree_none
      | Plus e1 e2 => isfree_merge (fvsExp e1 envT) (fvsExp e2 envT)

      | App _ _ e1 e2 => isfree_merge (fvsExp e1 envT) (fvsExp e2 envT)
      | Abs dom _ e' => snd (fvsExp (e' (length envT)) (dom :: envT))
    end.

  Lemma isfree_one_correct : forall t (v : natvar t) envT fvs,
    ok envT fvs v t
    -> ok envT (isfree_one (envT:=envT) v) v t.
    induction envT; my_crush; eauto.
  Defined.

  Lemma isfree_merge_correct1 : forall t (v : natvar t) envT fvs1 fvs2,
    ok envT fvs1 v t
    -> ok envT (isfree_merge (envT:=envT) fvs1 fvs2) v t.
    induction envT; my_crush; eauto.
  Defined.

  Hint Rewrite orb_true_r : cpdt.

  Lemma isfree_merge_correct2 : forall t (v : natvar t) envT fvs1 fvs2,
    ok envT fvs2 v t
    -> ok envT (isfree_merge (envT:=envT) fvs1 fvs2) v t.
    induction envT; my_crush; eauto.
  Defined.

  Hint Resolve isfree_one_correct isfree_merge_correct1 isfree_merge_correct2.
  
  Lemma fvsExp_correct : forall t (e : exp natvar t)
    envT (fvs : isfree envT), wfExp fvs e
    -> forall (fvs' : isfree envT),
      (forall v t, ok envT (fvsExp e envT) v t -> ok envT fvs' v t)
      -> wfExp fvs' e.
    Hint Extern 1 (_ = _) =>
      match goal with
        | [ H : lookup_type _ (fvsExp ?X ?Y) = _ |- _ ] =>
          destruct (fvsExp X Y); my_crush
      end.

    induction e; my_crush; eauto.
  Defined.

  Lemma lookup_type_unique : forall v t1 t2 envT (fvs1 fvs2 : isfree envT),
    lookup_type v fvs1 = Some t1
    -> lookup_type v fvs2 = Some t2
    -> t1 = t2.
    induction envT; my_crush; eauto.
  Defined.

  Implicit Arguments lookup_type_unique [v t1 t2 envT fvs1 fvs2].

  Hint Extern 2 (lookup_type _ _ = Some _) =>
    match goal with
      | [ H1 : lookup_type ?v _ = Some _,
        H2 : lookup_type ?v _ = Some _ |- _ ] =>
      (generalize (lookup_type_unique H1 H2); intro; subst)
      || rewrite <- (lookup_type_unique H1 H2)
    end.

  Lemma lookup_none : forall v t envT,
    lookup_type (envT:=envT) v (isfree_none (envT:=envT)) = Some t
    -> False.
    induction envT; my_crush.
  Defined.

  Hint Extern 2 (_ = _) => elimtype False; eapply lookup_none; eassumption.

  Lemma lookup_one : forall v' v t envT,
    lookup_type (envT:=envT) v' (isfree_one (envT:=envT) v) = Some t
    -> v' = v.
    induction envT; my_crush.
  Defined.

  Implicit Arguments lookup_one [v' v t envT].

  Hint Extern 2 (lookup_type _ _ = Some _) =>
    match goal with
      | [ H : lookup_type _ _ = Some _ |- _ ] =>
        generalize (lookup_one H); intro; subst
    end.

  Lemma lookup_merge : forall v t envT (fvs1 fvs2 : isfree envT),
    lookup_type v (isfree_merge fvs1 fvs2) = Some t
    -> lookup_type v fvs1 = Some t
    \/ lookup_type v fvs2 = Some t.
    induction envT; my_crush.
  Defined.

  Implicit Arguments lookup_merge [v t envT fvs1 fvs2].

  Lemma lookup_bound : forall v t envT (fvs : isfree envT),
    lookup_type v fvs = Some t
    -> v < length envT.
    Hint Resolve lt_S.
    induction envT; my_crush; eauto.
  Defined.

  Hint Resolve lookup_bound.

  Lemma lookup_bound_contra : forall t envT (fvs : isfree envT),
    lookup_type (length envT) fvs = Some t
    -> False.
    intros; assert (length envT < length envT); eauto; crush.
  Defined.

  Hint Resolve lookup_bound_contra.

  Lemma lookup_push_drop : forall v t t' envT fvs,
    v < length envT
    -> lookup_type (envT := t :: envT) v (true, fvs) = Some t'
    -> lookup_type (envT := envT) v fvs = Some t'.
    my_crush.
  Defined.

  Lemma lookup_push_add : forall v t t' envT fvs,
    lookup_type (envT := envT) v (snd fvs) = Some t'
    -> lookup_type (envT := t :: envT) v fvs = Some t'.
    my_crush; elimtype False; eauto.
  Defined.

  Hint Resolve lookup_bound lookup_push_drop lookup_push_add.

  Theorem fvsExp_minimal : forall t (e : exp natvar t)
    envT (fvs : isfree envT), wfExp fvs e
    -> (forall v t, ok envT (fvsExp e envT) v t -> ok envT fvs v t).
    Hint Extern 1 (_ = _) =>
      match goal with
        | [ H : lookup_type _ (isfree_merge _ _) = Some _ |- _ ] =>
          destruct (lookup_merge H); clear H; eauto
      end.

    induction e; my_crush; eauto.
  Defined.

  Fixpoint ccType (t : Source.type) : Closed.type :=
    match t with
      | Nat%source => Nat
      | (dom --> ran)%source => ccType dom --> ccType ran
    end%cc.

  Open Local Scope cc_scope.

  Fixpoint envType (envT : list Source.type) : isfree envT -> Closed.type :=
    match envT return (isfree envT -> _) with
      | nil => fun _ => Unit
      | t :: _ => fun tup =>
        if fst tup
          then ccType t ** envType _ (snd tup)
          else envType _ (snd tup)
    end.

  Implicit Arguments envType [envT].

  Fixpoint envOf (var : Closed.type -> Set) (envT : list Source.type) {struct envT}
    : isfree envT -> Set :=
    match envT return (isfree envT -> _) with
      | nil => fun _ => unit
      | first :: rest => fun fvs =>
        match fvs with
          | (true, fvs') => (var (ccType first) * envOf var rest fvs')%type
          | (false, fvs') => envOf var rest fvs'
        end
    end.

  Implicit Arguments envOf [envT].

  Notation "var <| to" := (match to with
                             | None => unit
                             | Some t => var (ccType t)
                           end) (no associativity, at level 70).

  Fixpoint lookup (var : Closed.type -> Set) (envT : list Source.type) :
    forall (n : nat) (fvs : isfree envT), envOf var fvs -> var <| lookup_type n fvs :=
      match envT return (forall (n : nat) (fvs : isfree envT), envOf var fvs
        -> var <| lookup_type n fvs) with
        | nil => fun _ _ _ => tt
        | first :: rest => fun n fvs =>
          match (eq_nat_dec n (length rest)) as Heq return
            (envOf var (envT := first :: rest) fvs
              -> var <| (if Heq
                then match fvs with
                       | (true, _) => Some first
                       | (false, _) => None
                     end
                else lookup_type n (snd fvs))) with
            | left _ =>
              match fvs return (envOf var (envT := first :: rest) fvs
                -> var <| (match fvs with
                             | (true, _) => Some first
                             | (false, _) => None
                           end)) with
                | (true, _) => fun env => fst env
                | (false, _) => fun _ => tt
              end
            | right _ =>
              match fvs return (envOf var (envT := first :: rest) fvs
                -> var <| (lookup_type n (snd fvs))) with
                | (true, fvs') => fun env => lookup var rest n fvs' (snd env)
                | (false, fvs') => fun env => lookup var rest n fvs' env
              end
          end
      end.

  Theorem lok : forall var n t envT (fvs : isfree envT),
    lookup_type n fvs = Some t
    -> var <| lookup_type n fvs = var (ccType t).
    crush.
  Defined.
End isfree.

Implicit Arguments lookup_type [envT].
Implicit Arguments lookup [envT fvs].
Implicit Arguments wfExp [t envT].
Implicit Arguments envType [envT].
Implicit Arguments envOf [envT].
Implicit Arguments lok [var n t envT fvs].

Section lookup_hints.
  Hint Resolve lookup_bound_contra.

  Hint Resolve lookup_bound_contra.

  Lemma lookup_type_push : forall t' envT (fvs1 fvs2 : isfree envT) b1 b2,
    (forall (n : nat) (t : Source.type),
      lookup_type (envT := t' :: envT) n (b1, fvs1) = Some t ->
      lookup_type (envT := t' :: envT) n (b2, fvs2) = Some t)
    -> (forall (n : nat) (t : Source.type),
      lookup_type n fvs1 = Some t ->
      lookup_type n fvs2 = Some t).
    intros until b2; intro H; intros n t;
      generalize (H n t); my_crush; elimtype False; eauto.
  Defined.

  Lemma lookup_type_push_contra : forall t' envT (fvs1 fvs2 : isfree envT),
    (forall (n : nat) (t : Source.type),
      lookup_type (envT := t' :: envT) n (true, fvs1) = Some t ->
      lookup_type (envT := t' :: envT) n (false, fvs2) = Some t)
    -> False.
    intros until fvs2; intro H; generalize (H (length envT) t'); my_crush.
  Defined.
End lookup_hints.

Section packing.
  Open Local Scope cc_scope.

  Hint Resolve lookup_type_push lookup_type_push_contra.

  Definition packExp (var : Closed.type -> Set) (envT : list Source.type)
    (fvs1 fvs2 : isfree envT)
    : (forall n t, lookup_type n fvs1 = Some t -> lookup_type n fvs2 = Some t)
    -> envOf var fvs2 -> exp var (envType fvs1).
    refine (fix packExp (var : Closed.type -> Set) (envT : list Source.type) {struct envT}
      : forall fvs1 fvs2 : isfree envT,
        (forall n t, lookup_type n fvs1 = Some t -> lookup_type n fvs2 = Some t)
        -> envOf var fvs2 -> exp var (envType fvs1) :=
        match envT return (forall fvs1 fvs2 : isfree envT,
          (forall n t, lookup_type n fvs1 = Some t -> lookup_type n fvs2 = Some t)
          -> envOf var fvs2
          -> exp var (envType fvs1)) with
          | nil => fun _ _ _ _ => ()
          | first :: rest => fun fvs1 =>
            match fvs1 return (forall fvs2 : isfree (first :: rest),
              (forall n t, lookup_type (envT := first :: rest) n fvs1 = Some t
                -> lookup_type n fvs2 = Some t)
              -> envOf var fvs2
              -> exp var (envType (envT := first :: rest) fvs1)) with
              | (false, fvs1') => fun fvs2 =>
                match fvs2 return ((forall n t, lookup_type (envT := first :: rest) n (false, fvs1') = Some t
                  -> lookup_type (envT := first :: rest) n fvs2 = Some t)
                -> envOf (envT := first :: rest) var fvs2
                -> exp var (envType (envT := first :: rest) (false, fvs1'))) with
                  | (false, fvs2') => fun Hmin env =>
                    packExp var _  fvs1' fvs2' _ env
                  | (true, fvs2') => fun Hmin env =>
                    packExp var _  fvs1' fvs2' _ (snd env)
                end
              | (true, fvs1') => fun fvs2 =>
                match fvs2 return ((forall n t, lookup_type (envT := first :: rest) n (true, fvs1') = Some t
                  -> lookup_type (envT := first :: rest) n fvs2 = Some t)
                -> envOf (envT := first :: rest) var fvs2
                -> exp var (envType (envT := first :: rest) (true, fvs1'))) with
                  | (false, fvs2') => fun Hmin env =>
                    False_rect _ _
                  | (true, fvs2') => fun Hmin env =>
                    [#(fst env), packExp var _ fvs1' fvs2' _ (snd env)]
                end
            end
        end); eauto.
  Defined.

  Hint Resolve fvsExp_correct fvsExp_minimal.
  Hint Resolve lookup_push_drop lookup_bound lookup_push_add.

  Implicit Arguments packExp [var envT].

  Fixpoint unpackExp (var : Closed.type -> Set) t (envT : list Source.type) {struct envT}
    : forall fvs : isfree envT,
      exp var (envType fvs)
      -> (envOf var fvs -> exp var t) -> exp var t :=
      match envT return (forall fvs : isfree envT,
        exp var (envType fvs)
        -> (envOf var fvs -> exp var t) -> exp var t) with
        | nil => fun _ _ f => f tt
        | first :: rest => fun fvs =>
          match fvs return (exp var (envType (envT := first :: rest) fvs)
            -> (envOf var (envT := first :: rest) fvs -> exp var t)
            -> exp var t) with
            | (false, fvs') => fun p f =>
              unpackExp rest fvs' p f
            | (true, fvs') => fun p f =>
              x <- #1 p;
              unpackExp rest fvs' (#2 p)
              (fun env => f (x, env))
          end
      end.
  
  Implicit Arguments unpackExp [var t envT fvs].

  Theorem wfExp_lax : forall t t' envT (fvs : isfree envT) (e : Source.exp natvar t),
    wfExp (envT := t' :: envT) (true, fvs) e
    -> wfExp (envT := t' :: envT) (true, snd (fvsExp e (t' :: envT))) e.
    Hint Extern 1 (_ = _) =>
      match goal with
        | [ H : lookup_type _ (fvsExp ?X ?Y) = _ |- _ ] =>
          destruct (fvsExp X Y); my_crush
      end.
    eauto.
  Defined.

  Implicit Arguments wfExp_lax [t t' envT fvs e].

  Lemma inclusion : forall t t' envT fvs (e : Source.exp natvar t),
    wfExp (envT := t' :: envT) (true, fvs) e
    -> (forall n t, lookup_type n (snd (fvsExp e (t' :: envT))) = Some t
      -> lookup_type n fvs = Some t).
    eauto.
  Defined.

  Implicit Arguments inclusion [t t' envT fvs e].

  Definition env_prog var t envT (fvs : isfree envT) :=
    funcs var (envOf var fvs -> Closed.exp var t).

  Implicit Arguments env_prog [envT].

  Import Source.
  Open Local Scope cc_scope.

  Definition proj1 A B (pf : A /\ B) : A :=
    let (x, _) := pf in x.
  Definition proj2 A B (pf : A /\ B) : B :=
    let (_, y) := pf in y.

  Fixpoint ccExp var t (e : Source.exp natvar t)
    (envT : list Source.type) (fvs : isfree envT)
    {struct e} : wfExp fvs e -> env_prog var (ccType t) fvs :=
    match e in (Source.exp _ t) return (wfExp fvs e -> env_prog var (ccType t) fvs) with
      | Const n => fun _ => Main (fun _ => ^n)
      | Plus e1 e2 => fun wf =>
        n1 <-- ccExp var e1 _ fvs (proj1 wf);
        n2 <-- ccExp var e2 _ fvs (proj2 wf);
        Main (fun env => n1 env +^ n2 env)

      | Var _ n => fun wf =>
        Main (fun env => #(match lok wf in _ = T return T with
                             | refl_equal => lookup var n env
                           end))

      | App _ _ f x => fun wf =>
        f' <-- ccExp var f _ fvs (proj1 wf);
        x' <-- ccExp var x _ fvs (proj2 wf);
        Main (fun env => f' env @ x' env)

      | Abs dom _ b => fun wf =>
        b' <-- ccExp var (b (length envT)) (dom :: envT) _ (wfExp_lax wf);
        f <== \\env, arg, unpackExp (#env) (fun env => b' (arg, env));
        Main (fun env => #f ##
          packExp
          (snd (fvsExp (b (length envT)) (dom :: envT)))
          fvs (inclusion wf) env)
    end.
End packing.

Implicit Arguments packExp [var envT].
Implicit Arguments unpackExp [var t envT fvs].

Implicit Arguments ccExp [var t envT].

Fixpoint map_funcs var T1 T2 (f : T1 -> T2) (fs : funcs var T1) {struct fs}
  : funcs var T2 :=
  match fs with
    | Main v => Main (f v)
    | Abs _ _ _ e fs' => Abs e (fun x => map_funcs f (fs' x))
  end.

Definition CcExp' t (E : Source.Exp t) (Hwf : wfExp (envT := nil) tt (E _)) : Prog (ccType t) :=
  fun _ => map_funcs (fun f => f tt) (ccExp (E _) (envT := nil) tt Hwf).


(** ** Examples *)

Open Local Scope source_scope.

Definition ident : Source.Exp (Nat --> Nat) := fun _ => \x, #x.
Theorem ident_ok : wfExp (envT := nil) tt (ident _).
  crush.
Defined.
Eval compute in CcExp' ident ident_ok.
Eval compute in ProgDenote (CcExp' ident ident_ok).

Definition app_ident : Source.Exp Nat := fun _ => ident _ @ ^0.
Theorem app_ident_ok : wfExp (envT := nil) tt (app_ident _).
  crush.
Defined.
Eval compute in CcExp' app_ident app_ident_ok.
Eval compute in ProgDenote (CcExp' app_ident app_ident_ok).

Definition first : Source.Exp (Nat --> Nat --> Nat) := fun _ =>
  \x, \y, #x.
Theorem first_ok : wfExp (envT := nil) tt (first _).
  crush.
Defined.
Eval compute in CcExp' first first_ok.
Eval compute in ProgDenote (CcExp' first first_ok).

Definition app_first : Source.Exp Nat := fun _ => first _ @ ^1 @ ^0.
Theorem app_first_ok : wfExp (envT := nil) tt (app_first _).
  crush.
Defined.
Eval compute in CcExp' app_first app_first_ok.
Eval compute in ProgDenote (CcExp' app_first app_first_ok).


(** ** Correctness *)

Section spliceFuncs_correct.
  Variables T1 T2 : Type.
  Variable f : T1 -> funcs typeDenote T2.

  Theorem spliceFuncs_correct : forall fs,
    funcsDenote (spliceFuncs fs f)
    = funcsDenote (f (funcsDenote fs)).
    induction fs; crush.
  Qed.
End spliceFuncs_correct.


Notation "var <| to" := (match to return Set with
                           | None => unit
                           | Some t => var (ccType t)
                         end) (no associativity, at level 70).

Section packing_correct.
  Fixpoint makeEnv (envT : list Source.type) : forall (fvs : isfree envT),
    Closed.typeDenote (envType fvs)
    -> envOf Closed.typeDenote fvs :=
    match envT return (forall (fvs : isfree envT),
      Closed.typeDenote (envType fvs)
      -> envOf Closed.typeDenote fvs) with
      | nil => fun _ _ => tt
      | first :: rest => fun fvs =>
        match fvs return (Closed.typeDenote (envType (envT := first :: rest) fvs)
          -> envOf (envT := first :: rest) Closed.typeDenote fvs) with
          | (false, fvs') => fun env => makeEnv rest fvs' env
          | (true, fvs') => fun env => (fst env, makeEnv rest fvs' (snd env))
        end
    end.

  Implicit Arguments makeEnv [envT fvs].

  Theorem unpackExp_correct : forall t (envT : list Source.type) (fvs : isfree envT)
    (e1 : Closed.exp Closed.typeDenote (envType fvs))
    (e2 : envOf Closed.typeDenote fvs -> Closed.exp Closed.typeDenote t),
    Closed.expDenote (unpackExp e1 e2)
    = Closed.expDenote (e2 (makeEnv (Closed.expDenote e1))).
    induction envT; my_crush.
  Qed.

  Lemma lookup_type_more : forall v2 envT (fvs : isfree envT) t b v,
    (v2 = length envT -> False)
    -> lookup_type v2 (envT := t :: envT) (b, fvs) = v
    -> lookup_type v2 fvs = v.
    my_crush.
  Qed.

  Lemma lookup_type_less : forall v2 t envT (fvs : isfree (t :: envT)) v,
    (v2 = length envT -> False)
    -> lookup_type v2 (snd fvs) = v
    -> lookup_type v2 (envT := t :: envT) fvs = v.
    my_crush.
  Qed.

  Hint Resolve lookup_bound_contra.

  Lemma lookup_bound_contra_eq : forall t envT (fvs : isfree envT) v,
    lookup_type v fvs = Some t
    -> v = length envT
    -> False.
    my_crush; elimtype False; eauto.
  Qed.

  Lemma lookup_type_inner : forall t t' envT v t'' (fvs : isfree envT) e,
    wfExp (envT := t' :: envT) (true, fvs) e
    -> lookup_type v (snd (fvsExp (t := t) e (t' :: envT))) = Some t''
    -> lookup_type v fvs = Some t''.
    Hint Resolve lookup_bound_contra_eq fvsExp_minimal
      lookup_type_more lookup_type_less.
    Hint Extern 2 (Some _ = Some _) => elimtype False.

    eauto 6.
  Qed.

  Lemma cast_irrel : forall T1 T2 x (H1 H2 : T1 = T2),
    match H1 in _ = T return T with
      | refl_equal => x
    end
    = match H2 in _ = T return T with
        | refl_equal => x
      end.
    intros; generalize H1; crush;
      repeat match goal with
               | [ |- context[match ?pf with refl_equal => _ end] ] =>
                 rewrite (UIP_refl _ _ pf)
             end;
      reflexivity.
  Qed.

  Hint Immediate cast_irrel.

  Hint Extern 3 (_ == _) =>
    match goal with
      | [ |- context[False_rect _ ?H] ] =>
        apply False_rect; exact H
    end.

  Theorem packExp_correct : forall v t envT (fvs1 fvs2 : isfree envT)
    Hincl env,
    lookup_type v fvs1 = Some t
    -> lookup Closed.typeDenote v env
    == lookup Closed.typeDenote v
    (makeEnv (Closed.expDenote
      (packExp fvs1 fvs2 Hincl env))).
    induction envT; my_crush.
  Qed.
End packing_correct.

Implicit Arguments packExp_correct [v envT fvs1].
Implicit Arguments lookup_type_inner [t t' envT v t'' fvs e].
Implicit Arguments inclusion [t t' envT fvs e].

Lemma typeDenote_same : forall t,
  Source.typeDenote t = Closed.typeDenote (ccType t).
  induction t; crush.
Qed.

Hint Resolve typeDenote_same.

Fixpoint lr (t : Source.type) : Source.typeDenote t -> Closed.typeDenote (ccType t) -> Prop :=
  match t return Source.typeDenote t -> Closed.typeDenote (ccType t) -> Prop with
    | Nat => @eq nat
    | dom --> ran => fun f1 f2 =>
      forall x1 x2, lr dom x1 x2
        -> lr ran (f1 x1) (f2 x2)
  end.

Theorem ccExp_correct : forall t G
  (e1 : Source.exp Source.typeDenote t)
  (e2 : Source.exp natvar t),
  exp_equiv G e1 e2
  -> forall (envT : list Source.type) (fvs : isfree envT)
    (env : envOf Closed.typeDenote fvs) (wf : wfExp fvs e2),
    (forall t (v1 : Source.typeDenote t) (v2 : natvar t),
      In (existT _ _ (v1, v2)) G
      -> v2 < length envT)
    -> (forall t (v1 : Source.typeDenote t) (v2 : natvar t),
      In (existT _ _ (v1, v2)) G
      -> forall pf,
        lr t v1 (match lok pf in _ = T return T with
                   | refl_equal => lookup Closed.typeDenote v2 env
                 end))
    -> lr t (Source.expDenote e1) (Closed.expDenote (funcsDenote (ccExp e2 fvs wf) env)).

  Hint Rewrite spliceFuncs_correct unpackExp_correct : cpdt.
  Hint Resolve packExp_correct lookup_type_inner.

  induction 1; crush;
    match goal with
      | [ IH : _, Hlr : lr ?T ?X1 ?X2, ENV : list Source.type, F2 : natvar _ -> _ |- _ ] =>
        apply (IH X1 (length ENV) (T :: ENV) (true, snd (fvsExp (F2 (length ENV)) (T :: ENV))))
    end; crush;
    match goal with
      | [ Hlt : forall t v1 v2, _ -> _ < _, Hin : In _ _ |- _ ] =>
        solve [ generalize (Hlt _ _ _ Hin); crush ]
      | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
    end; simpl;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; intuition; subst;
    match goal with
      | [ |- context[match ?pf with refl_equal => _ end] ] => rewrite (UIP_refl _ _ pf); assumption
      | [ Hlt : forall t v1 v2, _ -> _ < _, Hin : In (existT _ _ (_, length _)) _ |- _ ] =>
        generalize (Hlt _ _ _ Hin); crush
      | [ HG : _, Hin : In _ _, wf : wfExp _ _, pf : _ = Some _,
        fvs : isfree _, env : envOf _ _ |- _ ] =>
      generalize (HG _ _ _ Hin (lookup_type_inner wf pf)); clear_all;
        repeat match goal with
                 | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
               end; simpl;
        generalize (packExp_correct _ fvs (inclusion wf) env pf); simpl;
          match goal with
            | [ |- ?X == ?Y -> _ ] =>
              generalize X Y
          end;
          rewrite pf; rewrite (lookup_type_inner wf pf);
            intros lhs rhs Heq; intros;
              repeat match goal with
                       | [ H : _ = _ |- _ ] => rewrite (UIP_refl _ _ H) in *
                     end;
              rewrite <- Heq; assumption
    end.
Qed.


(** * Parametric version *)

Section wf.
  Lemma Exp_wf' : forall G t (e1 e2 : Source.exp natvar t),
    exp_equiv G e1 e2
    -> forall envT (fvs : isfree envT),
      (forall t (v1 v2 : natvar t), In (existT _ _ (v1, v2)) G
        -> lookup_type v1 fvs = Some t)
      -> wfExp fvs e1.
    Hint Extern 3 (Some _ = Some _) => elimtype False; eapply lookup_bound_contra; eauto.

    induction 1; crush.
    eapply H0.
    eauto.

    apply H0 with (length envT).
    my_crush.
    eauto.
  Qed.

  Theorem Exp_wf : forall t (E : Source.Exp t),
    wfExp (envT := nil) tt (E _).
    intros; eapply Exp_wf';
      [apply Exp_equiv
        | crush].
  Qed.
End wf.

Definition CcExp t (E : Source.Exp t) : Prog (ccType t) :=
  CcExp' E (Exp_wf E).

Lemma map_funcs_correct : forall T1 T2 (f : T1 -> T2) (fs : funcs Closed.typeDenote T1),
  funcsDenote (map_funcs f fs) = f (funcsDenote fs).
  induction fs; crush.
Qed.

Theorem CcExp_correct : forall (E : Source.Exp Nat),
  Source.ExpDenote E
  = ProgDenote (CcExp E).
  Hint Rewrite map_funcs_correct : cpdt.

  unfold Source.ExpDenote, ProgDenote, CcExp, CcExp', progDenote; crush;
    apply (ccExp_correct
      (G := nil)
      (e1 := E _)
      (e2 := E _)
      (Exp_equiv _ _ _)
      nil
      tt
      tt); crush.
Qed.
