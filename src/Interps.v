(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import String List.

Require Import AxiomsImpred Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Type-Theoretic Interpreters}% *)

(** TODO: Prose for this chapter *)


(** * Simply-Typed Lambda Calculus *)

Module STLC.
  Inductive type : Type :=
  | Nat : type
  | Arrow : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 60).

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

  Notation "# v" := (Var v) (at level 70).

  Notation "^ n" := (Const n) (at level 70).
  Infix "+^" := Plus (left associativity, at level 79).

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

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

  Eval compute in ExpDenote zero.
  Eval compute in ExpDenote one.
  Eval compute in ExpDenote zpo.
  Eval compute in ExpDenote ident.
  Eval compute in ExpDenote app_ident.
  Eval compute in ExpDenote app.
  Eval compute in ExpDenote app_ident'.

  Section cfold.
    Variable var : type -> Type.

    Fixpoint cfold t (e : exp var t) {struct e} : exp var t :=
      match e in exp _ t return exp _ t with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' +^ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => Abs (fun x => cfold (e' x))
      end.
  End cfold.

  Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).

  Lemma cfold_correct : forall t (e : exp _ t),
    expDenote (cfold e) = expDenote e.
    induction e; crush; try (ext_eq; crush);
      repeat (match goal with
                | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
              end; crush).
  Qed.

  Theorem Cfold_correct : forall t (E : Exp t),
    ExpDenote (Cfold E) = ExpDenote E.
    unfold ExpDenote, Cfold; intros; apply cfold_correct.
  Qed.
End STLC.


(** * Adding Products and Sums *)

Module PSLC.
  Inductive type : Type :=
  | Nat : type
  | Arrow : type -> type -> type
  | Prod : type -> type -> type
  | Sum : type -> type -> type.

  Infix "-->" := Arrow (right associativity, at level 62).
  Infix "**" := Prod (right associativity, at level 61).
  Infix "++" := Sum (right associativity, at level 60).

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
      -> exp (t1 --> t2)

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

    | Inl : forall t1 t2,
      exp t1
      -> exp (t1 ++ t2)
    | Inr : forall t1 t2,
      exp t2
      -> exp (t1 ++ t2)
    | SumCase : forall t1 t2 t,
      exp (t1 ++ t2)
      -> (var t1 -> exp t)
      -> (var t2 -> exp t)
      -> exp t.
  End vars.

  Definition Exp t := forall var, exp var t.

  Implicit Arguments Var [var t].
  Implicit Arguments Const [var].
  Implicit Arguments Abs [var t1 t2].
  Implicit Arguments Inl [var t1 t2].
  Implicit Arguments Inr [var t1 t2].

  Notation "# v" := (Var v) (at level 70).

  Notation "^ n" := (Const n) (at level 70).
  Infix "+^" := Plus (left associativity, at level 78).

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

  Notation "[ e1 , e2 ]" := (Pair e1 e2).
  Notation "#1 e" := (Fst e) (at level 75).
  Notation "#2 e" := (Snd e) (at level 75).

  Notation "'case' e 'of' x => e1 | y => e2" := (SumCase e (fun x => e1) (fun y => e2))
    (at level 79).

  Definition swap : Exp (Nat ** Nat --> Nat ** Nat) := fun _ =>
    \p, [#2 #p, #1 #p].
  Definition zo : Exp (Nat ** Nat) := fun _ => [^0, ^1].
  Definition swap_zo : Exp (Nat ** Nat) := fun _ => swap _ @ zo _.

  Definition natOut : Exp (Nat ++ Nat --> Nat) := fun _ =>
    \s, case #s of x => #x | y => #y +^ #y.
  Definition ns1 : Exp (Nat ++ Nat) := fun _ => Inl (^3).
  Definition ns2 : Exp (Nat ++ Nat) := fun _ => Inr (^5).
  Definition natOut_ns1 : Exp Nat := fun _ => natOut _ @ ns1 _.
  Definition natOut_ns2 : Exp Nat := fun _ => natOut _ @ ns2 _.

  Fixpoint typeDenote (t : type) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
      | t1 ** t2 => typeDenote t1 * typeDenote t2
      | t1 ++ t2 => typeDenote t1 + typeDenote t2
    end%type.

  Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
    match e in (exp _ t) return (typeDenote t) with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)

      | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
      | Fst _ _ e' => fst (expDenote e')
      | Snd _ _ e' => snd (expDenote e')

      | Inl _ _ e' => inl _ (expDenote e')
      | Inr _ _ e' => inr _ (expDenote e')
      | SumCase _ _ _ e' e1 e2 =>
        match expDenote e' with
          | inl v => expDenote (e1 v)
          | inr v => expDenote (e2 v)
        end
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).

  Eval compute in ExpDenote swap.
  Eval compute in ExpDenote zo.
  Eval compute in ExpDenote swap_zo.

  Eval compute in ExpDenote natOut.
  Eval compute in ExpDenote ns1.
  Eval compute in ExpDenote ns2.
  Eval compute in ExpDenote natOut_ns1.
  Eval compute in ExpDenote natOut_ns2.

  Section cfold.
    Variable var : type -> Type.

    Definition pairOutType t :=
      match t with
        | t1 ** t2 => option (exp var t1 * exp var t2)
        | _ => unit
      end.

    Definition pairOutDefault (t : type) : pairOutType t :=
      match t return pairOutType t with
        | _ ** _ => None
        | _ => tt
      end.

    Definition pairOut t1 t2 (e : exp var (t1 ** t2)) : option (exp var t1 * exp var t2) :=
      match e in exp _ t return pairOutType t with
        | Pair _ _ e1 e2 => Some (e1, e2)
        | _ => pairOutDefault _
      end.

    Fixpoint cfold t (e : exp var t) {struct e} : exp var t :=
      match e in exp _ t return exp _ t with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' +^ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => Abs (fun x => cfold (e' x))

        | Pair _ _ e1 e2 => [cfold e1, cfold e2]
        | Fst t1 _ e' =>
          let e'' := cfold e' in
            match pairOut e'' with
              | None => #1 e''
              | Some (e1, _) => e1
            end
        | Snd _ _ e' =>
          let e'' := cfold e' in
            match pairOut e'' with
              | None => #2 e''
              | Some (_, e2) => e2
            end

        | Inl _ _ e' => Inl (cfold e')
        | Inr _ _ e' => Inr (cfold e')
        | SumCase _ _ _ e' e1 e2 =>
          case cfold e' of
            x => cfold (e1 x)
          | y => cfold (e2 y)
      end.
  End cfold.

  Definition Cfold t (E : Exp t) : Exp t := fun _ => cfold (E _).

  Section pairs.
    Variables A B : Type.

    Variable v1 : A.
    Variable v2 : B.
    Variable v : A * B.

    Theorem pair_eta1 : (v1, v2) = v -> v1 = fst v.
      destruct v; crush.
    Qed.

    Theorem pair_eta2 : (v1, v2) = v -> v2 = snd v.
      destruct v; crush.
    Qed.
  End pairs.

  Hint Resolve pair_eta1 pair_eta2.

  Lemma cfold_correct : forall t (e : exp _ t),
    expDenote (cfold e) = expDenote e.
    induction e; crush; try (ext_eq; crush);
      repeat (match goal with
                | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
                | [ |- match ?E with inl _ => _ | inr _ => _ end = _ ] => destruct E
              end; crush); eauto.
  Qed.

  Theorem Cfold_correct : forall t (E : Exp t),
    ExpDenote (Cfold E) = ExpDenote E.
    unfold ExpDenote, Cfold; intros; apply cfold_correct.
  Qed.
End PSLC.


(** * Type Variables *)

Module SysF.
  Section vars.
    Variable tvar : Type.

    Inductive type : Type :=
    | Nat : type
    | Arrow : type -> type -> type
    | TVar : tvar -> type
    | All : (tvar -> type) -> type.

    Notation "## v" := (TVar v) (at level 40).
    Infix "-->" := Arrow (right associativity, at level 60).

    Section Subst.
      Variable t : type.

      Inductive Subst : (tvar -> type) -> type -> Prop :=
      | SNat : Subst (fun _ => Nat) Nat
      | SArrow : forall dom ran dom' ran',
        Subst dom dom'
        -> Subst ran ran'
        -> Subst (fun v => dom v --> ran v) (dom' --> ran')
      | SVarEq : Subst TVar t
      | SVarNe : forall v, Subst (fun _ => ##v) (##v)
      | SAll : forall ran ran',
        (forall v', Subst (fun v => ran v v') (ran' v'))
        -> Subst (fun v => All (ran v)) (All ran').
    End Subst.

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
      -> exp (t1 --> t2)

    | TApp : forall tf,
      exp (All tf)
      -> forall t tf', Subst t tf tf'
        -> exp tf'
    | TAbs : forall tf,
      (forall v, exp (tf v))
      -> exp (All tf).
  End vars.

  Definition Typ := forall tvar, type tvar.
  Definition Exp (T : Typ) := forall tvar (var : type tvar -> Type), exp var (T _).

  Implicit Arguments Nat [tvar].

  Notation "## v" := (TVar v) (at level 40).
  Infix "-->" := Arrow (right associativity, at level 60).
  Notation "\\\ x , t" := (All (fun x => t)) (at level 65).

  Implicit Arguments Var [tvar var t].
  Implicit Arguments Const [tvar var].
  Implicit Arguments Plus [tvar var].
  Implicit Arguments App [tvar var t1 t2].
  Implicit Arguments Abs [tvar var t1 t2].

  Implicit Arguments TAbs [tvar var tf].

  Notation "# v" := (Var v) (at level 70).

  Notation "^ n" := (Const n) (at level 70).
  Infix "+^" := Plus (left associativity, at level 79).

  Infix "@" := App (left associativity, at level 77).
  Notation "\ x , e" := (Abs (fun x => e)) (at level 78).
  Notation "\ ! , e" := (Abs (fun _ => e)) (at level 78).

  Notation "e @@ t" := (TApp e (t := t) _) (left associativity, at level 77).
  Notation "\\ x , e" := (TAbs (fun x => e)) (at level 78).
  Notation "\\ ! , e" := (TAbs (fun _ => e)) (at level 78).

  Definition zero : Exp (fun _ => Nat) := fun _ _ =>
    ^0.
  Definition ident : Exp (fun _ => \\\T, ##T --> ##T) := fun _ _ =>
    \\T, \x, #x.
  Definition ident_zero : Exp (fun _ => Nat).
    do 2 intro; refine (ident _ @@ _ @ zero _);
      repeat constructor.
  Defined.
  Definition ident_ident : Exp (fun _ => \\\T, ##T --> ##T).
    do 2 intro; refine (ident _ @@ _ @ ident _);
      repeat constructor.
  Defined.
  Definition ident5 : Exp (fun _ => \\\T, ##T --> ##T).
    do 2 intro; refine (ident_ident _ @@ _ @ ident_ident _ @@ _ @ ident _);
      repeat constructor.
  Defined.

  Fixpoint typeDenote (t : type Set) : Set :=
    match t with
      | Nat => nat
      | t1 --> t2 => typeDenote t1 -> typeDenote t2
      | ##v => v
      | All tf => forall T, typeDenote (tf T)
    end.

  Lemma Subst_typeDenote : forall t tf tf',
    Subst t tf tf'
    -> typeDenote (tf (typeDenote t)) = typeDenote tf'.
    induction 1; crush; ext_eq; crush.
  Defined.

  Fixpoint expDenote t (e : exp typeDenote t) {struct e} : typeDenote t :=
    match e in (exp _ t) return (typeDenote t) with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)

      | TApp _ e' t' _ pf => match Subst_typeDenote pf in _ = T return T with
                               | refl_equal => (expDenote e') (typeDenote t')
                             end
      | TAbs _ e' => fun T => expDenote (e' T)
    end.

  Definition ExpDenote T (E : Exp T) := expDenote (E _ _).

  Eval compute in ExpDenote zero.
  Eval compute in ExpDenote ident.
  Eval compute in ExpDenote ident_zero.
  Eval compute in ExpDenote ident_ident.
  Eval compute in ExpDenote ident5.

  Section cfold.
    Variable tvar : Type.
    Variable var : type tvar -> Type.

    Fixpoint cfold t (e : exp var t) {struct e} : exp var t :=
      match e in exp _ t return exp _ t with
        | Var _ v => #v

        | Const n => ^n
        | Plus e1 e2 =>
          let e1' := cfold e1 in
          let e2' := cfold e2 in
          match e1', e2' with
            | Const n1, Const n2 => ^(n1 + n2)
            | _, _ => e1' +^ e2'
          end

        | App _ _ e1 e2 => cfold e1 @ cfold e2
        | Abs _ _ e' => Abs (fun x => cfold (e' x))

        | TApp _ e' _ _ pf => TApp (cfold e') pf
        | TAbs _ e' => \\T, cfold (e' T)
      end.
  End cfold.

  Definition Cfold T (E : Exp T) : Exp T := fun _ _ => cfold (E _ _).

  Lemma cfold_correct : forall t (e : exp _ t),
    expDenote (cfold e) = expDenote e.
    induction e; crush; try (ext_eq; crush);
      repeat (match goal with
                | [ |- context[cfold ?E] ] => dep_destruct (cfold E)
              end; crush).
  Qed.

  Theorem Cfold_correct : forall t (E : Exp t),
    ExpDenote (Cfold E) = ExpDenote E.
    unfold ExpDenote, Cfold; intros; apply cfold_correct.
  Qed.
End SysF.
