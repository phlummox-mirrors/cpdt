(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith Eqdep List.

Require Import Axioms DepList Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Intensional Transformations}% *)

(* begin hide *)

Inductive type : Type :=
| Nat : type
| Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | t1 --> t2 => typeDenote t1 -> typeDenote t2
  end.

Module Phoas.
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

  Fixpoint expDenote t (e : exp typeDenote t) : typeDenote t :=
    match e with
      | Var _ v => v
        
      | Const n => n
      | Plus e1 e2 => expDenote e1 + expDenote e2
        
      | App _ _ e1 e2 => (expDenote e1) (expDenote e2)
      | Abs _ _ e' => fun x => expDenote (e' x)
    end.

  Definition ExpDenote t (e : Exp t) := expDenote (e _).

  Section exp_equiv.
    Variables var1 var2 : type -> Type.

    Inductive exp_equiv : list { t : type & var1 t * var2 t }%type
      -> forall t, exp var1 t -> exp var2 t -> Prop :=
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

  Definition Wf t (E : Exp t) := forall var1 var2, exp_equiv nil (E var1) (E var2).
End Phoas.
(* end hide *)

Module DeBruijn.
  Inductive exp : list type -> type -> Type :=
    | Var : forall G t,
      member t G
      -> exp G t

    | Const : forall G, nat -> exp G Nat
    | Plus : forall G, exp G Nat -> exp G Nat -> exp G Nat

    | App : forall G t1 t2,
      exp G (t1 --> t2)
      -> exp G t1
      -> exp G t2
    | Abs : forall G t1 t2,
      exp (t1 :: G) t2
      -> exp G (t1 --> t2).

  Implicit Arguments Const [G].

  Fixpoint expDenote G t (e : exp G t) : hlist typeDenote G -> typeDenote t :=
    match e with
      | Var _ _ v => fun s => hget s v
        
      | Const _ n => fun _ => n
      | Plus _ e1 e2 => fun s => expDenote e1 s + expDenote e2 s
        
      | App _ _ _ e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
      | Abs _ _ _ e' => fun s x => expDenote e' (x ::: s)
    end.
End DeBruijn.

Import Phoas DeBruijn.


(** * From De Bruijn to PHOAS *)

Section phoasify.
  Variable var : type -> Type.

  Fixpoint phoasify G t (e : DeBruijn.exp G t) : hlist var G -> Phoas.exp var t :=
    match e with
      | Var _ _ v => fun s => #(hget s v)

      | Const _ n => fun _ => ^n
      | Plus _ e1 e2 => fun s => phoasify e1 s +^ phoasify e2 s

      | App _ _ _ e1 e2 => fun s => phoasify e1 s @ phoasify e2 s
      | Abs _ _ _ e' => fun s => \x, phoasify e' (x ::: s)
    end.
End phoasify.

Definition Phoasify t (e : DeBruijn.exp nil t) : Phoas.Exp t :=
  fun _ => phoasify e HNil.

Theorem phoasify_sound : forall G t (e : DeBruijn.exp G t) s,
  Phoas.expDenote (phoasify e s) = DeBruijn.expDenote e s.
  induction e; crush; ext_eq; crush.
Qed.

Section vars.
  Variables var1 var2 : type -> Type.

  Fixpoint zip G (s1 : hlist var1 G) : hlist var2 G -> list {t : type & var1 t * var2 t}%type :=
    match s1 with
      | HNil => fun _ => nil
      | HCons _ _ v1 s1' => fun s2 => existT _ _ (v1, hhd s2) :: zip s1' (htl s2)
    end.

  Lemma In_zip : forall t G (s1 : hlist _ G) s2 (m : member t G),
    In (existT _ t (hget s1 m, hget s2 m)) (zip s1 s2).
    induction s1; intro s2; dep_destruct s2; intro m; dep_destruct m; crush.
  Qed.

  Lemma unsimpl_zip : forall t (v1 : var1 t) (v2 : var2 t)
    G (s1 : hlist _ G) s2 t' (e1 : Phoas.exp _ t') e2,
   exp_equiv (zip (v1 ::: s1) (v2 ::: s2)) e1 e2
   -> exp_equiv (existT _ _ (v1, v2) :: zip s1 s2) e1 e2.
    trivial.
  Qed.

  Hint Resolve In_zip unsimpl_zip.

  Theorem phoasify_wf : forall G t (e : DeBruijn.exp G t) s1 s2,
    exp_equiv (zip s1 s2) (phoasify e s1) (phoasify e s2).
    Hint Constructors exp_equiv.
    
    induction e; crush.
  Qed.
End vars.

Theorem Phoasify_wf : forall t (e : DeBruijn.exp nil t),
  Wf (Phoasify e).
  unfold Wf, Phoasify; intros;
    apply (phoasify_wf e (HNil (B := var1)) (HNil (B := var2))).
Qed.


(** * From PHOAS to De Bruijn *)

Fixpoint lookup (G : list type) (n : nat) : option type :=
  match G with
    | nil => None
    | t :: G' => if eq_nat_dec n (length G') then Some t else lookup G' n
  end.

Infix "##" := lookup (left associativity, at level 1).

Fixpoint wf (ts : list type) t (e : Phoas.exp (fun _ => nat) t) : Prop :=
  match e with
    | Phoas.Var t n => ts ## n = Some t
    | Phoas.Const _ => True
    | Phoas.Plus e1 e2 => wf ts e1 /\ wf ts e2
    | Phoas.App _ _ e1 e2 => wf ts e1 /\ wf ts e2
    | Phoas.Abs t1 _ e1 => wf (t1 :: ts) (e1 (length ts))
  end.

Fixpoint makeG (ts : list type) : list { t : type & nat * nat }%type :=
  match ts with
    | nil => nil
    | t :: ts' => existT _ t (length ts', length ts') :: makeG ts'
  end.

Opaque eq_nat_dec.
Hint Extern 1 (_ >= _) => omega.

Lemma lookup_contra' : forall t ts n,
  ts ## n = Some t
  -> n >= length ts
  -> False.
  induction ts; crush;
    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; crush
    end; eauto.
Qed.

Lemma lookup_contra : forall t ts,
  ts ## (length ts) = Some t
  -> False.
  intros; eapply lookup_contra'; eauto.
Qed.

Hint Resolve lookup_contra.

Lemma lookup_In : forall t v1 v2 ts,
  In (existT (fun _ : type => (nat * nat)%type) t (v1, v2)) (makeG ts)
  -> ts ## v1 = Some t.
  induction ts; crush;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; crush
    end; elimtype False; eauto.
Qed.

Hint Resolve lookup_In.

Hint Extern 1 (_ :: _ = makeG (_ :: _)) => reflexivity.

Lemma Wf_wf' : forall G t e1 (e2 : Phoas.exp (fun _ => nat) t),
  exp_equiv G e1 e2
  -> forall ts, G = makeG ts
    -> wf ts e1.
  induction 1; crush; eauto.
Qed.

Lemma Wf_wf : forall t (E : Exp t),
  Wf E
  -> wf nil (E (fun _ => nat)).
  intros; eapply Wf_wf'; eauto.
Qed.

Theorem None_Some : forall T (x : T),
  None = Some x
  -> False.
  congruence.
Qed.

Theorem Some_Some : forall T (x y : T),
  Some x = Some y
  -> x = y.
  congruence.
Qed.

Fixpoint makeVar {ts n t} : ts ## n = Some t -> member t ts :=
  match ts return ts ## n = Some t -> member t ts with
    | nil => fun Heq => match None_Some Heq with end
    | t' :: ts' => if eq_nat_dec n (length ts') as b
      return (if b then Some t' else lookup ts' n) = Some t -> member t (t' :: ts')
      then fun Heq => match Some_Some Heq in _ = t0 return member t0 (t' :: ts') with
                        | refl_equal => HFirst
                      end
      else fun Heq => HNext (makeVar Heq)
  end.

Axiom cheat : forall T, T.

Fixpoint dbify {ts} t (e : Phoas.exp (fun _ => nat) t) : wf ts e -> DeBruijn.exp ts t :=
  match e in Phoas.exp _ t return wf ts e -> DeBruijn.exp ts t with
    | Phoas.Var _ n => fun wf => DeBruijn.Var (makeVar wf)

    | Phoas.Const n => fun _ => DeBruijn.Const n
    | Phoas.Plus e1 e2 => fun wf => DeBruijn.Plus (dbify e1 (proj1 wf)) (dbify e2 (proj2 wf))

    | Phoas.App _ _ e1 e2 => fun wf => DeBruijn.App (dbify e1 (proj1 wf)) (dbify e2 (proj2 wf))
    | Phoas.Abs _ _ e1 => fun wf => DeBruijn.Abs (dbify (e1 (length ts)) wf)
  end.

Definition Dbify t (E : Phoas.Exp t) (W : Wf E) : DeBruijn.exp nil t :=
  dbify (E _) (Wf_wf W).

Fixpoint makeG' ts (s : hlist typeDenote ts) : list { t : type & nat * typeDenote t }%type :=
  match s with
    | HNil => nil
    | HCons _ ts' v s' => existT _ _ (length ts', v) :: makeG' s'
  end.

Lemma In_makeG'_contra' : forall t v2 ts (s : hlist _ ts) n,
  In (existT _ t (n, v2)) (makeG' s)
  -> n >= length ts
  -> False.
  induction s; crush; eauto.
Qed.

Lemma In_makeG'_contra : forall t v2 ts (s : hlist _ ts),
  In (existT _ t (length ts, v2)) (makeG' s)
  -> False.
  intros; eapply In_makeG'_contra'; eauto.
Qed.

Hint Resolve In_makeG'_contra.

Lemma In_makeG' : forall t v1 v2 ts s (w : ts ## v1 = Some t),
  In (existT _ t (v1, v2)) (makeG' s)
  -> hget s (makeVar w) = v2.
  induction s; crush;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; crush
    end;
    repeat match goal with
             | [ |- context[match ?pf with refl_equal => _ end] ] => rewrite (UIP_refl _ _ pf)
           end; crush; elimtype False; eauto.
Qed.

Hint Resolve In_makeG'.

Lemma dbify_sound : forall G t (e1 : Phoas.exp _ t) (e2 : Phoas.exp _ t),
  exp_equiv G e1 e2
  -> forall ts (w : wf ts e1) s,
    G = makeG' s
    -> DeBruijn.expDenote (dbify e1 w) s = Phoas.expDenote e2.
  induction 1; crush; ext_eq; crush.
Qed.

Theorem Dbify_sound : forall t (E : Exp t) (W : Wf E),
  DeBruijn.expDenote (Dbify W) HNil = Phoas.ExpDenote E.
  unfold Dbify, Phoas.ExpDenote; intros; eapply dbify_sound; eauto.
Qed.
