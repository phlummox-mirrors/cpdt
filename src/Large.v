(* Copyright (c) 2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Tactics.

Set Implicit Arguments.
(* end hide *)


(** %\chapter{Proving in the Large}% *)


(** * Modules *)

Module Type GROUP.
  Parameter G : Set.
  Parameter f : G -> G -> G.
  Parameter e : G.
  Parameter i : G -> G.

  Axiom assoc : forall a b c, f (f a b) c = f a (f b c).
  Axiom ident : forall a, f e a = a.
  Axiom inverse : forall a, f (i a) a = e.
End GROUP.

Module Type GROUP_THEOREMS.
  Declare Module M : GROUP.

  Axiom ident' : forall a, M.f a M.e = a.

  Axiom inverse' : forall a, M.f a (M.i a) = M.e.

  Axiom unique_ident : forall e', (forall a, M.f e' a = a) -> e' = M.e.
End GROUP_THEOREMS.

Module Group (M : GROUP) : GROUP_THEOREMS.
  Module M := M.

  Import M.

  Theorem inverse' : forall a, f a (i a) = e.
    intro.
    rewrite <- (ident (f a (i a))).
    rewrite <- (inverse (f a (i a))) at 1.
    rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc (i a) a (i a)).
    rewrite inverse.
    rewrite ident.
    apply inverse.
  Qed.

  Theorem ident' : forall a, f a e = a.
    intro.
    rewrite <- (inverse a).
    rewrite <- assoc.
    rewrite inverse'.
    apply ident.
  Qed.

  Theorem unique_ident : forall e', (forall a, M.f e' a = a) -> e' = M.e.
    intros.
    rewrite <- (H e).
    symmetry.
    apply ident'.
  Qed.
End Group.
