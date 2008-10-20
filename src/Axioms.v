(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Additional axioms not in the Coq standard library *)

Axiom ext_eq : forall (A : Type) (B : A -> Type)
  (f g : forall x, B x),
  (forall x, f x = g x)
  -> f = g.

Ltac ext_eq := apply ext_eq; intro.
