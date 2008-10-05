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

Set Implicit Arguments.
(* end hide *)


(** %\chapter{More Dependent Types}% *)

(** Subset types and their relatives help us integrate verification with programming.  Though they reorganize the certified programmer's workflow, they tend not to have deep effects on proofs.  We write largely the same proofs as we would for classical verification, with some of the structure moved into the programs themselves.  It turns out that, when we use dependent types to their full potential, we warp the development and proving process even more than that, picking up "free theorems" to the extent that often a certified program is hardly more complex than its uncertified counterpart in Haskell or ML.

   In particular, we have only scratched the tip of the iceberg that is Coq's inductive definition mechanism.  The inductive types we have seen so far have their counterparts in the other proof assistants that we surveyed in Chapter 1.  This chapter explores the strange new world of dependent inductive datatypes (that is, dependent inductive types outside [Prop]), a possibility which sets Coq apart from all of the competition not based on type theory. *)

