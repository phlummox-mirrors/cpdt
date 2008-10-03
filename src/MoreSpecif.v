(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Types and notations presented in Chapter 6 *)

Set Implicit Arguments.


Notation "!" := (False_rec _ _) : specif_scope.
Notation "[ e ]" := (exist _ e _) : specif_scope.
Notation "x <== e1 ; e2" := (let (x, _) := e1 in e2)
(right associativity, at level 60) : specif_scope.

Open Local Scope specif_scope.
Delimit Scope specif_scope with specif.

Notation "'Yes'" := (left _ _) : specif_scope.
Notation "'No'" := (right _ _) : specif_scope.
Notation "'Reduce' x" := (if x then Yes else No) (at level 50) : specif_scope.

Notation "x || y" := (if x then Yes else Reduce y) (at level 50) : specif_scope.

Inductive maybe (A : Type) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)) : specif_scope.
Notation "??" := (Unknown _) : specif_scope.
Notation "[[ x ]]" := (Found _ x _) : specif_scope.

Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60) : specif_scope.

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60) : specif_scope.

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60) : specif_scope.

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60) : specif_scope.
