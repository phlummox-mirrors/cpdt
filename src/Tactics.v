(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

Require Import List.

Require Omega.


Ltac inject H := injection H; clear H; intros; subst.

Ltac simplHyp :=
  match goal with
    | [ H : ?F _ = ?F _ |- _ ] => injection H;
      match goal with
        | [ |- _ = _ -> _ ] => clear H; intros; subst
      end
    | [ H : ?F _ _ = ?F _ _ |- _ ] => injection H;
      match goal with
        | [ |- _ = _ -> _ = _ -> _ ] => clear H; intros; subst
      end
  end.

Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H
  end.

Ltac rewriterP := repeat (rewriteHyp; autorewrite with cpdt in *).

Ltac rewriter := autorewrite with cpdt in *; rewriterP.

Hint Rewrite app_ass : cpdt.

Ltac sintuition := simpl in *; intuition; try simplHyp; try congruence.

Ltac crush := sintuition; rewriter; sintuition; try omega.
