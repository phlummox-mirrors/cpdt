(* Copyright (c) 2008, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

Require Import Eqdep List.

Require Omega.

Set Implicit Arguments.


Ltac inject H := injection H; clear H; intros; try subst.

Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

Ltac simplHyp invOne :=
  match goal with
    | [ H : ex _ |- _ ] => destruct H

    | [ H : ?F _ = ?F _ |- _ ] => injection H;
      match goal with
        | [ |- _ = _ -> _ ] => try clear H; intros; try subst
      end
    | [ H : ?F _ _ = ?F _ _ |- _ ] => injection H;
      match goal with
        | [ |- _ = _ -> _ = _ -> _ ] => try clear H; intros; try subst
      end

    | [ H : ?F _ |- _ ] => inList F invOne; inversion H; [idtac]; clear H; try subst
    | [ H : ?F _ _ |- _ ] => inList F invOne; inversion H; [idtac]; clear H; try subst
    | [ H : ?F _ _ _ |- _ ] => inList F invOne; inversion H; [idtac]; clear H; try subst
    | [ H : ?F _ _ _ _ |- _ ] => inList F invOne; inversion H; [idtac]; clear H; try subst
    | [ H : ?F _ _ _ _ _ |- _ ] => inList F invOne; inversion H; [idtac]; clear H; try subst
  end.

Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H
  end.

Ltac rewriterP := repeat (rewriteHyp; autorewrite with cpdt in *).

Ltac rewriter := autorewrite with cpdt in *; rewriterP.

Hint Rewrite app_ass : cpdt.

Definition done (T : Type) (x : T) := True.

Ltac inster e trace :=
  match type of e with
    | forall x : _, _ =>
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      match trace with
        | (_, _) =>
          match goal with
            | [ H : done (trace, _) |- _ ] => fail 1
            | _ =>
              let T := type of e in
                match type of T with
                  | Prop =>
                    generalize e; intro;
                      assert (done (trace, tt)); [constructor | idtac]
                  | _ =>
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)); [constructor | idtac])
                end
          end
      end
  end.

Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Ltac crush' lemmas invOne :=
  let sintuition := simpl in *; intuition; try subst; repeat (simplHyp invOne; intuition; try subst); try congruence
    in (sintuition; rewriter;
      match lemmas with
        | false => idtac
        | _ => repeat ((app ltac:(fun L => inster L L) lemmas || appHyps ltac:(fun L => inster L L));
          repeat (simplHyp invOne; intuition)); un_done
      end; sintuition; try omega; try (elimtype False; omega)).

Ltac crush := crush' false fail.

Theorem dep_destruct : forall (T : Type) (T' : T -> Type) x (v : T' x) (P : T' x -> Prop),
  (forall x' (v' : T' x') (Heq : x' = x), P (match Heq in (_ = x) return (T' x) with
                                               | refl_equal => v'
                                             end))
  -> P v.
  intros.
  generalize (H _ v (refl_equal _)); trivial.
Qed.

Ltac dep_destruct E :=
  let doit A :=
    let T := type of A in
      generalize dependent E;
        let e := fresh "e" in
          intro e; pattern e;
            apply (@dep_destruct T);
              let x := fresh "x" with v := fresh "v"  in
                intros x v; destruct v; crush;
                  let bestEffort Heq E tac :=
                    repeat match goal with
                             | [ H : context[E] |- _ ] =>
                               match H with
                                 | Heq => fail 1
                                 | _ => generalize dependent H
                               end
                           end;
                    generalize Heq; tac Heq; clear Heq; intro Heq;
                      rewrite (UIP_refl _ _ Heq); intros in
                  repeat match goal with
                           | [ Heq : ?X = ?X |- _ ] =>
                             generalize (UIP_refl _ _ Heq); intro; subst; clear Heq
                           | [ Heq : ?E = _ |- _ ] => bestEffort Heq E ltac:(fun E => rewrite E)
                           | [ Heq : _ = ?E |- _ ] => bestEffort Heq E ltac:(fun E => rewrite <- E)
                         end
                  in match type of E with
                       | _ _ ?A => doit A
                       | _ ?A => doit A
                     end.
