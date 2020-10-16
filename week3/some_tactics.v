Require Import Coq.micromega.Psatz. (* `lia` tactic for linear integer arithmetic *)

(* enables use of `eauto with lia` *)
Hint Extern 1 => lia: lia.

(* destruct pairs in context *)
Ltac destruct_pairs :=
  match goal with
  | H: _ * _ |- _ => destruct H
  end.

(* destruct existentials in context *)
Ltac destruct_exists :=
  match goal with
  | H: exists x, _ |- _ => let freshX := fresh x in destruct H as [ freshX ]
  end.

(* destruct refinements in context *)
Ltac destruct_refinements :=
  match goal with
  | H: { x: _ | _ } |- _ => let freshX := fresh x in destruct H as [ freshX ]
  end.

(* one step using basic Coq tactics, using computation simplification *)
Ltac step0 :=
  (intuition auto) || congruence || subst ||
  destruct_exists || destruct_pairs || destruct_refinements.

(* one step using basic Coq tactics, with computation simplification *)
(* use `repeat step` for performing all possible simplifications *)
Ltac step := step0 || cbn in *.

(* performs case analysis whenever there is a `match` somewhere *)
(* you can e.g. use `repeat step || destruct_match` if you want to *)
(* perform as many simplifications and case analyses as possible *)
Ltac destruct_match :=
  match goal with
  | [ |- context[match ?t with _ => _ end]] =>
    let matched := fresh "m" in
    destruct t eqn:matched
  | [ H: context[match ?t with _ => _ end] |- _ ] =>
    let matched := fresh "m" in
    destruct t eqn:matched
end.

(* when the goal is an equality between two terms starting using the same constructor *)
(* this generates subgoals for proving that the arguments are equal *)
Ltac constructor_equality :=
  match goal with
  | |- ?F _ = ?F _ => is_constructor F; f_equal
  | |- ?F _ _ = ?F _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ = ?F _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ = ?F _ _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ _ = ?F _ _ _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ _ _ = ?F _ _ _ _ _ _ => is_constructor F; f_equal
  end.

(* when there is an equality between the same constructor in a hypothesis H *)
(* this creates new hypotheses stating that the arguments are equal *)
Ltac invert_constructor_equality :=
  match goal with
  | H: ?F _ = ?F _ |- _ => is_constructor F; inversion H; clear H
  | H: ?F _ _ = ?F _ _ |- _ => is_constructor F; inversion H; clear H
  | H: ?F _ _ _ = ?F _ _ _ |- _ => is_constructor F; inversion H; clear H
  | H: ?F _ _ _ _ = ?F _ _ _ _ |- _ => is_constructor F; inversion H; clear H
  | H: ?F _ _ _ _ _ = ?F _ _ _ _ _ |- _ => is_constructor F; inversion H; clear H
  | H: ?F _ _ _ _ _ _ = ?F _ _ _ _ _ _ |- _ => is_constructor F; inversion H; clear H
  end.