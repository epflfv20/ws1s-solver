Require Import Coq.Lists.List.
Import ListNotations.
(* Somme usefull tactics *)

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
(* End of useful tactics *)

Definition queue (T : Type) : Type := list T * list T.

Definition empty_queue (T : Type) : queue T :=
  pair nil nil.

Definition enqueue { T } (x : T) (q : queue T) : queue T :=
  (fst q, cons x (snd q)).

Definition dequeue { T } (q : queue T) : option (T * queue T) :=
  match q with
  | (cons x ff, rr) => Some (x, (ff, rr))
  | (nil, rr) => 
    match rev rr with
    | cons x rf => Some (x, (rf, nil))
    | nil => None
    end
  end
.

Definition toList { T } (q : queue T) : list T := fst q ++ rev (snd q).

Lemma enqueue_correct:
  forall T (x : T) (q : queue T),
    toList (enqueue x q) = toList q ++ [x].
Proof.
  intros.
  unfold toList, enqueue.
  simpl.
  apply app_assoc.
Qed.

Lemma dequeue_none_sound:
  forall T (q : queue T),
    dequeue q = None ->
    toList q = [].
Proof.
  intros.
destruct q.
unfold toList.
simpl.
repeat step || destruct_match.
Qed.

Lemma dequeue_some_sound:
  forall T (x : T) (q q' : queue T),
    dequeue q = Some (x, q') ->
    toList q = x :: toList q'.
Proof.
  intros.
  destruct q.
  destruct q'.
  step.
  repeat step || destruct_match.
  invert_constructor_equality.
  rewrite app_nil_r.
reflexivity.
Qed.

Lemma dequeue_some_complete:
  forall T (x : T) (xs : list T) (q : queue T),
  toList q = x :: xs ->
  exists (q' : queue T),
    dequeue q = Some (x, q') /\
    toList q' = xs.
Proof.
  intros.
  destruct q.
  destruct l eqn:Eql.
+
  exists (xs, nil).
  simpl.
  destruct l0 eqn:eql0. 
  discriminate.
  simpl.
  repeat step||destruct_match||constructor_equality.
  apply app_nil_r.
+
exists (l1, l0).
simpl.
step.
repeat step||constructor_equality.
unfold toList.
unfold toList in H.
simpl.
simpl in H.
invert_constructor_equality.
reflexivity.
Qed.

Lemma dequeue_none_complete:
  forall T (q : queue T),
    toList q = [] ->
    dequeue q = None.
Proof.
  intros.
  unfold dequeue.
  repeat step || destruct_match.
Qed.

Theorem dequeue_none_correct:
  forall T (q : queue T),
    toList q = [] <->
    dequeue q = None.
Proof.
  intros.
  step.
apply dequeue_none_complete, H.
apply dequeue_none_sound, H.
Qed.

Theorem dequeue_some_correct:
forall T (q : queue T) (x : T) (xs : list T),
  toList q = x :: xs <->
  exists (q' : queue T),
    dequeue q = Some (x, q') /\
    toList q' = xs.
Proof.
  intros.
  step.
  apply dequeue_some_complete, H.
  repeat step. apply dequeue_some_sound, H0.
Qed.
