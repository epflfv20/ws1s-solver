Require Import Coq.Lists.List.
Import ListNotations.

Definition queue (T : Type) : Type := list T * list T.

Definition empty_queue (T : Type) : queue T := ([],[]).

Definition enqueue { T } (x : T) (q : queue T) : queue T :=
  (fst q, x :: snd q).

Definition dequeue { T } (q : queue T) : option (T * queue T) :=
  match fst q with
  | [] => match rev (snd q) with
          | [] => None
          | (x::xs) => Some (x,(xs,[]))
          end
  | (x::xs) => Some (x,(xs,snd q))
  end.



Definition toList { T } (q : queue T) : list T := fst q ++ rev (snd q).

Search app.

Lemma enqueue_correct:
  forall T (x : T) (q : queue T),
    toList (enqueue x q) = toList q ++ [x].
Proof.
  intros T x q.
  unfold toList.
  unfold enqueue.
  simpl.
  rewrite -> app_assoc.
  reflexivity.
Qed.


Lemma dequeue_some_sound:
  forall T (x : T) (q q' : queue T),
    dequeue q = Some (x, q') ->
    toList q = x :: toList q'.
Proof.
  intros. 
  unfold toList.
  destruct q.
  destruct q'.
  simpl.
  destruct l.
  + unfold dequeue in H. simpl in H. destruct (rev l0).
    - discriminate.
    - inversion H. simpl. rewrite -> app_nil_r. reflexivity.
  + unfold dequeue in H. simpl in H. inversion H. simpl. reflexivity.
Qed.

Lemma dequeue_none_sound:
  forall T (q : queue T),
    dequeue q = None ->
    toList q = [].
Proof.
  intros.
  unfold toList.
  unfold dequeue in H.
  destruct (fst q), (rev (snd q)).
  + simpl. reflexivity.
  + discriminate.
  + discriminate.
  + discriminate.
Qed.

Lemma dequeue_some_complete:
  forall T (x : T) (xs : list T) (q : queue T),
  toList q = x :: xs ->
  exists (q' : queue T),
    dequeue q = Some (x, q') /\
    toList q' = xs.
Proof.
  intros.
  unfold toList in H.
  unfold dequeue.
  destruct (fst q).
  + destruct (rev (snd q)).
    - simpl in H. discriminate.
    - simpl in H. inversion H. exists (xs,[]). split.
      * reflexivity.
      * unfold toList. simpl. rewrite -> app_nil_r. reflexivity.
  + simpl in H. exists (l, snd q). inversion H. split.
    * reflexivity.
    * unfold toList. simpl. reflexivity.
Qed.

Lemma dequeue_none_complete:
  forall T (q : queue T),
    toList q = [] ->
    dequeue q = None.
Proof.
  intros.
  unfold toList in H.
  unfold dequeue.
  destruct (fst q), (rev (snd q)).
  + reflexivity.
  + simpl in H. discriminate.
  + simpl in H. discriminate.
  + simpl in H. discriminate.
Qed.

Theorem dequeue_none_correct:
  forall T (q : queue T),
    toList q = [] <->
    dequeue q = None.
Proof.
  intros.
  split.
  + apply dequeue_none_complete.
  + intros. unfold dequeue in H. unfold toList. destruct (fst q).
    - destruct (rev (snd q)).
      * simpl. reflexivity. 
      * discriminate.
    - discriminate.
Qed.

Theorem dequeue_some_correct:
forall T (q : queue T) (x : T) (xs : list T),
  toList q = x :: xs <->
  exists (q' : queue T),
    dequeue q = Some (x, q') /\
    toList q' = xs.
Proof.
  intros.
  split.
  + apply dequeue_some_complete.
  + intros. destruct H. destruct H. rewrite <- H0. apply dequeue_some_sound. apply H.
Qed.