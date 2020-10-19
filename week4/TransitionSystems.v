Require Import List.
Import ListNotations.

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

(** Relations **)

(* A relation over a type `A` is a function `A -> A -> Prop` *)
Definition relation (A: Type) : Type := A -> A -> Prop.

Definition equivalent_relations {A: Type} (r1 r2: relation A) :=
  forall x y, r1 x y <-> r2 x y.

Notation "r1 == r2" := (equivalent_relations r1 r2) (at level 30).

Definition compose {A: Type} (r1 r2: relation A): relation A :=
  fun x y => (exists z, r1 x z /\ r2 z y).

Notation "r1 ** r2" := (compose r1 r2) (at level 20).

Lemma compose_assoc:
  forall A (r1 r2 r3: relation A),
    r1 ** (r2 ** r3) == (r1 ** r2) ** r3.
Proof.
  intros.
  unfold compose.
  intros Fx Fy.
  repeat step.
  all: exists z0; step; exists z; step.
Qed.

Fixpoint rel_pow {A: Type} (r: relation A) (n: nat): relation A :=
  match n with
  | 0 => fun a1 a2 => a1 = a2
  | S n => compose r (rel_pow r n)
  end.

Notation "r ^^ n" := (rel_pow r n) (at level 15).

Fixpoint is_path {A: Type} (r: relation A) (x: A) (p: list A) (y: A): Prop :=
  match p with
  | [] => x = y
  | z :: zs => r x z /\ is_path r z zs y
  end.

Lemma path_to_power: forall A (r: relation A) (p: list A) (y x: A),
    is_path r x p y -> (r ^^ (length p)) x y.
Proof. 
  induction p.
  + repeat step.
  + intros y.
    specialize(IHp y a).
    intros x.
    repeat step.
    unfold compose.
    exists a.
    step.
Qed.

Lemma is_path_cons:
  forall A (r: relation A) (x y z: A) (p: list A),
    r x y ->
    is_path r y p z ->
    is_path r x (y :: p) z.
Proof.
  intros.
  repeat step.
Qed.

Lemma power_to_path:
  forall A (r: relation A) (n: nat) (x y: A),
    (r ^^ n) x y ->
    exists p: list A, is_path r x p y /\ length p = n.
Proof.
  induction n.
  + repeat step || exists [].
  + intros.
    repeat step || unfold compose in H.
    repeat step || specialize(IHn z y) || exists (z::p).
Qed. 

Lemma path_compose:
  forall (A: Type) (r: relation A) (p1 p2: list A) (x y z: A),
    is_path r x p1 y ->
    is_path r y p2 z ->
    is_path r x (p1 ++ p2) z.
Proof.
  induction p1.
  + repeat step.
  + intros; specialize(IHp1 p2 a y z).
    repeat step.
Qed.

Lemma power_compose:
  forall A (r : relation A) (n1 n2: nat),
    (r ^^ n1) ** (r ^^ n2) == r ^^ (n1 + n2).
Proof.
  intros.
  induction n1.
  + unfold compose.
    split.
    all: repeat step || exists x.
  + repeat step. unfold compose.
    split.
    - repeat step || exists z0.
      apply IHn1.
      unfold compose.
      exists z; repeat step.
    - repeat step.
      apply IHn1 in H1; unfold compose in H1; repeat step.
      exists z0. repeat step.
      exists z. repeat step.
Qed.

(* `star r` is the reflexive and transitive closure of the relation `R` *)
Definition star { A } (r : relation A): A -> A -> Prop :=
  fun x y => (exists n, (r ^^ n) x y).

(* The reflexive and transitive closure of a relation is reflexive *)
Lemma star_refl:
  forall A (r: relation A) x,
    star r x x.
Proof.
  intros.
  unfold star.
  exists 0. step.
Qed.

(* The reflexive and transitive closure of a relation is transitive *)
Lemma star_trans:
  forall A (r : relation A) x y z,
    star r x y ->
    star r y z ->
    star r x z.
Proof.
  intros.
  unfold star.
  unfold star in H.
  unfold star in H0.
  repeat step.
  exists (n0 + n).
  apply power_compose.
  unfold compose.
  exists y.
  repeat step.
Qed.

(* The transitive closure of a relation "contains" the relation *)
Lemma star_step:
  forall A (r: relation A) x y,
    r x y ->
    star r x y.
Proof.
  intros.
  unfold star.
  exists 1.
  repeat step.
  unfold compose.
  exists y.
  repeat step.
Qed.

Lemma star_1n:
  forall A (r: relation A) x y z,
    r x y ->
    star r y z ->
    star r x z.
Proof.
  intros.
  apply star_step in H.
  apply (star_trans A r x y z).
  repeat step.
  apply H0.
Qed.


(** Transition Systems and Reachability **)

(* A transition system with states `Q` and alphabet `A` is a pair with:                *)
(* - An `initial` function of type `Q -> Prop` that says which states are initial      *)
(* - A function `r` of type `Q -> A -> Q -> Prop` such that `r q1 a q2` holds when the *)
(*   transition system has a transition from state `q1` to `q2` labelled by `a`        *)
Record Transition_System (Q A : Type) := new_Transition_System {
  initial : Q -> Prop;
  r : Q -> A -> Q -> Prop
}.

Arguments initial { Q A }.
Arguments r { Q A }.
Arguments new_Transition_System { Q A }.


(* Example *)
Definition ex_Q := nat.
Inductive ex_A := inc (n : nat) | dec (n : nat).

Definition ex_Counter_1 := {|
  initial := fun q => q = 0;
  r := fun q1 a q2 => match a with
               | inc 1 => q2 = q1 + 1
               | dec 1 => q2 = q1 - 1
               | _ => False
               end
  |}.

Definition ex_Counter_n := {|
  initial := fun q => q = 0;
  r := fun q1 a q2 => match a with
               | inc n => q2 = q1 + n
               | dec n => q2 = q1 - n
               end
  |}.

Notation "ts |- q1 ~ a '~>' q2" := (r ts q1 a q2) (at level 20).
Notation "ts |- q1 '~>' q2" := (exists a, ts |- q1 ~a~> q2) (at level 20).
Notation "ts |- q1 '~>*' q2" := (star (fun p q => ts |- p ~> q) q1 q2) (at level 20).
Notation "ts |- q1 '~>^' n q2" := (((fun p q => ts |- p ~> q) ^^ n) q1 q2) (at level 20, n at level 1).

Definition reachable { Q A } (ts : Transition_System Q A) (q: Q) : Prop :=
  exists q_i, initial ts q_i  /\  ts |- q_i ~>* q.


(** Traces of Transition Systems **)

(* A trace an a starting state `start` and sequences of states and labels *)
Record Trace (Q A : Type) := new_Trace {
  start: Q;
  states : list Q;
  labels : list A
}.

Arguments start { Q A }.
Arguments states { Q A }.
Arguments labels { Q A }.
Arguments new_Trace { Q A }.

Definition in_trace { Q A } q (tr : Trace Q A) : Prop :=
  q = start tr \/ In q (states tr).

(* `is_trace_aux ts q0 xs` holds when there are transition in `ts`   *)
(* starting from (not necessarily initial) state `q0`, going through *)
(* the states in `qs` and with labels in `xs`                        *)
Fixpoint is_trace_aux { Q A } (ts : Transition_System Q A)
  (q0 : Q) (qs : list Q) (xs : list A) : Prop :=
  match qs, xs with
  | nil, nil => True
  | q :: qs', x :: xs' => r ts q0 x q /\ is_trace_aux ts q qs' xs'
  | _, _ => False
  end.

(* A `trace` of `ts` starts with an initial state and then has valid transitions *)
Definition is_trace { Q A } (ts: Transition_System Q A) (tr: Trace Q A) : Prop :=
  is_trace_aux ts (start tr) (states tr) (labels tr) /\
  initial ts (start tr).

Lemma is_trace_aux_nil:
  forall Q A (ts : Transition_System Q A) q, is_trace_aux ts q nil nil.
Proof.
  intros.
  repeat step.
Qed.

(* A trace can be extended from the front with another transition *)
Lemma is_trace_aux_cons:
  forall A Q (ts : Transition_System Q A) q1 q2 qs x xs,
    ts |- q1 ~x~> q2 ->
    is_trace_aux ts q2 qs xs ->
    is_trace_aux ts q1 (q2 :: qs) (x :: xs).
Proof.
  intros.
  repeat step.
Qed.


(** Equivalence between reachability and traces **)
Search In.
Lemma trace_to_path:
  forall A Q (ts : Transition_System Q A) l1 q0 q l2 xs,
    is_trace_aux ts q0 (l1++q::l2) xs ->
    is_path (fun q1 q2 => ts |- q1 ~> q2) q0 (l1 ++ [q]) q.
Proof.
  induction l1.
  + repeat step || destruct_match.
    exists a. step.
  + repeat step || destruct_match.
    - exists a0. step.
    - specialize(IHl1 a q l2 l). step.
Qed.

(* All the states `q` that appear in the states of a trace are reachable *)
Lemma in_trace_reachable:
  forall A Q (ts : Transition_System Q A) (tr : Trace Q A) q,
    is_trace ts tr ->
    in_trace q tr ->
    reachable ts q.
Proof.
  intros.
  unfold reachable.
  exists (start tr).
  unfold is_trace in H.
  repeat step.
  unfold in_trace in H0.
  repeat step.
  + apply star_refl.
  + apply in_split in H. repeat step.
    rewrite -> H in H1.
    apply (trace_to_path A Q ts l1 (start tr) q l2 (labels tr)) in H1.
    apply path_to_power in H1.
    unfold star.
    exists (length (l1 ++ [q])); step.
Qed.

Lemma path_to_trace:
  forall A Q (ts : Transition_System Q A) p q0 q,
    is_path (fun q1 q2 => ts |- q1 ~> q2) q0 p q ->
    exists l, is_trace_aux ts q0 p l.
Proof.
  induction p.
  + repeat step || exists [].
  + repeat step || specialize(IHp a q).
    exists (a0 :: l). repeat step.
Qed.
  
Lemma path_end:
  forall A (r: relation A) p x y,
    is_path r x p y ->
    p = [] \/ exists l, p = l ++ [y].
Proof.
  induction p.
  + repeat step.
  + intros. unfold is_path in H. repeat step.
    specialize (IHp a y). repeat step.
    - right. exists []. repeat step.
    - right. exists (a :: l). repeat step.
Qed.

Lemma in_tail:
  forall A (q: A) (a: list A),
    In q (a ++ [q]).
Proof.
  induction a.
  + repeat step.
  + specialize(app_comm_cons a0 [q] a).
    intros.
    symmetry in H.
    rewrite -> H.
    apply in_cons.
    step.
Qed.

(* Conversely, if a state `q` is reachable, there exists a trace containing it *)
Lemma reachable_in_trace:
  forall A Q (ts : Transition_System Q A) q,
    reachable ts q ->
    exists tr,
      is_trace ts tr /\
      in_trace q tr.
Proof.
  intros.
  unfold reachable in H; repeat step.
  unfold star in H1; repeat step.
  apply power_to_path in H; repeat step.
  specialize(path_end Q (fun p q0 : Q => ts |- p ~> q0) p q_i q H1).
  intros.
  inversion H.
  + exists (new_Trace q [] []).
    unfold is_trace; unfold in_trace.
    repeat step.
  + inversion H2.
    rewrite -> H3 in H1.
    apply path_to_trace in H1.
    inversion H1.
    exists (new_Trace q_i (x++[q]) x0).
    unfold is_trace; unfold in_trace.
    repeat step.
    all: right; step; apply in_tail.
Qed.


(** Simulation Relations **)

Definition simulates { QC QA A }
  (tsc : Transition_System QC A) (tsa : Transition_System QA A) (R : QC -> QA -> Prop) :=

  (forall qc, initial tsc qc -> exists qa, R qc qa /\ initial tsa qa) /\
  (forall qc1 a qc2 qa1, tsc |- qc1 ~a~> qc2 -> R qc1 qa1 -> exists qa2, R qc2 qa2 /\ tsa |- qa1 ~a~> qa2).

(* The counter with `inc 1` and `dec 1` simulates the counter with `inc n` and `dec n`. *)
(* The relation used to show the simulation is the diagonal or identity relation.       *)
Lemma simulates_counter_1_n: simulates ex_Counter_1 ex_Counter_n (fun qc qa => True).
Proof.
  unfold simulates.
  split.
  + intros.
    step.
    exists 0; step.
  + intros.
    repeat step || destruct_match.
    - exists (qa1 + 1); step.
    - exists (qa1 - 1); step.
Qed.

Lemma simulates_trace_aux:
  forall QC QA A (tsc : Transition_System QC A) (tsa : Transition_System QA A) (R : QC -> QA -> Prop) xs qc1 qa1 ls,
    (forall qc1 a qc2 qa1, tsc |- qc1 ~a~> qc2 -> R qc1 qa1 -> exists qa2, R qc2 qa2 /\ tsa |- qa1 ~a~> qa2) ->
    is_trace_aux tsc qc1 xs ls ->
    R qc1 qa1 -> 
    exists xs',
      is_trace_aux tsa qa1 xs' ls.
Proof.
  induction xs.
  + repeat step || destruct_match.
    exists [].
    repeat step.
  + repeat step.
    repeat step || destruct_match.
    assert(H' := H).
    specialize(H qc1 a0 a qa1).
    specialize(H H2).
    specialize(H H1).
    repeat step.
    specialize(IHxs a qa2 l).
    specialize(IHxs H').
    specialize(IHxs H3).
    specialize(IHxs H0).
    repeat step.
    exists(qa2::xs').
    apply is_trace_aux_cons.
    repeat step.
    apply H.
Qed.


(* If a transition system `tsc` simulates a transition system `tsa`, then for every trace of *)
(* `tsc`, there exists a trace of `tsa` with the same labels.                                *)
Lemma simulates_inclusion_observable:
  forall QC QA A (tsc : Transition_System QC A) (tsa : Transition_System QA A) (R : QC -> QA -> Prop) trc,
    simulates tsc tsa R ->
    is_trace tsc trc ->
    exists tra,
      is_trace tsa tra /\
      labels trc = labels tra.
Proof.
  repeat step.
  unfold is_trace in H0; repeat step.
  unfold simulates in H; repeat step.
  specialize(H0 (start trc)).
  specialize(H0 H2); repeat step.
  specialize(simulates_trace_aux QC QA A tsc tsa R (states trc) (start trc) qa (labels trc)).
  repeat step.
  exists (new_Trace qa xs' (labels trc)); repeat step.
  unfold is_trace; repeat step.
Qed.