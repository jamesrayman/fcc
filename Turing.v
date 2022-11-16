Require Import Arith List Alphabet.
Import ListNotations.

Section Turing.
  Context {state_count symbol_count: positive}.

  Local Definition state := alphabet state_count.
  Local Definition symbol := alphabet symbol_count.

  Local Definition blank := sym_0 symbol_count.

  Inductive direction :=
  | Left
  | Right.

  Definition turing_machine (stc symc: positive) :=
    alphabet stc -> alphabet symc -> alphabet stc -> alphabet symc -> direction -> bool.
  Local Definition machine := turing_machine state_count symbol_count.
  Definition tape := str symbol_count.

  Definition head (t: tape): symbol := hd blank t.

  Definition tail (t: tape): tape := tl t.

  Definition State: Set := state * tape * tape.

  Definition go_left (s: State) (sym: symbol) :=
    let (st'l, r) := s in let (st, l) := st'l in
    (st, tail l, cons (head r) (cons sym (tail r))).

  Definition go_right (s: State) (sym: symbol) :=
    let (st'l, r) := s in let (st, l) := st'l in
    (st, cons sym l, tail r).

  Lemma go_left_sym: forall (s: State) (sym: symbol) (s': state) (l r: tape),
    go_left s sym = (s', l, r) -> sym = head (tail r).
  Proof.
    intros.
    unfold go_left in H.
    destruct s in H.
    destruct p in H.
    inversion H. subst. auto.
  Qed.

  Lemma go_left_state: forall (sym: symbol) (s s': state) (l r l' r': tape),
    go_left (s, l, r) sym = (s', l', r') -> s = s'.
  Proof.
    intros.
    unfold go_left in H.
    inversion H. subst. auto.
  Qed.

  Lemma go_right_sym: forall (s: State) (sym: symbol) (s': state) (l r: tape),
    go_right s sym = (s', l, r) -> sym = head l.
  Proof.
    intros.
    unfold go_right in H.
    destruct s in H.
    destruct p in H.
    inversion H. subst. auto.
  Qed.

  Lemma go_right_state: forall (sym: symbol) (s s': state) (l r l' r': tape),
    go_right (s, l, r) sym = (s', l', r') -> s = s'.
  Proof.
    intros.
    unfold go_left in H.
    inversion H. subst. auto.
  Qed.

  Definition go_d (d: direction) :=
    match d with
    | Left => go_left
    | Right => go_right
    end.

  Inductive step: machine -> State -> State -> Prop :=
  | stepCons: forall (m: machine) (l r: tape) (s s': state) (sym': symbol) (d: direction),
      m s (head r) s' sym' d = true ->
      step m (s, l, r) (go_d d (s', l, r) sym').
End Turing.

Section RunTuring.
  Context {state_count symbol_count: positive}.

  Local Definition machine := turing_machine state_count symbol_count.
  Local Definition state := alphabet state_count.
  Local Definition symbol := alphabet symbol_count.
  Local Definition tape := str symbol_count.
  Local Definition State: Set := state * tape * tape.
  Local Definition blank := sym_0 symbol_count.
  Local Definition initial := sym_0 state_count.

  Variable m: machine.
  Variable program input: tape.
  Local Definition Initial: State := (initial, program, input).
  Local Definition m_step := step m.
  Local Definition m_steps := steps m_step.

  Local Definition tm_halts := halts Initial m_step.
  Local Definition tm_halted (s: State) := halted s m_step.

  Local Definition m_runtime_func := runtime_func Initial m_step.

  Local Definition next_steps_point (s: State) (i: state) (j: symbol): list State :=
    let (st'l, r) := s in let (st, l) := st'l in
    match m st (head r) i j Left with
    | false => nil
    | true => cons (go_left (i, l, r) j) nil
    end ++
    match m st (head r) i j Right with
    | false => nil
    | true => cons (go_right (i, l, r) j) nil
    end.

  Local Lemma next_steps_point_correct:
    forall (s s': State),
    let (st'l, r) := s' in let (st, l) := st'l in
    m_step s s' -> In s' (next_steps_point s st (head (tail r))) \/
                   In s' (next_steps_point s st (head l)).
  Proof.
    destruct s as [st'l r].
    destruct st'l as [st l].
    destruct s' as [st'l' r'].
    destruct st'l' as [st' l'].
    intros.
    unfold next_steps_point.
    inversion H; subst.
    assert (head (head r :: sym' :: tail r) = head r). unfold head. unfold hd. auto.
    destruct d.
    - left.
      unfold go_d in H5.
      remember H5 as H7. clear HeqH7.
      apply go_left_state in H7.
      apply go_left_sym in H5.
      rewrite <- H5.
      rewrite <- H7.
      rewrite H2. simpl. auto.
    - right.
      unfold go_d in H5.
      remember H5 as H7. clear HeqH7.
      apply go_right_state in H7.
      apply go_right_sym in H5.
      rewrite <- H5.
      rewrite <- H7.
      rewrite H2. simpl.
      intuition.
  Qed.

  Local Lemma next_steps_point_correct':
    forall (s s': State), m_step s s' ->
    exists (st: state) (sym: symbol), In s' (next_steps_point s st sym).
  Proof.
    intros.
    remember (next_steps_point_correct s s').
    destruct s'.
    destruct p.
    apply y in H.
    destruct H; eauto.
  Qed.

  Definition next_steps (s: State): list State :=
    flat_map
      (fun sym =>
         flat_map (fun st => next_steps_point s st sym) (all_syms state_count)
      )
      (all_syms symbol_count).

  Theorem next_steps_correct: forall (s s': State), m_step s s' <-> In s' (next_steps s).
  Proof.
    split; intros.
    - apply next_steps_point_correct' in H.
      destruct H.
      destruct H.
      unfold next_steps.
      apply in_flat_map.
      exists x0.
      split.
      apply all_syms_correct.
      apply in_flat_map.
      exists x.
      split.
      apply all_syms_correct.
      exact H.
    - unfold next_steps in H.
      apply in_flat_map in H.
      destruct H.
      destruct H.
      clear H.
      apply in_flat_map in H0.
      destruct H0.
      destruct H.
      clear H.
  Admitted.

  Definition is_halted (s: State) :=
    match next_steps s with
    | nil => true
    | _ => false
    end.

  Theorem is_halted_correct: forall (s: State), tm_halted s <-> is_halted s = true.
  Proof.
    intros.
    unfold is_halted.
    unfold tm_halted.
    unfold halted.
    split; intros.
    - destruct (next_steps s) eqn:Hs; auto.
      remember (List.in_eq s0 l) as Hin.
      clear HeqHin.
      rewrite <- Hs in Hin.
      apply <- next_steps_correct in Hin.
      exfalso.
      exact (H s0 Hin).
    - intro.
      destruct (next_steps s) eqn:Hs.
      + apply next_steps_correct in H0.
        rewrite Hs in H0.
        exact (List.in_nil H0).
      + inversion H.
  Qed.

  Definition read_decision (s: State) :=
    let (st'l, r) := s in
    match sym_to_nat (head r) with
    | 0 => false
    | _ => true
    end.

  Inductive decision': State -> bool -> Prop :=
  | Rejects: tm_halts -> forall (init: State), (
      forall (l r: tape) (s: state),
        tm_halted (s, l, r) -> m_steps init (s, l, r) -> sym_to_nat (head r) = 0
    ) -> decision' init false
  | Accepts: tm_halts -> forall (init: State), (
      exists (l r: tape) (s: state),
        tm_halted (s, l, r) /\ m_steps init (s, l, r) /\ sym_to_nat (head r) <> 0
    ) -> decision' init true.

  Fixpoint simulate (n: nat) (s: State): option bool :=
    if is_halted s then Some (read_decision s)
    else None.

  Theorem simulate_correct:
    forall (b: bool) (s: State), decision' s b <-> exists (n: nat), simulate n s = Some b.
  Proof.

  Qed.
End RunTuring.
