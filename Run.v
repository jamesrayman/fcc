Require Import List Relations Arith Turing Alphabet Bool.

Section Run.
  Context {state: Type}.
  Variable initial: state.
  Variable step_rel: relation state.

  Inductive steps: relation state :=
  | stepsRefl: forall (s: state), steps s s
  | stepsOnce: forall (s s' s'': state),
      steps s s' /\ step_rel s' s'' -> steps s s''.

  Definition halted := forall (s: state), ~step_rel initial s.

  Definition runtime_func (f: state -> nat) :=
    forall (s s': state), steps initial s -> step_rel s s' -> f s > f s'.

  Definition halts := exists (f: state -> nat), runtime_func f.
End Run.

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

  Local Fixpoint next_steps' (s: State) (i: state) (j: symbol) (k: nat): list State.
    remember (next_steps_point s i j) as rest.
    destruct k. exact rest.

    destruct i as [n_i prf_i].
    destruct (sym_dec state_count (S n_i)) as [prf_i'|prf_i'].
    - remember (nat_to_sym state_count (S n_i) prf_i') as i'.
      exact (rest ++ (next_steps' s i' j (k-1))).
    - destruct j as [n_j prf_j].
      destruct (sym_dec symbol_count (S n_j)) as [prf_j'|prf_j'].
      + remember (nat_to_sym symbol_count (S n_j) prf_j') as j'.
        exact (rest ++ (next_steps' s initial j' (k-1))).
      + exact rest.
  Defined.

  Definition next_steps (s: State): list State :=
    next_steps' s initial blank (state_count * symbol_count).

  Theorem next_steps_correct: forall (s s': State), m_step s s' <-> In s' (next_steps s).
  Proof.

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

  Inductive decision: bool -> Prop :=
  | Rejects: tm_halts -> (
      forall (l r: tape) (s: state),
        tm_halted (s, l, r) -> m_steps Initial (s, l, r) -> sym_to_nat (head r) = 0
    ) -> decision false
  | Accepts: tm_halts -> (
      exists (l r: tape) (s: state),
        tm_halted (s, l, r) /\ m_steps Initial (s, l, r) /\ sym_to_nat (head r) <> 0
    ) -> decision true.



  Fixpoint simulate (n: nat) (s: State): option bool :=
    if is_halted s then read_decision s
    else 

  Theroem simulate_implies_halt: .
  Proof.

  Qed.

  Theorem halt_implies_simulate: .
  Proof.

  Qed.
End RunTuring.

Section Decision'.
  Definition decision': .
  language_of

End Decision'.
