Require Import Relations Arith Turing Alphabet Bool.

Section Run.
  Variable state: Type.
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
  Variable state_count symbol_count: positive.

  Local Definition machine := machine state_count symbol_count.
  Local Definition state := alphabet state_count.
  Local Definition symbol := alphabet symbol_count.
  Local Definition tape := tape symbol_count.
  Local Definition State: Set := state * tape * tape.
  Local Definition head := head symbol_count.
  Local Definition tail := tail symbol_count.
  Local Definition blank_sym := blank symbol_count.
  Local Definition blank_state := blank state_count.

  Variable m: machine.
  Variable initial: state = sym_0 state_count.
  Variable program input: tape.
  Local Definition Initial: State := (initial, program, input).
  Local Definition m_step := step state_count symbol_count m.
  Local Definition m_steps := steps State m_step.

  Definition tm_halts := halts State Initial m_step.
  Definition tm_halted (s: State) := halted State s m_step.

  Local Definition m_runtime_func := runtime_func State Initial m_step.

  Local Definition next_steps' (s: State) (i: state) (j: symbol): list State :=
  nil.

  Definition next_steps (s: State): list State := next_steps' s blank_state blank_sym.

  Definition is_halted (s: State) := next_steps s = nil.

  Inductive decision: bool -> Prop :=
  | Rejects: tm_halts -> (
      forall (l r: tape) (s: state),
        tm_halted (s, l, r) -> m_steps Initial (s, l, r) -> sym_to_nat (head r) = 0
    ) -> decision false
  | Accepts: tm_halts -> (
      exists (l r: tape) (s: state),
        tm_halted (s, l, r) /\ m_steps Initial (s, l, r) /\ sym_to_nat (head r) <> 0
    ) -> decision true.

  Fixpoint simulate (s: State) (n: nat).

  Theroem simulate_implies_halt: .
  Proof.

  Qed.

  Theorem halt_implies_simulate: .
  Proof.

  Qed.
End RunTuring.
