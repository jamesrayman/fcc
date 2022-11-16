Require Import List Relations Arith Alphabet Bool Language.

Section Computation.
  Context {state: Type}.
  Variable step_rel: relation state.
  Variable accepting_state: state -> Prop.
  Variable encode_input: bitstr -> state.

  Definition deterministic :=
    forall (s s' s'': state), step_rel s s' -> step_rel s s'' -> s' = s''.

  Definition decision_model: Type := (relation state) * (state -> Prop) * (bitstr -> state).
  Local Definition dm := (step_rel, accepting_state, encode_input).
  Definition dm_class := decision_model -> Prop.

  Inductive steps: relation state :=
  | stepsRefl: forall (s: state), steps s s
  | stepsOnce: forall (s s' s'': state),
      steps s s' /\ step_rel s' s'' -> steps s s''.

  Definition halted (s: state) := forall (s': state), ~step_rel s s'.

  Definition runtime_f (initial: state) (f: state -> nat) :=
    forall (s s': state), steps initial s -> step_rel s s' -> f s > f s'.

  Definition halts (initial: state) :=
    exists (f: state -> nat), runtime_f initial f.

  Definition halts_within (initial: state) (n: nat) :=
    exists (f: state -> nat), runtime_f initial f /\ f initial = n.

  Lemma halts_halts_within:
    forall (initial: state), halts initial -> exists (n: nat), halts_within initial n.
  Proof.
    intros.
    destruct H as [f].
    exists (f initial).
    unfold halts_within.
    exists f.
    auto.
  Qed.

  Lemma halts_within_monotone:
    forall (initial: state) (n m: nat), n < m ->
    halts_within initial n -> halts_within initial m.
  Proof.
    intros.
    destruct H0 as [f].
    destruct H0.
    unfold halts_within.
    apply Nat.le_exists_sub in H.
    destruct H.
    destruct H.
    exists (fun s => x + S (f s)).
    unfold runtime_f.
    rewrite H1.
    intuition.
  Qed.

  Definition runtime (initial: state) (t: nat) :=
    halts_within initial t /\ forall t', t' < t -> ~halts_within initial t'.

  Lemma runtime_unique:
    forall (initial: state) (t t': nat),
    runtime initial t -> runtime initial t' -> t = t'.
  Proof.
    intros.
    destruct (t ?= t') eqn: Hc.
    - apply Nat.compare_eq_iff in Hc. auto.
    - exfalso.
      apply Nat.compare_lt_iff in Hc.
      unfold runtime in H, H0.
      destruct H, H0.
      exact (H2 t Hc H).
    - exfalso.
      apply Nat.compare_gt_iff in Hc.
      unfold runtime in H, H0.
      destruct H, H0.
      exact (H1 t' Hc H0).
  Qed.

  Lemma runtime_exists:
    forall (initial: state), halts initial -> exists (t: nat), runtime initial t.
  Proof.
    intros.
    apply halts_halts_within in H.
    destruct H as [t].
    unfold runtime.
    induction t.
    - exists 0.
      intuition.
      inversion H0.
    - 
  Qed.

  Lemma runtime_monotone:

  Definition halts' (input: bitstr) := halts (encode_input input).

  Inductive decision: state -> bool -> Prop :=
  | decisionRejects: forall (s: state),
      halts s -> (forall (s': state), steps s s' -> halted s' -> ~accepting_state s') ->
      decision s false
  | decisionAccepts: forall (s: state),
      halts s -> (exists (s': state), steps s s' /\ halted s' /\ accepting_state s') ->
      decision s true.

  Lemma not_accept_reject: forall (s: state), ~(decision s false /\ decision s true).
  Proof.
    intro. intro.
    destruct H.
    inversion H. inversion H0. subst. clear H H0.
    destruct H5.
    specialize H2 with x.
    intuition.
  Qed.

  Definition decision' (w: bitstr) (b: bool) := decision (encode_input w) b.
  Definition rejects (w: bitstr) := decision' w false.
  Definition accepts (w: bitstr) := decision' w true.

  Lemma not_accept_reject': forall (w: bitstr), ~(rejects w /\ accepts w).
  Proof.
    intro.
    unfold rejects.
    unfold decision'.
    apply not_accept_reject.
  Qed.

  Definition next_steps_f (f: state -> list state) :=
    forall (s s': state), step_rel s s' <-> In s' (f s).

  Lemma next_steps_f_halt_dec:
    forall f, next_steps_f f -> forall (s: state), {halted s} + {~halted s}.
  Proof.
    unfold next_steps_f.
    intros.
    unfold halted.
    destruct (f s) eqn: Hfs.
    - left. intros.
      specialize H with s s'.
      rewrite Hfs in H.
      intuition.
    - right.
      intro.
      specialize H0 with s0.
      specialize H with s s0.
      rewrite Hfs in H.
      intuition.
  Qed.

  Theorem next_steps_comp_halt_decision:
    forall f, next_steps_f f ->
    forall (init: state), halts init -> {decision init false} + {decision init true}.
  Proof.
    unfold next_steps_f.
    unfold halts.
    intros.
  Qed.

  Definition decides (l: language): Prop :=
    forall (w: bitstr), halts' w /\ (accepts w <-> l w).
End Computation.

Section Simulation.
  Definition decidable {state: Type} (c: @dm_class state) (l: language) :=
    exists (dm: decision_model), c dm /\
    let (sr'as, encode_input) := dm in
    let (step_rel, accepting_state) := sr'as in
    decides step_rel accepting_state encode_input l.

  Definition simulates {state: Type} (c c': @dm_class state) :=
    forall (l: language), decidable c' l -> decidable c l.

End Simulation.
