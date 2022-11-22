Require Import List Relations Arith Alphabet Bool Language Lia.

Section Computation.
  Context {state: Type}.
  Variable step_rel: relation state.
  Variable accepting_state: state -> Prop.
  Variable encode_input: bitstr -> state.

  Definition deterministic :=
    forall (s s' s'': state), step_rel s s' -> step_rel s s'' -> s' = s''.

  Record decision_model :=
    { dm_step: relation state; dm_acc: state -> Prop; dm_enc: bitstr -> state }.
  Definition dm_class := decision_model -> Prop.

  Inductive steps: relation state :=
  | stepsRefl: forall (s: state), steps s s
  | stepsOnce: forall (s s' s'': state),
      steps s s' -> step_rel s' s'' -> steps s s''.


  Lemma steps_transitive: forall (s s' s'': state),
    steps s s' -> steps s' s'' -> steps s s''.
  Proof.
    intros.
    induction H0; auto.
    apply stepsOnce with (s' := s'); auto.
  Qed.

  Lemma first_step: forall (s s': state),
    steps s s' -> s = s' \/ exists s'', step_rel s s''.
  Proof.
    clear accepting_state.
    intros.
    induction H.
    - intuition.
    - destruct IHsteps.
      + subst.
        eauto.
      + eauto.
  Qed.

  Definition halted (s: state) := forall (s': state), ~step_rel s s'.

  Definition runtime_f (initial: state) (f: state -> nat) :=
    forall (s s': state), steps initial s -> step_rel s s' -> f s > f s'.

  Lemma runtime_f_monotone:
    forall f (s s': state), steps s s' -> runtime_f s f -> f s >= f s'.
  Proof.
    intros.
    unfold runtime_f in H0.
    induction H.
    - auto.
    - remember (IHsteps H0).
      enough (f s' > f s'').
      + lia.
      + apply H0; auto.
  Qed.

  Lemma runtime_f_monotone':
    forall f (s s': state), steps s s' -> runtime_f s f -> runtime_f s' f.
  Proof.
    unfold runtime_f.
    intros.
    apply H0; auto.
    apply steps_transitive with (s' := s'); auto.
  Qed.

  Definition halts (initial: state) :=
    exists f, runtime_f initial f.

  Lemma halts_steps_monotone:
    forall (s s': state), steps s s' -> halts s -> halts s'.
  Proof.
    intros.
    unfold halts in *.
    destruct H0 as [f].
    exists f.
    unfold runtime_f in *.
    induction H.
    - exact H0.
    - intros.
      apply H0; auto.
      apply steps_transitive with (s' := s'); auto.
      apply steps_transitive with (s' := s''); auto.
      apply stepsOnce with (s' := s'); auto.
      constructor.
  Qed.

  Definition halts_within (initial: state) (n: nat) :=
    exists (f: state -> nat), runtime_f initial f /\ f initial = n.

  Axiom halts_within_constructible:
    forall (initial: state) (n: nat), halts_within initial n ->
    { f | runtime_f initial f /\ f initial = n }.

  Lemma halts_within_monotone:
    forall (initial: state) (n m: nat), n < m ->
    halts_within initial n -> halts_within initial m.
  Proof.
    clear accepting_state.
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

  Lemma halts_within_monotone':
    forall (initial: state) (n m: nat), n <= m ->
    halts_within initial n -> halts_within initial m.
  Proof.
    intros.
    apply Nat.lt_eq_cases in H.
    destruct H.
    - eapply halts_within_monotone; eauto.
    - subst. auto.
  Qed.

  Lemma halts_within_step_monotone:
    forall (s s': state) (t : nat),
    step_rel s s' -> halts_within s (S t) -> halts_within s' t.
  Proof.
    intros.
    unfold halts_within in H0.
    destruct H0 as [f].
    destruct H0.
    apply halts_within_monotone' with (n := f s').
    - unfold runtime_f in H0.
      specialize H0 with s s'.
      remember (H0 (stepsRefl s) H).
      lia.
    - unfold halts_within.
      exists f. intuition.
      apply (runtime_f_monotone' f s s'); repeat econstructor; auto.
  Qed.

  Lemma halts_within_steps_monotone:
    forall (s s': state) (t : nat),
    steps s s' -> halts_within s t -> halts_within s' t.
  Proof.
    intros.
    unfold halts_within in H0.
    destruct H0 as [f].
    destruct H0.
    assert (halts_within s' (f s')).
    - exists f.
      unfold runtime_f in *.
      intuition.
      apply H0; intuition.
      apply steps_transitive with (s' := s'); auto.
    - destruct (Nat.eq_dec t (f s')).
      + exists f.
        unfold runtime_f.
        intuition.
        apply H0; intuition.
        apply steps_transitive with (s' := s'); auto.
      + apply halts_within_monotone with (n := f s'); auto.
        rewrite <- H1.
        rewrite <- H1 in n.
        remember (runtime_f_monotone f s s' H H0).
        lia.
  Qed.

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

  Lemma runtime_zero_halted:
    forall (s: state),
    halted s <-> runtime s 0.
  Proof.
    unfold halted.
    unfold runtime.
    unfold halts_within.
    unfold runtime_f.
    intuition.
    - exists (fun x => 0).
      intuition.
      exfalso.
      remember (first_step s s0 H0) as Ht.
      destruct Ht.
      + subst.
        eapply H. eauto.
      + destruct e.
        eapply H. eauto.
    - lia.
    - destruct H0 as [f].
      destruct H0.
      remember (H0 s s' (stepsRefl s) H).
      lia.
  Qed.

  Lemma runtime_step_monotone:
    forall (s s': state) (t t': nat),
    runtime s t -> runtime s' t' -> step_rel s s' -> t > t'.
  Proof.
    intros.
    unfold runtime in H, H0.
    destruct H, H0.
    destruct t.
    - assert (runtime s 0).
      + unfold runtime. intuition.
      + apply runtime_zero_halted in H4.
        exfalso.
        unfold halted in H4.
        apply (H4 s').
        auto.
    - remember (halts_within_step_monotone s s' t H1 H).
      destruct (S t ?= t') eqn: Hc.
      + apply Nat.compare_eq_iff in Hc.
        exfalso.
        assert (t < t') by lia.
        exact (H3 t H4 h).
      + apply Nat.compare_lt_iff in Hc.
        exfalso.
        assert (t < t') by lia.
        exact (H3 t H4 h).
      + apply Nat.compare_gt_iff in Hc.
        auto.
  Qed.

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

  Definition next_steps_exists :=
    { f: state -> list state | forall (s s': state), step_rel s s' <-> In s' (f s)}.

  Lemma runtime_tight:
    next_steps_exists ->
    forall (s: state) (t: nat),
    runtime s (S t) -> exists (s': state), step_rel s s' /\ runtime s' t.
  Proof.
    intros.
    destruct X as [f Hf].
    remember (Hf s) as Hfs. clear HeqHfs Hf.
  Admitted.

  Local Definition inductive_runtime_f (s: state) (t: nat)
    (H: forall (s': state), {halts_within s' t} + {~halts_within s' t}): state -> nat.
    intro s'.
    destruct (H s').
    - apply halts_within_constructible in h.
      destruct h as [f].
      exact (f s').
    - exact (S t).
  Defined.

  Local Lemma inductive_runtime_f_correct:
    forall (s: state) (t: nat)
    (H: forall (s': state), {halts_within s' t} + {~halts_within s' t})
    (H': forall s' : state, step_rel s s' -> halts_within s' t),
    runtime_f s (inductive_runtime_f s t H).
  Proof.
    intros.
    unfold runtime_f.
    intros.
    unfold inductive_runtime_f.
    apply first_step in H0.
    destruct H0, (H s0), (H s'); repeat destruct halts_within_constructible.
    - destruct a, a0.
      unfold runtime_f in H2.
      specialize H2 with s0 s'.
      remember (H2 (stepsRefl s0) H1).

  Admitted.

  Local Lemma halts_within_comp:
    next_steps_exists ->
    forall (s: state) (t t': nat), t < t' -> {halts_within s t} + {~halts_within s t}.
  Proof.
    intros.
    destruct X as [f Hf].
    revert s.
    revert H.
    revert t.
    induction t'; intros.
    - exfalso. inversion H.
    - destruct t'.
      + assert (t = 0) by lia.
        subst.
        destruct (f s) eqn:Hl.
        * left.
          apply runtime_zero_halted.
          unfold halted.
          intros.
          specialize Hf with s s'.
          intro.
          rewrite Hl in Hf.
          destruct Hf.
          apply in_nil in H1; auto.
        * right.
          intro.
          unfold halts_within in H0.
          destruct H0 as [f'].
          destruct H0.
          unfold runtime_f in H0.
          specialize Hf with s s0.
          destruct Hf.
          rewrite Hl in H3.
          remember (H3 (in_eq s0 l)).
          remember (H0 s s0 (stepsRefl s) s1).
          lia.
      + assert (forall (t: nat),
          t < S t' -> forall s: state, {~halts_within s t} + {~~halts_within s t}
        ).
          intros.
          specialize IHt' with t0 s0.
          apply IHt' in H0.
          destruct H0; intuition.
        destruct (Nat.eq_dec t (S t')).
        * subst. clear H.
          assert (t' < S t') by lia.
          remember (Exists_dec (fun s' => ~halts_within s' t') (f s) (X t' H)).
          clear Heqs0 X.
          destruct s0.
          -- right. intro.
             apply Exists_exists in e.
             destruct e.
             destruct H1.
             specialize Hf with s x.
             destruct Hf.
             remember (H4 H1).
             exact (H2 (halts_within_step_monotone s x t' s0 H0)).
          -- left.
             apply <- Forall_Exists_neg in n.
             simpl in n.
             remember (@Forall_forall state (fun x : state => ~ ~ halts_within x t') (f s)).
             destruct i.
             remember (n0 n) as H1.
             clear HeqH1 Heqi f0 n0 n.
             assert (forall s': state, step_rel s s' -> halts_within s' t').
             ++ intros.
                specialize Hf with s s'.
                specialize IHt' with t' s'.
                specialize H1 with s'.
                apply IHt' in H.
                apply Hf in H0.
                apply H1 in H0.
                destruct H; intuition.
             ++ admit.
        * assert (t < S t') by lia.
          exact (IHt' t H0 s).
  Admitted.

  Local Lemma runtime_exists':
    next_steps_exists ->
    forall (t: nat) (initial: state),
    halts_within initial t -> exists (t': nat), runtime initial t'.
  Proof.
    intros.
    induction t.
    - exists 0.
      unfold runtime.
      intuition.
      lia.
    - assert (t < S t) by lia.
      destruct (halts_within_comp X initial t (S t) H0).
      + exact (IHt h).
      + exists (S t).
        unfold runtime.
        intuition.
        assert (t' <= t) by lia.
        exact (n (halts_within_monotone' initial t' t H3 H2)).
  Qed.

  Definition decides (l: language): Prop :=
    forall (w: bitstr), halts' w /\ (accepts w <-> l w).
End Computation.


Section Simulation.
  Definition dm_steps {state: Type} (dm: @decision_model state) := steps (dm_step dm).
  Definition dm_halts {state: Type} (dm: @decision_model state) :=
    halts' (dm_step dm) (dm_enc dm).

  Definition decidable {state: Type} (c: @dm_class state) (l: language) :=
    exists (dm: decision_model), c dm /\
    let (step_rel, accepting_state, encode_input) := dm in
    decides step_rel accepting_state encode_input l.

  Definition simulates {state: Type} (c c': @dm_class state) :=
    forall (l: language), decidable c' l -> decidable c l.

  Definition homomorphism {state state': Type}
    (dm: @decision_model state) (dm': @decision_model state') (f: state -> state') :=
    (forall (w: bitstr), f (dm_enc dm w) = dm_enc dm' w) /\
    (forall (s: state), dm_acc dm s <-> dm_acc dm' (f s)) /\
    (forall (s s': state), dm_steps dm s s' -> dm_steps dm' (f s) (f s')).

  Definition homomorphic {state state': Type}
    (dm: @decision_model state) (dm': @decision_model state') :=
    exists f, homomorphism dm dm' f.

  Lemma homomorphism_halts {state state': Type}
    (dm: @decision_model state) (dm': @decision_model state'):
    homomorphic dm dm' -> forall w, dm_halts dm' w -> dm_halts dm w.
  Proof.
    intros.
    destruct dm as [step acc enc].
    destruct dm' as [step' acc' enc'].
    unfold dm_halts in *.
    unfold homomorphic in H.
    destruct H as [f].
    destruct H.
    destruct H1.
    unfold dm_steps in H2.
    simpl in *.
    unfold halts' in *.
    unfold halts in *.
    destruct H0 as [rf].
    unfold runtime_f in *.
  Qed.

End Simulation.
