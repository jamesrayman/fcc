Require Import List Arith Alphabet Function Lia.

Definition transition (state: Type) := state -> state + nat.

Section Computation.
  Context {state: Type}.
  Variable next: transition state.
  Variable encode_input: nat -> state.

  Inductive steps: state -> state -> Prop :=
  | stepsRefl: forall (s: state), steps s s
  | stepsOnce: forall (s s' s'': state),
      steps s s' -> next s' = inl s'' -> steps s s''.

  Definition halted (s: state) := exists n, next s = inr n.

  Inductive eval: state -> nat -> Prop :=
  | evalHalted: forall (s: state) (n: nat), next s = inr n -> eval s n
  | evalStep:
      forall (s s': state) (n: nat), next s = inl s' -> eval s' n -> eval s n.

  Inductive runtime: state -> nat -> Prop :=
  | runtimeHalted: forall (s: state), halted s -> runtime s 0
  | runtimeStep: forall (s s': state) (n: nat), next s = inl s' -> runtime s' n -> runtime s (S n).

  Definition halts (s: state) := exists n, eval s n.
  Definition halts' (s: state) := exists n, runtime s n.

  Lemma halts_iff_halts': forall (s: state), halts s <-> halts' s.
  Proof.
    intros.
    split; intros.
    - destruct H.
      induction H.
      + unfold halts'. exists 0. constructor. unfold halted. exists n. auto.
      + unfold halts' in *. destruct IHeval.
        exists (S x). econstructor; eauto.
    - destruct H.
      induction H.
      + destruct H. exists x. econstructor; eauto.
      + destruct IHruntime. exists x. eapply evalStep; eauto.
  Qed.

  Lemma steps_eval:
    forall (s s': state) (n: nat), steps s s' -> (eval s n <-> eval s' n).
  Proof.
    clear encode_input.
    intros.
    induction H.
    - intuition.
    - rewrite IHsteps. clear IHsteps H s.
      split; intro.
      + inversion H; subst; rewrite H0 in H1.
        * discriminate.
        * inversion H1. auto.
      + apply evalStep with (s' := s''); auto.
  Qed.

  Lemma steps_halts:
    forall (s s': state), steps s s' -> (halts s <-> halts s').
  Proof.
    intros.
    split; intro; destruct H0;
      apply (steps_eval s s' x H) in H0; unfold halts; eauto.
  Qed.

  Lemma eval_unique: forall (s: state) (n n': nat),
    eval s n -> eval s n' -> n = n'.
  Proof.
    intros.
    assert (halts s).
    - exists n. auto.
    - rewrite halts_iff_halts' in H1.
      destruct H1.
      induction H1.
      + destruct H1.
        inversion H; inversion H0; subst.
        * rewrite H2 in H5. inversion H5. auto.
        * rewrite H2 in H5. discriminate.
        * rewrite H2 in H6. discriminate.
        * rewrite H2 in H1. discriminate.
      + apply IHruntime; inversion H; inversion H0; subst.
        * rewrite H1 in H3. discriminate.
        * rewrite H6 in H3. discriminate.
        * rewrite H3 in H7. discriminate.
        * rewrite H1 in H3. inversion H3. subst. auto.
        * rewrite H1 in H3. discriminate.
        * rewrite H6 in H3. discriminate.
        * rewrite H3 in H7. discriminate.
        * rewrite H1 in H7. inversion H7. subst. auto.
  Qed.

  Definition evaluates (f: function) :=
    forall (n: nat), eval (encode_input n) (f n).

  Definition always_halts :=
    exists f, evaluates f.

  Lemma evaluation_unique: forall (f f': function), evaluates f -> evaluates f' -> f = f'.
  Proof.
    intros.
    apply func_extensionality.
    intro.
    unfold evaluates in *.
    specialize H with n.
    specialize H0 with n.
    apply eval_unique with (s := encode_input n); auto.
  Qed.

  Fixpoint simulate (s: state) (n: nat): option nat :=
    match n with
    | 0 => None
    | S m => match next s with
             | inl s' => simulate s' m
             | inr x => Some x
             end
    end.

End Computation.

Lemma lockstep' (A B: Type)
  (next_A: transition A) (next_B: transition B) (sim: A -> B):
  forall t initial n', runtime next_A initial t ->
  (forall a a', next_A a = inl a' -> steps next_B (sim a) (sim a')) ->
  (forall a x, next_A a = inr x -> next_B (sim a) = inr x) ->
  eval next_A initial n' -> eval next_B (sim initial) n'.
Proof.
  induction t.
  - intros.
    inversion H. subst.
    destruct H3.
    inversion H2; subst.
    + constructor. apply H1. auto.
    + rewrite H4 in H3. inversion H3.
  - intros.
    inversion H. subst.
    remember (H0 initial s' H4) as Hs.
    remember (steps_eval next_B (sim initial) (sim s') n' Hs) as Hs'.
    apply Hs'.
    apply IHt; auto.
    assert (steps next_A initial s').
    + apply stepsOnce with (s' := initial); auto.
      constructor.
    + remember (steps_eval next_A initial s' n' H3).
      apply i.
      auto.
Qed.

Theorem lockstep (A B: Type) (f: function)
  (next_A: transition A) (next_B: transition B)
  (enc_A: nat -> A) (enc_B: nat -> B) (sim: A -> B):
  (forall n, sim (enc_A n) = enc_B n) ->
  (forall a a', next_A a = inl a' -> steps next_B (sim a) (sim a')) ->
  (forall a x, next_A a = inr x -> next_B (sim a) = inr x) ->
  evaluates next_A enc_A f ->  evaluates next_B enc_B f.
Proof.
  unfold evaluates.
  intros.
  rewrite <- H.
  specialize H2 with n.
  assert (halts' next_A (enc_A n)).
  - apply halts_iff_halts'.
    exists (f n). auto.
  - destruct H3 as [t].
    apply lockstep' with (next_A := next_A) (t := t); auto.
Qed.
