Require Import List Arith Alphabet Language Lia.

Definition transition (state: Type) := state -> state + nat.

Section Computation.
  Context {state: Type}.
  Variable next: transition state.
  Variable encode_input: nat -> state.

  Record decision_model :=
    { dm_next: transition state; dm_enc: nat -> state }.
  Definition dm_class := decision_model -> Prop.

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
    forall (s s': state) (n: nat), steps s s' -> (decision s b <-> decision s' b).
  Proof.
    intros.
    induction H.
    - intuition.
    - rewrite IHsteps. clear IHsteps H s.
      split; intro.
      + inversion H; subst; rewrite H0 in H1.
        * discriminate.
        * inversion H1. auto.
      + apply decisionStep with (s' := s''); auto.
  Qed.

  Lemma steps_halts:
    forall (s s': state), steps s s' -> (halts s <-> halts s').
  Proof.
    intros.
    split; intro.
    - destruct H0.
      + apply (steps_decision s s' true H) in H0. unfold halts. auto.
      + apply (steps_decision s s' false H) in H0. unfold halts. auto.
    - destruct H0.
      + apply (steps_decision s s' true H) in H0. unfold halts. auto.
      + apply (steps_decision s s' false H) in H0. unfold halts. auto.
  Qed.

  Lemma decision_unique: forall (s: state), ~(decision s true /\ decision s false).
  Proof.
    intros. intro.
    destruct H.
    assert (halts' s).
    - apply halts_iff_halts'. unfold halts. auto.
    - destruct H1.
      induction H1.
      + unfold halted in H1.
        destruct H1.
        * inversion H0; subst; rewrite H1 in H2; discriminate.
        * inversion H; subst; rewrite H1 in H2; discriminate.
      + inversion H; inversion H0; subst.
        * rewrite H3 in H6. discriminate.
        * rewrite H3 in H6. discriminate.
        * rewrite H3 in H7. discriminate.
        * rewrite H3 in H7. inversion H7. rewrite H1 in H3. inversion H3. subst.
          apply IHruntime; auto.
  Qed.

  Definition decides (l: language) :=
    forall (w: bitstr), halts (encode_input w) /\ (decision (encode_input w) true <-> l w).

  Lemma language_unique: forall (l l': language), decides l -> decides l' -> l = l'.
  Proof.
    intros.
    apply lang_extensionality.
    intro. split; intro; unfold decides in *;
    specialize H with w; specialize H0 with w; destruct H, H0; intuition.
  Qed.

  Fixpoint simulate (s: state) (n: nat): option bool :=
    match n with
    | 0 => None
    | S m => match next s with
             | inl s' => simulate s' m
             | inr b => Some b
             end
    end.

  (* simulate correct *)
End Computation.

Section Simulation.
  Definition dm_steps
    {state: Type} (dm: @decision_model state) := steps (dm_next dm).
  Definition dm_halts
    {state: Type} (dm: @decision_model state) := halts (dm_next dm).
  Definition dm_halted
    {state: Type} (dm: @decision_model state) := halted (dm_next dm).
  Definition dm_decision
    {state: Type} (dm: @decision_model state) := decision (dm_next dm).
  Definition dm_decides
    {state: Type} (dm: @decision_model state) := decides (dm_next dm) (dm_enc dm).

  Definition homomorphism
    {state state': Type} (dm: @decision_model state) (dm': @decision_model state')
    (h: state -> state') :=
    (forall (w: bitstr), h (dm_enc dm w) = dm_enc dm' w) /\
    (forall (s s': state), dm_steps dm s s' -> dm_steps dm' (h s) (h s')) /\
    (forall (s: state), dm_halted dm s -> dm_halted dm' (h s)) /\
    (forall (s: state) (b: bool), dm_next dm s = inr b -> dm_next dm' (h s) = inr b).

  Local Lemma homomorphism_decision
    {state state': Type} (dm: @decision_model state) (dm': @decision_model state')
    (h: state -> state') (s: state) (b: bool):
    homomorphism dm dm' h -> dm_decision dm s b -> dm_decision dm' (h s) b.
  Proof.
    intros.
    destruct dm as [next enc].
    destruct dm' as [next' enc'].
    unfold homomorphism in H.
    destruct H. destruct H1. destruct H2.
    unfold dm_decision in *.
    unfold dm_halted in *.
    unfold dm_steps in *.
    simpl in *.
    induction H0.
    - apply H3 in H0.
      repeat econstructor. auto.
    - assert (steps next s s').
      + repeat econstructor. auto.
      + apply H1 in H5.
        rewrite (steps_decision next' (h s) (h s') b H5).
        auto.
  Qed.

  Lemma homomorphism_decides
    {state state': Type} (dm: @decision_model state) (dm': @decision_model state')
    (h: state -> state') (l: language):
    homomorphism dm dm' h -> dm_decides dm l -> dm_decides dm' l.
  Proof.
    intros.
    destruct dm as [next enc].
    destruct dm' as [next' enc'].
    unfold dm_decides in *.
    remember H as He. clear HeqHe.
    destruct He as [Henc H']. clear H'.
    simpl in *.
    intro.
    specialize Henc with w.
    split.
    - unfold decides in H0.
      specialize H0 with w.
      destruct H0.
      unfold halts in *.
      destruct H0.
      + left.
        remember H as He. clear HeqHe.
        apply homomorphism_decision with (s := enc w) (b := true) in H; auto.
        unfold dm_decision in H. simpl in H.
        rewrite <- Henc.
        auto.
      + right.
        apply homomorphism_decision with (s := enc w) (b := false) in H; auto.
        unfold dm_decision in H. simpl in H.
        rewrite <- Henc.
        auto.
    - unfold decides in H0.
      specialize H0 with w.
      destruct H0.
      rewrite <- H1. clear H1.
      split.
      + intro.
        destruct H0; auto.
        apply homomorphism_decision with (s := enc w) (b := false) in H.
        unfold dm_decision in H; simpl in H; intros.
        * rewrite Henc in H.
          exfalso.
          apply (decision_unique next' (enc' w)).
          intuition.
        * unfold dm_decision. simpl. auto.
      + intro.
        apply homomorphism_decision with (s := enc w) (b := true) in H;
        unfold dm_decision in H; simpl in H; intros.
        * rewrite <- Henc. auto.
        * unfold dm_decision. simpl.
          destruct H0 eqn: Ha; auto.
  Qed.

  Lemma homomorphism_compose
    {state state' state'': Type}
    (dm: @decision_model state) (dm': @decision_model state') (dm'': @decision_model state'')
    (h: state -> state') (h': state' -> state''):
    homomorphism dm dm' h -> homomorphism dm' dm'' h' ->
    homomorphism dm dm'' (fun x => h' (h x)).
  Proof.
    intros.
    destruct dm as [next enc].
    destruct dm' as [next' enc'].
    destruct dm'' as [next'' enc''].
    unfold homomorphism in *.
    destruct H. destruct H1. destruct H2.
    destruct H0. destruct H4. destruct H5.
    unfold dm_decision in *.
    unfold dm_halted in *.
    unfold dm_steps in *.
    simpl in *.
    split; try split; try split; intros.
    - rewrite <- H0. rewrite <- H. auto.
    - apply H4. apply H1. auto.
    - apply H5. apply H2. auto.
    - apply H6. apply H3. auto.
  Qed.

  (*
     Lemma homomorphism identity
     Definition class_subset
     Lemma subset_refl
     Lemma subset_transitive
     Lemma subset_subset
   *)

End Simulation.
