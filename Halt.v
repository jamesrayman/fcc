Require Import Arith Function Computation Lia List IMP Util.

Definition HALT_0 (f: function) :=
  forall n, f n < 2 /\
  (f n = 1 <-> halts (L_next (nat_to_limp n)) L_initial).


Definition HALT_ALL (f: function) :=
  forall n, f n < 2 /\
  (f n = 1 <-> forall m, halts (L_next (nat_to_limp n)) (L_input_initial m)).

Definition ENUM_C (f: function) :=
  (forall n, L_always_halts (nat_to_limp (f n))) /\
  (forall p: L_prog, L_always_halts p -> exists n, nat_to_limp (f n) = p).

Definition SIM_DIAG (f: function) :=
  forall n, L_eval (nat_to_limp n) n (f n).

Lemma sim_diag_computable:
  forall f, HALT_0 f -> turing_computable f ->
  exists g, turing_computable g /\ SIM_DIAG g.
Proof.
Admitted.

Lemma halt_halt_all:
  forall f, HALT_0 f -> turing_computable f ->
  exists g, turing_computable g /\ HALT_ALL g.
Proof.
Admitted.

Lemma halt_all_enumerate_computable:
  forall f, HALT_ALL f -> turing_computable f ->
  exists g, turing_computable g /\ ENUM_C g.
Proof.
Admitted.

Lemma composition_computable (f g: function):
  turing_computable f ->
  turing_computable g ->
  turing_computable (fun n => f (g n)).
Proof.
Admitted.

Lemma S_computable:
  turing_computable S.
Proof.
Admitted.

Theorem halt_undecidable:
  forall f, HALT_0 f -> ~turing_computable f.
Proof.
  intros. intro.
  remember (halt_halt_all f H H0) as Hg. clear HeqHg.
  destruct Hg as [g Hg].
  destruct Hg.

  remember (sim_diag_computable f H H0) as Hsim. clear HeqHsim.
  destruct Hsim as [sim Hsim].
  destruct Hsim as [Hsim Hsim'].
  clear f H H0.

  remember (halt_all_enumerate_computable g H2 H1) as Hh. clear HeqHh.
  destruct Hh as [h Hh].
  destruct Hh.
  clear g H1 H2.
  unfold ENUM_C in H0.
  destruct H0.

  remember (composition_computable S sim S_computable Hsim) as HG. clear HeqHG.
  destruct HG as [G HG].
  destruct (nat_to_limp_onto G) as [Gn].
  unfold evaluates in HG.
  specialize HG with Gn.
  unfold SIM_DIAG in Hsim'.
  specialize Hsim' with Gn.
  unfold L_eval in Hsim'.
  rewrite <- H2 in Hsim'.
  remember (eval_unique (L_next G) (L_input_initial Gn) (sim Gn) (S (sim Gn)) Hsim' HG).
  lia.
Qed.

Print Assumptions halt_undecidable.
