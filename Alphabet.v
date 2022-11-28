Require Import Arith List Lia.
Import ListNotations.

Section Alphabet.
  Record at_least (n: nat) := { atl_i :> nat; atl_prf: atl_i >= n }.
  Definition positive := at_least 1.

  Definition atl_to_nat {n: nat} (m: at_least n): nat.
    destruct m.
    exact atl_i0.
  Defined.

  Axiom atl_extensionality: forall (n: nat) (a b: at_least n),
    a = b <-> atl_to_nat a = atl_to_nat b.

  Definition nat_to_atl (n m: nat) (prf: m >= n): at_least n :=
    {| atl_i := m; atl_prf := prf |}.

  Lemma pos_gt_zero (n: positive): 0 < atl_to_nat n.
  Proof.
    unfold positive in n.
    destruct n.
    unfold atl_to_nat.
    auto.
  Qed.

  Record alphabet (n: positive) := { sym_i :> nat; sym_prf: sym_i < atl_to_nat n }.

  Definition nat_to_sym (m: positive) (n: nat) (prf: n < atl_to_nat m): alphabet m :=
    {| sym_i := n; sym_prf := prf |}.

  Definition sym_to_nat {n: positive} (a: alphabet n): nat.
    destruct a.
    exact sym_i0.
  Defined.

  Axiom sym_extensionality: forall (n: positive) (a b: alphabet n),
    a = b <-> sym_to_nat a = sym_to_nat b.

  Definition str (n: positive) := list (alphabet n).

  Definition sym_0 (n: positive) := nat_to_sym n 0 (pos_gt_zero n).

  Lemma sym_dec (m: positive) (n: nat): {n < atl_to_nat m} + {n >= atl_to_nat m}.
  Proof.
    destruct (n ?= atl_to_nat m) eqn:H.
    - right. apply Nat.compare_eq_iff in H. lia.
    - left. apply Nat.compare_lt_iff in H. lia.
    - right. apply Nat.compare_gt_iff in H. lia.
  Qed.

  Definition sym_1 (n: positive): alphabet n.
    destruct (sym_dec n 1).
    - exact (nat_to_sym n 1 l).
    - exact (sym_0 n).
  Defined.

  Definition is_sym_0 {n: positive} (a: alphabet n): bool.
    destruct (Nat.eq_dec 0 (sym_to_nat a)).
    - exact true.
    - exact false.
  Defined.

  Fixpoint iota (n: nat): list nat :=
    match n with
    | 0 => nil
    | S m => (iota m) ++ [m]
    end.

  Lemma nat_in_iota: forall (n m: nat), In m (iota n) <-> m < n.
  Proof.
    split; revert m; induction n; intros.
    - simpl in H. contradiction.
    - unfold iota in H.
      fold iota in H.
      destruct (Nat.eq_dec m n).
      + lia.
      + apply in_app_or in H. destruct H; intuition.
        simpl in H. intuition.
        symmetry in H0.
        apply n0 in H0.
        contradiction.
    - lia.
    - unfold iota.
      fold iota.
      destruct (Nat.eq_dec m n); apply in_or_app.
      + right. simpl. auto.
      + left. apply IHn. lia.
  Qed.

  Lemma length_iota: forall (n: nat), length (iota n) = n.
  Proof.
    induction n; intuition.
    unfold iota.
    fold iota.
    rewrite List.app_length.
    rewrite IHn.
    simpl. lia.
  Qed.

  Definition all_syms (n: positive): list (alphabet n).
    apply map with (A := nat).
    - intro k.
      destruct (sym_dec n k).
      + exact (nat_to_sym n k l).
      + exact (sym_0 n).
    - exact (iota (atl_to_nat n)).
  Defined.

  Lemma length_all_syms: forall (n: positive), length (all_syms n) = atl_to_nat n.
  Proof.
    destruct n. unfold all_syms. simpl.
    rewrite List.map_length.
    rewrite length_iota. auto.
  Qed.

  Lemma all_syms_correct (n: positive) (sym: alphabet n): In sym (all_syms n).
  Proof.
    destruct sym eqn:H. rewrite <- H.
    unfold all_syms.
    apply in_map_iff.
    exists sym_i0.
    split.
    - destruct (sym_dec n sym_i0).
      + apply sym_extensionality.
        rewrite H.
        simpl. auto.
      + lia.
    - apply nat_in_iota. auto.
  Qed.
End Alphabet.
