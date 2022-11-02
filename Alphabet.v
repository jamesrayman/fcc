Require Import Arith List.
Import ListNotations.

Section Alphabet.
  Record at_least (n: nat) := { atl_i :> nat; atl_prf: atl_i >= n }.
  Definition positive := at_least 1.

  Definition atl_to_nat {n: nat} (m: at_least n): nat.
    destruct m.
    exact atl_i0.
  Defined.

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

  Definition sym_0 (n: positive) := nat_to_sym n 0 (pos_gt_zero n).

  Local Fixpoint all_syms' (n: positive) (i: nat) (prf: i < atl_to_nat n): list (alphabet n).
    destruct i.
    - exact (cons (nat_to_sym n 0 prf) nil).
    - remember (nat_to_sym n (S i) prf) as m.
      assert (prf' := prf).
      apply Nat.lt_succ_l in prf'.
      specialize all_syms' with n i.
      exact (all_syms' prf' ++ [m]).
  Defined.

  Definition all_syms (n: positive): list (alphabet n).
    remember (Nat.lt_pred_l (atl_to_nat n)) as H.
    remember (Nat.lt_neq 0 (atl_to_nat n) (pos_gt_zero n)) as Hn.
    clear HeqHn.
    apply Nat.neq_sym in Hn.
    apply H in Hn.
    exact (all_syms' n (Nat.pred (atl_to_nat n)) Hn).
  Defined.

  Lemma five_gt_one: 5 >= 1. Proof. auto 10. Qed.

  Theorem sym_in_all_syms: forall (n: positive) (a: alphabet n), .
  Proof.
  Qed.

End Alphabet.
