Require Import Arith.

Section Alphabet.
  Definition at_least (n: nat) := { i: nat | i >= n }.
  Definition positive := at_least 1.

  Definition atl_to_nat {n: nat} (m: at_least n): nat.
    destruct m.
    exact x.
  Defined.

  Definition nat_to_atl (n m: nat) {prf: m >= n}: at_least n.
    exact (exist _ m prf).
  Defined.

  Lemma pos_gt_zero (n: positive): 0 < atl_to_nat n.
  Proof.
    simpl in *.
    unfold positive in n.
    unfold at_least in n.
    destruct n.
    simpl.
    auto.
  Qed.

  Definition alphabet (n: positive) := { i: nat | i < atl_to_nat n }.

  Definition nat_to_alph (m: positive) (n: nat) (prf: n < atl_to_nat m): alphabet m.
    exact (exist _ n prf).
  Defined.

  Definition alph_to_nat {m: positive} (n: alphabet m): nat.
    destruct n.
    exact x.
  Defined.
End Alphabet.
