Require Import Arith List Alphabet.

Section Language.
  Local Lemma two_gte_one: 2 >= 1. Proof. auto. Qed.
  Definition binstr := list (alphabet (nat_to_atl 1 2 two_gte_one)).
  Definition language := binstr -> Prop.
End Language.
