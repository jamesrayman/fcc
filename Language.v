Require Import Arith List Alphabet.

Section Language.
  Lemma two_gt_one: 2 >= 1. Proof. auto. Qed.
  Definition binstr := list (alphabet (@nat_to_atl 1 2 two_gt_one)).
  Definition language := binstr -> Prop.
End Language.
