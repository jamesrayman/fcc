Require Import Arith List Alphabet.

Section Language.
  Local Lemma two_gte_one: 2 >= 1. Proof. auto. Qed.
  Definition bitstr := str (nat_to_atl 1 2 two_gte_one).
  Definition language := bitstr -> Prop.

  Axiom lang_extensionality: forall (l m: language),
    l = m <-> forall (w: bitstr), l w <-> m w.
End Language.
