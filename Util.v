Require Import Arith Language Lia.


Definition isomorphism {A B: Type} (f: A -> B) (finv: B -> A) :=
  (forall x, finv (f x) = x) /\ (forall x, f (finv x) = x).
