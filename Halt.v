Require Import Arith Function Computation Lia List IMP Util.

Print halts.


Definition HALT_0 (f: function) :=
  forall n, f n < 2 /\
  (f n = 1 <-> halts (L_next (nat_to_limp n)) L_initial).


Definition HALT_ALL (f: function) :=
  forall n, f n < 2 /\
  (f n = 1 <-> forall m, halts (L_next (nat_to_limp n)) (L_input_initial m)).
