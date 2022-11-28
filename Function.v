Require Import Arith List Alphabet.

Section Function.
  Definition bitstr := list bool.
  Definition language := bitstr -> Prop.
  Definition function := nat -> nat.

  Axiom lang_extensionality: forall (l l': language),
    l = l' <-> forall (w: bitstr), l w <-> l' w.

  Axiom func_extensionality: forall (f f': function),
    f = f' <-> forall (n: nat), f n = f' n.
End Function.
