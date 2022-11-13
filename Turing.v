Require Import Arith List Alphabet.
Import ListNotations.

Section Turing.
  Context {state_count symbol_count: positive}.

  Local Definition state := alphabet state_count.
  Local Definition symbol := alphabet symbol_count.

  Local Definition blank := sym_0 symbol_count.

  Inductive direction :=
  | Left
  | Right.

  Definition turing_machine (stc symc: positive) :=
    alphabet stc -> alphabet symc -> alphabet stc -> alphabet symc -> direction -> bool.
  Local Definition machine := turing_machine state_count symbol_count.
  Definition tape := str symbol_count.

  Definition head (t: tape): symbol := hd blank t.

  Definition tail (t: tape): tape := tl t.

  Definition State: Set := state * tape * tape.

  Definition go_left (s: State) (sym: symbol) :=
    let (st'l, r) := s in let (st, l) := st'l in
    (st, tail l, cons (head r) (cons sym (tail r))).

  Definition go_right (s: State) (sym: symbol) :=
    let (st'l, r) := s in let (st, l) := st'l in
    (st, cons sym l, tail r).

  Lemma go_left_sym: forall (s: State) (sym: symbol) (s': state) (l r: tape),
    go_left s sym = (s', l, r) -> sym = head (tail r).
  Proof.
    intros.
    unfold go_left in H.
    destruct s in H.
    destruct p in H.
    inversion H. subst. auto.
  Qed.

  Lemma go_left_state: forall (sym: symbol) (s s': state) (l r l' r': tape),
    go_left (s, l, r) sym = (s', l', r') -> s = s'.
  Proof.
    intros.
    unfold go_left in H.
    inversion H. subst. auto.
  Qed.

  Lemma go_right_sym: forall (s: State) (sym: symbol) (s': state) (l r: tape),
    go_right s sym = (s', l, r) -> sym = head l.
  Proof.
    intros.
    unfold go_right in H.
    destruct s in H.
    destruct p in H.
    inversion H. subst. auto.
  Qed.

  Lemma go_right_state: forall (sym: symbol) (s s': state) (l r l' r': tape),
    go_right (s, l, r) sym = (s', l', r') -> s = s'.
  Proof.
    intros.
    unfold go_left in H.
    inversion H. subst. auto.
  Qed.

  Definition go_d (d: direction) :=
    match d with
    | Left => go_left
    | Right => go_right
    end.

  Inductive step: machine -> State -> State -> Prop :=
  | stepCons: forall (m: machine) (l r: tape) (s s': state) (sym': symbol) (d: direction),
      m s (head r) s' sym' d = true ->
      step m (s, l, r) (go_d d (s', l, r) sym').
End Turing.
