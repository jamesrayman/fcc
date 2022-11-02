Require Import Arith List Alphabet.
Import ListNotations.

Section Turing.
  Variable state_count symbol_count: positive.

  Local Definition state := alphabet state_count.
  Local Definition symbol := alphabet symbol_count.

  Local Definition blank := sym_0 symbol_count.

  Inductive direction :=
  | Left
  | Right.

  Definition machine :=
    state -> symbol -> state -> symbol -> direction -> bool.
  Definition tape := list (alphabet symbol_count).

  Definition head (t: tape): symbol :=
    match t with
    | cons s rest => s
    | nil => blank
    end.

  Definition tail (t: tape): tape :=
    match t with
    | cons s rest => rest
    | nil => nil
    end.

  Definition State: Set := state * tape * tape.

  Inductive step: machine -> State -> State -> Prop :=
  | stepLeft: forall (m: machine) (l r l' r': tape) (s s': state),
      m s (head r) s' (head (tail r')) Left = true ->
      l' = tail l ->
      r' = cons (head l) (cons (head (tail r')) (tail r)) ->
      step m (s, l, r) (s', l', r')
  | stepRight: forall (m: machine) (l r l' r': tape) (s s': state),
      m s (head r) s' (head l') Right = true ->
      l' = cons (head l') l ->
      r' = tail r ->
      step m (s, l, r) (s', l', r').
End Turing.
