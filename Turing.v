Require Import Arith List Alphabet Language.
Import ListNotations.

Section Turing.
  Context {state_count symbol_count: positive}.

  Local Definition state := alphabet state_count.
  Local Definition symbol := alphabet symbol_count.

  Local Definition initial := sym_0 state_count.
  Local Definition blank := sym_0 symbol_count.
  Local Definition marked := sym_1 symbol_count.

  Inductive direction :=
  | Left
  | Right.

  Definition turing_machine (stc symc: positive) :=
    alphabet stc -> alphabet symc -> (alphabet stc * alphabet symc * direction) + bool.
  Local Definition machine := turing_machine state_count symbol_count.
  Definition tape := str symbol_count.
  Variable tm: machine.

  Definition head (t: tape): symbol := hd blank t.

  Definition tail (t: tape): tape := tl t.

  Record State := { st_st: state; st_l: tape; st_r: tape }.

  Definition st_sym (s: State) :=
    let (_, _, r) := s in head r.

  Definition go_left (s: State) (st: state) (sym: symbol) :=
    let (_, l, r) := s in
    Build_State st (tail l) (cons (head r) (cons sym (tail r))).

  Definition go_right (s: State) (st: state) (sym: symbol) :=
    let (_, l, r) := s in
    Build_State st (cons sym l) (tail r).

  Definition go_dir (s: State) (st: state) (sym: symbol) (d: direction) :=
    match d with
    | Left => go_left s st sym
    | Right => go_right s st sym
    end.

  Definition tm_next (s: State): State + bool :=
    match tm (st_st s) (st_sym s) with
    | inl (st, sym, d) => inl (go_dir s st sym d)
    | inr b => inr b
    end.

  Fixpoint tm_enc' (w: bitstr) :=
    match w with
    | nil => nil
    | cons b l => cons marked (cons (if b then marked else blank) (tm_enc' l))
    end.

  Definition tm_enc (w: bitstr): State :=
    {| st_st := initial; st_l := nil; st_r := tm_enc' w |}.
End Turing.
