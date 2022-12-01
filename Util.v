Require Import Arith Function Lia List IMP.
Import ListNotations.


Definition isomorphism {A B: Type} (f: A -> B) (finv: B -> A) :=
  (forall x, finv (f x) = x) /\ (forall x, f (finv x) = x).


Fixpoint str_S (w: bitstr) :=
  match w with
  | nil => cons false nil
  | cons b rest => match b with
                   | false => cons true rest
                   | true => cons false (str_S rest)
                   end
  end.

Fixpoint str_P (w: bitstr): option bitstr :=
  match w with
  | nil => None
  | cons b rest => Some (match b with
                         | true => cons false rest
                         | false => match (str_P rest) with
                                    | None => nil
                                    | Some r => cons true r
                                    end
                         end)
  end.

Lemma str_P_correct: forall w, str_P (str_S w) = Some w.
Proof.
  intros.
  induction w; auto.
  unfold str_S. fold str_S.
  destruct a.
  - unfold str_P. fold str_P.
    rewrite IHw. auto.
  - unfold str_P. fold str_P.
    auto.
Qed.

Fixpoint nat_to_str (n: nat) :=
  match n with
  | 0 => nil
  | S m => str_S (nat_to_str m)
  end.

Lemma nat_to_str_inj (n n': nat): nat_to_str n = nat_to_str n' -> n = n'.
Proof.

Admitted.


Fixpoint str_to_nat' (w: bitstr) :=
  match w with
  | nil => 1
  | cons b rest => (if b then 1 else 0) + 2 * (str_to_nat' rest)
  end.

Definition str_to_nat (w: bitstr) := (str_to_nat' w) - 1.

Lemma nat_to_str'_pos: forall w, str_to_nat' w > 0.
Proof.
  intros.
  induction w; auto.
  unfold str_to_nat'. fold str_to_nat'. lia.
Qed.

Lemma S_nat_to_str': forall w, S (str_to_nat' w) = str_to_nat' (str_S w).
Proof.
  intros.
  induction w; auto.
  destruct a;
  unfold str_S; fold str_S;
  unfold str_to_nat'; fold str_to_nat'.
  - rewrite <- IHw. lia.
  - lia.
Qed.

Lemma S_nat_to_str: forall w, S (str_to_nat w) = str_to_nat (str_S w).
Proof.
  unfold str_to_nat.
  intro.
  rewrite <- S_nat_to_str'.
  remember (nat_to_str'_pos w).
  lia.
Qed.


Lemma nat_str_iso: isomorphism nat_to_str str_to_nat.
Proof.

Admitted.


Fixpoint read_n (w: bitstr): nat * bitstr :=
  match w with
  | nil => (0, nil)
  | false :: w' => (0, w')
  | true :: w' => let (n, w'') := read_n w' in (n+1, w'')
  end.

Definition read_instr (w: bitstr): L_instr * bitstr :=
  match w with
  | false :: false :: false :: false :: w' => (NOP, w')
  | false :: false :: false :: true :: w' =>
      let (rt, w'') := read_n w' in let (n, w''') := read_n w'' in (LDI rt n, w''')
  | false :: false :: true :: false :: w' =>
      let (rt, w'') := read_n w' in let (ra, w''') := read_n w'' in
      let (rb, w'''') := read_n w''' in (ADD rt ra rb, w'''')
  | false :: false :: true :: true :: w' =>
      let (rt, w'') := read_n w' in let (ra, w''') := read_n w'' in
      let (rb, w'''') := read_n w''' in (SUB rt ra rb, w'''')
  | false :: true :: true :: true :: w' =>
      let (rt, w'') := read_n w' in let (ra, w''') := read_n w'' in
      let (rb, w'''') := read_n w''' in (MUL rt ra rb, w'''')
  | false :: true :: true :: false :: w' =>
      let (rt, w'') := read_n w' in let (ra, w''') := read_n w'' in
      let (rb, w'''') := read_n w''' in (DIV rt ra rb, w'''')
  | false :: true :: false :: false :: w' =>
      let (rt, w'') := read_n w' in let (ra, w''') := read_n w'' in
      let (rb, w'''') := read_n w''' in (MOD rt ra rb, w'''')
  | false :: true :: false :: true :: w' =>
      let (rt, w'') := read_n w' in let (ra, w''') := read_n w'' in
      let (rb, w'''') := read_n w''' in (EQ rt ra rb, w'''')
  | true :: false :: true :: false :: w' =>
      let (i, w'') := read_n w' in let (rc, w''') := read_n w'' in (JFNE i rc, w''')
  | true :: false :: false :: false :: w' =>
      let (i, w'') := read_n w' in let (rc, w''') := read_n w'' in (JBNE i rc, w''')
  | true :: true :: false :: false :: w' =>
      let (rt, w'') := read_n w' in (RET rt, w'')
  | _ => (NOP, nil)
  end.

Fixpoint str_to_limp (w: bitstr) (n: nat): L_prog :=
  match n with
  | 0 => nil
  | S m => match read_instr w with
           | (instr, nil) => [instr]
           | (instr, w') => instr :: str_to_limp w' m
           end
  end.

Definition nat_to_limp (n: nat) := str_to_limp (nat_to_str n) (length (nat_to_str n)).

Lemma nat_to_limp_onto: forall p, exists n, p = nat_to_limp n.
Proof.
Admitted.
