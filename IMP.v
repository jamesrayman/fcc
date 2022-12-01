Require Import Arith List Function Computation.
Import ListNotations.

Definition reg_map := nat -> nat.
Definition empty_reg_map (n: nat) := 0.
Definition upd_reg_map (m: reg_map) (i x j: nat) :=
  if Nat.eq_dec i j then x else m j.


Inductive L_instr :=
  | NOP
  | LDI (rt n: nat)
  | ADD (rt ra rb: nat)
  | SUB (rt ra rb: nat)
  | MUL (rt ra rb: nat)
  | DIV (rt ra rb: nat)
  | MOD (rt ra rb: nat)
  | EQ (rt ra rb: nat)
  | JFNE (i rc: nat)
  | JBNE (i rc: nat)
  | RET (ra: nat)
.

Definition L_prog := list L_instr.

Record L_state := { l_ip: nat; l_mem: reg_map }.
Definition L_initial := Build_L_state 0 empty_reg_map.
Definition L_input_initial (x: nat) := Build_L_state 0 (upd_reg_map empty_reg_map 0 x).

Definition eq (n m: nat) :=
  if Nat.eq_dec n m then 1 else 0.

Definition L_next' (instr: L_instr) (st: L_state): L_state + nat :=
  let (ip, mem) := st in
  match instr with
  | NOP => inl (Build_L_state (ip+1) mem)
  | LDI rt n => inl (Build_L_state (ip+1) (upd_reg_map mem rt n))
  | ADD rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra + mem rb)))
  | SUB rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra - mem rb)))
  | MUL rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra * mem rb)))
  | DIV rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra / mem rb)))
  | MOD rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra mod mem rb)))
  | EQ rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (eq (mem ra) (mem rb))))
  | JFNE i rc =>
      inl (Build_L_state (if mem rc then ip+i else ip+1) mem)
  | JBNE i rc =>
      inl (Build_L_state (if mem rc then ip-i else ip+1) mem)
  | RET ra => inr (mem ra)
  end.

Definition L_next (p: L_prog) (st: L_state): L_state + nat :=
  let (ip, mem) := st in L_next' (nth ip p (RET 0)) st.

Inductive C_instr (P: function -> Prop) :=
  | LINSTR (instr: L_instr)
  | CALL (f: function) (prf: P f) (rt ra: nat)
.

Definition C_prog (P: function -> Prop) := list (C_instr P).

Definition C_next { P: function -> Prop } (p: C_prog P) (st: L_state): L_state + nat :=
  let (ip, mem) := st in
  match nth ip p (LINSTR P (RET 0)) with
  | LINSTR _ instr => L_next' instr st
  | CALL _ f prf rt ra => inl (Build_L_state (ip+1) (upd_reg_map mem rt (f (mem ra))))
  end.

Definition L_eval (p: L_prog) (n n': nat) :=
  eval (L_next p) (L_input_initial n) n'.

Definition turing_computable (f: function) :=
  exists p: L_prog, evaluates (L_next p) L_input_initial f.

Definition L_always_halts (p: L_prog) := always_halts (L_next p) L_input_initial.

Lemma computable_oracles_computable:
  forall (f: function) (p: C_prog turing_computable),
    evaluates (C_next p) L_input_initial f -> turing_computable f.
Proof.
Admitted.

