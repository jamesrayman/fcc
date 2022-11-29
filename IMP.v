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
  | JNE (i rc: nat)
  | JRNE (i rc: nat)
  | JBNE (i rc: nat)
  | RET (ra: nat)
.

Definition L_prog := list L_instr.

Record L_state := { l_ip: nat; l_mem: reg_map }.
Definition L_initial := Build_L_state 0 empty_reg_map.
Definition L_input_initial (x: nat) := Build_L_state 0 (upd_reg_map empty_reg_map 0 x).

Definition eq (n m: nat) :=
  if Nat.eq_dec n m then 1 else 0.

Definition L_next (p: L_prog) (st: L_state): L_state + nat :=
  let (ip, mem) := st in
  match nth ip p (RET 0) with
  | NOP => inl (Build_L_state (ip+1) mem)
  | LDI rt n => inl (Build_L_state (ip+1) (upd_reg_map mem rt n))
  | ADD rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra + mem rb)))
  | SUB rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra - mem rb)))
  | MUL rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra * mem rb)))
  | DIV rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra / mem rb)))
  | MOD rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (mem ra mod mem rb)))
  | EQ rt ra rb => inl (Build_L_state (ip+1) (upd_reg_map mem rt (eq (mem ra) (mem rb))))
  | JNE i rc =>
      inl (Build_L_state (if mem rc then i else ip+1) mem)
  | JRNE i rc =>
      inl (Build_L_state (if mem rc then ip+i else ip+1) mem)
  | JBNE i rc =>
      inl (Build_L_state (if mem rc then ip-i else ip+1) mem)
  | RET ra => inr (mem ra)
  end.



