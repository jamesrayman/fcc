Require Import Turing Run Alphabet Language.

(*
  Symbols: blank 0 1 cursor
  Statements:
     Left
     Right
     While
     End
     Toggle
     EOF
 *)

Section UniversalTM.
  Print decision.

  Definition tm_universal {state_count symbol_count: positive}
    (m: machine state_count symbol_count) :=
    forall (state_count' symbol_count': positive) (m': machine state_count' symbol_count')
    (str: binstr) (b: bool), 
End UniversalTM.
