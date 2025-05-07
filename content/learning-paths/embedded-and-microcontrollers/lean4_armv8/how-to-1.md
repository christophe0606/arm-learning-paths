---
title: Lean4 theorem prover and Arm v8 code
weight: 2

### FIXED, DO NOT MODIFY
layout: learningpathall
---

## Introduction 
YOUR CONTENT GOES HERE

```bash
name () {
  commands
}
```


```leanlike
axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

def add {n : Nat} (x _ : Int) : Vec n Int := <1,2>
```

```leanlike
import Arm.Exec
import Arm.Util
import Arm.Syntax
import Arm.Memory.SeparateAutomation
import Arm.BitVec
import Tactics.Sym
import Tactics.Aggregate
import Tactics.StepThms
import Std.Tactic.BVDecide


import TestLeanArm.Myprog
open Myprog

section mytest

open ArmState
open BitVec
open Int
open Nat

def N : Nat := 4

def get_bit (x : BitVec 32) (n : Nat)  : BitVec 32 :=
   (BitVec.ofBool (getLsbD x n)).zeroExtend 32

def parity_rec (n : Nat) (x : BitVec 32) : BitVec 32 :=
 match n with
  | 0 => 0#32
  | (i+1) => get_bit x 0 + parity_rec i (x >>> 1)

def parity_spec (x : BitVec 32) : BitVec 32 :=
    (BitVec.ofBool ((parity_rec 32 x).getLsbD 0)).zeroExtend 32


#eval parity_spec 0xFFFF#32

--set_option diagnostics true
--set_option maxRecDepth 10000
--set_option maxHeartbeats 1000000

#genStepEqTheorems my_program

#eval my_program.length


theorem small_asm_snippet_sym (s0 sf : ArmState)
  (h_s0_pc : read_pc s0 = 0x4005a8#64)
  (h_s0_program : s0.program = my_program)
  (h_s0_err : read_err s0 = StateError.None)
  (h_s0_sp_aligned : CheckSPAlignment s0)
  (h_run : sf = run my_program.length s0):
  w0 sf  = parity_spec (w0 s0) := by
  -- Prelude
  simp_all only [state_simp_rules, -h_run]
  -- Symbolic simulation
  sym_n 7
  -- TODO(@bollu): automation for SP alignment
  --case h_s1_sp_aligned =>
  --  apply Aligned_BitVecSub_64_4 (by assumption) (by decide)
  --case h_s33_sp_aligned =>
  --  apply Aligned_BitVecAdd_64_4 (by assumption) (by decide)
  -- Split the conclusion
  --repeat' apply And.intro
  --· -- Functional Correctness
  simp only [parity_spec,parity_rec,get_bit]
  bv_decide
  done

end mytest

inductive Bool where
  | false : Bool
  | true : Bool

```

```python
def add(x,y):
    return (x+y)
```