import EM.EnsembleStructure

/-!
# Ensemble EM: Walk and Multiplier Infrastructure for Generalized EM

This file defines the **generalized walk** and **multiplier** for the
generalized EM sequence from an arbitrary starting point n, cast into
`ZMod q`. It then proves the walk recurrence, the bridge to the
standard EM walk (`walkZ`, `multZ`), and a hit characterization.

## Main Definitions

* `genWalkZ n q k` -- walk position `genProd n k` cast into `ZMod q`
* `genMultZ n q k` -- multiplier `genSeq n k` cast into `ZMod q`

## Main Results

* `genWalkZ_succ`          -- walk recurrence: w(k+1) = w(k) * m(k)
* `genWalkZ_zero`          -- initial value: w(0) = (n : ZMod q)
* `genWalkZ_two_eq_walkZ`  -- bridge: genWalkZ 2 q k = walkZ q k
* `genMultZ_two_eq_multZ`  -- bridge: genMultZ 2 q k = multZ q k
* `genWalkZ_eq_neg_one_iff` -- hit characterization: w(k) = -1 iff q | P(k)+1
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Generalized Walk and Multiplier in ZMod -/

section GenWalk

/-- Walk position for the generalized EM sequence from starting point n mod q.
    This is simply `genProd n k` cast into `ZMod q`. -/
def genWalkZ (n : Nat) (q : Nat) (k : Nat) : ZMod q :=
  (genProd n k : ZMod q)

/-- Multiplier for the generalized EM sequence from starting point n mod q.
    This is simply `genSeq n k` cast into `ZMod q`. -/
def genMultZ (n : Nat) (q : Nat) (k : Nat) : ZMod q :=
  (genSeq n k : ZMod q)

/-- Walk recurrence: genWalkZ n q (k+1) = genWalkZ n q k * genMultZ n q k.
    This follows directly from `genProd_succ` and `Nat.cast_mul`. -/
theorem genWalkZ_succ (n q k : Nat) :
    genWalkZ n q (k + 1) = genWalkZ n q k * genMultZ n q k := by
  simp only [genWalkZ, genMultZ, genProd_succ]
  push_cast
  ring

/-- Initial value of the generalized walk: genWalkZ n q 0 = (n : ZMod q). -/
theorem genWalkZ_zero (n q : Nat) : genWalkZ n q 0 = (n : ZMod q) := by
  simp [genWalkZ, genProd]

end GenWalk

/-! ## Bridge to Standard EM Walk -/

section StandardBridge

/-- The generalized walk from starting point 2 equals the standard walk.
    This follows from `genProd_two_eq_prod`. -/
theorem genWalkZ_two_eq_walkZ (q k : Nat) :
    genWalkZ 2 q k = MullinGroup.walkZ q k := by
  simp only [genWalkZ, MullinGroup.walkZ, genProd_two_eq_prod]

/-- The generalized multiplier from starting point 2 equals the standard multiplier.
    This follows from `genSeq_two_eq_seq_succ`: genSeq 2 k = seq (k+1),
    and multZ q k = (seq (k+1) : ZMod q). -/
theorem genMultZ_two_eq_multZ (q k : Nat) :
    genMultZ 2 q k = MullinGroup.multZ q k := by
  simp only [genMultZ, MullinGroup.multZ, genSeq_two_eq_seq_succ]

/-- The generalized walk recurrence from starting point 2 is consistent
    with the standard walk recurrence. -/
theorem genWalkZ_two_succ_eq (q k : Nat) :
    genWalkZ 2 q (k + 1) = MullinGroup.walkZ q k * MullinGroup.multZ q k := by
  rw [genWalkZ_succ, genWalkZ_two_eq_walkZ, genMultZ_two_eq_multZ]

end StandardBridge

/-! ## Hit Characterization -/

section HitCharacterization

/-- The generalized walk hits -1 mod q iff q divides genProd n k + 1.
    This is the generalized analogue of `walkZ_eq_neg_one_iff`. -/
theorem genWalkZ_eq_neg_one_iff (n q k : Nat) :
    genWalkZ n q k = -1 ↔ (q ∣ genProd n k + 1) := by
  simp only [genWalkZ]
  constructor
  · intro h
    have h1 : (genProd n k : ZMod q) + 1 = 0 := by rw [h]; ring
    have h2 : ((genProd n k + 1 : Nat) : ZMod q) = 0 := by push_cast; exact h1
    rwa [ZMod.natCast_eq_zero_iff] at h2
  · intro h
    have h1 : ((genProd n k + 1 : Nat) : ZMod q) = 0 := by
      rwa [ZMod.natCast_eq_zero_iff]
    have h2 : (genProd n k : ZMod q) + 1 = 0 := by push_cast at h1; exact h1
    calc (genProd n k : ZMod q) = (genProd n k : ZMod q) + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h2]
      _ = -1 := by ring

/-- The generalized walk from starting point 2 hits -1 iff the standard
    walk hits -1. Combined with `walkZ_eq_neg_one_iff`, this gives full
    consistency. -/
theorem genWalkZ_two_eq_neg_one_iff (q k : Nat) :
    genWalkZ 2 q k = -1 ↔ MullinGroup.walkZ q k = -1 := by
  rw [genWalkZ_two_eq_walkZ]

end HitCharacterization

end
