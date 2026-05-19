import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Generalized EM Sequences: Core Definitions

The generalized EM sequence started from an arbitrary squarefree seed n:
P(0) = n, P(k+1) = P(k) * minFac(P(k)+1). Each P(k) is squarefree and each
genSeq(n,k) = minFac(P(k)+1) is prime. The classical EM sequence is the
n = 2 instance (`genProd_two_eq_prod` in `EM/Ensemble/Structure.lean`).

This file is a dependency-free leaf holding only the definitions and their
elementary structural properties, so that the ensemble/population consumers
of `genProd`/`genSeq` need not pull in the reciprocal-sum analysis of
`EM/Population/ReciprocalSum.lean` (extracted from there, Session 301 reorg).
-/

noncomputable section
open Classical

/-! ## Generalized EM Sequence -/

section GeneralizedEM

/-- Generalized EM accumulator: P(0) = n, P(k+1) = P(k) * minFac(P(k)+1). -/
def genProd (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => genProd n k * Nat.minFac (genProd n k + 1)

/-- The k-th prime: genSeq(n,k) = minFac(P(k)+1). -/
def genSeq (n k : Nat) : Nat := Nat.minFac (genProd n k + 1)

/-- genProd n (k+1) = genProd n k * genSeq n k. -/
@[simp] theorem genProd_succ (n k : Nat) :
    genProd n (k + 1) = genProd n k * genSeq n k := rfl

/-- genSeq n k = Nat.minFac (genProd n k + 1). -/
theorem genSeq_def (n k : Nat) : genSeq n k = Nat.minFac (genProd n k + 1) := rfl

/-- The generalized accumulator is positive when starting from n >= 1. -/
theorem genProd_pos {n : Nat} (hn : 1 ≤ n) (k : Nat) : 1 ≤ genProd n k := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    simp only [genProd_succ]
    calc 1 ≤ 1 * 2 := by omega
      _ ≤ genProd n k * Nat.minFac (genProd n k + 1) :=
          Nat.mul_le_mul ih (Nat.minFac_prime (by omega)).two_le

/-- The k-th generalized EM prime is prime when n >= 1. -/
theorem genSeq_prime {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    Nat.Prime (genSeq n k) :=
  Nat.minFac_prime (by have := genProd_pos hn k; omega)

/-- The k-th generalized EM prime divides P(k) + 1. -/
theorem genSeq_dvd_genProd_succ (n k : Nat) :
    genSeq n k ∣ genProd n k + 1 :=
  Nat.minFac_dvd (genProd n k + 1)

/-- genSeq(n,k) is coprime to genProd(n,k). -/
theorem genSeq_coprime_genProd {n : Nat} (_hn : 1 ≤ n) (k : Nat) :
    Nat.Coprime (genSeq n k) (genProd n k) := by
  rw [Nat.coprime_comm]
  exact (Nat.coprime_self_add_right.mpr
    ((Nat.coprime_one_right_iff _).mpr trivial)).coprime_dvd_right
    (genSeq_dvd_genProd_succ n k)

/-- genProd(n,k) is squarefree when n is squarefree. -/
theorem genProd_squarefree {n : Nat} (hn : Squarefree n) (k : Nat) :
    Squarefree (genProd n k) := by
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn.ne_zero
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [genProd_succ]
    exact Nat.squarefree_mul_iff.mpr
      ⟨(genSeq_coprime_genProd hn_pos k).symm, ih,
       (genSeq_prime hn_pos k).squarefree⟩

end GeneralizedEM
