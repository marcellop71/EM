import EM.CME.Decomposition
import Mathlib.Data.Nat.Squarefree

/-!
# Weak Ergodicity via the Shifted Squarefree Population

The EM accumulators P(n) are squarefree integers (products of distinct primes).
The Euclid numbers P(n)+1 therefore belong to the **shifted squarefree
population** S = {m ≥ 2 : m−1 squarefree}.

The former decomposition of Weak Ergodicity into PopulationEquidist (PE) + PopulationTransfer
(PT) is RETIRED (2026-08-17, Dead End #160): PE is false by head domination — see
`EM/Population/HeadDomination.lean` — so PT and the chain PE + PT → EMDirichlet are vacuous.
The definitions and that chain are archived in
`EM/Archive/Population/PopulationEquidistArchive.lean`.

## Main Results

### S93. Squarefree Accumulator
* `seq_succ_dvd_euclid` : seq(n+1) ∣ prod(n)+1 (PROVED)
* `seq_succ_coprime_prod` : Coprime (seq(n+1)) (prod(n)) (PROVED)
* `prod_squarefree` : Squarefree (prod n) (PROVED)

### S94. Shifted Squarefree Population
* `ShiftedSquarefree` : the set {m ≥ 2 : m-1 squarefree} (DEF)
* `euclid_in_shifted_squarefree` : prod(n)+1 ∈ ShiftedSquarefree (PROVED)

### S95. Population Decomposition — ARCHIVED (Dead End #160)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## S93. Squarefree Accumulator -/

section SquarefreeAccumulator

/-- **The EM accumulator is squarefree.** `prod(n) = em(0) · em(1) · ⋯ · em(n)`
    is a product of distinct primes, hence squarefree. The proof is by induction:
    at each step, the new prime seq(n+1) is coprime to the existing product
    (by `seq_succ_coprime_prod`), so the product remains squarefree. -/
theorem prod_squarefree (n : Nat) : Squarefree (prod n) := by
  induction n with
  | zero =>
    rw [prod_zero]
    exact (show Nat.Prime 2 by decide).squarefree
  | succ n ih =>
    rw [prod_succ]
    exact Nat.squarefree_mul_iff.mpr
      ⟨(seq_succ_coprime_prod n).symm, ih,
       ((isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))).squarefree⟩

end SquarefreeAccumulator

/-! ## S94. Shifted Squarefree Population -/

section ShiftedSquarefreePopulation

/-- The **shifted squarefree population**: the set of integers m ≥ 2 whose
    predecessor m−1 is squarefree. This set has density 6/π² ≈ 0.608 among
    the positive integers.

    Every Euclid number P(n)+1 belongs to this set, since P(n) is squarefree
    (a product of distinct primes). -/
def ShiftedSquarefree : Set Nat :=
  {m : Nat | 2 ≤ m ∧ Squarefree (m - 1)}

/-- Every Euclid number `prod(n) + 1` is in the shifted squarefree population. -/
theorem euclid_in_shifted_squarefree (n : Nat) :
    prod n + 1 ∈ ShiftedSquarefree :=
  ⟨by have := prod_ge_two n; omega,
   by rw [show prod n + 1 - 1 = prod n from by omega]; exact prod_squarefree n⟩

end ShiftedSquarefreePopulation

