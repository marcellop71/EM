import EM.Population.TransferStrategy
import EM.SDDS.Bridge

/-!
# Ensemble Structure: Structural Properties of Generalized EM Sequences

This file extends the generalized EM sequence infrastructure from
`ReciprocalSumDivergence.lean` with structural properties needed for
the ensemble averaging framework (Steps 6–10 of the master proof strategy).

## New Results

### Divisibility and Growth
* `genProd_dvd_genProd`       — genProd n k ∣ genProd n (k + j) (PROVED)
* `genSeq_dvd_genProd_later`  — genSeq n k ∣ genProd n (k + 1 + j) (PROVED)
* `genProd_strict_mono`       — genProd n k < genProd n (k + 1) when n ≥ 1 (PROVED)

### Tail Identification
* `genProd_restart`           — genProd (genProd n M) k = genProd n (M + k) (PROVED)
* `genSeq_restart`            — genSeq (genProd n M) k = genSeq n (M + k) (PROVED)

### Distinctness
* `genSeq_ne_of_lt`           — genSeq n j ≠ genSeq n k when j < k, n sqfree (PROVED)
* `genSeq_injective`          — genSeq n is injective when n is squarefree (PROVED)

### Connection to Standard EM
* `genProd_two_eq_prod`       — genProd 2 k = prod k for all k (PROVED)
* `genSeq_two_eq_seq_succ`    — genSeq 2 k = seq (k + 1) for all k (PROVED)

### DSL-Hitting (Weaker Variant)
* (DSLHitting section ARCHIVED 2026-08-17, Dead End #160 — PE is false)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Divisibility Structure -/

section Divisibility

/-- The generalized accumulator divides all later accumulators:
    genProd n k ∣ genProd n (k + j) for all j. This follows from the
    recurrence genProd n (k+1) = genProd n k * genSeq n k. -/
theorem genProd_dvd_genProd (n k j : Nat) : genProd n k ∣ genProd n (k + j) := by
  induction j with
  | zero => exact dvd_refl _
  | succ j ih =>
    simp only [Nat.add_succ, genProd_succ]
    exact dvd_mul_of_dvd_left ih _

/-- Each generalized EM prime divides all later accumulators:
    genSeq n k ∣ genProd n (k + 1 + j) for all j. This is because
    genSeq n k divides genProd n (k+1) = genProd n k * genSeq n k,
    and genProd n (k+1) divides genProd n (k+1+j). -/
theorem genSeq_dvd_genProd_later (n k j : Nat) :
    genSeq n k ∣ genProd n (k + 1 + j) := by
  have h : genSeq n k ∣ genProd n (k + 1) := by
    rw [genProd_succ]; exact dvd_mul_left _ _
  exact dvd_trans h (genProd_dvd_genProd n (k + 1) j)

end Divisibility

/-! ## Tail Identification

The orbit starting from the M-th accumulator of orbit n is the tail
of orbit n from step M: `genProd (genProd n M) k = genProd n (M + k)`. -/

section TailIdentification

/-- **Tail identification**: restarting the EM process from the M-th accumulator
    of orbit n gives the tail of the original orbit.
    genProd (genProd n M) k = genProd n (M + k).

    Proof by induction on k:
    - Base: genProd (genProd n M) 0 = genProd n M = genProd n (M + 0).
    - Step: genProd (genProd n M) (k+1)
          = genProd (genProd n M) k * minFac(genProd (genProd n M) k + 1)
          = (IH) genProd n (M+k) * minFac(genProd n (M+k) + 1)
          = genProd n (M+k+1). -/
theorem genProd_restart (n M k : Nat) :
    genProd (genProd n M) k = genProd n (M + k) := by
  induction k with
  | zero => simp [genProd]
  | succ k ih =>
    simp only [Nat.add_succ, genProd_succ, genSeq_def, ih]

/-- **Tail identification for sequences**: the k-th prime of the orbit
    restarted from genProd n M equals the (M+k)-th prime of orbit n. -/
theorem genSeq_restart (n M k : Nat) :
    genSeq (genProd n M) k = genSeq n (M + k) := by
  simp only [genSeq_def, genProd_restart]

end TailIdentification

/-! ## Monotonicity -/

section Monotonicity

/-- The generalized accumulator is strictly increasing: genProd n k < genProd n (k+1)
    whenever n ≥ 1. Since genProd n (k+1) = genProd n k * genSeq n k and
    genSeq n k ≥ 2 (prime), the accumulator at least doubles at each step. -/
theorem genProd_strict_mono {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    genProd n k < genProd n (k + 1) := by
  rw [genProd_succ]
  exact lt_mul_of_one_lt_right (genProd_pos hn k) (genSeq_prime hn k).one_lt

end Monotonicity

/-! ## Distinctness of Generalized EM Primes -/

section Distinctness

/-- Generalized EM primes at different steps are distinct: if j < k and n is
    squarefree, then genSeq n j ≠ genSeq n k.

    Proof: genSeq n j divides genProd n (j+1), which divides genProd n k
    (by `genSeq_dvd_genProd_later` and `genProd_dvd_genProd`). But genSeq n k
    is coprime to genProd n k (by `genSeq_coprime_genProd`). If genSeq n j
    equalled genSeq n k, then genSeq n j would both divide and be coprime to
    genProd n k, forcing genSeq n j ∣ 1, contradicting primality. -/
theorem genSeq_ne_of_lt {n : Nat} (hn : Squarefree n) {j k : Nat} (hjk : j < k) :
    genSeq n j ≠ genSeq n k := by
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (Squarefree.ne_zero hn)
  intro heq
  have h_dvd : genSeq n j ∣ genProd n k := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hjk)
    rw [hd]; exact genSeq_dvd_genProd_later n j d
  have h_cop : Nat.Coprime (genSeq n j) (genProd n k) :=
    heq ▸ genSeq_coprime_genProd hn_pos k
  exact absurd (Nat.eq_one_of_dvd_coprimes h_cop dvd_rfl h_dvd)
    (Nat.Prime.one_lt (genSeq_prime hn_pos j)).ne'

/-- The generalized EM sequence from a squarefree starting point is injective:
    distinct steps always produce distinct primes. -/
theorem genSeq_injective {n : Nat} (hn : Squarefree n) :
    Function.Injective (genSeq n) :=
  Function.Injective.of_lt_imp_ne fun _ _ hjk => genSeq_ne_of_lt hn hjk

end Distinctness

/-! ## Connection to Standard EM Sequence -/

section StandardConnection

/-- The generalized accumulator from starting point 2 equals the standard
    EM accumulator at every step: genProd 2 k = prod k.

    This connects the ensemble framework (which averages over starting points)
    to the standard EM sequence (starting from n = 2), ensuring that ensemble
    results about "almost all squarefree starting points" include the
    specific trajectory relevant to Mullin's Conjecture.

    The proof is by induction, using `euclid_minFac_eq_nat_minFac` to bridge
    the two implementations of minFac (Euclid.minFac in MullinDefs and
    Nat.minFac in ReciprocalSumDivergence). -/
theorem genProd_two_eq_prod (k : Nat) : genProd 2 k = prod k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    -- First prove the genSeq connection at step k
    have h_seq : genSeq 2 k = seq (k + 1) := by
      rw [genSeq_def, ih]
      -- Goal: Nat.minFac (prod k + 1) = seq (k + 1)
      -- seq (k+1) is definitionally Euclid.minFac (prod k + 1)
      exact (euclid_minFac_eq_nat_minFac _
        (by have := prod_ge_two k; omega)).symm
    -- Now close: genProd 2 (k+1) = genProd 2 k * genSeq 2 k
    --          = prod k * seq (k+1) = prod (k+1)
    rw [genProd_succ, prod_succ, ih, h_seq]

/-- The generalized EM primes from starting point 2 equal the standard EM
    sequence shifted by 1: genSeq 2 k = seq (k + 1).

    This says: the k-th prime produced by the generalized construction starting
    from 2 is exactly the (k+1)-th term of the Euclid-Mullin sequence. -/
theorem genSeq_two_eq_seq_succ (k : Nat) : genSeq 2 k = seq (k + 1) := by
  rw [genSeq_def, genProd_two_eq_prod]
  exact (euclid_minFac_eq_nat_minFac _
    (by have := prod_ge_two k; omega)).symm

end StandardConnection

/-! ## Asymptotic Growth -/

section AsymptoticGrowth

/-- The generalized EM sequence tends to infinity: for squarefree n,
    genSeq n k → ∞ as k → ∞.

    This follows directly from injectivity of `genSeq n` (proved in this file).
    An injective function ℕ → ℕ must tend to infinity because it cannot
    repeat values, so it must eventually exceed any bound.

    Same technique as `seq_tendsto_atTop` in `LargeSieve/Structural.lean`. -/
theorem genSeq_tendsto_atTop {n : Nat} (hn : Squarefree n) :
    Filter.Tendsto (genSeq n) Filter.atTop Filter.atTop :=
  Function.Injective.nat_tendsto_atTop (genSeq_injective hn)

/-- Eventually exceeding any bound: for squarefree n and any M,
    there exists N such that for all k ≥ N, M < genSeq n k. -/
theorem genSeq_eventually_gt {n : Nat} (hn : Squarefree n) (M : Nat) :
    ∃ N, ∀ k ≥ N, M < genSeq n k := by
  have h := (genSeq_tendsto_atTop hn) (Filter.Ioi_mem_atTop M)
  exact (Filter.eventually_atTop.mp h).imp fun N hN => fun k hk => hN k hk

/-- Exponential lower bound on the generalized accumulator: for n ≥ 1,
    genProd n k ≥ n * 2^k for all k.

    Proof by induction: genProd n (k+1) = genProd n k * genSeq n k
    ≥ (n * 2^k) * 2 = n * 2^(k+1), since genSeq n k ≥ 2 (prime). -/
theorem genProd_ge_mul_pow_two {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    n * 2 ^ k ≤ genProd n k := by
  induction k with
  | zero => simp [genProd]
  | succ k ih =>
    rw [genProd_succ]
    calc n * 2 ^ (k + 1) = n * (2 ^ k * 2) := by ring
      _ = (n * 2 ^ k) * 2 := by ring
      _ ≤ genProd n k * genSeq n k :=
          Nat.mul_le_mul ih (genSeq_prime hn k).two_le

/-- The generalized accumulator tends to infinity: for n ≥ 1,
    genProd n k → ∞ as k → ∞.

    From genProd n k ≥ n * 2^k and n * 2^k → ∞ for n ≥ 1. -/
theorem genProd_tendsto_atTop {n : Nat} (hn : 1 ≤ n) :
    Filter.Tendsto (genProd n) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun k => genProd_ge_mul_pow_two hn k)
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  use b
  intro k hk
  calc b ≤ k := hk
    _ ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ n * 2 ^ k := Nat.le_mul_of_pos_left _ (by omega)

end AsymptoticGrowth

/-! ## Former "DSL-Hitting" section — ARCHIVED (Dead End #160, 2026-08-17)

`DSLHitting := PopulationEquidist → DynamicalHitting` and the chain
`pe_dsl_hitting_implies_mc` are vacuous because `PopulationEquidist` is false (head
domination, `EM/Population/HeadDomination.lean`).  They are preserved in
`EM/Archive/Population/PopulationEquidistArchive.lean`.  The live target is
`DynamicalHitting → MC` (`dynamical_hitting_implies_mullin`) and CME. -/

end
