import EM.Advanced.InterpolationMC
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# Transition Kernel for the Mixed Walk

## Overview

This file defines the probabilistic transition kernel for the mixed (1-epsilon) minFac +
epsilon uniform factor walk. At each step from accumulator P:
- With probability (1-epsilon), choose minFac(P+1)
- With probability epsilon, choose a uniformly random prime factor of P+1

The transition is formalized both as a `PMF` (uniform over prime factors of P+1) and as
an explicit weight function `epsStepWeight` that gives each factor its exact probability
under the epsilon-process.

## Key Results

### Definitions
* `factorPMF P` -- uniform PMF over prime factors of P+1
* `epsStepWeight eps P p` -- probability of choosing factor p under the epsilon-process

### Proved Theorems
* `factorPMF_support` -- support is exactly (P+1).primeFactors
* `factorPMF_apply_eq` -- each prime factor gets weight 1/omega(P+1)
* `factorPMF_prime` -- elements of support are prime
* `factorPMF_dvd` -- elements of support divide P+1
* `epsStepWeight_nonneg` -- weights are non-negative for 0 <= eps <= 1
* `epsStepWeight_sum_one` -- weights sum to 1 for P >= 1
* `epsStepWeight_ge_stepWeightLB` -- each weight >= eps/omega(P+1)
* `epsStepWeight_minFac_ge` -- minFac weight >= 1 - eps
* `epsStepWeight_le_one` -- each weight <= 1

## Connection to Existing Infrastructure

The weight lower bound `stepWeightLB` from `InterpolationMC.lean` is exactly
`eps / omega(P+1)`. Theorem `epsStepWeight_ge_stepWeightLB` shows that the actual
epsilon-process weight for ANY prime factor is at least this lower bound, justifying
the path weight analysis in the interpolation framework.
-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Uniform PMF over Prime Factors -/

section FactorPMF

/-- The prime factors of P+1 are nonempty when P >= 1 (since P+1 >= 2). -/
theorem primeFactors_succ_nonempty {P : ℕ} (hP : 1 ≤ P) : (P + 1).primeFactors.Nonempty :=
  Nat.nonempty_primeFactors.mpr (by omega)

/-- Uniform PMF over the prime factors of P+1. Each prime factor gets equal weight. -/
noncomputable def factorPMF (P : ℕ) (hP : 1 ≤ P) : PMF ℕ :=
  PMF.uniformOfFinset (P + 1).primeFactors (primeFactors_succ_nonempty hP)

/-- The support of factorPMF is exactly the set of prime factors of P+1. -/
theorem factorPMF_support {P : ℕ} (hP : 1 ≤ P) :
    (factorPMF P hP).support = ↑(P + 1).primeFactors := by
  exact PMF.support_uniformOfFinset (primeFactors_succ_nonempty hP)

/-- Each prime factor of P+1 gets weight 1/omega(P+1) under the uniform PMF. -/
theorem factorPMF_apply_eq {P : ℕ} (hP : 1 ≤ P) {p : ℕ} (hp : p ∈ (P + 1).primeFactors) :
    factorPMF P hP p = ((P + 1).primeFactors.card : ENNReal)⁻¹ := by
  simp [factorPMF, hp]

/-- Elements of factorPMF's support are prime. -/
theorem factorPMF_prime {P : ℕ} (hP : 1 ≤ P) {p : ℕ}
    (hp : p ∈ (factorPMF P hP).support) : p.Prime := by
  rw [factorPMF_support] at hp
  exact Nat.prime_of_mem_primeFactors hp

/-- Elements of factorPMF's support divide P+1. -/
theorem factorPMF_dvd {P : ℕ} (hP : 1 ≤ P) {p : ℕ}
    (hp : p ∈ (factorPMF P hP).support) : p ∣ P + 1 := by
  rw [factorPMF_support] at hp
  exact Nat.dvd_of_mem_primeFactors hp

/-- minFac(P+1) is in factorPMF's support for P >= 1. -/
theorem factorPMF_minFac_mem {P : ℕ} (hP : 1 ≤ P) :
    (P + 1).minFac ∈ (factorPMF P hP).support := by
  rw [factorPMF_support]
  exact Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),
    Nat.minFac_dvd _, by omega⟩

end FactorPMF

/-! ## Part 2: Epsilon-Process Step Weights -/

section EpsStepWeight

/-- Weight assigned to prime factor p at accumulator P under the epsilon-process.
    minFac gets weight (1-epsilon) + epsilon/omega, other factors get epsilon/omega,
    where omega = omega(P+1) = number of distinct prime factors of P+1.
    Non-factors get weight 0. -/
noncomputable def epsStepWeight (ε : ℝ) (P : ℕ) (p : ℕ) : ℝ :=
  if p ∈ (P + 1).primeFactors then
    if p = (P + 1).minFac then
      (1 - ε) + ε / ((P + 1).primeFactors.card : ℝ)
    else
      ε / ((P + 1).primeFactors.card : ℝ)
  else
    0

/-- Prime factor count of P+1 is positive when P >= 1. -/
private theorem omega_pos {P : ℕ} (hP : 1 ≤ P) :
    (0 : ℝ) < ((P + 1).primeFactors.card : ℝ) := by
  have hne : (P + 1).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  exact Nat.cast_pos.mpr hne.card_pos

/-- The epsilon-process weight is non-negative for 0 <= epsilon <= 1. -/
theorem epsStepWeight_nonneg {ε : ℝ} {P p : ℕ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    0 ≤ epsStepWeight ε P p := by
  unfold epsStepWeight
  split_ifs with hmem hmin
  · -- p = minFac: weight = (1 - ε) + ε/ω
    apply add_nonneg
    · linarith
    · exact div_nonneg hε0 (by positivity)
  · -- p ∈ factors but not minFac: weight = ε/ω
    exact div_nonneg hε0 (by positivity)
  · -- p ∉ factors: weight = 0
    exact le_refl _

/-- The epsilon-process weight for minFac is at least 1 - epsilon for P >= 1. -/
theorem epsStepWeight_minFac_ge {ε : ℝ} {P : ℕ} (hε0 : 0 ≤ ε) (hP : 1 ≤ P) :
    1 - ε ≤ epsStepWeight ε P (P + 1).minFac := by
  unfold epsStepWeight
  have hmem : (P + 1).minFac ∈ (P + 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩
  rw [if_pos hmem, if_pos rfl]
  linarith [div_nonneg hε0 (show (0 : ℝ) ≤ ((P + 1).primeFactors.card : ℝ) by positivity)]

/-- Every prime factor p of P+1 gets weight at least epsilon/omega(P+1). -/
theorem epsStepWeight_ge_eps_div_omega {ε : ℝ} {P p : ℕ}
    (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hp : p ∈ (P + 1).primeFactors) :
    ε / ((P + 1).primeFactors.card : ℝ) ≤ epsStepWeight ε P p := by
  unfold epsStepWeight
  rw [if_pos hp]
  split_ifs with hmin
  · -- p = minFac: weight = (1 - ε) + ε/ω >= ε/ω
    linarith [sub_nonneg.mpr hε1]
  · -- p ≠ minFac: weight = ε/ω
    exact le_refl _

/-- Bridge to InterpolationMC: every prime factor gets weight >= stepWeightLB. -/
theorem epsStepWeight_ge_stepWeightLB {ε : ℝ} {P p : ℕ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hp : p ∈ (P + 1).primeFactors) :
    stepWeightLB ε P ≤ epsStepWeight ε P p := by
  unfold stepWeightLB
  exact epsStepWeight_ge_eps_div_omega hε0 hε1 hp

/-- The epsilon-process weight is at most 1 for 0 <= epsilon <= 1 and P >= 1. -/
theorem epsStepWeight_le_one {ε : ℝ} {P p : ℕ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hP : 1 ≤ P) :
    epsStepWeight ε P p ≤ 1 := by
  unfold epsStepWeight
  split_ifs with hmem hmin
  · -- p = minFac: weight = (1 - ε) + ε/ω ≤ (1 - ε) + ε = 1
    have hω_pos : (0 : ℝ) < ((P + 1).primeFactors.card : ℝ) := omega_pos hP
    have hle : ε / ((P + 1).primeFactors.card : ℝ) ≤ ε := by
      rw [div_le_iff₀ hω_pos]
      calc ε = ε * 1 := (mul_one ε).symm
        _ ≤ ε * ((P + 1).primeFactors.card : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hε0
          exact_mod_cast (primeFactors_succ_nonempty hP).card_pos
    linarith
  · -- p ≠ minFac: weight = ε/ω ≤ ε ≤ 1
    have hω_pos : (0 : ℝ) < ((P + 1).primeFactors.card : ℝ) := omega_pos hP
    calc ε / ((P + 1).primeFactors.card : ℝ) ≤ ε := by
          rw [div_le_iff₀ hω_pos]
          calc ε = ε * 1 := (mul_one ε).symm
            _ ≤ ε * ((P + 1).primeFactors.card : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ hε0
              exact_mod_cast (primeFactors_succ_nonempty hP).card_pos
      _ ≤ 1 := hε1
  · -- p ∉ factors: weight = 0 ≤ 1
    exact zero_le_one

end EpsStepWeight

/-! ## Part 3: Sum-to-One Property -/

section SumOne

/-- minFac(P+1) is a prime factor of P+1 for P >= 1. -/
private theorem minFac_mem_primeFactors' {P : ℕ} (hP : 1 ≤ P) :
    (P + 1).minFac ∈ (P + 1).primeFactors :=
  Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, by omega⟩

/-- The epsilon-process weights sum to 1 over the prime factors of P+1 when P >= 1. -/
theorem epsStepWeight_sum_one {ε : ℝ} {P : ℕ} (hP : 1 ≤ P) :
    ∑ p ∈ (P + 1).primeFactors, epsStepWeight ε P p = 1 := by
  -- Split the sum into the minFac term and the rest
  set S := (P + 1).primeFactors with hS_def
  set ω := S.card with hω_def
  have hne : S.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hω_pos : (0 : ℝ) < (ω : ℝ) := Nat.cast_pos.mpr hne.card_pos
  have hω_ne : (ω : ℝ) ≠ 0 := ne_of_gt hω_pos
  have hminFac_mem : (P + 1).minFac ∈ S := minFac_mem_primeFactors' hP
  -- Rewrite using Finset.add_sum_erase
  rw [← Finset.add_sum_erase S _ hminFac_mem]
  -- The minFac term
  have h_minFac : epsStepWeight ε P (P + 1).minFac = (1 - ε) + ε / (ω : ℝ) := by
    unfold epsStepWeight
    rw [if_pos hminFac_mem, if_pos rfl]
  rw [h_minFac]
  -- For all other elements, weight = ε/ω
  have h_other : ∀ p ∈ S.erase (P + 1).minFac, epsStepWeight ε P p = ε / (ω : ℝ) := by
    intro p hp
    have hmem : p ∈ S := Finset.mem_of_mem_erase hp
    have hne_mf : p ≠ (P + 1).minFac := Finset.ne_of_mem_erase hp
    unfold epsStepWeight
    rw [if_pos hmem, if_neg hne_mf]
  rw [Finset.sum_congr rfl h_other]
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Now: (1 - ε) + ε/ω + (ω - 1) * (ε/ω) = 1
  have hcard_erase : (S.erase (P + 1).minFac).card = ω - 1 := by
    rw [Finset.card_erase_of_mem hminFac_mem]
  rw [hcard_erase]
  have hω_ge : 1 ≤ ω := hne.card_pos
  have hcast : (↑(ω - 1) : ℝ) = (ω : ℝ) - 1 := by
    rw [Nat.cast_sub hω_ge]; simp
  rw [hcast]
  field_simp
  ring

end SumOne

/-! ## Part 4: Landscape -/

section Landscape

/-- Summary of the transition kernel infrastructure:
    1. factorPMF is a well-defined PMF on prime factors of P+1
    2. epsStepWeight is non-negative for 0 <= eps <= 1
    3. epsStepWeight sums to 1
    4. epsStepWeight >= stepWeightLB (bridge to InterpolationMC)
    5. epsStepWeight for minFac >= 1 - eps -/
theorem transition_kernel_landscape :
    -- (1) PMF support = primeFactors
    (∀ (P : ℕ) (hP : 1 ≤ P), (factorPMF P hP).support = ↑(P + 1).primeFactors) ∧
    -- (2) Weights non-negative
    (∀ {ε : ℝ} {P p : ℕ}, 0 ≤ ε → ε ≤ 1 → 0 ≤ epsStepWeight ε P p) ∧
    -- (3) Weights sum to 1
    (∀ {ε : ℝ} {P : ℕ}, 1 ≤ P → ∑ p ∈ (P + 1).primeFactors, epsStepWeight ε P p = 1) ∧
    -- (4) Bridge to stepWeightLB
    (∀ {ε : ℝ} {P p : ℕ}, 0 ≤ ε → ε ≤ 1 → p ∈ (P + 1).primeFactors →
      stepWeightLB ε P ≤ epsStepWeight ε P p) ∧
    -- (5) minFac gets most of the weight
    (∀ {ε : ℝ} {P : ℕ}, 0 ≤ ε → 1 ≤ P →
      1 - ε ≤ epsStepWeight ε P (P + 1).minFac) :=
  ⟨fun _P hP => factorPMF_support hP,
   fun hε0 hε1 => epsStepWeight_nonneg hε0 hε1,
   fun hP => epsStepWeight_sum_one hP,
   fun hε0 hε1 hp => epsStepWeight_ge_stepWeightLB hε0 hε1 hp,
   fun hε0 hP => epsStepWeight_minFac_ge hε0 hP⟩

end Landscape

end
