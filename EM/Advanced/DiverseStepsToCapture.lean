import EM.Advanced.FactorDiversity

/-!
# Diverse Steps to Capture: Bridging Factor Diversity to Stochastic MC

## Overview

This file connects the ensemble-level factor diversity infrastructure
(genFactorSetMod has >= 2 distinct residues infinitely often) to the
stochastic MC framework (positive probability capture of primes).

The key insight: each prime factor of genProd(2, k) + 1 gives a reachable
position in the mixed walk from accumulator 2. When the factor set has >= 2
distinct residues mod q, these produce >= 2 distinct elements of the
ever-reachable set R_infty(q, 2).

## Main Results

* `genFactorSet_dvd_mixedWalk` -- factor set divides mixed walk accumulator + 1
* `genFactor_in_reachableAt` -- each prime factor gives a reachable position
* `genFactor_in_reachableEver` -- ... in the ever-reachable set
* `diverse_step_two_reachable` -- diverse step implies >= 2 distinct reachable positions
* `DiversityImpliesReachable` -- open Prop: diversity implies -1 reachable
* `diversity_reachable_implies_stochastic_mc` -- conditional chain to StochasticMC
* `tsd_implies_diversity_reachable` -- TreeSieveDecay implies DiversityImpliesReachable
* `diverse_steps_to_capture_landscape` -- summary conjunction

-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Standard Walk Bridge

Each prime factor of `genProd(2, k) + 1` divides `mixedWalkProd 2 minFacMixed k + 1`,
since `mixedWalkProd 2 minFacMixed k = prod k = genProd 2 k` by the bridge theorem. -/

section StandardWalkBridge

/-- Every prime factor of `genProd(2, k) + 1` divides the mixed walk accumulator + 1.
    This bridges the ensemble factor set to the mixed walk infrastructure. -/
theorem genFactorSet_dvd_mixedWalk (k : ℕ) {p : ℕ} (hp : p ∈ genFactorSet 2 k) :
    p ∣ mixedWalkProd 2 minFacMixed k + 1 := by
  rw [mixedWalkProd_two_minFac_eq_prod, ← genProd_two_eq_prod]
  exact genFactorSet_dvd hp

end StandardWalkBridge

/-! ## Part 2: Fan Inclusion in Reachable Set

Each prime factor of `genProd(2, k) + 1` gives a reachable position at step `k + 1`
via the `reachableAt_from_factor` growth lemma. We use the standard all-minFac
selection `minFacMixed`, which is always valid. -/

section FanInclusion

/-- Each prime factor of `genProd(2, k) + 1` produces a reachable position at step `k + 1`.
    The reachable position is `(prod k * p : ZMod q)`. -/
theorem genFactor_in_reachableAt (q k : ℕ) {p : ℕ} (hp : p ∈ genFactorSet 2 k) :
    (mixedWalkProd 2 minFacMixed k * p : ZMod q) ∈ reachableAt q 2 (k + 1) :=
  reachableAt_from_factor (minFacMixed_valid 2) (genFactorSet_all_prime hp)
    (genFactorSet_dvd_mixedWalk k hp)

/-- Each prime factor of `genProd(2, k) + 1` produces an element of the
    ever-reachable set `R_infty(q, 2)`. -/
theorem genFactor_in_reachableEver (q k : ℕ) {p : ℕ} (hp : p ∈ genFactorSet 2 k) :
    (mixedWalkProd 2 minFacMixed k * p : ZMod q) ∈ reachableEver q 2 :=
  reachableAt_subset_reachableEver q 2 (k + 1) (genFactor_in_reachableAt q k hp)

/-- Variant using `prod k` directly instead of `mixedWalkProd 2 minFacMixed k`. -/
theorem genFactor_in_reachableEver' (q k : ℕ) {p : ℕ} (hp : p ∈ genFactorSet 2 k) :
    ((prod k : ℕ) : ZMod q) * (p : ZMod q) ∈ reachableEver q 2 := by
  have := genFactor_in_reachableEver q k hp
  simp only [mixedWalkProd_two_minFac_eq_prod] at this
  exact this

end FanInclusion

/-! ## Part 3: Diverse Step Fan Cardinality

At a diverse step (genFactorSetMod has >= 2 distinct residues), the fan of
reachable positions contains >= 2 DISTINCT elements. The key: left multiplication
by `(prod k : ZMod q)` is injective when `(prod k : ZMod q) != 0`, which holds
in `ZMod q` (a field for prime q) since `q` does not divide `prod k`. -/

section DiverseStepFan

/-- At a diverse step, the fan of reachable positions contains at least 2 distinct
    elements. The distinctness follows from the injectivity of left multiplication
    by `(prod k : ZMod q)` in the field `ZMod q` for prime `q`.

    Hypothesis `hcoprime`: `(prod k : ZMod q) != 0`, which holds whenever `q` does not
    divide `prod k`. For the standard EM walk, this is true whenever `q` has not yet
    been captured (i.e., `q` never appears in the sequence before step `k`). -/
theorem diverse_step_two_reachable (q k : ℕ) [Fact (Nat.Prime q)]
    (hdiv : FactorDiversityAtStep q 2 k)
    (hcoprime : ((prod k : ℕ) : ZMod q) ≠ 0) :
    ∃ a b : ZMod q, a ∈ reachableEver q 2 ∧ b ∈ reachableEver q 2 ∧ a ≠ b := by
  -- Get two prime factors with distinct residues mod q
  obtain ⟨p₁, hp₁, p₂, hp₂, hneq⟩ := factor_diversity_has_distinct_residues 2 hdiv
  -- Both give reachable positions
  have hr₁ := genFactor_in_reachableEver' q k hp₁
  have hr₂ := genFactor_in_reachableEver' q k hp₂
  refine ⟨_, _, hr₁, hr₂, ?_⟩
  -- Show distinctness: prod k * p₁ != prod k * p₂ in ZMod q
  intro heq
  apply hneq
  exact mul_left_cancel₀ hcoprime heq

end DiverseStepFan

/-! ## Part 4: Conditional Bridge

We define an open hypothesis `DiversityImpliesReachable`: infinitely many diverse
steps implies `-1` is in the ever-reachable set. This bridges the purely combinatorial
diversity condition to the topological reachability needed for StochasticMC.

Note: this is strictly WEAKER than TreeSieveDecay, which gives full unit coverage
(GoodAccumulator = all units reachable). Here we only need `-1` reachable. -/

section ConditionalBridge

/-- Factor diversity implies `-1` is reachable (open hypothesis).
    Strictly weaker than TreeSieveDecay: TSD gives full unit coverage
    (all elements of `(ZMod q)*` reachable), while this only requires
    `-1` to be in the ever-reachable set.

    The gap is genuine: having >= 2 distinct reachable positions at i.o.
    steps does not by itself force `-1` into the reachable set. The
    difficulty is that reachable set growth depends on WHICH positions
    are reached, not just their count. -/
def DiversityImpliesReachable (q : ℕ) : Prop :=
  InfinitelyManyDiverseSteps q 2 → (-1 : ZMod q) ∈ reachableEver q 2

/-- **Conditional chain**: DiversityImpliesReachable + InfinitelyManyDiverseSteps
    implies StochasticMC for any epsilon > 0. -/
theorem diversity_reachable_implies_stochastic_mc (q : ℕ) (hq : Nat.Prime q)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbridge : DiversityImpliesReachable q)
    (himds : InfinitelyManyDiverseSteps q 2) :
    StochasticMC ε q := by
  right
  exact ⟨hq, hε, hε1,
    reachable_implies_positive_prob_capture hq le_rfl hε (hbridge himds)⟩

/-- **One-hypothesis chain**: DiversityImpliesReachable alone suffices (when combined
    with the diversity hypothesis it wraps). Exposes the structure clearly. -/
theorem diversity_reachable_implies_mixed_mc (q : ℕ) (hq : Nat.Prime q)
    (hbridge : DiversityImpliesReachable q)
    (himds : InfinitelyManyDiverseSteps q 2) :
    MixedMC q := by
  intro _
  by_cases hq2 : q = 2

  · left; exact hq2
  · right
    have hreach := hbridge himds
    rw [reachableEver, Set.mem_iUnion] at hreach
    obtain ⟨n, σ, hv, hmod⟩ := hreach
    have hdvd : q ∣ mixedWalkProd 2 σ n + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hmod]; ring
    obtain ⟨σ', hv', k, hk⟩ := hit_implies_capture' hq 2 σ hv n hdvd
    exact ⟨σ', hv', ⟨k, hk⟩⟩

end ConditionalBridge

/-! ## Part 5: TSD Implies DiversityImpliesReachable

TreeSieveDecay is strictly stronger than DiversityImpliesReachable: TSD gives
`GoodAccumulator` (every unit reachable from large squarefree accumulators),
which in particular gives `-1` reachable from acc = 2. The diversity hypothesis
is not even used. -/

section TSDImpliesDIR

/-- TreeSieveDecay implies DiversityImpliesReachable: TSD gives `-1` reachable
    from acc = 2 unconditionally (without needing the diversity hypothesis).
    The proof ignores the diversity input entirely. -/
theorem tsd_implies_diversity_reachable (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q) :
    DiversityImpliesReachable q := by
  intro _
  exact tsd_implies_reachable_from_two q hq hq2 hTSD

/-- **Full chain via TSD**: TreeSieveDecay implies StochasticMC, factoring
    through DiversityImpliesReachable as an intermediate step. -/
theorem tsd_via_diversity_implies_stochastic_mc (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    StochasticMC ε q :=
  stochastic_mc_of_tsd q hq hq2 hTSD ε hε hε1

end TSDImpliesDIR

/-! ## Part 6: Unconditional Structural Results

Even without the open hypothesis, we can establish structural properties
that connect factor diversity to the reachable set geometry. -/

section Unconditional

/-- At any step k, the standard EM walk position `prod k mod q` is reachable. -/
theorem prod_in_reachable_ever (q k : ℕ) :
    ((prod k : ℕ) : ZMod q) ∈ reachableEver q 2 := by
  apply reachableAt_subset_reachableEver q 2 k
  show ((prod k : ℕ) : ZMod q) ∈ reachableAt q 2 k
  rw [reachableAt]
  exact ⟨minFacMixed, minFacMixed_valid 2, by rw [mixedWalkProd_two_minFac_eq_prod]⟩

/-- At a diverse step k, the reachable set grows by at least 2 elements from step k.
    These elements are `prod(k) * p₁ mod q` and `prod(k) * p₂ mod q` for two prime
    factors p₁, p₂ of `genProd(2, k) + 1` with distinct residues mod q. -/
theorem diverse_step_reachable_growth (q k : ℕ) [Fact (Nat.Prime q)]
    (hdiv : FactorDiversityAtStep q 2 k) :
    ∃ p₁ ∈ genFactorSet 2 k, ∃ p₂ ∈ genFactorSet 2 k,
      (p₁ : ZMod q) ≠ (p₂ : ZMod q) ∧
      ((prod k : ℕ) : ZMod q) * (p₁ : ZMod q) ∈ reachableEver q 2 ∧
      ((prod k : ℕ) : ZMod q) * (p₂ : ZMod q) ∈ reachableEver q 2 := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hneq⟩ := factor_diversity_has_distinct_residues 2 hdiv
  exact ⟨p₁, hp₁, p₂, hp₂, hneq,
    genFactor_in_reachableEver' q k hp₁,
    genFactor_in_reachableEver' q k hp₂⟩

end Unconditional

/-! ## Part 7: Landscape -/

section Landscape

/-- **Diverse Steps to Capture Landscape**: Summary of the bridge from
    factor diversity to stochastic MC.

    1. Each prime factor of genProd(2,k)+1 divides the mixed walk accumulator + 1
    2. Each prime factor gives a reachable position in R_infty(q, 2)
    3. Diverse steps produce >= 2 distinct reachable positions (when walk pos is unit)
    4. DiversityImpliesReachable + IMDS implies StochasticMC
    5. TreeSieveDecay implies DiversityImpliesReachable (stronger hypothesis)
    6. Diverse steps produce >= 2 distinct-residue factors in the reachable set -/
theorem diverse_steps_to_capture_landscape (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q) :
    -- 1. Factor set bridge to mixed walk
    (∀ k p, p ∈ genFactorSet 2 k → p ∣ mixedWalkProd 2 minFacMixed k + 1)
    ∧
    -- 2. Fan inclusion in reachable set
    (∀ k p, p ∈ genFactorSet 2 k →
      (mixedWalkProd 2 minFacMixed k * p : ZMod q) ∈ reachableEver q 2)
    ∧
    -- 3. Diverse step produces distinct reachable elements (conditional on unit position)
    (letI : Fact (Nat.Prime q) := Fact.mk hq
     ∀ k, FactorDiversityAtStep q 2 k → ((prod k : ℕ) : ZMod q) ≠ 0 →
       ∃ a b : ZMod q, a ∈ reachableEver q 2 ∧ b ∈ reachableEver q 2 ∧ a ≠ b)
    ∧
    -- 4. DiversityImpliesReachable + IMDS implies StochasticMC
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → DiversityImpliesReachable q →
      InfinitelyManyDiverseSteps q 2 → StochasticMC ε q)
    ∧
    -- 5. TSD implies DiversityImpliesReachable
    (TreeSieveDecay q → DiversityImpliesReachable q)
    ∧
    -- 6. Diverse step reachable growth (unconditional)
    (letI : Fact (Nat.Prime q) := Fact.mk hq
     ∀ k, FactorDiversityAtStep q 2 k →
       ∃ p₁ ∈ genFactorSet 2 k, ∃ p₂ ∈ genFactorSet 2 k,
         (p₁ : ZMod q) ≠ (p₂ : ZMod q) ∧
         ((prod k : ℕ) : ZMod q) * (p₁ : ZMod q) ∈ reachableEver q 2 ∧
         ((prod k : ℕ) : ZMod q) * (p₂ : ZMod q) ∈ reachableEver q 2) :=
  ⟨fun k _ hp => genFactorSet_dvd_mixedWalk k hp,
   fun k _ hp => genFactor_in_reachableEver q k hp,
   fun k hdiv hcop => by
     letI : Fact (Nat.Prime q) := Fact.mk hq
     exact diverse_step_two_reachable q k hdiv hcop,
   fun ε hε hε1 hb hi => diversity_reachable_implies_stochastic_mc q hq ε hε hε1 hb hi,
   fun hTSD => tsd_implies_diversity_reachable q hq hq2 hTSD,
   fun k hdiv => by
     letI : Fact (Nat.Prime q) := Fact.mk hq
     exact diverse_step_reachable_growth q k hdiv⟩

end Landscape

end
