import EM.Advanced.RandomTwoPointMC
import EM.Ensemble.TwoPointEnsemble

/-!
# Ensemble Epsilon-Walk MC

## Overview

This file formalizes the **ensemble epsilon-walk MC** framework: under population-level
hypotheses, for every prime q, a positive density of squarefree starting points n yield
epsilon-walks where every unit class mod q is visited.

The key construction is:
1. Starting from squarefree n, run the epsilon-walk `epsWalkProdFrom n sigma` with a
   binary decision sequence `sigma : N -> Bool`.
2. A prime q is "eps-captured" if it appears as a chosen factor `epsWalkFactorFrom n sigma k`
   for some k.
3. Under CRT equidistribution for sigma-walks, a positive density of starting points n
   have the property that the walk visits the "death fiber" mod q infinitely often.

The main definitions:
- `epsCaptured q acc sigma` -- q appears as a factor in the epsilon-walk
- `epsVisitCount q acc sigma K` -- number of lethal visits (q | P_k + 1) in K steps
- `sigmaAccumCount/Density` -- ensemble counting for sigma-walks
- `EnsembleEpsilonMC` -- every unit class reachable for positive density of starts

## Main Results

### Proved Theorems
* `epsCaptured_of_factor_eq` -- factor equality implies capture
* `epsVisitCount_zero` -- no visits in zero steps
* `epsVisitCount_mono` -- visit count monotone in K
* `visit_implies_minFac_le` -- minFac bound at lethal visit
* `epsVisitCount_le` -- visit count bounded by K
* `sigma_accum_base_case` -- base case k=0 for sigma-walk equidist

### Archived (RED #3 analog -- see EM/Archive/Advanced/EpsilonWalkArchive.lean)
* `SigmaCRTPropagationStep` -- CRT equidist propagation for sigma-walks
* `sigma_sre_crt_implies_accum_equidist` -- SRE + SigmaCRT => equidist for all k
* `sigma_death_density_tendsto` -- death density convergence
* `sigma_death_positive_of_crt` -- eventually positive death density
* `eps_walk_ensemble_landscape` -- 8-clause landscape summary

### Open Hypotheses
* `EnsembleEpsilonMC` -- main conjecture
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Basic Definitions -/

section BasicDefs

/-- A prime q is **eps-captured** along the epsilon-walk from `acc` with decisions `sigma`
    if q appears as the chosen factor at some step k. -/
def epsCaptured (q acc : ℕ) (σ : ℕ → Bool) : Prop :=
  ∃ k, epsWalkFactorFrom acc σ k = q

/-- Count of steps k < K where q divides epsWalkProdFrom(acc, sigma, k) + 1.
    These are "lethal visits" where the walk is in the death fiber mod q. -/
def epsVisitCount (q acc : ℕ) (σ : ℕ → Bool) (K : ℕ) : ℕ :=
  ((Finset.range K).filter fun k => q ∣ (epsWalkProdFrom acc σ k + 1)).card

/-- Count of squarefree n in [1,X] with sigma-walk accumulator in residue class a mod r
    at step k. Generalizes `sqfreeAccumCount` to sigma-walks. -/
def sigmaAccumCount (X k r : ℕ) (a : ZMod r) (σ : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 X).filter fun n =>
    Squarefree n ∧ (epsWalkProdFrom n σ k : ZMod r) = a).card

/-- Density of squarefree n in [1,X] with sigma-walk accumulator in residue class a mod r
    at step k. -/
def sigmaAccumDensity (X k r : ℕ) (a : ZMod r) (σ : ℕ → Bool) : ℝ :=
  (sigmaAccumCount X k r a σ : ℝ) / (sqfreeCount X : ℝ)

end BasicDefs

/-! ## Part 2: Structural Lemmas -/

section StructuralLemmas

/-- If the chosen factor at step k equals q, then q is eps-captured. -/
theorem epsCaptured_of_factor_eq (q acc : ℕ) (σ : ℕ → Bool) (k : ℕ)
    (hfac : epsWalkFactorFrom acc σ k = q) :
    epsCaptured q acc σ :=
  ⟨k, hfac⟩

/-- No lethal visits in zero steps. -/
theorem epsVisitCount_zero (q acc : ℕ) (σ : ℕ → Bool) :
    epsVisitCount q acc σ 0 = 0 := by
  simp [epsVisitCount]

/-- Lethal visit count is monotone in K. -/
theorem epsVisitCount_mono (q acc : ℕ) (σ : ℕ → Bool) {K₁ K₂ : ℕ} (hK : K₁ ≤ K₂) :
    epsVisitCount q acc σ K₁ ≤ epsVisitCount q acc σ K₂ := by
  unfold epsVisitCount
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_mono hK))

/-- At a lethal visit, minFac of (P_k + 1) is at most q. -/
theorem visit_implies_minFac_le (q acc : ℕ) (σ : ℕ → Bool) (k : ℕ)
    (hq : Nat.Prime q) (hdvd : q ∣ (epsWalkProdFrom acc σ k + 1)) :
    (epsWalkProdFrom acc σ k + 1).minFac ≤ q :=
  Nat.minFac_le_of_dvd hq.two_le hdvd

/-- Lethal visit count is bounded by K. -/
theorem epsVisitCount_le (q acc : ℕ) (σ : ℕ → Bool) (K : ℕ) :
    epsVisitCount q acc σ K ≤ K := by
  unfold epsVisitCount
  calc ((Finset.range K).filter _).card
      ≤ (Finset.range K).card := Finset.card_filter_le _ _
    _ = K := Finset.card_range K

/-- If q | (P_k + 1) and q is the smallest prime factor, then minFac = q.
    Combined with the coin flip, this gives capture. -/
theorem eps_minFac_eq_of_dvd_and_le (q acc : ℕ) (σ : ℕ → Bool) (k : ℕ)
    (hq : Nat.Prime q) (hdvd : q ∣ (epsWalkProdFrom acc σ k + 1))
    (hle : ∀ p : ℕ, Nat.Prime p → p ∣ (epsWalkProdFrom acc σ k + 1) → q ≤ p) :
    (epsWalkProdFrom acc σ k + 1).minFac = q := by
  have hmf_dvd := Nat.minFac_dvd (epsWalkProdFrom acc σ k + 1)
  have hmf_le := Nat.minFac_le_of_dvd hq.two_le hdvd
  have hmf_prime : (epsWalkProdFrom acc σ k + 1).minFac.Prime :=
    Nat.minFac_prime (by
      intro h1
      have hle2 := Nat.le_of_dvd (by omega) hdvd
      have := hq.two_le
      omega)
  exact Nat.le_antisymm hmf_le (hle _ hmf_prime hmf_dvd)

end StructuralLemmas

/-! ## Part 3: Sigma-Walk Counting Properties -/

section SigmaCounting

/-- The sigma-walk accumulator count is bounded by the total squarefree count. -/
theorem sigmaAccumCount_le_sqfreeCount (X k r : ℕ) (a : ZMod r) (σ : ℕ → Bool) :
    sigmaAccumCount X k r a σ ≤ sqfreeCount X := by
  unfold sigmaAccumCount sqfreeCount
  exact Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩

/-- The sigma-walk accumulator density is non-negative. -/
theorem sigmaAccumDensity_nonneg (X k r : ℕ) (a : ZMod r) (σ : ℕ → Bool) :
    0 ≤ sigmaAccumDensity X k r a σ :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The sigma-walk accumulator density is at most 1. -/
theorem sigmaAccumDensity_le_one (X k r : ℕ) (a : ZMod r) (σ : ℕ → Bool) :
    sigmaAccumDensity X k r a σ ≤ 1 := by
  unfold sigmaAccumDensity
  rcases eq_or_ne (sqfreeCount X) 0 with h | h
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sigmaAccumCount_le_sqfreeCount X k r a σ))

end SigmaCounting

/-! ## Part 4: Base Case — sigma-walk at k=0 agrees with deterministic walk -/

section BaseCase

/-- At k=0, epsWalkProdFrom n sigma 0 = n for all sigma. -/
theorem epsWalkProdFrom_at_zero (n : ℕ) (σ : ℕ → Bool) :
    epsWalkProdFrom n σ 0 = n := rfl

/-- The sigma-walk accumulator count at k=0 equals the standard accumulator count,
    because epsWalkProdFrom n sigma 0 = n = genProd n 0. -/
theorem sigmaAccumCount_zero_eq (X r : ℕ) (a : ZMod r) (σ : ℕ → Bool) :
    sigmaAccumCount X 0 r a σ = sqfreeAccumCount X 0 r a := by
  unfold sigmaAccumCount sqfreeAccumCount
  congr 1

/-- The sigma-walk accumulator density at k=0 equals the standard accumulator density. -/
theorem sigmaAccumDensity_zero_eq (X r : ℕ) (a : ZMod r) (σ : ℕ → Bool) :
    sigmaAccumDensity X 0 r a σ = sqfreeAccumDensity X 0 r a := by
  unfold sigmaAccumDensity sqfreeAccumDensity
  rw [sigmaAccumCount_zero_eq]

/-- **Base case**: SquarefreeResidueEquidist implies sigma-walk equidistribution at k=0
    for ALL decision sequences sigma, because at step 0 the decision is irrelevant. -/
theorem sigma_accum_base_case
    (hsre : SquarefreeResidueEquidist) (r : ℕ) (hr : Nat.Prime r)
    (a : ZMod r) (ha : a ≠ 0) (σ : ℕ → Bool) :
    Filter.Tendsto
      (fun X : ℕ => sigmaAccumDensity X 0 r a σ)
      Filter.atTop
      (nhds ((r : ℝ) / ((r : ℝ) ^ 2 - 1))) := by
  have h := hsre r hr a ha
  simp_rw [sigmaAccumDensity_zero_eq]
  exact h

end BaseCase

/-! ## Part 5: SigmaCRTPropagationStep — Open Hypothesis -/

section SigmaCRT

-- SigmaCRTPropagationStep archived to EM/Archive/Advanced/EpsilonWalkArchive.lean (RED #3 analog)
-- sigma_sre_crt_implies_accum_equidist archived to EM/Archive/Advanced/EpsilonWalkArchive.lean (RED #3 analog)

end SigmaCRT

/-! ## Part 6: Death Fiber Visit Density -/

section DeathFiberDensity

variable (q : ℕ) [hqp : Fact (Nat.Prime q)]

/-- Count of squarefree n in [1,X] with sigma-walk accumulator in the death fiber
    (i.e., q | epsWalkProdFrom n sigma k + 1, equivalently, accumulator ≡ -1 mod q)
    at step k. -/
def sigmaDeathCount (X k : ℕ) (σ : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 X).filter fun n =>
    Squarefree n ∧ (epsWalkProdFrom n σ k + 1 : ZMod q) = 0).card

/-- Death count is bounded by squarefree count. -/
theorem sigmaDeathCount_le (X k : ℕ) (σ : ℕ → Bool) :
    sigmaDeathCount q X k σ ≤ sqfreeCount X := by
  unfold sigmaDeathCount sqfreeCount
  exact Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩

/-- Death density: fraction of squarefree starts landing in death fiber. -/
def sigmaDeathDensity (X k : ℕ) (σ : ℕ → Bool) : ℝ :=
  (sigmaDeathCount q X k σ : ℝ) / (sqfreeCount X : ℝ)

/-- Death density is non-negative. -/
theorem sigmaDeathDensity_nonneg (X k : ℕ) (σ : ℕ → Bool) :
    0 ≤ sigmaDeathDensity q X k σ :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Death density is at most 1. -/
theorem sigmaDeathDensity_le_one (X k : ℕ) (σ : ℕ → Bool) :
    sigmaDeathDensity q X k σ ≤ 1 := by
  unfold sigmaDeathDensity
  rcases eq_or_ne (sqfreeCount X) 0 with h | h
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sigmaDeathCount_le q X k σ))

-- sigma_death_density_tendsto archived to EM/Archive/Advanced/EpsilonWalkArchive.lean (RED #3 analog)

end DeathFiberDensity

/-! ## Part 7: Ensemble Epsilon-Walk MC (Open Hypothesis) -/

section EnsembleEpsMC

/-- **EnsembleEpsilonMC**: For every prime q >= 3, under SRE + SigmaCRT, a positive
    density of squarefree starting points n yield sigma-walks that visit the death
    fiber mod q at some step k (for all decision sequences sigma with infinitely many
    true flips).

    This is the ensemble version of RandomTwoPointMC: instead of asking that EVERY
    starting point 2 yields paths hitting -1 mod q, we ask that a positive density
    of starting points yield epsilon-walks that visit the death fiber.

    **Status**: open hypothesis. -/
def EnsembleEpsilonMC (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (σ : ℕ → Bool),
    (∀ N, ∃ k, N ≤ k ∧ σ k = true) →  -- infinitely many true flips
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X in Filter.atTop,
        c ≤ ((Finset.Icc 1 X).filter fun n =>
          Squarefree n ∧ ∃ k, q ∣ (epsWalkProdFrom n σ k + 1)).card /
          (sqfreeCount X : ℝ)

-- sigma_death_positive_of_crt archived to EM/Archive/Advanced/EpsilonWalkArchive.lean (RED #3 analog)

end EnsembleEpsMC

/-! ## Part 8: Landscape -/

section Landscape

-- eps_walk_ensemble_landscape archived to EM/Archive/Advanced/EpsilonWalkArchive.lean (RED #3 analog, clause 8)

end Landscape
