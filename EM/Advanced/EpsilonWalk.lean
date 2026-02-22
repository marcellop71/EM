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
- `SigmaCRTPropagationStep` -- CRT equidist propagation for sigma-walks (open Prop)
- `EnsembleEpsilonMC` -- every unit class reachable for positive density of starts

## Main Results

### Proved Theorems
* `epsCaptured_of_factor_eq` -- factor equality implies capture
* `epsVisitCount_zero` -- no visits in zero steps
* `epsVisitCount_mono` -- visit count monotone in K
* `visit_implies_minFac_le` -- minFac bound at lethal visit
* `epsVisitCount_le` -- visit count bounded by K
* `sigma_accum_base_case` -- base case k=0 for sigma-walk equidist
* `sigma_sre_crt_implies_accum_equidist` -- SRE + SigmaCRT => equidist for all k
* `eps_walk_landscape` -- 8-clause landscape summary

### Open Hypotheses
* `SigmaCRTPropagationStep` -- CRT equidist propagation for sigma-walks
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

/-- **SigmaCRTPropagationStep**: CRT equidistribution propagation for sigma-walks.

    If the sigma-walk accumulator equidistributes mod r at step k (over squarefree
    starting points), then it equidistributes at step k+1. This is the sigma-walk
    analog of `CRTPropagationStep`.

    The key structural difference from the deterministic case: at step k, the factor
    chosen (minFac or secondMinFac) depends on sigma(k), but by the CRT argument,
    the residue class of the factor mod r is determined by the accumulator's residues
    mod primes other than r. When the accumulator equidistributes mod r and
    independently in other coordinates, the product equidistributes mod r regardless
    of which factor is chosen.

    **Status**: open hypothesis (analog of CRTPropagationStep for sigma-walks). -/
def SigmaCRTPropagationStep : Prop :=
  ∀ (r : ℕ), Nat.Prime r → ∀ (k : ℕ) (σ : ℕ → Bool),
    (∀ (a : ZMod r), a ≠ 0 →
      Filter.Tendsto (fun X => sigmaAccumDensity X k r a σ)
        Filter.atTop (nhds ((r : ℝ) / ((r : ℝ) ^ 2 - 1)))) →
    (∀ (a : ZMod r), a ≠ 0 →
      Filter.Tendsto (fun X => sigmaAccumDensity X (k + 1) r a σ)
        Filter.atTop (nhds ((r : ℝ) / ((r : ℝ) ^ 2 - 1))))

/-- SRE + SigmaCRTPropagationStep => sigma-walk accumulator equidistributes for all k.
    PROVED by induction on k using the base case and propagation step. -/
theorem sigma_sre_crt_implies_accum_equidist
    (hsre : SquarefreeResidueEquidist) (hcrt : SigmaCRTPropagationStep)
    (r : ℕ) (hr : Nat.Prime r) (k : ℕ) (σ : ℕ → Bool)
    (a : ZMod r) (ha : a ≠ 0) :
    Filter.Tendsto
      (fun X : ℕ => sigmaAccumDensity X k r a σ)
      Filter.atTop
      (nhds ((r : ℝ) / ((r : ℝ) ^ 2 - 1))) := by
  induction k generalizing a with
  | zero => exact sigma_accum_base_case hsre r hr a ha σ
  | succ k ih =>
    exact hcrt r hr k σ (fun aU haU => ih aU haU) a ha

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

/-- Under SRE + SigmaCRT, the death density converges to q/(q^2-1).
    The death fiber {n : epsWalkProdFrom n sigma k ≡ -1 mod q} corresponds to
    the residue class (q-1) mod q (since -1 = q-1 in ZMod q), which is nonzero
    when q >= 2. -/
theorem sigma_death_density_tendsto
    (hsre : SquarefreeResidueEquidist) (hcrt : SigmaCRTPropagationStep)
    (hq2 : 2 ≤ q) (k : ℕ) (σ : ℕ → Bool) :
    Filter.Tendsto
      (fun X : ℕ => sigmaDeathDensity q X k σ)
      Filter.atTop
      (nhds ((q : ℝ) / ((q : ℝ) ^ 2 - 1))) := by
  -- Death fiber corresponds to accumulator ≡ -1 mod q
  -- Since epsWalkProdFrom n sigma k + 1 ≡ 0 mod q iff epsWalkProdFrom n sigma k ≡ -1 mod q
  -- The density of {acc ≡ -1 mod q} tends to 1/(q-1) by sigma-walk equidistribution
  -- We need: -1 ≠ 0 in ZMod q (true for q >= 2)
  have hq_ne : (q : ℕ) ≠ 0 := by omega
  have hq_prime := hqp.out
  -- The death condition "epsWalkProdFrom n sigma k + 1 ≡ 0 mod q" is equivalent to
  -- "epsWalkProdFrom n sigma k ≡ -1 mod q"
  -- The class -1 in ZMod q is nonzero when q >= 2
  have hminus_one_ne : (-1 : ZMod q) ≠ 0 := by
    intro h
    have h1 : (1 : ZMod q) = 0 := by rw [show (1 : ZMod q) = -(-1 : ZMod q) from by ring, h, neg_zero]
    have : (q : ℕ) ∣ 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact_mod_cast h1
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  -- sigmaDeathCount counts n with (epsWalkProdFrom n σ k + 1 : ZMod q) = 0
  -- which is equivalent to (epsWalkProdFrom n σ k : ZMod q) = -1
  -- so sigmaDeathDensity = sigmaAccumDensity X k q (-1 : ZMod q) sigma
  suffices h : ∀ X, sigmaDeathDensity q X k σ = sigmaAccumDensity X k q (-1 : ZMod q) σ by
    simp_rw [h]
    exact sigma_sre_crt_implies_accum_equidist hsre hcrt q hq_prime k σ (-1) hminus_one_ne
  intro X
  unfold sigmaDeathDensity sigmaAccumDensity sigmaDeathCount sigmaAccumCount
  have hfe : ∀ n ∈ Finset.Icc 1 X,
      (Squarefree n ∧ (epsWalkProdFrom n σ k : ZMod q) + 1 = 0) ↔
      (Squarefree n ∧ (epsWalkProdFrom n σ k : ZMod q) = -1) := by
    intro n _
    constructor
    · intro ⟨hsf, heq⟩
      exact ⟨hsf, eq_neg_of_add_eq_zero_left heq⟩
    · intro ⟨hsf, heq⟩
      exact ⟨hsf, by rw [heq]; ring⟩
  congr 1
  rw [Finset.filter_congr hfe]

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

/-- CRT equidist gives lethal visit density bounded below for each fixed step k.
    Under SRE + SigmaCRT, death density at step k tends to q/(q^2-1) > 0. -/
theorem sigma_death_positive_of_crt
    (q : ℕ) [hqp : Fact (Nat.Prime q)]
    (hsre : SquarefreeResidueEquidist) (hcrt : SigmaCRTPropagationStep)
    (hq2 : 2 ≤ q) (k : ℕ) (σ : ℕ → Bool) :
    ∀ᶠ X in Filter.atTop,
      (0 : ℝ) < sigmaDeathDensity q X k σ := by
  have htend := sigma_death_density_tendsto q hsre hcrt hq2 k σ
  have hpos : (0 : ℝ) < (q : ℝ) / ((q : ℝ) ^ 2 - 1) := by
    apply div_pos (Nat.cast_pos.mpr (by omega))
    have hq_cast : (2 : ℝ) ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr hq2
    nlinarith [sq_nonneg ((q : ℝ) - 1)]
  -- Use that tendsto to a positive limit implies eventually positive
  have hset : Set.Ioi (0 : ℝ) ∈ nhds ((q : ℝ) / ((q : ℝ) ^ 2 - 1)) :=
    Ioi_mem_nhds hpos
  exact htend hset

end EnsembleEpsMC

/-! ## Part 8: Landscape -/

section Landscape

/-- **Epsilon-walk landscape**: summary of all results in this file.

    PROVED results:
    1. epsCaptured_of_factor_eq (capture from factor equality)
    2. epsVisitCount_zero (no visits in zero steps)
    3. epsVisitCount_mono (monotonicity)
    4. epsVisitCount_le (bounded by K)
    5. sigmaAccumCount_le_sqfreeCount (counting bound)
    6. sigmaAccumDensity_nonneg / le_one (density bounds)
    7. sigma_accum_base_case (k=0 from SRE, unconditional in sigma)
    8. sigma_sre_crt_implies_accum_equidist (SRE + SigmaCRT => equidist all k)

    Open Hypotheses:
    A. SigmaCRTPropagationStep (CRT propagation for sigma-walks)
    B. EnsembleEpsilonMC (main conjecture) -/
theorem eps_walk_ensemble_landscape (q : ℕ) [Fact (Nat.Prime q)] :
    -- 1. Capture from factor equality
    (∀ (acc : ℕ) (σ : ℕ → Bool) (k : ℕ),
      epsWalkFactorFrom acc σ k = q → epsCaptured q acc σ)
    ∧
    -- 2. No visits in zero steps
    (∀ (acc : ℕ) (σ : ℕ → Bool), epsVisitCount q acc σ 0 = 0)
    ∧
    -- 3. Visit count monotone
    (∀ (acc : ℕ) (σ : ℕ → Bool) {K₁ K₂ : ℕ}, K₁ ≤ K₂ →
      epsVisitCount q acc σ K₁ ≤ epsVisitCount q acc σ K₂)
    ∧
    -- 4. Visit count bounded by K
    (∀ (acc : ℕ) (σ : ℕ → Bool) (K : ℕ),
      epsVisitCount q acc σ K ≤ K)
    ∧
    -- 5. Sigma accumulator count bounded
    (∀ (X k r : ℕ) (a : ZMod r) (σ : ℕ → Bool),
      sigmaAccumCount X k r a σ ≤ sqfreeCount X)
    ∧
    -- 6. Sigma density in [0,1]
    (∀ (X k r : ℕ) (a : ZMod r) (σ : ℕ → Bool),
      0 ≤ sigmaAccumDensity X k r a σ ∧ sigmaAccumDensity X k r a σ ≤ 1)
    ∧
    -- 7. Base case: k=0 agrees with standard accumulator count
    (∀ (X r : ℕ) (a : ZMod r) (σ : ℕ → Bool),
      sigmaAccumCount X 0 r a σ = sqfreeAccumCount X 0 r a)
    ∧
    -- 8. SRE + SigmaCRT => equidistribution for all k
    (SquarefreeResidueEquidist → SigmaCRTPropagationStep →
      ∀ (r : ℕ), Nat.Prime r → ∀ (k : ℕ) (σ : ℕ → Bool)
        (a : ZMod r), a ≠ 0 →
        Filter.Tendsto
          (fun X => sigmaAccumDensity X k r a σ)
          Filter.atTop (nhds ((r : ℝ) / ((r : ℝ) ^ 2 - 1)))) :=
  ⟨fun acc σ k hf => epsCaptured_of_factor_eq q acc σ k hf,
   fun acc σ => epsVisitCount_zero q acc σ,
   fun acc σ => epsVisitCount_mono q acc σ,
   fun acc σ K => epsVisitCount_le q acc σ K,
   fun X k r a σ => sigmaAccumCount_le_sqfreeCount X k r a σ,
   fun X k r a σ => ⟨sigmaAccumDensity_nonneg X k r a σ,
                      sigmaAccumDensity_le_one X k r a σ⟩,
   fun X r a σ => sigmaAccumCount_zero_eq X r a σ,
   fun hsre hcrt r hr k σ a ha =>
     sigma_sre_crt_implies_accum_equidist hsre hcrt r hr k σ a ha⟩

end Landscape
