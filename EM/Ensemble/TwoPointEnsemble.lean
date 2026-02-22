import EM.Advanced.VanishingNoiseVariantB
import EM.Ensemble.CRT
import EM.Ensemble.FirstMoment

/-!
# Ensemble Two-Point MC: Population-Level Reduction

## Overview

This file reduces the **Stochastic Two-Point MC** problem to population-level hypotheses
via an ensemble averaging argument. The key chain is:

```
PopulationRatioEscapeDensity (per step, positive density of starting points escape ker(chi))
  --> ensembleAvgEscapeCount = sum of densities (Fubini for finite sums)
  --> escape_first_moment_linear (E[cumulative escape count] >= delta * K)
  --> positive_density_high_escape (positive density of starting points have many escapes)
```

The mathematical content: for the generalized EM walk starting from squarefree n,
we count how many steps k have the factor ratio `genFactorRatio q n k` outside
ker(chi) for a nontrivial character chi. If a positive density of starting points
escape at each step (PopulationRatioEscapeDensity), then by linearity of expectation,
the ensemble average of the cumulative escape count grows linearly. By the partition
argument (following `density_lower_bound_from_mean` in ReciprocalSum.lean), a positive
density of starting points have cumulative escape count at least proportional to K.

## Main Results

### Definitions
* `genRawTwoPointUnitSet`  -- generalized raw two-point unit set for starting point n
* `genPaddedUnitSet`       -- generalized padded unit set (fallback to Finset.univ)
* `genFactorRatio`         -- generalized factor ratio at step k
* `ratioEscapeCount`       -- count of squarefree n with ratio outside ker(chi)
* `ratioEscapeDensity`     -- density of ratio escape at step k
* `cumulRatioEscapeCount`  -- cumulative escape count over K steps

### Open Hypotheses
* `PopulationRatioEscapeDensity`      -- positive escape density per step (from MFRE)
* `MFREImpliesPopulationRatioEscape`  -- MFRE -> population ratio escape

### Proved Theorems
* `ratioEscapeCount_le_sqfreeCount`        -- escape count bounded by total
* `ratioEscapeDensity_nonneg`              -- density >= 0
* `ratioEscapeDensity_le_one`              -- density <= 1
* `cumulRatioEscapeCount_le`               -- cumulative escape <= K
* `ensembleAvgEscapeCount_eq_sum_densities`-- Fubini: ensemble avg = sum of densities
* `genPaddedUnitSet_card_ge_two`           -- padded set has card >= 2 for q >= 3
* `positive_density_high_escape`           -- partition argument: positive density with many escapes
* `ensemble_two_point_landscape`           -- summary landscape theorem
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Section 1: Generalized Factor Set for Arbitrary Starting Points -/

section GenFactorSet

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- Generalized raw two-point unit set for starting point n at step k.
    Contains {liftToUnit(minFac(P_n(k)+1)), liftToUnit(secondMinFac(P_n(k)+1))}
    as a Finset of units in (ZMod q)^*. -/
noncomputable def genRawTwoPointUnitSet (q : ℕ) [Fact (Nat.Prime q)] (n k : ℕ) :
    Finset (ZMod q)ˣ :=
  {liftToUnit (q := q) (Nat.minFac (genProd n k + 1) : ZMod q),
   liftToUnit (q := q) (secondMinFac (genProd n k + 1) : ZMod q)}

/-- Generalized padded unit set: uses raw set when card >= 2, falls back to Finset.univ
    when both factors collapse mod q (giving perfect contraction for nontrivial chi). -/
noncomputable def genPaddedUnitSet (q : ℕ) [Fact (Nat.Prime q)] (n k : ℕ) :
    Finset (ZMod q)ˣ :=
  let raw := genRawTwoPointUnitSet q n k
  if 2 ≤ raw.card then raw else Finset.univ

/-- The generalized padded unit set is always nonempty. -/
theorem genPaddedUnitSet_nonempty (n k : ℕ) :
    (genPaddedUnitSet q n k).Nonempty := by
  simp only [genPaddedUnitSet]
  split
  · exact Finset.card_pos.mp (by omega)
  · exact Finset.univ_nonempty

/-- For q >= 3, the generalized padded unit set has card >= 2. -/
theorem genPaddedUnitSet_card_ge_two (hq3 : 2 < q) (n k : ℕ) :
    2 ≤ (genPaddedUnitSet q n k).card := by
  simp only [genPaddedUnitSet]
  split
  · assumption
  · rw [Finset.card_univ]
    exact card_units_zmod_ge_two hq3

/-- Generalized factor ratio at step k for starting point n:
    liftToUnit(minFac(P_n(k)+1)) * liftToUnit(secondMinFac(P_n(k)+1))^(-1). -/
noncomputable def genFactorRatio (q : ℕ) [Fact (Nat.Prime q)] (n k : ℕ) : (ZMod q)ˣ :=
  liftToUnit (q := q) (Nat.minFac (genProd n k + 1) : ZMod q) *
  (liftToUnit (q := q) (secondMinFac (genProd n k + 1) : ZMod q))⁻¹

end GenFactorSet

/-! ## Section 2: Ratio Escape Counting -/

section RatioEscapeCounting

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- Count of squarefree n in [1,X] with genFactorRatio(q,n,k) NOT in ker(chi) at step k. -/
def ratioEscapeCount (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n =>
    Squarefree n ∧ genFactorRatio q n k ∉ chi.ker)).card

/-- Density of ratio escape at step k: escape count / total squarefree count. -/
noncomputable def ratioEscapeDensity (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ) : ℝ :=
  (ratioEscapeCount q chi k X : ℝ) / (sqfreeCount X : ℝ)

/-- The escape count is bounded by the total squarefree count. -/
theorem ratioEscapeCount_le_sqfreeCount (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ) :
    ratioEscapeCount q chi k X ≤ sqfreeCount X := by
  unfold ratioEscapeCount sqfreeCount
  exact Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩

/-- The escape density is non-negative. -/
theorem ratioEscapeDensity_nonneg (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ) :
    0 ≤ ratioEscapeDensity q chi k X :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The escape density is at most 1. -/
theorem ratioEscapeDensity_le_one (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ) :
    ratioEscapeDensity q chi k X ≤ 1 := by
  unfold ratioEscapeDensity
  rcases eq_or_ne (sqfreeCount X) 0 with h | h
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (ratioEscapeCount_le_sqfreeCount chi k X))

end RatioEscapeCounting

/-! ## Section 3: PopulationRatioEscapeDensity (Open Hypothesis) -/

section PopulationEscape

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- **PopulationRatioEscapeDensity**: Among squarefree starting points, a positive density
    have genFactorRatio not in ker(chi) at each step k >= 1.

    This follows from MFRE: when minFac and secondMinFac are approximately independently
    distributed mod q, the ratio is approximately uniform on (ZMod q)^*, giving escape
    density approximately (index - 1)/index >= 1/2.

    **Status**: open hypothesis (from MFRE + CRT independence). -/
def PopulationRatioEscapeDensity (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  chi ≠ 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, 1 ≤ k → ∀ᶠ X in Filter.atTop,
    δ ≤ ratioEscapeDensity q chi k X

/-- **MFREImpliesPopulationRatioEscape**: MFRE implies population-level ratio escape density.

    Proof sketch: apply MFRE to minFac and secondMinFac independently (the latter is
    minFac of the cofactor genProd(n,k)+1 / minFac(...)), then use CRT independence to
    argue that the ratio minFac/secondMinFac is approximately uniform on (ZMod q)^*.
    For ker(chi) a proper subgroup of index >= 2, the escape density is at least
    (index - 1)/index >= 1/2 minus error terms from MFRE.

    **Status**: open hypothesis. -- OPEN -/
def MFREImpliesPopulationRatioEscape (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  MinFacResidueEquidist q →
    ∀ (chi : (ZMod q)ˣ →* ℂˣ), PopulationRatioEscapeDensity q chi

end PopulationEscape

/-! ## Section 4: Cumulative Escape Count -/

section CumulativeEscape

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- Cumulative escape count: number of steps k < K where genFactorRatio(q,n,k) is
    NOT in ker(chi). This is the ensemble-level analog of counting spectral gap
    events for a single starting point n. -/
def cumulRatioEscapeCount (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) (n K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => genFactorRatio q n k ∉ chi.ker)).card

/-- The cumulative escape count is at most K (trivially: filtering a range K set). -/
theorem cumulRatioEscapeCount_le (chi : (ZMod q)ˣ →* ℂˣ) (n K : ℕ) :
    cumulRatioEscapeCount q chi n K ≤ K := by
  unfold cumulRatioEscapeCount
  calc ((Finset.range K).filter _).card ≤ (Finset.range K).card := Finset.card_filter_le _ _
    _ = K := Finset.card_range K

/-- The cumulative escape count is monotone in K. -/
theorem cumulRatioEscapeCount_mono (chi : (ZMod q)ˣ →* ℂˣ) (n : ℕ) {K₁ K₂ : ℕ}
    (hK : K₁ ≤ K₂) :
    cumulRatioEscapeCount q chi n K₁ ≤ cumulRatioEscapeCount q chi n K₂ := by
  unfold cumulRatioEscapeCount
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_mono hK))

/-- Helper: cumulRatioEscapeCount expressed as a sum of indicators. -/
private theorem cumulRatioEscapeCount_eq_sum (chi : (ZMod q)ˣ →* ℂˣ) (n K : ℕ) :
    (cumulRatioEscapeCount q chi n K : ℝ) =
    ∑ k ∈ Finset.range K,
      if genFactorRatio q n k ∉ chi.ker then (1 : ℝ) else 0 := by
  simp only [cumulRatioEscapeCount, Finset.card_eq_sum_ones]
  push_cast
  rw [← Finset.sum_filter]

/-- Helper: ratioEscapeCount expressed as a sum of indicators. -/
private theorem ratioEscapeCount_eq_sum (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ) :
    (ratioEscapeCount q chi k X : ℝ) =
    ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
      if genFactorRatio q n k ∉ chi.ker then (1 : ℝ) else 0 := by
  simp only [ratioEscapeCount, Finset.card_eq_sum_ones]
  push_cast
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, and_assoc]

/-- The ensemble sum of cumulative escape counts equals the sum of per-step escape counts.
    This is Fubini for finite sums: swapping the order of summation over (n, k). -/
theorem ensemble_cumul_eq_sum_escape (chi : (ZMod q)ˣ →* ℂˣ) (K X : ℕ) :
    ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
      (cumulRatioEscapeCount q chi n K : ℝ) =
    ∑ k ∈ Finset.range K, (ratioEscapeCount q chi k X : ℝ) := by
  simp_rw [cumulRatioEscapeCount_eq_sum, ratioEscapeCount_eq_sum]
  exact Finset.sum_comm

end CumulativeEscape

/-! ## Section 5: Ensemble Average and Linearity (Fubini) -/

section EnsembleAverage

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- Ensemble average of cumulative escape count over squarefree starting points. -/
noncomputable def ensembleAvgEscapeCount (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) (K X : ℕ) : ℝ :=
  (∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
    (cumulRatioEscapeCount q chi n K : ℝ)) / (sqfreeCount X : ℝ)

/-- **Fubini for finite sums**: The ensemble average of the cumulative escape count
    equals the sum of per-step escape densities.

    Proof: swap the order of summation over (starting point n) and (step k). -/
theorem ensembleAvgEscapeCount_eq_sum_densities (chi : (ZMod q)ˣ →* ℂˣ) (K X : ℕ) :
    ensembleAvgEscapeCount q chi K X =
    ∑ k ∈ Finset.range K, ratioEscapeDensity q chi k X := by
  simp only [ensembleAvgEscapeCount, ratioEscapeDensity]
  rw [ensemble_cumul_eq_sum_escape chi K X]
  rw [Finset.sum_div]

/-- The ensemble average escape count is non-negative. -/
theorem ensembleAvgEscapeCount_nonneg (chi : (ZMod q)ˣ →* ℂˣ) (K X : ℕ) :
    0 ≤ ensembleAvgEscapeCount q chi K X := by
  rw [ensembleAvgEscapeCount_eq_sum_densities]
  exact Finset.sum_nonneg fun k _ => ratioEscapeDensity_nonneg chi k X

/-- The ensemble average escape count is at most K. -/
theorem ensembleAvgEscapeCount_le (chi : (ZMod q)ˣ →* ℂˣ) (K X : ℕ) :
    ensembleAvgEscapeCount q chi K X ≤ K := by
  rw [ensembleAvgEscapeCount_eq_sum_densities]
  calc ∑ k ∈ Finset.range K, ratioEscapeDensity q chi k X
      ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => ratioEscapeDensity_le_one chi k X
    _ = K := by simp [Finset.sum_const, Finset.card_range]

end EnsembleAverage

/-! ## Section 6: First Moment Lower Bound -/

section FirstMomentBound

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- Under PopulationRatioEscapeDensity, the ensemble average escape count grows
    at least linearly in K. For each step k >= 1, density >= delta eventually, so
    summing K-1 terms each >= delta gives average >= delta * (K-1). -/
theorem escape_first_moment_linear
    (chi : (ZMod q)ˣ →* ℂˣ)
    (hpred : PopulationRatioEscapeDensity q chi)
    (hchi : chi ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℕ, 2 ≤ K →
      ∀ᶠ X in Filter.atTop, δ * ((K : ℝ) - 1) ≤ ensembleAvgEscapeCount q chi K X := by
  obtain ⟨δ, hδ_pos, hpred'⟩ := hpred hchi
  refine ⟨δ, hδ_pos, fun K hK => ?_⟩
  -- For each k in [1, K), get X_k such that for X >= X_k, density >= delta
  -- We need to combine finitely many "eventually" conditions
  -- The sum over range K includes terms for k = 0, 1, ..., K-1
  -- The terms with k >= 1 are each >= delta eventually
  -- We extract the eventually condition for each k in [1, K)
  have hfin : ∀ k ∈ Finset.Ico 1 K, ∀ᶠ X in Filter.atTop,
      δ ≤ ratioEscapeDensity q chi k X :=
    fun k hk => hpred' k (by simp [Finset.mem_Ico] at hk; exact hk.1)
  -- Use Filter.Eventually.forall_finset for finitely many
  have hall : ∀ᶠ X in Filter.atTop,
      ∀ k ∈ Finset.Ico 1 K, δ ≤ ratioEscapeDensity q chi k X := by
    exact (Finset.Ico 1 K).eventually_all.mpr hfin
  apply Filter.Eventually.mono hall
  intro X hX
  rw [ensembleAvgEscapeCount_eq_sum_densities]
  -- Sum over range K = sum over {0} + sum over [1, K)
  have hdecomp : Finset.range K = {0} ∪ Finset.Ico 1 K := by
    ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
  have hdisj : Disjoint ({0} : Finset ℕ) (Finset.Ico 1 K) := by
    simp [Finset.mem_Ico]
  rw [hdecomp, Finset.sum_union hdisj]
  have h_k0 : 0 ≤ ∑ k ∈ ({0} : Finset ℕ), ratioEscapeDensity q chi k X :=
    Finset.sum_nonneg fun k _ => ratioEscapeDensity_nonneg chi k X
  have h_ico : δ * ((K : ℝ) - 1) ≤
      ∑ k ∈ Finset.Ico 1 K, ratioEscapeDensity q chi k X := by
    calc δ * ((K : ℝ) - 1) = ∑ _k ∈ Finset.Ico 1 K, δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard_ico : (Finset.Ico 1 K).card = K - 1 := Nat.card_Ico 1 K
          rw [hcard_ico, Nat.cast_sub (by omega : 1 ≤ K)]
          ring
      _ ≤ ∑ k ∈ Finset.Ico 1 K, ratioEscapeDensity q chi k X :=
          Finset.sum_le_sum fun k hk => hX k hk
  linarith

end FirstMomentBound

/-! ## Section 7: Partition Argument -- Positive Density of High-Escape Starting Points

Following the pattern of `density_lower_bound_from_mean` in ReciprocalSum.lean:
if E[S_K] >= mu and 0 <= S_K <= B for all n, then
  density{S_K >= M} >= (mu - M) / (B - M).

Here S_K = cumulRatioEscapeCount, B = K, and we want density{S_K >= delta*K/2}.
-/

section PartitionArgument

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- Partition lemma for ensemble escape counts: if the ensemble average is at least mu,
    and each individual count is at most B, then a positive density of starting points
    have count at least M, provided M < mu and M < B. -/
private theorem escape_density_lower_bound
    (chi : (ZMod q)ˣ →* ℂˣ) (K X : ℕ)
    (μ M B : ℝ)
    (hμ : μ ≤ ensembleAvgEscapeCount q chi K X)
    (hB : ∀ n ∈ (Finset.Icc 1 X).filter Squarefree,
      (cumulRatioEscapeCount q chi n K : ℝ) ≤ B)
    (hMB : M < B) (_hμM : M < μ) (hX : 0 < sqfreeCount X) :
    (μ - M) / (B - M) ≤
      ((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ M ≤ (cumulRatioEscapeCount q chi n K : ℝ))).card /
      (sqfreeCount X : ℝ) := by
  set S := (Finset.Icc 1 X).filter Squarefree with hS_def
  set f : ℕ → ℝ := fun n => (cumulRatioEscapeCount q chi n K : ℝ)
  set good := S.filter (fun n => M ≤ f n) with hgood_def
  set bad := S.filter (fun n => ¬(M ≤ f n)) with hbad_def
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hX
  have hBM_pos : (0 : ℝ) < B - M := by linarith
  -- Partition: sum_S f = sum_good f + sum_bad f
  have hpart : ∑ n ∈ S, f n = ∑ n ∈ good, f n + ∑ n ∈ bad, f n := by
    rw [hgood_def, hbad_def]
    exact (Finset.sum_filter_add_sum_filter_not S (fun n => M ≤ f n) f).symm
  -- Card partition
  have hcard_part : good.card + bad.card = S.card := by
    rw [hgood_def, hbad_def]
    exact S.card_filter_add_card_filter_not (fun n => M ≤ f n)
  -- Bound good: sum_good f <= |good| * B
  have hgood_le : ∑ n ∈ good, f n ≤ (good.card : ℝ) * B := by
    calc ∑ n ∈ good, f n ≤ ∑ _n ∈ good, B :=
          Finset.sum_le_sum fun n hn => hB n (Finset.filter_subset _ _ hn)
      _ = (good.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Bound bad: sum_bad f <= |bad| * M
  have hbad_le : ∑ n ∈ bad, f n ≤ (bad.card : ℝ) * M := by
    calc ∑ n ∈ bad, f n ≤ ∑ _n ∈ bad, M := by
          apply Finset.sum_le_sum
          intro n hn
          simp only [hbad_def, Finset.mem_filter, not_le] at hn
          exact le_of_lt hn.2
      _ = (bad.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
  -- From hμ: mu * |S| <= sum_S f
  have hμS : μ * (S.card : ℝ) ≤ ∑ n ∈ S, f n := by
    have h := hμ
    unfold ensembleAvgEscapeCount at h
    have hS_card : (S.card : ℝ) = (sqfreeCount X : ℝ) := by
      simp [hS_def, sqfreeCount]
    rw [hS_card]
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (sqfreeCount X : ℝ))] at h
    linarith
  -- Combine: mu * |S| <= |good| * B + |bad| * M
  have hcombine : μ * (S.card : ℝ) ≤ (good.card : ℝ) * B + (bad.card : ℝ) * M := by
    linarith [hpart, hμS]
  -- Substitute |bad| = |S| - |good|
  have hbad_eq : (bad.card : ℝ) = (S.card : ℝ) - (good.card : ℝ) := by
    have := hcard_part; push_cast [← this]; ring
  -- |good| * (B - M) >= |S| * (mu - M)
  have hgood_bound : (S.card : ℝ) * (μ - M) ≤ (good.card : ℝ) * (B - M) := by
    rw [hbad_eq] at hcombine
    nlinarith
  -- Relate good to the target filtered set
  have hgood_eq : good.card = ((Finset.Icc 1 X).filter (fun n =>
      Squarefree n ∧ M ≤ (cumulRatioEscapeCount q chi n K : ℝ))).card := by
    congr 1
    ext n
    simp only [hgood_def, hS_def, Finset.mem_filter, f, and_assoc]
  have hS_card : S.card = sqfreeCount X := by simp [hS_def, sqfreeCount]
  rw [div_le_div_iff₀ hBM_pos (by rw [← hS_card]; exact hcard_pos)]
  rw [← hgood_eq, ← hS_card]
  linarith

/-- **Positive density of high-escape starting points**: Under PopulationRatioEscapeDensity,
    for each M, there exists K and c > 0 such that a positive density of squarefree starting
    points have cumulative escape count at least M within K steps.

    Proof: Choose K large enough that delta*(K-1) > M+1. Then the partition argument gives
    density >= (delta*(K-1) - M)/(K - M) >= 1/(K - M) > 0. -/
theorem positive_density_high_escape
    (chi : (ZMod q)ˣ →* ℂˣ)
    (hpred : PopulationRatioEscapeDensity q chi)
    (hchi : chi ≠ 1) :
    ∀ M : ℕ, ∃ K : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X in Filter.atTop,
        c ≤ (((Finset.Icc 1 X).filter (fun n =>
          Squarefree n ∧ (M : ℝ) ≤ (cumulRatioEscapeCount q chi n K : ℝ))).card : ℝ) /
          (sqfreeCount X : ℝ) := by
  -- Get delta from the first moment linear bound
  obtain ⟨δ, hδ_pos, hfm⟩ := escape_first_moment_linear chi hpred hchi
  intro M
  -- Choose K large enough that delta * (K - 1) > M + 1 and K >= M + 2
  set K := max (M + 2) (Nat.ceil ((M + 1 : ℝ) / δ) + 2)
  have hK_ge_M2 : M + 2 ≤ K := le_max_left _ _
  have hK2 : 2 ≤ K := by omega
  have hK_large : (M : ℝ) + 1 < δ * ((K : ℝ) - 1) := by
    have hK_ge_ceil : Nat.ceil ((M + 1 : ℝ) / δ) + 2 ≤ K := le_max_right _ _
    have hceil_lt : Nat.ceil ((M + 1 : ℝ) / δ) < K - 1 := by omega
    have hceil_bound : (M + 1 : ℝ) / δ < (K : ℝ) - 1 := by
      calc (M + 1 : ℝ) / δ ≤ ↑(Nat.ceil ((M + 1 : ℝ) / δ)) := Nat.le_ceil _
        _ < ↑(K - 1) := by exact_mod_cast hceil_lt
        _ = (K : ℝ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ K)]; norm_cast
    linarith [mul_comm δ ((K : ℝ) - 1), (div_lt_iff₀ hδ_pos).mp hceil_bound]
  -- Use c = 1/(K - M), which is positive since K > M
  have hKM_pos : (0 : ℝ) < (K : ℝ) - (M : ℝ) := by
    exact_mod_cast (by omega : (0 : ℤ) < (K : ℤ) - (M : ℤ))
  refine ⟨K, 1 / ((K : ℝ) - (M : ℝ)), by positivity, ?_⟩
  -- Get the first moment bound
  have hfmK := hfm K hK2
  -- Filter to get the eventual conclusion
  apply Filter.Eventually.mono hfmK
  intro X hXev
  -- Handle sqfreeCount = 0 case
  have hcard_pos : 0 < sqfreeCount X := by
    by_contra h
    push_neg at h
    have hcard_zero : sqfreeCount X = 0 := by omega
    have hea_zero : ensembleAvgEscapeCount q chi K X = 0 := by
      unfold ensembleAvgEscapeCount
      have : (sqfreeCount X : ℝ) = 0 := by exact_mod_cast hcard_zero
      rw [this, div_zero]
    have : δ * ((K : ℝ) - 1) ≤ 0 := by linarith [hXev]
    have : (0 : ℝ) < δ * ((K : ℝ) - 1) := by
      apply mul_pos hδ_pos
      have : (1 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 1 < K)
      linarith
    linarith
  -- Apply the partition lemma
  have hB : ∀ n ∈ (Finset.Icc 1 X).filter Squarefree,
      (cumulRatioEscapeCount q chi n K : ℝ) ≤ (K : ℝ) := by
    intro n _
    exact_mod_cast cumulRatioEscapeCount_le chi n K
  have hM_lt_K : (M : ℝ) < (K : ℝ) := by
    exact_mod_cast (by omega : (M : ℕ) < K)
  have hM_lt_mu : (M : ℝ) < δ * ((K : ℝ) - 1) := by linarith
  have h_dens := escape_density_lower_bound chi K X
    (δ * ((K : ℝ) - 1)) (M : ℝ) (K : ℝ)
    hXev hB hM_lt_K hM_lt_mu hcard_pos
  -- Show 1/(K - M) ≤ (delta*(K-1) - M) / (K - M)
  calc 1 / ((K : ℝ) - (M : ℝ))
      ≤ (δ * ((K : ℝ) - 1) - (M : ℝ)) / ((K : ℝ) - (M : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hKM_pos)
        linarith
    _ ≤ _ := h_dens

end PartitionArgument

/-! ## Section 8: Assembly and Landscape -/

section Assembly

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- **AlmostAllInfiniteRatioEscapes**: For each escape threshold M, a positive density
    of squarefree starting points have cumulative escape count at least M.

    This follows from PopulationRatioEscapeDensity via linearity of expectation +
    partition argument (positive_density_high_escape).

    Note: both K and the density constant c depend on M (c = 1/(K - M) where K ≈ M/delta).
    This is still meaningful: it says that for any threshold, there exists a number of steps
    within which a positive fraction of starting points achieve it. -/
def AlmostAllInfiniteRatioEscapes (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  chi ≠ 1 → ∀ M : ℕ, ∃ K : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ᶠ X in Filter.atTop,
      c ≤ (((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ (M : ℝ) ≤ (cumulRatioEscapeCount q chi n K : ℝ))).card : ℝ) /
        (sqfreeCount X : ℝ)

/-- PopulationRatioEscapeDensity implies AlmostAllInfiniteRatioEscapes. PROVED. -/
theorem pred_implies_almost_all_infinite
    (chi : (ZMod q)ˣ →* ℂˣ)
    (hpred : PopulationRatioEscapeDensity q chi) :
    AlmostAllInfiniteRatioEscapes q chi :=
  fun hchi => positive_density_high_escape chi hpred hchi

/-- **Ensemble Two-Point Landscape**: summary of all results in this file.

    ALL internal reductions PROVED (no sorry). Open hypotheses:
    A. PopulationRatioEscapeDensity (from MFRE)
    B. MFREImpliesPopulationRatioEscape (MFRE -> PRED)

    PROVED results:
    1. ratioEscapeCount_le_sqfreeCount (counting bound)
    2. ratioEscapeDensity_nonneg / le_one (density bounds)
    3. cumulRatioEscapeCount_le (cumulative escape <= K)
    4. ensembleAvgEscapeCount_eq_sum_densities (Fubini for finite sums)
    5. escape_first_moment_linear (linear growth of first moment)
    6. positive_density_high_escape (partition argument)
    7. pred_implies_almost_all_infinite (PRED => positive density of infinite escapers)
    8. genPaddedUnitSet_card_ge_two (padded set card >= 2 for q >= 3) -/
theorem ensemble_two_point_landscape :
    -- 1. Escape count bounded by sqfreeCount
    (∀ (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ),
      ratioEscapeCount q chi k X ≤ sqfreeCount X)
    ∧
    -- 2. Escape density is in [0, 1]
    (∀ (chi : (ZMod q)ˣ →* ℂˣ) (k X : ℕ),
      0 ≤ ratioEscapeDensity q chi k X ∧ ratioEscapeDensity q chi k X ≤ 1)
    ∧
    -- 3. Cumulative escape count bounded by K
    (∀ (chi : (ZMod q)ˣ →* ℂˣ) (n K : ℕ),
      cumulRatioEscapeCount q chi n K ≤ K)
    ∧
    -- 4. Fubini: ensemble average = sum of densities
    (∀ (chi : (ZMod q)ˣ →* ℂˣ) (K X : ℕ),
      ensembleAvgEscapeCount q chi K X =
      ∑ k ∈ Finset.range K, ratioEscapeDensity q chi k X)
    ∧
    -- 5. PRED => almost all infinite ratio escapes
    (∀ (chi : (ZMod q)ˣ →* ℂˣ),
      PopulationRatioEscapeDensity q chi → AlmostAllInfiniteRatioEscapes q chi)
    ∧
    -- 6. Padded unit set card >= 2 for q >= 3
    (2 < q → ∀ (n k : ℕ), 2 ≤ (genPaddedUnitSet q n k).card) :=
  ⟨fun chi k X => ratioEscapeCount_le_sqfreeCount chi k X,
   fun chi k X => ⟨ratioEscapeDensity_nonneg chi k X, ratioEscapeDensity_le_one chi k X⟩,
   fun chi n K => cumulRatioEscapeCount_le chi n K,
   fun chi K X => ensembleAvgEscapeCount_eq_sum_densities chi K X,
   fun chi hpred => pred_implies_almost_all_infinite chi hpred,
   fun hq3 n k => genPaddedUnitSet_card_ge_two hq3 n k⟩

end Assembly
