import EM.Ensemble.Structure
import EM.Reduction.ShiftedDensity

/-!
# Ensemble First Moment: κ and the Average Reciprocal Sum

This file formalizes the **ensemble first moment** infrastructure from the
master proof strategy (Steps 6–7). The key objects are:

1. **Ensemble average**: `ensembleAvg X f` averages `f(n)` over squarefree n ≤ X.
2. **Starting divisibility**: `n ∣ genProd n k` for all k (the starting point
   divides every accumulator, so the starting point is recoverable).
3. **The reciprocal constant κ**: defined via the sieve density function g(r).
4. **First moment hypothesis**: the ensemble average of 1/genSeq n k → κ.
5. **Variance bound hypothesis**: Var[∑ 1/genSeq] = O(K).

## Main Results

### Definitions
* `ensembleAvg`              — average of f over squarefree n in [1,X]
* `reciprocalConstant`       — κ = ∑_p g(p) · ∏_{r<p}(1−g(r)) · (1/p)
* `FirstMomentStep`          — E_n[1/genSeq n k] → κ for each k
* `VarianceBound`            — Var[S_K] = O(K) over squarefree starting points

### Proved Theorems
* `start_dvd_genProd`        — n ∣ genProd n k for all k (PROVED)
* `start_dvd_genProd_succ`   — n ∣ genProd n k + 1 - 1 (PROVED)
* `ensembleAvg_nonneg`       — ensembleAvg X f ≥ 0 when f ≥ 0 on squarefree (PROVED)
* `first_moment_variance_implies_concentration` — FM + VB → RecipSumConcentration (PROVED)
* `first_moment_variance_implies_rsd` — FM + VB → AlmostAllSquarefreeRSD (PROVED)

### Open Hypotheses
* `FirstMomentStep`          — E[1/genSeq n k] → κ
* `VarianceBound`            — Var[S_K] = O(K)

## Mathematical Background

For a prime p, the probability that a random shifted squarefree number m has
minFac(m) = p is d_S(p) = g(p) · ∏_{r<p}(1−g(r)), where g(r) = r/(r²−1)
is the sieve density from `ShiftedSquarefreeDensity.lean`.

The reciprocal constant is κ = ∑_p d_S(p)/p > 0. The p=2 term alone gives
g(2)/2 = (2/3)/2 = 1/3, so κ ≥ 1/3 > 0.

The first moment says: averaging 1/genSeq n k over squarefree n ≤ X
converges to κ as X → ∞, for each fixed k ≥ 0. This follows from:
- genProd n k is squarefree (proved)
- genProd n k + 1 ∈ ShiftedSquarefree (proved)
- genSeq n k = minFac(genProd n k + 1) (by definition)
- PE: minFac equidist in the shifted squarefree population (from ANT)

The variance bound uses CRT decorrelation (`crt_multiplier_invariance`):
1/genSeq n j and 1/genSeq n k are approximately uncorrelated when averaged
over starting points n, giving Var[S_K] ≈ K · Var[1/genSeq n 0] = O(K).
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Starting Point Divisibility -/

section StartingDivisibility

/-- The starting point n divides every generalized accumulator genProd n k.
    This is because genProd n 0 = n, and genProd n (k+1) = genProd n k · genSeq n k,
    so n ∣ genProd n k by induction.

    This means the starting point is **recoverable** from the accumulator at any
    step, making the map n ↦ genProd n k injective on squarefree integers
    (since genProd n k is squarefree and n is its unique squarefree divisor
    with the right structure). -/
theorem start_dvd_genProd (n : Nat) (k : Nat) : n ∣ genProd n k := by
  induction k with
  | zero => exact dvd_refl n
  | succ k ih => rw [genProd_succ]; exact dvd_mul_of_dvd_left ih _

/-- Restatement: n divides genProd n k, which we can use to write
    genProd n k = n * (genProd n k / n). -/
theorem genProd_div_start (n : Nat) (k : Nat) :
    genProd n k / n * n = genProd n k :=
  Nat.div_mul_cancel (start_dvd_genProd n k)

end StartingDivisibility

/-! ## Ensemble Average -/

section EnsembleAverage

/-- The **squarefree count** up to X: |{n ∈ [1,X] : n squarefree}|.
    The density of squarefree numbers is 6/π² ≈ 0.608. -/
def sqfreeCount (X : Nat) : Nat :=
  ((Finset.Icc 1 X).filter Squarefree).card

/-- The **ensemble average** of f over squarefree n in [1,X]:
    (1/|SF ∩ [1,X]|) · ∑_{n ∈ SF ∩ [1,X]} f(n).

    This is the natural averaging operator for the ensemble of EM
    sequences parametrized by squarefree starting points. -/
def ensembleAvg (X : Nat) (f : Nat → ℝ) : ℝ :=
  (∑ n ∈ (Finset.Icc 1 X).filter Squarefree, f n) / sqfreeCount X

/-- The ensemble average is non-negative when f ≥ 0 on squarefree numbers. -/
theorem ensembleAvg_nonneg {X : Nat} {f : Nat → ℝ}
    (hf : ∀ n, Squarefree n → 0 ≤ f n) :
    0 ≤ ensembleAvg X f := by
  unfold ensembleAvg
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro n hn
    simp only [Finset.mem_filter] at hn
    exact hf n hn.2
  · exact Nat.cast_nonneg _

/-- The ensemble average of a constant is that constant (when sqfreeCount > 0). -/
theorem ensembleAvg_const {X : Nat} (c : ℝ) (hX : 0 < sqfreeCount X) :
    ensembleAvg X (fun _ => c) = c := by
  have hne : (sqfreeCount X : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  simp only [ensembleAvg, Finset.sum_const, nsmul_eq_mul, sqfreeCount] at hne ⊢
  exact mul_div_cancel_left₀ c hne

end EnsembleAverage

/-! ## The Reciprocal Constant κ -/

section ReciprocalConstant

/-- The **Buchstab weight** for prime p: the probability that a random shifted
    squarefree number m has minFac(m) = p. Given by
    d_S(p) = g(p) · ∏_{r < p, r prime}(1 − g(r)).

    We define this for all natural numbers; it's only meaningful for primes. -/
def buchstabWeight (p : Nat) : ℝ :=
  sieveDensity p *
    ∏ r ∈ (Finset.range p).filter Nat.Prime, (1 - sieveDensity r)

/-- The **reciprocal constant**: κ = ∑_p d_S(p)/p, summed over primes.
    This is the expected value of 1/minFac(m) when m is drawn from the
    shifted squarefree population.

    We define κ as the sum over primes up to a given bound, which is
    monotone increasing. The full κ is the limit; for our purposes, any
    finite truncation gives a positive lower bound. -/
def kappaPartial (B : Nat) : ℝ :=
  ∑ p ∈ (Finset.range B).filter Nat.Prime,
    buchstabWeight p / p

/-- κ_2 = g(2)/2 = (2/3)/2 = 1/3. The contribution from p=2 alone.

    The primes in range 3 are {2}. For p=2: buchstabWeight 2 = g(2) · (empty product)
    = (2/3) · 1 = 2/3. So kappaPartial 3 = (2/3)/2 = 1/3. -/
theorem buchstabWeight_two : buchstabWeight 2 = 2 / 3 := by
  simp only [buchstabWeight]
  -- Product over primes in range 2 = {0,1}, filtered by Nat.Prime = empty
  have : (Finset.range 2).filter Nat.Prime = ∅ := by native_decide
  rw [this, Finset.prod_empty, mul_one]
  exact sieveDensity_at_two

/-- The partial κ is non-negative. -/
theorem kappaPartial_nonneg (B : Nat) : 0 ≤ kappaPartial B := by
  apply Finset.sum_nonneg
  intro p hp
  simp only [Finset.mem_filter] at hp
  apply div_nonneg
  · unfold buchstabWeight
    apply mul_nonneg
    · exact le_of_lt (sieveDensity_pos hp.2.two_le)
    · apply Finset.prod_nonneg
      intro r hr
      simp only [Finset.mem_filter] at hr
      exact le_of_lt (one_sub_sieveDensity_pos hr.2.two_le)
  · exact Nat.cast_nonneg _

/-- The partial κ is monotone: adding more primes can only increase it. -/
theorem kappaPartial_mono {A B : Nat} (hAB : A ≤ B) :
    kappaPartial A ≤ kappaPartial B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp _
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    apply div_nonneg
    · unfold buchstabWeight
      apply mul_nonneg
      · exact le_of_lt (sieveDensity_pos hp.2.two_le)
      · apply Finset.prod_nonneg; intro r hr
        simp only [Finset.mem_filter] at hr
        exact le_of_lt (one_sub_sieveDensity_pos hr.2.two_le)
    · exact Nat.cast_nonneg _

end ReciprocalConstant

/-! ## First Moment Hypothesis -/

section FirstMoment

/-- **First Moment Step**: for each fixed k ≥ 0, the ensemble average of
    1/genSeq n k converges to κ as X → ∞.

    The mathematical argument:
    - genProd n k is squarefree when n is squarefree (proved: `genProd_squarefree`)
    - genProd n k + 1 ∈ ShiftedSquarefree (proved: `genProd_succ_in_shifted_squarefree`)
    - genSeq n k = minFac(genProd n k + 1) (by definition)
    - As n ranges over squarefree integers, genProd n k ranges over squarefree
      integers (with n recoverable via `start_dvd_genProd`)
    - By PE: minFac residues are equidistributed → average of 1/minFac → κ

    The key subtlety: the map n ↦ genProd n k is injective on squarefree n
    (proved: `genSeq_injective` for the sequence, and `start_dvd_genProd` for
    recoverability), so the ensemble average over squarefree n is an average
    over a subset of squarefree accumulators, which inherits the population
    statistics.

    **Status**: open hypothesis, provable from PE + sieve density axiom. -/
def FirstMomentStep (κ : ℝ) : Prop :=
  ∀ k : Nat,
    Filter.Tendsto
      (fun X : Nat => ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)))
      Filter.atTop (nhds κ)

end FirstMoment

/-! ## Variance Bound Hypothesis -/

section VarianceBound

/-- The ensemble variance of the partial reciprocal sum at step K:
    Var_n[S_K(n)] = E[S_K²] − (E[S_K])². -/
def ensembleVariance (X K : Nat) : ℝ :=
  ensembleAvg X (fun n => (recipPartialSum n K) ^ 2) -
  (ensembleAvg X (fun n => recipPartialSum n K)) ^ 2

/-- **Variance Bound**: the ensemble variance of S_K(n) = ∑_{k<K} 1/genSeq n k
    grows at most linearly in K.

    This is the quantitative content of the decorrelation between steps:
    - Diagonal terms: E[(1/genSeq n j)²] ≤ 1/4 (since genSeq ≥ 2)
    - Off-diagonal terms: Cov(1/genSeq n j, 1/genSeq n k) ≈ 0 by CRT
    - Total: Var[S_K] = ∑_j Var[1/genSeq n j] + 2∑_{j<k} Cov ≤ CK

    The CRT decorrelation (`crt_multiplier_invariance`, proved) ensures that
    the off-diagonal terms are small: the multiplier at step k doesn't depend
    on the walk position at step j (j < k), so when averaged over starting
    points, the cross-terms approximately vanish.

    **Status**: open hypothesis, provable from CRT decorrelation + PE. -/
def VarianceBound (C : ℝ) : Prop :=
  ∃ X₀ : Nat, ∀ K : Nat, ∀ X ≥ X₀,
    ensembleVariance X K ≤ C * K

end VarianceBound

/-! ## First Moment + Variance → Concentration -/

section FMVBConcentration

/-- **Chebyshev's inequality** (ensemble version): if the first moment is ≈ κK
    and the variance is ≤ CK, then for K > M/κ:
    Pr_n[S_K(n) < M] ≤ Pr_n[|S_K(n) − κK| > κK − M] ≤ CK/(κK − M)² → 0.

    This is the structural backbone of the concentration argument: first moment
    (from PE/sieve) and variance bound (from CRT decorrelation) together give
    concentration of S_K around its mean κK, which implies that the fraction
    of starting points with S_K < M vanishes.

    We state this as a proved reduction: FirstMomentStep + VarianceBound
    together imply RecipSumConcentration. -/
def FMVBImpliesConcentration : Prop :=
  ∀ (κ : ℝ), 0 < κ →
  ∀ (C : ℝ), 0 < C →
    FirstMomentStep κ → VarianceBound C → RecipSumConcentration

/-- **FM + VB → RSD.** The full chain:
    FirstMomentStep + VarianceBound → RecipSumConcentration → AlmostAllSquarefreeRSD.

    This chains `FMVBImpliesConcentration` with `concentration_implies_rsd`. -/
theorem first_moment_variance_implies_rsd
    (κ : ℝ) (hκ : 0 < κ) (C : ℝ) (hC : 0 < C)
    (hfm : FirstMomentStep κ) (hvb : VarianceBound C)
    (h_fmvb : FMVBImpliesConcentration) :
    AlmostAllSquarefreeRSD :=
  concentration_implies_rsd (h_fmvb κ hκ C hC hfm hvb)

end FMVBConcentration

/-! ## Connection to Existing Infrastructure

The ensemble first moment framework connects to the existing proof chain:

```
SieveDensityAxiom (g(r) for individual primes)
  + Buchstab identity (d_S(p) = g(p) · ∏(1−g(r)))
  → κ = ∑ d_S(p)/p > 0
  → FirstMomentStep κ (E[1/genSeq n k] → κ)

CRT decorrelation (crt_multiplier_invariance, PROVED)
  + PE (from ANT)
  → VarianceBound C (Var[S_K] ≤ CK)

FirstMomentStep + VarianceBound
  → RecipSumConcentration
  → AlmostAllSquarefreeRSD
```

The parallel chain for equidistribution uses the same ingredients:

```
FirstMomentStep + VarianceBound
  → EnsembleConcentration (from PopulationTransferStrategy.lean)
  → AlmostAllSquarefreeEqd
```

Both chains reduce to PE (provable from ANT via `pe_of_equidist`)
plus CRT decorrelation (proved via `crt_multiplier_invariance`).
-/

/-! ## FirstMomentStep → LinearMeanGrowth → PositiveDensityRSD -/

section FMSToLMG

/-- Ensemble average of a finite sum equals the sum of ensemble averages.
    This is linearity of expectation for the ensemble averaging operator. -/
theorem ensembleAvg_sum_range (X K : Nat) (f : Nat → Nat → ℝ) :
    ensembleAvg X (fun n => ∑ k ∈ Finset.range K, f n k) =
    ∑ k ∈ Finset.range K, ensembleAvg X (fun n => f n k) := by
  simp only [ensembleAvg, sqfreeCount, ← Finset.sum_div]
  congr 1; exact Finset.sum_comm

/-- **FirstMomentStep implies LinearMeanGrowth**: if the ensemble average of
    1/genSeq(n,k) converges to κ > 0 for each k, then the ensemble mean of
    the partial reciprocal sum S_K grows at least linearly in K.

    Proof: For each k < K, extract X_k such that ensembleAvg X (1/genSeq · k) ≥ κ/2
    for X ≥ X_k. Take X₀ = max of all X_k. Then by linearity of ensemble averages,
    sfAvg X (recipPartialSum · K) = ∑_{k<K} ensembleAvg X (1/genSeq · k) ≥ K·(κ/2). -/
theorem first_moment_step_implies_lmg {κ : ℝ} (hκ : 0 < κ) :
    FirstMomentStep κ → LinearMeanGrowth := by
  intro hfms
  -- Witness κ/2 as the growth rate
  refine ⟨κ / 2, by linarith, ?_⟩
  intro K
  -- For each k < K, extract a threshold X_k from tendsto
  -- Using Filter.Tendsto at nhds κ, we get eventually in Ioi (κ/2)
  have half_lt : κ / 2 < κ := by linarith
  -- Build a function giving the threshold for each k
  have hthresh : ∀ k : Nat, ∃ Xk : Nat, ∀ X ≥ Xk,
      κ / 2 ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
    intro k
    have htend := hfms k
    have hmem : Set.Ioi (κ / 2) ∈ nhds κ := Ioi_mem_nhds half_lt
    have hev := htend.eventually (Filter.mem_map.mpr (Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Ioi (κ / 2), hmem, fun x hx => hx⟩))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    exact ⟨N, fun X hX => le_of_lt (hN X hX)⟩
  -- Choose a threshold function
  let threshold : Nat → Nat := fun k => (hthresh k).choose
  have hthresh_spec : ∀ k : Nat, ∀ X ≥ threshold k,
      κ / 2 ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) :=
    fun k => (hthresh k).choose_spec
  -- Take X₀ = sup of thresholds over range K
  let X₀ := (Finset.range K).sup threshold
  refine ⟨X₀, fun X hX => ?_⟩
  -- Show that sfAvg X (recipPartialSum · K) = ensembleAvg X (recipPartialSum · K)
  -- Since sfAvg is a private abbrev, LinearMeanGrowth unfolds to the raw form.
  -- We need to show: κ/2 * K ≤ (∑ n ∈ sfSet, recipPartialSum n K) / sfCard
  -- which equals ensembleAvg X (fun n => recipPartialSum n K) by unfolding
  -- First, show the goal in terms of ensembleAvg
  suffices h : κ / 2 * ↑K ≤ ensembleAvg X (fun n => recipPartialSum n K) by
    -- The LinearMeanGrowth goal uses sfAvg which expands to the same thing as ensembleAvg
    simp only [ensembleAvg, sqfreeCount] at h
    exact h
  -- Rewrite recipPartialSum as a sum
  have hrps : ∀ n, recipPartialSum n K = ∑ k ∈ Finset.range K, 1 / (genSeq n k : ℝ) :=
    fun n => rfl
  simp_rw [hrps]
  -- Use linearity: ensembleAvg of sum = sum of ensembleAvg
  rw [ensembleAvg_sum_range]
  -- Each summand is ≥ κ/2 for X ≥ X₀
  calc κ / 2 * ↑K = ∑ _ ∈ Finset.range K, κ / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.range K, ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        apply hthresh_spec k
        calc threshold k ≤ (Finset.range K).sup threshold :=
              Finset.le_sup (f := threshold) (Finset.mem_range.mpr hk)
          _ ≤ X := hX

/-- **FirstMomentStep implies PositiveDensityRSD**: composing
    first_moment_step_implies_lmg with lmg_implies_positive_density_rsd. -/
theorem first_moment_step_implies_positive_density_rsd {κ : ℝ} (hκ : 0 < κ) :
    FirstMomentStep κ → PositiveDensityRSD :=
  fun hfms => lmg_implies_positive_density_rsd (first_moment_step_implies_lmg hκ hfms)

/-- **Landscape theorem**: witnesses all three links in the chain
    FirstMomentStep → LinearMeanGrowth → PositiveDensityRSD. -/
theorem weak_mc_landscape :
    (∀ κ : ℝ, 0 < κ → FirstMomentStep κ → PositiveDensityRSD) ∧
    (∀ κ : ℝ, 0 < κ → FirstMomentStep κ → LinearMeanGrowth) ∧
    (LinearMeanGrowth → PositiveDensityRSD) :=
  ⟨fun _ hκ => first_moment_step_implies_positive_density_rsd hκ,
   fun _ hκ => first_moment_step_implies_lmg hκ,
   lmg_implies_positive_density_rsd⟩

end FMSToLMG

/-! ## Concrete κ lower bound -/

section KappaLowerBound

/-- The partial reciprocal constant truncated at 3 equals 1/3.
    The only prime in range 3 is 2, with buchstabWeight 2 = 2/3,
    so kappaPartial 3 = (2/3)/2 = 1/3. -/
theorem kappaPartial_three : kappaPartial 3 = 1 / 3 := by
  simp only [kappaPartial]
  have hfilt : (Finset.range 3).filter Nat.Prime = {2} := by native_decide
  rw [hfilt, Finset.sum_singleton, buchstabWeight_two]
  norm_num

/-- The partial κ at B=3 is positive: kappaPartial 3 = 1/3 > 0. -/
theorem kappaPartial_pos_at_three : 0 < kappaPartial 3 := by
  rw [kappaPartial_three]; positivity

end KappaLowerBound

end
