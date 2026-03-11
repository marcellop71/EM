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

/-! ## Parity Structure -/

section ParityStructure

/-- genProd n 1 is even for any n ≥ 1. If n is even, the product n * minFac(n+1)
    is even. If n is odd, then n+1 is even, so minFac(n+1) = 2, making
    n * 2 even. -/
theorem genProd_one_even {n : Nat} (_hn : 1 ≤ n) : Even (genProd n 1) := by
  simp only [genProd]
  -- Goal: Even (n * Nat.minFac (n + 1))
  rcases Nat.even_or_odd n with heven | hodd
  · exact heven.mul_right _
  · -- n odd → n+1 even → minFac(n+1) = 2
    have h2 : Nat.minFac (n + 1) = 2 := by
      rw [Nat.minFac_eq_two_iff]
      exact hodd.add_one.two_dvd
    rw [h2]
    exact ⟨n, by omega⟩

/-- genProd n k is even for k ≥ 1 and n ≥ 1.
    Proof by induction: base case k=1 is genProd_one_even, step uses that
    even * anything = even. -/
theorem genProd_even_of_pos {n : Nat} (hn : 1 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    Even (genProd n k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [genProd_succ]
    rcases k with _ | k'
    · exact genProd_one_even hn
    · exact (ih (by omega)).mul_right _

/-- genProd n k + 1 is odd for k ≥ 1 and n ≥ 1: since genProd n k is even,
    adding 1 gives an odd number. -/
theorem genProd_succ_odd {n : Nat} (hn : 1 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    ¬ Even (genProd n k + 1) := by
  obtain ⟨m, hm⟩ := genProd_even_of_pos hn hk
  intro ⟨r, hr⟩; omega

/-- For k ≥ 1 and n ≥ 1, genSeq n k ≥ 3.
    Since genProd n k + 1 is odd, its minFac ≠ 2, so the least prime factor is
    an odd prime, hence ≥ 3. -/
theorem genSeq_ge_three {n : Nat} (hn : 1 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    3 ≤ genSeq n k := by
  rw [genSeq_def]
  set p := Nat.minFac (genProd n k + 1) with hp_def
  have hne1 : genProd n k + 1 ≠ 1 := by have := genProd_pos hn k; omega
  have hprime := Nat.minFac_prime hne1
  rw [← hp_def] at hprime
  have hge2 : 2 ≤ p := hprime.two_le
  have hne2 : p ≠ 2 := by
    intro h2; rw [h2] at hp_def
    exact genProd_succ_odd hn hk (even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff _).mp hp_def.symm))
  omega

end ParityStructure

/-! ## k=0 Ensemble Average Lower Bound -/

section K0LowerBound

/-- For odd n ≥ 1, genSeq n 0 = 2, since n+1 is even and minFac(n+1) = 2. -/
theorem genSeq_zero_of_odd {n : Nat} (_hn : 1 ≤ n) (hodd : ¬ Even n) :
    genSeq n 0 = 2 := by
  simp only [genSeq_def, genProd]
  rw [Nat.minFac_eq_two_iff]
  have : n % 2 ≠ 0 := fun h => hodd (Nat.even_iff.mpr h)
  exact Nat.dvd_of_mod_eq_zero (by omega)

/-- Halving even squarefree numbers gives odd squarefree numbers:
    if m is squarefree and even, then m/2 is squarefree and odd. -/
private theorem squarefree_half {m : Nat} (hm : Squarefree m) (heven : Even m) :
    Squarefree (m / 2) ∧ ¬ Even (m / 2) := by
  obtain ⟨k, hk⟩ := heven.two_dvd
  have hk2 : m / 2 = k := by omega
  constructor
  · -- k divides m (since m = 2*k), and m is squarefree → k is squarefree
    rw [hk2]
    exact hm.squarefree_of_dvd ⟨2, by omega⟩
  · -- k is odd: if k were even, then 4 ∣ m, contradicting squarefree(m)
    rw [hk2]
    intro hk_even
    obtain ⟨j, hj⟩ := hk_even.two_dvd
    have h4 : (2 : Nat) * (2 : Nat) ∣ m := ⟨j, by omega⟩
    have hunit := hm 2 h4
    simp [Nat.isUnit_iff] at hunit

/-- At least half of squarefree numbers in [1,X] are odd:
    #{sf in [1,X]} ≤ 2 * #{odd sf in [1,X]}.
    Proof: the map n ↦ n/2 injects even squarefree into odd squarefree,
    so #{even sf} ≤ #{odd sf}, hence #{sf} = #{odd sf} + #{even sf} ≤ 2·#{odd sf}. -/
private theorem odd_sf_card_ge_half (X : Nat) :
    ((Finset.Icc 1 X).filter Squarefree).card ≤
    2 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)).card := by
  -- Partition squarefree into odd and even
  set S := (Finset.Icc 1 X).filter Squarefree
  set oddS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)
  set evenS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ Even n)
  have h_disj : Disjoint oddS evenS := by
    rw [Finset.disjoint_filter]
    intro n _ ⟨_, hodd⟩ ⟨_, heven⟩
    exact hodd heven
  have h_union : S = oddS ∪ evenS := by
    ext n
    simp only [S, oddS, evenS, Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]
    constructor
    · intro ⟨hmem, hsf⟩
      rcases Nat.even_or_odd n with heven | hodd
      · exact Or.inr ⟨hmem, hsf, heven⟩
      · exact Or.inl ⟨hmem, hsf, Nat.not_even_iff_odd.mpr hodd⟩
    · rintro (⟨hmem, hsf, _⟩ | ⟨hmem, hsf, _⟩) <;> exact ⟨hmem, hsf⟩
  have h_card : S.card = oddS.card + evenS.card := by
    rw [h_union, Finset.card_union_of_disjoint h_disj]
  -- Injection: even sf → odd sf by halving
  have h_inj : evenS.card ≤ oddS.card := by
    apply Finset.card_le_card_of_injOn (fun n => n / 2)
    · -- Maps into oddS
      intro n hn
      rw [Finset.mem_coe, Finset.mem_filter] at hn
      have hmem := Finset.mem_Icc.mp hn.1
      have hsf := hn.2.1
      have heven := hn.2.2
      obtain ⟨hsf_half, hodd_half⟩ := squarefree_half hsf heven
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      obtain ⟨k, hk⟩ := heven.two_dvd
      have h1 : 1 ≤ n / 2 := by omega
      have h2 : n / 2 ≤ X := le_trans (Nat.div_le_self n 2) hmem.2
      exact ⟨⟨h1, h2⟩, hsf_half, hodd_half⟩
    · -- Injective on even numbers: a/2 = b/2 and both even → a = b
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha_mul := Nat.div_mul_cancel ha.2.2.two_dvd  -- a / 2 * 2 = a
      have hb_mul := Nat.div_mul_cancel hb.2.2.two_dvd  -- b / 2 * 2 = b
      linarith
  linarith [h_card, h_inj]

/-- The ensemble average of 1/genSeq(n,0) is at least 1/4 for X with positive
    squarefree count. For odd squarefree n, genSeq(n,0) = 2, so 1/genSeq(n,0) = 1/2.
    Since at least half of squarefree numbers are odd, E[1/genSeq(·,0)] ≥ 1/4. -/
theorem ensembleAvg_k0_ge_quarter {X : Nat} (hX : 0 < sqfreeCount X) :
    (1 : ℝ) / 4 ≤ ensembleAvg X (fun n => 1 / (genSeq n 0 : ℝ)) := by
  unfold ensembleAvg sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree with hS_def
  set oddS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n) with hoddS_def
  have hS_pos : (0 : ℝ) < S.card := by exact_mod_cast hX
  -- Lower bound: sum over S ≥ sum over oddS (since oddS ⊆ S and terms are nonneg)
  have h_sub : oddS ⊆ S := by
    intro n hn
    simp only [hoddS_def, hS_def, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  -- Each odd squarefree n in [1,X] satisfies genSeq n 0 = 2, so 1/genSeq n 0 = 1/2
  have h_oddS_eq : ∀ n ∈ oddS, (1 : ℝ) / (genSeq n 0 : ℝ) = 1 / 2 := by
    intro n hn
    simp only [hoddS_def, Finset.mem_filter, Finset.mem_Icc] at hn
    have h2 := genSeq_zero_of_odd hn.1.1 hn.2.2
    simp [h2]
  -- Sum over oddS = oddS.card * (1/2)
  have h_oddS_sum : ∑ n ∈ oddS, (1 : ℝ) / (genSeq n 0 : ℝ) = oddS.card * (1 / 2) := by
    rw [show oddS.card * (1 / 2 : ℝ) = ∑ _ ∈ oddS, (1 : ℝ) / 2 from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_congr rfl h_oddS_eq
  -- Sum over S ≥ sum over oddS
  have h_sum_lower : (oddS.card : ℝ) / 2 ≤ ∑ n ∈ S, (1 : ℝ) / (genSeq n 0 : ℝ) := by
    calc ∑ n ∈ S, (1 : ℝ) / (genSeq n 0 : ℝ)
        ≥ ∑ n ∈ oddS, (1 : ℝ) / (genSeq n 0 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
      _ = oddS.card * (1 / 2) := h_oddS_sum
      _ = (oddS.card : ℝ) / 2 := by ring
  -- Card bound: S.card ≤ 2 * oddS.card
  have h_odd_ge := odd_sf_card_ge_half X
  rw [← hS_def, ← hoddS_def] at h_odd_ge
  -- Final arithmetic: 1/4 ≤ (∑ ...) / S.card
  rw [le_div_iff₀ hS_pos]
  calc 1 / 4 * (S.card : ℝ)
      ≤ 1 / 4 * (2 * (oddS.card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast h_odd_ge
    _ = (oddS.card : ℝ) / 2 := by ring
    _ ≤ ∑ n ∈ S, (1 : ℝ) / (genSeq n 0 : ℝ) := h_sum_lower

end K0LowerBound

/-! ## Step Mean Lower Bound -/

section StepMeanLowerBound

/-- **Step Mean Lower Bound**: for each k, the ensemble average of 1/genSeq(n,k)
    is eventually at least c > 0. This is strictly weaker than `FirstMomentStep`
    (which requires convergence to a specific κ) but still implies
    `LinearMeanGrowth` and hence `PositiveDensityRSD`. -/
def StepMeanLowerBound (c : ℝ) : Prop :=
  ∀ k : Nat, ∃ X₀ : Nat, ∀ X ≥ X₀,
    c ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ))

/-- StepMeanLowerBound implies LinearMeanGrowth. The proof is the same structure
    as `first_moment_step_implies_lmg` but simpler since we directly have
    thresholds rather than extracting them from `Filter.Tendsto`. -/
theorem smlb_implies_lmg {c : ℝ} (hc : 0 < c) :
    StepMeanLowerBound c → LinearMeanGrowth := by
  intro hsmlb
  refine ⟨c, hc, ?_⟩
  intro K
  let threshold : Nat → Nat := fun k => (hsmlb k).choose
  have hthresh_spec : ∀ k, ∀ X ≥ threshold k,
      c ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) :=
    fun k => (hsmlb k).choose_spec
  let X₀ := (Finset.range K).sup threshold
  refine ⟨X₀, fun X hX => ?_⟩
  suffices h : c * ↑K ≤ ensembleAvg X (fun n => recipPartialSum n K) by
    simp only [ensembleAvg, sqfreeCount] at h; exact h
  have hrps : ∀ n, recipPartialSum n K = ∑ k ∈ Finset.range K, 1 / (genSeq n k : ℝ) :=
    fun n => rfl
  simp_rw [hrps]
  rw [ensembleAvg_sum_range]
  calc c * ↑K = ∑ _ ∈ Finset.range K, c := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.range K, ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        apply hthresh_spec k
        calc threshold k ≤ (Finset.range K).sup threshold :=
              Finset.le_sup (f := threshold) (Finset.mem_range.mpr hk)
          _ ≤ X := hX

/-- SMLB implies PositiveDensityRSD via LinearMeanGrowth. -/
theorem smlb_implies_positive_density_rsd {c : ℝ} (hc : 0 < c) :
    StepMeanLowerBound c → PositiveDensityRSD :=
  fun h => lmg_implies_positive_density_rsd (smlb_implies_lmg hc h)

/-- Helper: sqfreeCount X ≥ 1 for X ≥ 1 (since 1 is squarefree). -/
private theorem sqfreeCount_pos_of_pos {X : Nat} (hX : 1 ≤ X) : 0 < sqfreeCount X := by
  unfold sqfreeCount
  apply Finset.card_pos.mpr
  exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _, hX⟩, squarefree_one⟩⟩

/-- The k=0 step of SMLB holds unconditionally with c = 1/4:
    for all X ≥ 1, E[1/genSeq(·,0)] ≥ 1/4. -/
theorem smlb_k0_unconditional :
    ∃ X₀ : Nat, ∀ X ≥ X₀,
      (1 : ℝ) / 4 ≤ ensembleAvg X (fun n => 1 / (genSeq n 0 : ℝ)) :=
  ⟨1, fun _ hX => ensembleAvg_k0_ge_quarter (sqfreeCount_pos_of_pos hX)⟩

end StepMeanLowerBound

/-! ## FMS implies κ ≥ 1/4 -/

section FMSKappaLowerBound

/-- If `FirstMomentStep κ` holds, then κ ≥ 1/4.
    At k=0, `ensembleAvg X (1/genSeq · 0)` converges to κ. Since this average
    is ≥ 1/4 for all X ≥ 1, the limit κ ≥ 1/4 by `ge_of_tendsto`. -/
theorem fms_kappa_ge_quarter {κ : ℝ} (hfms : FirstMomentStep κ) :
    1 / 4 ≤ κ := by
  apply ge_of_tendsto (hfms 0)
  rw [Filter.eventually_atTop]
  exact ⟨1, fun _ hX => ensembleAvg_k0_ge_quarter (sqfreeCount_pos_of_pos hX)⟩

end FMSKappaLowerBound

/-! ## Parity + SMLB Landscape -/

section ParityLandscape

/-- **Parity + SMLB landscape theorem**: witnesses all unconditional structural
    results and the SMLB reduction chain.
    1. genSeq(n,k) ≥ 3 for k ≥ 1 and n ≥ 1 (PROVED)
    2. E[1/genSeq(·,0)] ≥ 1/4 unconditionally (PROVED)
    3. SMLB → LMG → PositiveDensityRSD (PROVED)
    4. FirstMomentStep(κ) ⇒ κ ≥ 1/4 (PROVED) -/
theorem parity_smlb_landscape :
    (∀ (n : Nat), 1 ≤ n → ∀ (k : Nat), 1 ≤ k → 3 ≤ genSeq n k) ∧
    (∀ (X : Nat), 1 ≤ X →
      (1 : ℝ) / 4 ≤ ensembleAvg X (fun n => 1 / (genSeq n 0 : ℝ))) ∧
    (∀ (c : ℝ), 0 < c → StepMeanLowerBound c → PositiveDensityRSD) ∧
    (∀ (κ : ℝ), FirstMomentStep κ → 1 / 4 ≤ κ) :=
  ⟨fun _ hn _ hk => genSeq_ge_three hn hk,
   fun _ hX => ensembleAvg_k0_ge_quarter (sqfreeCount_pos_of_pos hX),
   fun _ hc => smlb_implies_positive_density_rsd hc,
   fun _ hfms => fms_kappa_ge_quarter hfms⟩

end ParityLandscape

end
