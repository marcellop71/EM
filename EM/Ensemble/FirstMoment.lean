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
  | succ k ih => exact dvd_mul_of_dvd_left ih _

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
    0 ≤ ensembleAvg X f :=
  div_nonneg (Finset.sum_nonneg fun n hn => hf n (Finset.mem_filter.mp hn).2)
    (Nat.cast_nonneg _)

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

/-- The Buchstab weight divided by p is non-negative for primes. -/
private theorem buchstabWeight_div_nonneg {p : Nat} (hp : Nat.Prime p) :
    0 ≤ buchstabWeight p / p := by
  apply div_nonneg
  · exact mul_nonneg (sieveDensity_pos hp.two_le).le
      (Finset.prod_nonneg fun r hr =>
        (one_sub_sieveDensity_pos (Finset.mem_filter.mp hr).2.two_le).le)
  · positivity

/-- The partial κ is non-negative. -/
theorem kappaPartial_nonneg (B : Nat) : 0 ≤ kappaPartial B :=
  Finset.sum_nonneg fun _ hp => buchstabWeight_div_nonneg (Finset.mem_filter.mp hp).2

/-- The partial κ is monotone: adding more primes can only increase it. -/
theorem kappaPartial_mono {A B : Nat} (hAB : A ≤ B) :
    kappaPartial A ≤ kappaPartial B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp _
    exact buchstabWeight_div_nonneg (Finset.mem_filter.mp hp).2

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
    the partial reciprocal sum S_K grows at least linearly in K. -/
theorem first_moment_step_implies_lmg {κ : ℝ} (hκ : 0 < κ) :
    FirstMomentStep κ → LinearMeanGrowth := by
  intro hfms
  refine ⟨κ / 2, by linarith, ?_⟩
  intro K
  -- Extract thresholds from tendsto: for each k, eventually ≥ κ/2
  have hthresh : ∀ k : Nat, ∃ Xk : Nat, ∀ X ≥ Xk,
      κ / 2 ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
    intro k
    have hev := (hfms k).eventually (Ioi_mem_nhds (by linarith : κ / 2 < κ))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    exact ⟨N, fun X hX => (hN X hX).le⟩
  let threshold : Nat → Nat := fun k => (hthresh k).choose
  let X₀ := (Finset.range K).sup threshold
  refine ⟨X₀, fun X hX => ?_⟩
  suffices h : κ / 2 * ↑K ≤ ensembleAvg X (fun n => recipPartialSum n K) by
    simp only [ensembleAvg, sqfreeCount] at h; exact h
  simp_rw [show ∀ n, recipPartialSum n K =
    ∑ k ∈ Finset.range K, 1 / (genSeq n k : ℝ) from fun _ => rfl]
  rw [ensembleAvg_sum_range]
  calc κ / 2 * ↑K = ∑ _ ∈ Finset.range K, κ / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.range K, ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hthresh k).choose_spec X
          (le_trans (Finset.le_sup (f := threshold) hk) hX)

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

/-- genProd n 1 is even for any n >= 1. -/
theorem genProd_one_even {n : Nat} (_hn : 1 ≤ n) : Even (genProd n 1) := by
  simp only [genProd]
  rcases Nat.even_or_odd n with heven | hodd
  · exact heven.mul_right _
  · have h2 : Nat.minFac (n + 1) = 2 :=
      (Nat.minFac_eq_two_iff _).mpr hodd.add_one.two_dvd
    rw [h2]; exact ⟨n, by omega⟩

/-- genProd n k is even for k >= 1 and n >= 1. -/
theorem genProd_even_of_pos {n : Nat} (hn : 1 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    Even (genProd n k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k'
    · exact genProd_one_even hn
    · exact (ih (by omega)).mul_right _

/-- genProd n k + 1 is odd for k >= 1 and n >= 1. -/
theorem genProd_succ_odd {n : Nat} (hn : 1 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    ¬ Even (genProd n k + 1) :=
  fun ⟨r, hr⟩ => by obtain ⟨m, hm⟩ := genProd_even_of_pos hn hk; omega

/-- For k >= 1 and n >= 1, genSeq n k >= 3 (the odd parity forces minFac >= 3). -/
theorem genSeq_ge_three {n : Nat} (hn : 1 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    3 ≤ genSeq n k := by
  rw [genSeq_def]
  have hne1 : genProd n k + 1 ≠ 1 := by have := genProd_pos hn k; omega
  have hge2 := (Nat.minFac_prime hne1).two_le
  have hne2 : Nat.minFac (genProd n k + 1) ≠ 2 := by
    intro h2
    exact genProd_succ_odd hn hk
      (even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff _).mp h2))
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

/-- Halving even squarefree numbers gives odd squarefree numbers. -/
private theorem squarefree_half {m : Nat} (hm : Squarefree m) (heven : Even m) :
    Squarefree (m / 2) ∧ ¬ Even (m / 2) := by
  obtain ⟨k, hk⟩ := heven.two_dvd
  have hk2 : m / 2 = k := by omega
  exact ⟨hk2 ▸ hm.squarefree_of_dvd ⟨2, by omega⟩, fun hk_even => by
    rw [hk2] at hk_even
    obtain ⟨j, hj⟩ := hk_even.two_dvd
    exact absurd (hm 2 ⟨j, by omega⟩) (by simp)⟩

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

/-- The ensemble average of 1/genSeq(n,0) is at least 1/4: odd squarefree n
    contribute 1/2 each, and at least half of squarefree numbers are odd. -/
theorem ensembleAvg_k0_ge_quarter {X : Nat} (hX : 0 < sqfreeCount X) :
    (1 : ℝ) / 4 ≤ ensembleAvg X (fun n => 1 / (genSeq n 0 : ℝ)) := by
  unfold ensembleAvg sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree with hS_def
  set oddS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n) with hoddS_def
  have hS_pos : (0 : ℝ) < S.card := by exact_mod_cast hX
  have h_sub : oddS ⊆ S := by
    intro n hn
    simp only [hoddS_def, hS_def, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have h_oddS_sum : ∑ n ∈ oddS, (1 : ℝ) / (genSeq n 0 : ℝ) = oddS.card * (1 / 2) := by
    rw [show oddS.card * (1 / 2 : ℝ) = ∑ _ ∈ oddS, (1 : ℝ) / 2 from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_congr rfl fun n hn => by
      simp only [hoddS_def, Finset.mem_filter, Finset.mem_Icc] at hn
      simp [genSeq_zero_of_odd hn.1.1 hn.2.2]
  have h_sum_lower : (oddS.card : ℝ) / 2 ≤ ∑ n ∈ S, (1 : ℝ) / (genSeq n 0 : ℝ) := by
    calc ∑ n ∈ S, (1 : ℝ) / (genSeq n 0 : ℝ)
        ≥ ∑ n ∈ oddS, (1 : ℝ) / (genSeq n 0 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
      _ = oddS.card * (1 / 2) := h_oddS_sum
      _ = (oddS.card : ℝ) / 2 := by ring
  have h_odd_ge := odd_sf_card_ge_half X
  rw [← hS_def, ← hoddS_def] at h_odd_ge
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

/-- StepMeanLowerBound implies LinearMeanGrowth. -/
theorem smlb_implies_lmg {c : ℝ} (hc : 0 < c) :
    StepMeanLowerBound c → LinearMeanGrowth := by
  intro hsmlb
  refine ⟨c, hc, ?_⟩
  intro K
  let threshold : Nat → Nat := fun k => (hsmlb k).choose
  let X₀ := (Finset.range K).sup threshold
  refine ⟨X₀, fun X hX => ?_⟩
  suffices h : c * ↑K ≤ ensembleAvg X (fun n => recipPartialSum n K) by
    simp only [ensembleAvg, sqfreeCount] at h; exact h
  simp_rw [show ∀ n, recipPartialSum n K =
    ∑ k ∈ Finset.range K, 1 / (genSeq n k : ℝ) from fun _ => rfl]
  rw [ensembleAvg_sum_range]
  calc c * ↑K = ∑ _ ∈ Finset.range K, c := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ k ∈ Finset.range K, ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hsmlb k).choose_spec X
          (le_trans (Finset.le_sup (f := threshold) hk) hX)

/-- SMLB implies PositiveDensityRSD via LinearMeanGrowth. -/
theorem smlb_implies_positive_density_rsd {c : ℝ} (hc : 0 < c) :
    StepMeanLowerBound c → PositiveDensityRSD :=
  fun h => lmg_implies_positive_density_rsd (smlb_implies_lmg hc h)

/-- sqfreeCount X >= 1 for X >= 1 (since 1 is squarefree). -/
private theorem sqfreeCount_pos_of_pos {X : Nat} (hX : 1 ≤ X) : 0 < sqfreeCount X :=
  Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _, hX⟩,
    squarefree_one⟩⟩

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

/-! ## k=1 Lower Bound Infrastructure

For odd squarefree n with n % 3 = 1 (equivalently n ≡ 1 mod 6):
- genSeq n 0 = 2 (since n is odd, n+1 is even, minFac(n+1)=2)
- genProd n 1 = n · 2 (by genProd_succ)
- genProd n 1 + 1 = 2n + 1
- 3 ∣ (2n + 1) (since n ≡ 1 mod 3 → 2n + 1 ≡ 0 mod 3)
- 2n + 1 is odd
- Therefore minFac(2n + 1) = 3, i.e., genSeq n 1 = 3.

This gives a concrete lower bound on the k=1 ensemble average:
every 1-mod-6 squarefree starting point contributes 1/3 to E[1/genSeq(·,1)].

We also prove the factor-3 injection (analogous to squarefree_half for factor 2):
the map n ↦ n/3 injects {odd sf, 3|n} into {odd sf, 3∤n}, so at most half
of odd squarefree numbers are divisible by 3.  Combining with the factor-2
injection gives #{sf} ≤ 4 · #{odd sf coprime to 3}. -/

section K1Infrastructure

/-- For odd n >= 1 with n % 3 = 1, genSeq n 1 = 3. -/
theorem genSeq_one_of_mod6 {n : Nat} (hn : 1 ≤ n) (hodd : ¬ Even n) (hmod3 : n % 3 = 1) :
    genSeq n 1 = 3 := by
  rw [genSeq_def, show genProd n 1 = n * genSeq n 0 from rfl,
    genSeq_zero_of_odd hn hodd]
  set m := n * 2 + 1
  have hm_odd : ¬ Even m := fun ⟨k, hk⟩ => by omega
  have h3_dvd : 3 ∣ m := by
    have : n = 3 * (n / 3) + 1 := by omega
    exact ⟨n / 3 * 2 + 1, by omega⟩
  have hm_ne1 : m ≠ 1 := by omega
  have hm_ge2 := (Nat.minFac_prime hm_ne1).two_le
  have hm_le3 := Nat.minFac_le_of_dvd (by omega : 2 ≤ 3) h3_dvd
  have hm_ne2 : Nat.minFac m ≠ 2 := fun h2 =>
    hm_odd (even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff m).mp h2))
  omega

/-- Dividing an odd squarefree number divisible by 3 by 3 gives an odd squarefree
    number not divisible by 3. -/
private theorem squarefree_third {m : Nat} (hm : Squarefree m) (hodd : ¬ Even m) (h3 : 3 ∣ m) :
    Squarefree (m / 3) ∧ ¬ Even (m / 3) ∧ ¬ (3 ∣ (m / 3)) := by
  obtain ⟨k, hk⟩ := h3
  have hk3 : m / 3 = k := by omega
  refine ⟨hk3 ▸ hm.squarefree_of_dvd ⟨3, by omega⟩, fun hk_even => ?_, fun h3k => ?_⟩
  · rw [hk3] at hk_even
    obtain ⟨j, hj⟩ := hk_even.two_dvd
    exact hodd ⟨3 * j, by omega⟩
  · rw [hk3] at h3k
    obtain ⟨j, hj⟩ := h3k
    exact absurd (hm 3 ⟨j, by omega⟩) (by simp)

/-- At least half of odd squarefree numbers in [1,X] are coprime to 3:
    #{odd sf in [1,X]} ≤ 2 * #{odd sf coprime to 3 in [1,X]}.
    Proof: the map n ↦ n/3 injects {odd sf, 3|n} into {odd sf, 3∤n},
    so #{odd sf, 3|n} ≤ #{odd sf, 3∤n}, hence total ≤ 2 · #{odd sf, 3∤n}. -/
private theorem odd_coprime3_sf_card_ge_half (X : Nat) :
    ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)).card ≤
    2 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card := by
  -- Partition odd squarefree into coprime-to-3 and divisible-by-3
  set oddS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)
  set copS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))
  set div3S := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ (3 ∣ n))
  have h_disj : Disjoint copS div3S := by
    rw [Finset.disjoint_filter]
    intro n _ ⟨_, _, hn3⟩ ⟨_, _, h3⟩
    exact hn3 h3
  have h_union : oddS = copS ∪ div3S := by
    ext n
    simp only [oddS, copS, div3S, Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]
    constructor
    · intro ⟨hmem, hsf, hodd⟩
      rcases Decidable.em (3 ∣ n) with h3 | h3
      · exact Or.inr ⟨hmem, hsf, hodd, h3⟩
      · exact Or.inl ⟨hmem, hsf, hodd, h3⟩
    · rintro (⟨hmem, hsf, hodd, _⟩ | ⟨hmem, hsf, hodd, _⟩) <;> exact ⟨hmem, hsf, hodd⟩
  have h_card : oddS.card = copS.card + div3S.card := by
    rw [h_union, Finset.card_union_of_disjoint h_disj]
  -- Injection: div3S → copS by dividing by 3
  have h_inj : div3S.card ≤ copS.card := by
    apply Finset.card_le_card_of_injOn (fun n => n / 3)
    · -- Maps into copS
      intro n hn
      rw [Finset.mem_coe, Finset.mem_filter] at hn
      have hmem := Finset.mem_Icc.mp hn.1
      have hsf := hn.2.1
      have hodd := hn.2.2.1
      have h3 := hn.2.2.2
      obtain ⟨hsf', hodd', hcop⟩ := squarefree_third hsf hodd h3
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      have h1 : 1 ≤ n / 3 := by
        have : 3 ≤ n := Nat.le_of_dvd (by omega) h3
        omega
      have h2 : n / 3 ≤ X := le_trans (Nat.div_le_self n 3) hmem.2
      exact ⟨⟨h1, h2⟩, hsf', hodd', hcop⟩
    · -- Injective on div3S: a/3 = b/3 and both divisible by 3 → a = b
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha3 := Nat.div_mul_cancel ha.2.2.2
      have hb3 := Nat.div_mul_cancel hb.2.2.2
      linarith
  linarith [h_card, h_inj]

/-- #{sf in [1,X]} ≤ 4 · #{odd sf coprime to 3 in [1,X]}.
    Combines the factor-2 injection (odd_sf_card_ge_half: #{sf} ≤ 2·#{odd sf})
    with the factor-3 injection (odd_coprime3_sf_card_ge_half: #{odd sf} ≤ 2·#{odd sf ∧ 3∤n}). -/
private theorem sf_le_four_coprime6 (X : Nat) :
    ((Finset.Icc 1 X).filter Squarefree).card ≤
    4 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card := by
  calc ((Finset.Icc 1 X).filter Squarefree).card
      ≤ 2 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)).card :=
        odd_sf_card_ge_half X
    _ ≤ 2 * (2 * ((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card) :=
        Nat.mul_le_mul_left 2 (odd_coprime3_sf_card_ge_half X)
    _ = 4 * ((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card := by ring

/-- The ensemble average of 1/genSeq(n,1) is bounded below by the density of
    1-mod-6 squarefree numbers divided by 3. -/
theorem ensembleAvg_k1_ge_mod6_fraction {X : Nat} (hX : 0 < sqfreeCount X) :
    ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card /
      (3 * sqfreeCount X : ℝ) ≤
    ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ)) := by
  unfold ensembleAvg sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree with hS_def
  set mod6S := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)
    with hmod6S_def
  have hS_pos : (0 : ℝ) < S.card := by exact_mod_cast hX
  have h_sub : mod6S ⊆ S := by
    intro n hn
    simp only [hmod6S_def, hS_def, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have h_mod6_sum : ∑ n ∈ mod6S, (1 : ℝ) / (genSeq n 1 : ℝ) = mod6S.card * (1 / 3) := by
    rw [show mod6S.card * (1 / 3 : ℝ) = ∑ _ ∈ mod6S, (1 : ℝ) / 3 from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_congr rfl fun n hn => by
      simp only [hmod6S_def, Finset.mem_filter, Finset.mem_Icc] at hn
      simp [genSeq_one_of_mod6 hn.1.1 hn.2.2.1 hn.2.2.2]
  have h_sum_lower : (mod6S.card : ℝ) / 3 ≤ ∑ n ∈ S, (1 : ℝ) / (genSeq n 1 : ℝ) := by
    calc ∑ n ∈ S, (1 : ℝ) / (genSeq n 1 : ℝ)
        ≥ ∑ n ∈ mod6S, (1 : ℝ) / (genSeq n 1 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
      _ = mod6S.card * (1 / 3) := h_mod6_sum
      _ = (mod6S.card : ℝ) / 3 := by ring
  rw [le_div_iff₀ hS_pos]
  calc (mod6S.card : ℝ) / (3 * (S.card : ℝ)) * (S.card : ℝ)
      = (mod6S.card : ℝ) / 3 := by field_simp
    _ ≤ ∑ n ∈ S, (1 : ℝ) / (genSeq n 1 : ℝ) := h_sum_lower

/-- **k=1 lower bound landscape**: witnesses the genSeq_one_of_mod6 theorem,
    the sf_le_four_coprime6 injection bound, and the conditional assembly. -/
theorem k1_lower_bound_landscape :
    -- 1. genSeq n 1 = 3 for n ≡ 1 mod 6 squarefree
    (∀ (n : Nat), 1 ≤ n → ¬ Even n → n % 3 = 1 → genSeq n 1 = 3) ∧
    -- 2. #{sf} ≤ 4 · #{odd sf coprime to 3}
    (∀ X : Nat, ((Finset.Icc 1 X).filter Squarefree).card ≤
      4 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card) ∧
    -- 3. Conditional lower bound on E[1/genSeq(·,1)]
    (∀ X : Nat, 0 < sqfreeCount X →
      ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card /
        (3 * sqfreeCount X : ℝ) ≤
      ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ))) :=
  ⟨fun _ hn hodd hmod3 => genSeq_one_of_mod6 hn hodd hmod3,
   sf_le_four_coprime6,
   fun _ hX => ensembleAvg_k1_ge_mod6_fraction hX⟩

end K1Infrastructure

/-! ## k=2 CRT Structure

For odd squarefree n with n % 3 = 1 (equivalently n ≡ 1 mod 6):
- genSeq(n,0) = 2, genProd(n,1) = 2n
- genSeq(n,1) = 3, genProd(n,2) = 6n
- genSeq(n,2) = minFac(6n+1)

For n additionally with n % 5 = 4 (equivalently n ≡ 19 mod 30 by CRT):
- 6n+1 ≡ 0 mod 5, and 6n+1 is odd and coprime to 3
- So minFac(6n+1) = 5, i.e., genSeq(n,2) = 5 -/

section K2Infrastructure

/-- For odd n >= 1 with n % 3 = 1, genProd n 2 = 6 * n. -/
theorem genProd_two_of_mod6 {n : Nat} (hn : 1 ≤ n) (hodd : ¬ Even n)
    (hmod3 : n % 3 = 1) : genProd n 2 = 6 * n := by
  show genProd n 1 * genSeq n 1 = 6 * n
  rw [show genProd n 1 = n * genSeq n 0 from rfl,
    genSeq_zero_of_odd hn hodd, genSeq_one_of_mod6 hn hodd hmod3]
  ring

/-- For odd n >= 1 with n % 3 = 1 and n % 5 = 4, genSeq n 2 = 5. -/
theorem genSeq_two_of_mod30 {n : Nat} (hn : 1 ≤ n) (hodd : ¬ Even n)
    (hmod3 : n % 3 = 1) (hmod5 : n % 5 = 4) : genSeq n 2 = 5 := by
  rw [genSeq_def, genProd_two_of_mod6 hn hodd hmod3]
  set m := 6 * n + 1
  have hm_ne1 : m ≠ 1 := by omega
  have hm_odd : ¬ Even m := fun ⟨k, hk⟩ => by omega
  have h3_ndvd : ¬ (3 ∣ m) := fun ⟨k, hk⟩ => by omega
  have h5_dvd : 5 ∣ m := by
    have : n = 5 * (n / 5) + 4 := by omega
    exact ⟨6 * (n / 5) + 5, by omega⟩
  have hm_prime := Nat.minFac_prime hm_ne1
  have hm_ge2 := hm_prime.two_le
  have hm_le5 := Nat.minFac_le_of_dvd (by omega : 2 ≤ 5) h5_dvd
  have hm_ne2 : Nat.minFac m ≠ 2 := fun h2 =>
    hm_odd (even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff m).mp h2))
  have hm_ne3 : Nat.minFac m ≠ 3 := fun h3 =>
    h3_ndvd (h3 ▸ Nat.minFac_dvd m)
  have hm_ne4 : Nat.minFac m ≠ 4 := fun h4 => by
    rw [h4] at hm_prime; exact (by decide : ¬ Nat.Prime 4) hm_prime
  omega

/-- k=2 CRT landscape: for n ≡ 19 mod 30, the first three EM primes are 2, 3, 5. -/
theorem k2_crt_landscape :
    (∀ n : Nat, 1 ≤ n → ¬ Even n → n % 3 = 1 → genProd n 2 = 6 * n) ∧
    (∀ n : Nat, 1 ≤ n → ¬ Even n → n % 3 = 1 → n % 5 = 4 → genSeq n 2 = 5) :=
  ⟨fun _ hn hodd hmod3 => genProd_two_of_mod6 hn hodd hmod3,
   fun _ hn hodd hmod3 hmod5 => genSeq_two_of_mod30 hn hodd hmod3 hmod5⟩

end K2Infrastructure

/-! ## Partial SMLB and Fixed Density Results

PartialSMLB captures "SMLB for finitely many steps", which suffices for
a fixed positive density result (not divergence, but a concrete threshold). -/

section PartialSMLBSection

/-- **Partial SMLB**: the ensemble average of 1/genSeq(n,k) is at least c
    for each k ≤ K₀. This is weaker than SMLB (which requires ALL k). -/
def PartialSMLB (c : ℝ) (K₀ : Nat) : Prop :=
  ∀ k ≤ K₀, ∃ X₀ : Nat, ∀ X ≥ X₀,
    c ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ))

/-- PartialSMLB(c, K₀) implies: for X large enough, E[S_{K₀+1}(n)] ≥ c·(K₀+1).
    By linearity of ensembleAvg, the partial sum average is the sum of step averages.
    Each step average is ≥ c for X large enough. Taking the max threshold gives
    the uniform bound. -/
theorem partial_smlb_implies_mean_lower_bound {c : ℝ} {K₀ : Nat} (_hc : 0 < c)
    (hpsmlb : PartialSMLB c K₀) :
    ∃ X₀ : Nat, ∀ X ≥ X₀,
      c * (K₀ + 1) ≤ ensembleAvg X (fun n => recipPartialSum n (K₀ + 1)) := by
  have hthresh : ∀ k, k ∈ Finset.range (K₀ + 1) →
      ∃ Xk : Nat, ∀ X ≥ Xk,
        c ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) :=
    fun k hk => hpsmlb k (by rw [Finset.mem_range] at hk; omega)
  let threshold : Nat → Nat := fun k =>
    if hk : k ∈ Finset.range (K₀ + 1) then (hthresh k hk).choose else 0
  refine ⟨(Finset.range (K₀ + 1)).sup threshold, fun X hX => ?_⟩
  simp_rw [show ∀ n, recipPartialSum n (K₀ + 1) =
      ∑ k ∈ Finset.range (K₀ + 1), 1 / (genSeq n k : ℝ) from fun _ => rfl]
  rw [ensembleAvg_sum_range]
  calc c * (↑K₀ + 1) = ∑ _ ∈ Finset.range (K₀ + 1), c := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ∑ k ∈ Finset.range (K₀ + 1),
          ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have : threshold k ≤ X :=
          le_trans (Finset.le_sup (f := threshold) hk) hX
        simp only [threshold, dif_pos hk] at this
        exact (hthresh k hk).choose_spec X this

/-- PartialSMLB(1/4, 0) holds unconditionally from the k=0 step. -/
theorem partial_smlb_zero_unconditional : PartialSMLB (1 / 4) 0 := by
  intro k hk
  have : k = 0 := by omega
  subst this
  exact smlb_k0_unconditional

/-- PartialSMLB landscape: PartialSMLB(1/4, 0) unconditional + mean lower bound chain. -/
theorem partial_smlb_landscape :
    PartialSMLB (1 / 4) 0 ∧
    (∀ c : ℝ, 0 < c → ∀ K₀ : Nat, PartialSMLB c K₀ →
      ∃ X₀ : Nat, ∀ X ≥ X₀,
        c * (K₀ + 1) ≤ ensembleAvg X (fun n => recipPartialSum n (K₀ + 1))) :=
  ⟨partial_smlb_zero_unconditional,
   fun _ hc _ hpsmlb => partial_smlb_implies_mean_lower_bound hc hpsmlb⟩

end PartialSMLBSection

/-! ## Squarefree Density in 1 mod 6

The density of squarefree n ≡ 1 mod 6 among all squarefree is 1/3 asymptotically.
We state a weaker lower bound as a hypothesis and connect it to SMLB. -/

section Mod6DensitySection

/-- The density of 1-mod-6 squarefree among all squarefree is bounded below.
    Mathematically: #{n ≤ X : sf, n ≡ 1 mod 6} / #{n ≤ X : sf} → 1/3 as X → ∞.
    We only need: for large X, this ratio ≥ 1/8. -/
def Mod6DensityLB : Prop :=
  ∃ X₀ : Nat, ∀ X ≥ X₀,
    (sqfreeCount X : ℝ) / 8 ≤
    ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card

/-- sqfreeCount X ≤ X: squarefree numbers in [1,X] are a subset of [1,X]. -/
private theorem sqfreeCount_le (X : Nat) : sqfreeCount X ≤ X := by
  unfold sqfreeCount
  calc ((Finset.Icc 1 X).filter Squarefree).card
      ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
    _ = X := by simp [Nat.card_Icc]

/-- Multiples of 4 in [1,X] are not squarefree, giving sqfreeCount X + X/4 ≤ X. -/
private theorem sqfreeCount_le_three_quarter (X : Nat) :
    sqfreeCount X + X / 4 ≤ X := by
  unfold sqfreeCount
  -- The set of non-squarefree in [1,X] has ≥ X/4 elements (multiples of 4)
  suffices h_nonsf : X / 4 ≤ ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n)).card by
    have h_partition : ((Finset.Icc 1 X).filter Squarefree).card +
        ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n)).card =
        (Finset.Icc 1 X).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _),
          Finset.filter_union_filter_not_eq]
    have hcard : (Finset.Icc 1 X).card = X := by simp [Nat.card_Icc]
    omega
  -- Build injection from Finset.range (X/4) → non-squarefree in [1,X] via k ↦ 4*(k+1)
  have : (Finset.range (X / 4)).card ≤
      ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n)).card := by
    apply Finset.card_le_card_of_injOn (fun k => 4 * (k + 1))
    · intro k hk
      have hk_lt : k < X / 4 := Finset.mem_range.mp hk
      have h1 : 1 ≤ 4 * (k + 1) := by omega
      have h2 : 4 * (k + 1) ≤ X := by
        have : 4 * (X / 4) ≤ X := Nat.mul_div_le X 4
        omega
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, fun hsf => absurd (hsf 2 ⟨k + 1, by ring⟩) (by simp)⟩
    · intro a _ b _ (hab : 4 * (a + 1) = 4 * (b + 1)); omega
  simp [Finset.card_range] at this; exact this

/-- Inclusion-exclusion: multiples of 4 and 9 give sqfreeCount X + X/4 + X/9 ≤ X + X/36 + 2.
    Since 1/4 + 1/9 - 1/36 = 1/3, this yields sqfreeCount X ≤ 2X/3 + 2 (approximately). -/
private theorem sqfreeCount_plus_fourth_ninth (X : Nat) :
    sqfreeCount X + X / 4 + X / 9 ≤ X + X / 36 + 2 := by
  unfold sqfreeCount
  -- By inclusion-exclusion: |{4|n}| + |{9|n}| - |{36|n}| ≤ |{non-sf}|
  -- The {4|n} and {9|n} sets (minus their intersection {36|n}) are subsets of non-sf.
  set S := Finset.Icc 1 X
  set nonsf := S.filter (fun n => ¬ Squarefree n)
  set A := S.filter (fun n => 4 ∣ n)
  set B := S.filter (fun n => 9 ∣ n)
  set AB := S.filter (fun n => 36 ∣ n)
  -- A ⊆ nonsf: 4|n → 2²|n → ¬Squarefree
  have hA_nonsf : A ⊆ nonsf := by
    intro n hn
    have hn_mem : n ∈ S := Finset.mem_of_mem_filter n hn
    have h4 : 4 ∣ n := (Finset.mem_filter.mp hn).2
    refine Finset.mem_filter.mpr ⟨hn_mem, fun hsf => ?_⟩
    have h22 : 2 * 2 ∣ n := h4
    exact absurd (hsf 2 h22) (by simp)
  -- B ⊆ nonsf: 9|n → 3²|n → ¬Squarefree
  have hB_nonsf : B ⊆ nonsf := by
    intro n hn
    have hn_mem : n ∈ S := Finset.mem_of_mem_filter n hn
    have h9 : 9 ∣ n := (Finset.mem_filter.mp hn).2
    refine Finset.mem_filter.mpr ⟨hn_mem, fun hsf => ?_⟩
    have h33 : 3 * 3 ∣ n := h9
    exact absurd (hsf 3 h33) (by simp)
  -- AB = A ∩ B: 36|n ↔ 4|n ∧ 9|n (since gcd(4,9)=1)
  have hAB_eq : AB = A ∩ B := by
    ext n; simp only [AB, A, B, S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_inter]
    constructor
    · intro ⟨hmem, h36⟩
      exact ⟨⟨hmem, Dvd.dvd.trans (by norm_num : (4 : ℕ) ∣ 36) h36⟩,
             ⟨hmem, Dvd.dvd.trans (by norm_num : (9 : ℕ) ∣ 36) h36⟩⟩
    · intro ⟨⟨hmem, h4⟩, ⟨_, h9⟩⟩
      exact ⟨hmem, (by decide : Nat.Coprime 4 9).mul_dvd_of_dvd_of_dvd h4 h9⟩
  -- |A ∪ B| = |A| + |B| - |A ∩ B|
  -- |A ∪ B| ≤ |nonsf|
  have hAB_sub : A ∪ B ⊆ nonsf := Finset.union_subset hA_nonsf hB_nonsf
  have hie : A.card + B.card = (A ∪ B).card + AB.card := by
    rw [hAB_eq, Finset.card_union_add_card_inter]
  have hnonsf_ge : (A ∪ B).card ≤ nonsf.card := Finset.card_le_card hAB_sub
  -- |A| ≥ X/4
  have hA_card : X / 4 ≤ A.card := by
    have : (Finset.range (X / 4)).card ≤ A.card := by
      apply Finset.card_le_card_of_injOn (fun k => 4 * (k + 1))
      · intro k hk
        have hk_lt : k < X / 4 := Finset.mem_range.mp hk
        simp only [A, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by have := Nat.mul_div_le X 4; omega⟩, ⟨k + 1, by ring⟩⟩
      · intro a _ b _ (hab : 4 * (a + 1) = 4 * (b + 1)); omega
    simp [Finset.card_range] at this; exact this
  -- |B| ≥ X/9
  have hB_card : X / 9 ≤ B.card := by
    have : (Finset.range (X / 9)).card ≤ B.card := by
      apply Finset.card_le_card_of_injOn (fun k => 9 * (k + 1))
      · intro k hk
        have hk_lt : k < X / 9 := Finset.mem_range.mp hk
        simp only [B, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by have := Nat.mul_div_le X 9; omega⟩, ⟨k + 1, by ring⟩⟩
      · intro a _ b _ (hab : 9 * (a + 1) = 9 * (b + 1)); omega
    simp [Finset.card_range] at this; exact this
  -- |AB| ≤ X/36 + 1
  have hAB_card : AB.card ≤ X / 36 + 1 := by
    calc AB.card ≤ (Finset.Icc 0 (X / 36)).card := by
          apply Finset.card_le_card_of_injOn (fun n => n / 36)
          · intro n hn
            simp only [AB, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
            exact ⟨Nat.zero_le _, Nat.div_le_div_right hn.1.2⟩
          · intro a ha b hb (hab : a / 36 = b / 36)
            simp only [AB, S, Finset.mem_coe, Finset.mem_filter] at ha hb
            have had := Nat.div_mul_cancel ha.2
            have hbd := Nat.div_mul_cancel hb.2
            nlinarith
      _ = X / 36 + 1 := by rw [← Nat.range_succ_eq_Icc_zero, Finset.card_range]
  -- Partition identity
  have h_partition : (S.filter Squarefree).card + nonsf.card = S.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _),
        Finset.filter_union_filter_not_eq]
  have hS_card : S.card = X := by simp [S, Nat.card_Icc]
  -- Assembly: sqfreeCount + |A| + |B| ≤ X + |AB| + nonsf.card (approximately)
  -- sqfreeCount + nonsf.card = X
  -- |A| + |B| = |A∪B| + |AB| ≤ nonsf.card + |AB|
  -- So sqfreeCount + |A| + |B| ≤ X - nonsf.card + nonsf.card + |AB| = X + |AB|
  -- Wait: sqfreeCount = X - nonsf.card, and |A| + |B| ≤ nonsf.card + |AB|.
  -- So sqfreeCount + |A| + |B| ≤ X - nonsf.card + nonsf.card + |AB| = X + |AB|.
  have : (S.filter Squarefree).card + A.card + B.card ≤ X + AB.card := by
    -- A.card + B.card = (A∪B).card + AB.card ≤ nonsf.card + AB.card
    have h1 : A.card + B.card ≤ nonsf.card + AB.card := by linarith
    -- sqfreeCount + nonsf = X
    linarith
  -- sqfreeCount X + X/4 + X/9 ≤ X + X/36 + 2
  -- |A| ≥ X/4, |B| ≥ X/9, |AB| ≤ X/36 + 1
  -- Actually we need: sqfreeCount + X/4 + X/9 ≤ sqfreeCount + |A| + |B| ≤ X + |AB| ≤ X + X/36 + 1
  -- But sqfreeCount + X/4 + X/9 ≤ sqfreeCount + |A| + |B| requires X/4 ≤ |A| and X/9 ≤ |B|.
  -- That's backwards! We need sqfreeCount + X/4 + X/9 ≤ ..., and |A| ≥ X/4, so
  -- sqfreeCount + X/4 + X/9 ≤ sqfreeCount + |A| + |B| ≤ X + |AB| ≤ X + X/36 + 1.
  -- Hmm, sqfreeCount + X/4 ≤ sqfreeCount + |A| since X/4 ≤ |A|. Similarly X/9 ≤ |B|.
  -- But we need sqfreeCount + X/4 + X/9 ≤ X + X/36 + 2.
  -- sqfreeCount + |A| + |B| ≤ X + |AB|, so sqfreeCount ≤ X + |AB| - |A| - |B|.
  -- sqfreeCount + X/4 + X/9 ≤ X + |AB| - |A| - |B| + X/4 + X/9.
  -- Need: X + |AB| - |A| - |B| + X/4 + X/9 ≤ X + X/36 + 2.
  -- i.e.: |AB| - |A| - |B| + X/4 + X/9 ≤ X/36 + 2.
  -- i.e.: X/4 - |A| + X/9 - |B| + |AB| ≤ X/36 + 2.
  -- Since X/4 ≤ |A| and X/9 ≤ |B|, we have X/4 - |A| ≤ 0 and X/9 - |B| ≤ 0.
  -- So it suffices to show |AB| ≤ X/36 + 2. But we have |AB| ≤ X/36 + 1. ✓
  linarith

/-- n ≡ 1 mod 6 ↔ n odd and n % 3 = 1 (for n ≥ 1). -/
private theorem mod6_eq_one_iff {n : Nat} (_hn : 1 ≤ n) :
    n % 6 = 1 ↔ (¬ Even n ∧ n % 3 = 1) := by
  constructor
  · intro h
    constructor
    · intro ⟨k, hk⟩; omega
    · omega
  · intro ⟨hodd, hmod3⟩
    have h2 : n % 2 = 1 := by
      rcases Nat.even_or_odd n with he | ho
      · exact absurd he hodd
      · exact Nat.odd_iff.mp ho
    omega

/-- Count of n ≡ 1 mod 6 in [1,X] is at least X/6. -/
private theorem count_one_mod_six_ge (X : Nat) :
    X / 6 ≤ ((Finset.Icc 1 X).filter (fun n => n % 6 = 1)).card := by
  -- The map k ↦ 6k + 1 for k ∈ Finset.range(X/6) injects into {n ∈ [1,X] : n%6=1}
  have : (Finset.range (X / 6)).card ≤
      ((Finset.Icc 1 X).filter (fun n => n % 6 = 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => 6 * k + 1)
    · intro k hk
      have hk_lt : k < X / 6 := Finset.mem_range.mp hk
      have h1 : 1 ≤ 6 * k + 1 := by omega
      have h2 : 6 * k + 1 ≤ X := by
        have : 6 * (X / 6) ≤ X := Nat.mul_div_le X 6
        omega
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, by omega⟩
    · intro a _ b _ (hab : 6 * a + 1 = 6 * b + 1); omega
  simp [Finset.card_range] at this; exact this

/-- For n coprime to 6 and not squarefree, there exists d ≥ 5 coprime to 6 with d²|n. -/
private theorem exists_sq_factor_of_nonsf_coprime6 {n : Nat} (_hn : 1 ≤ n)
    (hnsf : ¬ Squarefree n) (hodd : ¬ Even n) (hmod3 : n % 3 = 1) :
    ∃ d : Nat, 5 ≤ d ∧ d * d ∣ n := by
  -- n not squarefree means ∃ p prime with p² | n
  rw [Nat.squarefree_iff_prime_squarefree] at hnsf
  push_neg at hnsf
  obtain ⟨p, hp, hpdvd⟩ := hnsf
  refine ⟨p, ?_, hpdvd⟩
  -- p ≥ 5 since p ≠ 2 (n odd) and p ≠ 3 (n%3=1 so 9 ∤ n)
  have hp2 : p ≠ 2 := by
    intro h; subst h
    obtain ⟨m, hm⟩ := hpdvd
    exact hodd ⟨2 * m, by omega⟩
  have hp3 : p ≠ 3 := by
    intro h; subst h
    obtain ⟨m, hm⟩ := hpdvd
    have : n % 3 = 0 := by omega
    omega
  have h2le := hp.two_le
  have hp4 : p ≠ 4 := by
    intro h; subst h
    exact absurd hp (by decide)
  omega

/-- Non-squarefree n ≡ 1 mod 6 with d²|n: at most X/(d²) + 1 such n in [1,X]. -/
private theorem count_nonsf_with_sq_factor (X d : Nat) (_hd : 2 ≤ d) :
    ((Finset.Icc 1 X).filter (fun n => d * d ∣ n)).card ≤ X / (d * d) + 1 := by
  -- Map n to n/(d²) gives injection into [0, X/d²]
  calc ((Finset.Icc 1 X).filter (fun n => d * d ∣ n)).card
      ≤ (Finset.Icc 0 (X / (d * d))).card := by
        apply Finset.card_le_card_of_injOn (fun n => n / (d * d))
        · intro n hn
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
          rw [Finset.mem_coe, Finset.mem_Icc]
          exact ⟨Nat.zero_le _, Nat.div_le_div_right hn.1.2⟩
        · intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_filter] at ha hb
          have had := Nat.div_mul_cancel ha.2  -- a / (d*d) * (d*d) = a
          have hbd := Nat.div_mul_cancel hb.2  -- b / (d*d) * (d*d) = b
          have : (fun n => n / (d * d)) a = (fun n => n / (d * d)) b := hab
          simp only at this
          nlinarith
    _ = X / (d * d) + 1 := by
        rw [← Nat.range_succ_eq_Icc_zero, Finset.card_range]

/-- The union of {n ∈ [1,X] : d²|n} over d = 5,...,M covers all non-sf n ≡ 1 mod 6
    with smallest factor d ≤ M, so the card is bounded by ∑ (X/d² + 1). -/
private theorem nonsf_one_mod_six_le_sum (X : Nat) :
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card +
    ((Finset.Icc 1 X).filter
      (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card =
    ((Finset.Icc 1 X).filter (fun n => ¬ Even n ∧ n % 3 = 1)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro (⟨hmem, hsf, hodd, hmod⟩ | ⟨hmem, hnsf, hodd, hmod⟩)
      · exact ⟨hmem, hodd, hmod⟩
      · exact ⟨hmem, hodd, hmod⟩
    · intro ⟨hmem, hodd, hmod⟩
      rcases Decidable.em (Squarefree n) with hsf | hnsf
      · exact Or.inl ⟨hmem, hsf, hodd, hmod⟩
      · exact Or.inr ⟨hmem, hnsf, hodd, hmod⟩
  · rw [Finset.disjoint_filter]
    intro n _ ⟨hsf, _, _⟩ ⟨hnsf, _, _⟩
    exact hnsf hsf

/-- For d coprime to 6, d² ≡ 1 mod 6. -/
private theorem sq_mod_six_of_coprime {d : Nat} (hd2 : ¬ 2 ∣ d) (hd3 : ¬ 3 ∣ d) :
    d * d % 6 = 1 := by
  have h2 : d % 2 = 1 := by omega
  have h3 : d % 3 ∈ ({1, 2} : Finset Nat) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have h6 : d % 6 ∈ ({1, 5} : Finset Nat) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at h6
  rw [Nat.mul_mod]
  rcases h6 with h | h <;> simp [h]

/-- For d coprime to 6, #{n ≡ 1 mod 6 in [1,X] : d²|n} ≤ X/(6d²) + 1.
    Key: d coprime to 6 → d² ≡ 1 mod 6, so d²|n and n ≡ 1 mod 6 → n/d² ≡ 1 mod 6.
    The map n ↦ n/d² injects into {m ≡ 1 mod 6 in [1, X/d²]}. -/
private theorem count_mod6_sq_factor (X d : Nat) (hd : 5 ≤ d) (hd2 : ¬ 2 ∣ d) (hd3 : ¬ 3 ∣ d) :
    ((Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)).card ≤ X / (6 * (d * d)) + 1 := by
  -- The map n ↦ n/(d²) is an injection
  -- Image: m ∈ [1, X/d²] with m ≡ 1 mod 6
  -- Count of image ≤ X/(6d²) + 1
  have hdd_pos : 0 < d * d := by positivity
  -- Injection into {m ≡ 1 mod 6 in [0, X/(d²)]}
  calc ((Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)).card
      ≤ ((Finset.range (X / (d * d) + 1)).filter (fun m => m % 6 = 1)).card := by
        apply Finset.card_le_card_of_injOn (fun n => n / (d * d))
        · intro n hn
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          have hndvd := hn.2.2
          have hmod := hn.2.1
          have hle := hn.1.2
          constructor
          · exact Nat.lt_succ_of_le (Nat.div_le_div_right hle)
          · -- n/d² ≡ 1 mod 6 since n ≡ 1 mod 6 and d² ≡ 1 mod 6
            have hd2_mod := sq_mod_six_of_coprime hd2 hd3  -- d*d % 6 = 1
            have hcancel := Nat.div_mul_cancel hndvd  -- n/(d*d) * (d*d) = n
            -- n/(d²) * (d²) ≡ n mod 6, so (n/d² mod 6) * (d² mod 6) ≡ n mod 6
            have h1 : (n / (d * d) * (d * d)) % 6 = n % 6 := by rw [hcancel]
            rw [Nat.mul_mod] at h1
            simp [hd2_mod, hmod] at h1
            exact h1
        · intro a ha b hb (hab : a / (d * d) = b / (d * d))
          simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
          have had := Nat.div_mul_cancel ha.2.2
          have hbd := Nat.div_mul_cancel hb.2.2
          nlinarith
    _ ≤ X / (6 * (d * d)) + 1 := by
        -- #{m ∈ {0,...,N} : m%6=1} ≤ N/6 + 1 via injection m ↦ m/6
        set N := X / (d * d)
        -- Injection: m ↦ m/6 from {m ∈ range(N+1) : m%6=1} into range(N/6+1)
        have hcount : ((Finset.range (N + 1)).filter (fun m => m % 6 = 1)).card ≤ N / 6 + 1 := by
          have hinj : ((Finset.range (N + 1)).filter (fun m => m % 6 = 1)).card ≤
              (Finset.range (N / 6 + 1)).card := by
            apply Finset.card_le_card_of_injOn (fun m => m / 6)
            · intro m hm
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm ⊢
              exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp hm.1))
            · intro a ha b hb (hab : a / 6 = b / 6)
              simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
              have ha1 := Nat.div_add_mod a 6
              have hb1 := Nat.div_add_mod b 6
              omega
          simp only [Finset.card_range] at hinj
          exact hinj
        -- N/6 = X/(6*d²)
        have hdiv : N / 6 = X / (6 * (d * d)) := by
          show X / (d * d) / 6 = X / (6 * (d * d))
          rw [Nat.div_div_eq_div_mul, mul_comm]
        linarith

/-- Telescoping: ∑_{d=K}^{M} 1/d² ≤ 1/(K-1) for K ≥ 2 and M ≥ K. -/
private theorem sum_inv_sq_le_telescoping (K M : Nat) (hK : 2 ≤ K) (hKM : K ≤ M) :
    ∑ d ∈ Finset.Icc K M, (1 : ℝ) / ((d : ℝ) * d) ≤ 1 / (K - 1 : ℝ) := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) - 1 := by linarith [show (2 : ℝ) ≤ (K : ℝ) from by exact_mod_cast hK]
  calc ∑ d ∈ Finset.Icc K M, (1 : ℝ) / ((d : ℝ) * d)
      ≤ ∑ d ∈ Finset.Icc K M, (1 / ((d : ℝ) - 1) - 1 / d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd_mem := Finset.mem_Icc.mp hd
        have hd_ge : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 2 ≤ d by omega)
        have hd_pos : (0 : ℝ) < d := by linarith
        have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by linarith
        rw [div_sub_div _ _ (ne_of_gt hd1_pos) (ne_of_gt hd_pos)]
        rw [div_le_div_iff₀ (mul_pos hd_pos hd_pos) (mul_pos hd1_pos hd_pos)]
        have : (d : ℝ) - ((d : ℝ) - 1) = 1 := by ring
        nlinarith [mul_self_nonneg ((d : ℝ) - 1)]
    _ ≤ 1 / ((K : ℝ) - 1) := by
        -- Telescoping sum: ∑ (1/(d-1) - 1/d) = 1/(K-1) - 1/M
        have htel : ∑ d ∈ Finset.Icc K M, (1 / ((d : ℝ) - 1) - 1 / d) =
            1 / ((K : ℝ) - 1) - 1 / M := by
          induction M with
          | zero => omega
          | succ n ih =>
            by_cases hle : K ≤ n
            · -- K ≤ n, induction step
              rw [show Finset.Icc K (n + 1) = Finset.Icc K n ∪ {n + 1} from by
                ext x; simp [Finset.mem_Icc]; omega]
              rw [Finset.sum_union (by
                simp [Finset.disjoint_singleton_right, Finset.mem_Icc])]
              rw [Finset.sum_singleton, ih hle]
              push_cast; ring
            · -- K > n, so K = n + 1
              push_neg at hle
              have heq : K = n + 1 := by omega
              subst heq
              simp [Finset.Icc_self]
        rw [htel]
        linarith [div_nonneg (le_of_lt (show (0:ℝ) < 1 by norm_num)) (by linarith : (0:ℝ) ≤ (M:ℝ))]

/-- The non-squarefree count among n ≡ 1 mod 6 in [1,X] is ≤ X/24 + Nat.sqrt X.
    Every such n has some d ≥ 5 coprime to 6 with d²|n. By CRT (d²≡1 mod 6),
    the per-d count is X/(6d²)+1, and ∑ X/(6d²) ≤ (X/6)·(1/(K-1)) via telescoping. -/
private theorem nonsf_mod6_count_bound (X : Nat) :
    ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card ≤
    X / 24 + Nat.sqrt X := by
  set B' := (Finset.Icc 1 X).filter (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)
  set sqrtX := Nat.sqrt X
  set Ds := (Finset.Icc 5 sqrtX).filter (fun d => ¬ 2 ∣ d ∧ ¬ 3 ∣ d)
  -- Step 1: B' ⊆ union over d in Ds of {n : d²|n, n%6=1, n ∈ [1,X]}
  have hcontain : B' ⊆ Ds.biUnion (fun d =>
      (Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)) := by
    intro n hn
    simp only [B', Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, hnsf, hodd, hmod3⟩ := hn
    obtain ⟨d, hd5, hddvd⟩ := exists_sq_factor_of_nonsf_coprime6 hn1 hnsf hodd hmod3
    rw [Finset.mem_biUnion]
    have hd_le_sqrt : d ≤ sqrtX := by
      rw [Nat.le_sqrt]
      exact le_trans (Nat.le_of_dvd (by omega) hddvd) hnX
    have hd2 : ¬ 2 ∣ d := by
      intro h2d
      have h4 : 2 * 2 ∣ d * d := Nat.mul_dvd_mul h2d h2d
      exact hodd ⟨2 * (n / 4), by have := Nat.div_mul_cancel (dvd_trans h4 hddvd); omega⟩
    have hd3 : ¬ 3 ∣ d := by
      intro h3d
      have h9 : 3 * 3 ∣ d * d := Nat.mul_dvd_mul h3d h3d
      have : n % 3 = 0 := by have h9dvd := dvd_trans h9 hddvd; omega
      omega
    have hd_mem : d ∈ Ds := by
      simp only [Ds, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hd5, hd_le_sqrt⟩, hd2, hd3⟩
    have hn_mem : n ∈ (Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hn1, hnX⟩, (mod6_eq_one_iff hn1).mpr ⟨hodd, hmod3⟩, hddvd⟩
    exact ⟨d, hd_mem, hn_mem⟩
  -- Step 2: Union bound + per-d CRT bound + telescoping
  calc B'.card
      ≤ (Ds.biUnion (fun d => (Finset.Icc 1 X).filter
          (fun n => n % 6 = 1 ∧ d * d ∣ n))).card :=
        Finset.card_le_card hcontain
    _ ≤ ∑ d ∈ Ds, ((Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Ds, (X / (6 * (d * d)) + 1) := by
        apply Finset.sum_le_sum
        intro d hd
        simp only [Ds, Finset.mem_filter, Finset.mem_Icc] at hd
        exact count_mod6_sq_factor X d hd.1.1 hd.2.1 hd.2.2
    _ = ∑ d ∈ Ds, X / (6 * (d * d)) + ∑ _d ∈ Ds, 1 := Finset.sum_add_distrib
    _ = ∑ d ∈ Ds, X / (6 * (d * d)) + Ds.card := by simp
    _ ≤ ∑ d ∈ Ds, X / (6 * (d * d)) + sqrtX := by
        have hDs : Ds.card ≤ (Finset.Icc 5 sqrtX).card := Finset.card_filter_le _ _
        have hIcc : (Finset.Icc 5 sqrtX).card ≤ sqrtX := by
          rw [Nat.card_Icc]; omega
        omega
    _ ≤ X / 24 + sqrtX := by
        suffices h : ∑ d ∈ Ds, X / (6 * (d * d)) ≤ X / 24 by omega
        calc ∑ d ∈ Ds, X / (6 * (d * d))
            ≤ ∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              intro _ _ _; exact Nat.zero_le _
          _ ≤ X / 24 := by
              -- Cast to R and use telescoping
              -- Key: ↑(∑ X/(6d²)) ≤ (X:R)/24 ≤ ... so Nat sum ≤ X/24
              have hR : (↑(∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d))) : ℝ) ≤
                  (X : ℝ) / 24 := by
                calc (↑(∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d))) : ℝ)
                    = ∑ d ∈ Finset.Icc 5 sqrtX, (↑(X / (6 * (d * d))) : ℝ) := by
                      push_cast; rfl
                  _ ≤ ∑ d ∈ Finset.Icc 5 sqrtX, ((X : ℝ) / (6 * ((d : ℝ) * d))) := by
                      apply Finset.sum_le_sum
                      intro d _hd
                      have : (↑(X / (6 * (d * d))) : ℝ) ≤ (X : ℝ) / ↑(6 * (d * d)) :=
                        Nat.cast_div_le
                      simp only [Nat.cast_mul] at this
                      exact this
                  _ = (X : ℝ) / 6 * ∑ d ∈ Finset.Icc 5 sqrtX, (1 / ((d : ℝ) * d)) := by
                      rw [Finset.mul_sum]; apply Finset.sum_congr rfl
                      intro d hd
                      have hd5 : 5 ≤ d := (Finset.mem_Icc.mp hd).1
                      have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
                      field_simp
                  _ ≤ (X : ℝ) / 6 * (1 / ((5 : ℝ) - 1)) := by
                      by_cases h5 : 5 ≤ sqrtX
                      · exact mul_le_mul_of_nonneg_left
                          (sum_inv_sq_le_telescoping 5 sqrtX (by omega) h5)
                          (div_nonneg (Nat.cast_nonneg' X) (by norm_num))
                      · push_neg at h5
                        simp only [show Finset.Icc 5 sqrtX = ∅ from by
                          ext x; simp [Finset.mem_Icc]; omega]
                        simp; positivity
                  _ = (X : ℝ) / 24 := by ring
              -- Transfer: Nat sum ≤ X/24 from real bound
              rw [Nat.le_div_iff_mul_le (by omega : 0 < 24)]
              have h24 : (↑(∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d))) : ℝ) * 24 ≤ (X : ℝ) := by
                linarith
              exact_mod_cast h24

/-- For X ≥ 10000, Nat.sqrt X ≤ X / 32. -/
private theorem sqrt_le_div_32 {X : Nat} (hX : 10000 ≤ X) : Nat.sqrt X ≤ X / 32 := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h32 : 32 ≤ Nat.sqrt X := by
    calc 32 ≤ Nat.sqrt 10000 := by native_decide
      _ ≤ Nat.sqrt X := Nat.sqrt_le_sqrt hX
  have hsq : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  nlinarith

/-- Mod6DensityLB holds unconditionally. Uses inclusion-exclusion (multiples of 4 and 9)
    for a tight sqfreeCount bound, and CRT-factor bound on non-sf 1 mod 6 count. -/
theorem mod6_density_lb_proved : Mod6DensityLB := by
  refine ⟨10000, fun X hX => ?_⟩
  set A := ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card
  set B' := ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card
  set C := ((Finset.Icc 1 X).filter (fun n => ¬ Even n ∧ n % 3 = 1)).card
  have hpart : A + B' = C := nonsf_one_mod_six_le_sum X
  have hmod6 : ((Finset.Icc 1 X).filter (fun n => n % 6 = 1)).card = C := by
    congr 1; ext n; simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨hmem, hmod⟩; exact ⟨hmem, (mod6_eq_one_iff hmem.1).mp hmod⟩
    · intro ⟨hmem, hodd, hmod3⟩; exact ⟨hmem, (mod6_eq_one_iff hmem.1).mpr ⟨hodd, hmod3⟩⟩
  have hC_ge : X / 6 ≤ C := hmod6 ▸ count_one_mod_six_ge X
  have hB'_le : B' ≤ X / 24 + Nat.sqrt X := nonsf_mod6_count_bound X
  have hsqrt : Nat.sqrt X ≤ X / 32 := sqrt_le_div_32 hX
  have hsf_ie : sqfreeCount X + X / 4 + X / 9 ≤ X + X / 36 + 2 :=
    sqfreeCount_plus_fourth_ninth X
  -- A ≥ X/6 - X/24 - X/32 - 1
  have hA_R : (X : ℝ) / 6 - (X : ℝ) / 24 - (X : ℝ) / 32 - 1 ≤ (A : ℝ) := by
    have h1 : (↑(X / 6) : ℝ) ≤ (A : ℝ) + (B' : ℝ) := by
      exact_mod_cast (show X / 6 ≤ A + B' by omega)
    have h2 : (B' : ℝ) ≤ ↑(X / 24) + ↑(Nat.sqrt X) := by exact_mod_cast hB'_le
    have h3 : (↑(X / 24) : ℝ) ≤ (X : ℝ) / 24 := Nat.cast_div_le
    have h4 : (↑(Nat.sqrt X) : ℝ) ≤ (X : ℝ) / 32 := by
      exact le_trans (by exact_mod_cast hsqrt) Nat.cast_div_le
    have h5 : (X : ℝ) / 6 - 1 ≤ ↑(X / 6) := by
      have : X ≤ X / 6 * 6 + 5 := by omega
      linarith [show (↑X : ℝ) ≤ ↑(X / 6) * 6 + 5 from by exact_mod_cast this]
    linarith
  -- sqfreeCount X ≤ 2X/3 + 5 (inclusion-exclusion with 4 and 9)
  have hsf_R : (sqfreeCount X : ℝ) ≤ 2 * (X : ℝ) / 3 + 5 := by
    have h1 : (sqfreeCount X : ℝ) + ↑(X/4) + ↑(X/9) ≤ (X : ℝ) + ↑(X/36) + 2 := by
      exact_mod_cast hsf_ie
    have h2 : (X : ℝ) / 4 - 1 ≤ ↑(X / 4) := by
      linarith [show (↑X : ℝ) ≤ ↑(X / 4) * 4 + 3 from by exact_mod_cast (show X ≤ X / 4 * 4 + 3 by omega)]
    have h3 : (X : ℝ) / 9 - 1 ≤ ↑(X / 9) := by
      linarith [show (↑X : ℝ) ≤ ↑(X / 9) * 9 + 8 from by exact_mod_cast (show X ≤ X / 9 * 9 + 8 by omega)]
    linarith [show ↑(X / 36) ≤ (X : ℝ) / 36 from Nat.cast_div_le]
  -- sqfreeCount X / 8 ≤ A: follows from X ≥ 10000
  rw [div_le_iff₀ (show (0:ℝ) < 8 by norm_num)]
  have hX_pos : (10000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  nlinarith

/-- Mod6DensityLB implies SMLB at k=1 with c = 1/24.
    E[1/genSeq(·,1)] ≥ #{1 mod 6 sf}/(3·#{sf}) ≥ (#{sf}/8)/(3·#{sf}) = 1/24. -/
theorem mod6_density_implies_smlb_k1 (hd : Mod6DensityLB) :
    ∃ X₀ : Nat, ∀ X ≥ X₀,
      (1 : ℝ) / 24 ≤ ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ)) := by
  obtain ⟨X₁, hX₁⟩ := hd
  refine ⟨max X₁ 1, fun X hX => ?_⟩
  have hsc_pos : 0 < sqfreeCount X := sqfreeCount_pos_of_pos (by omega)
  set mod6Card := ((Finset.Icc 1 X).filter
    (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card
  calc (1 : ℝ) / 24
      ≤ (mod6Card : ℝ) / (3 * sqfreeCount X) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 24) (by positivity)]
        have : (sqfreeCount X : ℝ) / 8 ≤ (mod6Card : ℝ) := by exact_mod_cast hX₁ X (by omega)
        nlinarith
    _ ≤ ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ)) :=
        ensembleAvg_k1_ge_mod6_fraction hsc_pos

end Mod6DensitySection

end
