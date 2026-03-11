import EM.Population.WeakErgodicity
import EM.Population.WeakMullin

/-!
# Reciprocal Sum Divergence for Generalized EM Sequences

The **generalized EM sequence** from a squarefree starting point n iterates
the Euclid–Mullin construction: P(0) = n, P(k+1) = P(k) · minFac(P(k)+1).
Each P(k) is squarefree, and each em_n(k) = minFac(P(k)+1) is prime.

**Main Theorem (RSD).** For almost all squarefree integers n (in the
sense of natural density), the reciprocal sum ∑_k 1/em_n(k) diverges.

The proof uses:
1. **First moment**: the average of ∑_{k<K} 1/em_n(k) over squarefree n ≤ X
   is asymptotic to κK, where κ = E_{m ∈ S}[1/minFac(m)] > 0.
2. **Variance bound**: Var[∑_{k<K} 1/em_n(k)] = O(K), from approximate
   decorrelation between steps.
3. **Chebyshev + Borel-Cantelli**: the exceptional set has density 0.

## Main Results

### Definitions
* `genProd`     — generalized accumulator P(k) from starting point n
* `genSeq`      — k-th prime em_n(k) = minFac(P(k)+1)
* `recipPartialSum` — partial reciprocal sum ∑_{k<K} 1/em_n(k)

### Proved Theorems
* `genProd_pos`                      — P(k) ≥ 1 when n ≥ 1
* `genSeq_prime`                     — em_n(k) is prime when n ≥ 1
* `genSeq_dvd_genProd_succ`          — em_n(k) ∣ P(k)+1
* `genSeq_coprime_genProd`           — Coprime em_n(k) P(k)
* `genProd_squarefree`               — P(k) is squarefree when n is squarefree
* `genProd_succ_in_shifted_squarefree` — P(k)+1 ∈ ShiftedSquarefree
* `recipPartialSum_nonneg`           — partial sum ≥ 0
* `recipPartialSum_mono`             — partial sum is non-decreasing

### Open Hypotheses
* `RecipSumConcentration`  — Chebyshev + decorrelation over starting points

### Reduction
* `concentration_implies_rsd` — RecipSumConcentration → AlmostAllSquarefreeRSD (PROVED)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Generalized EM Sequence -/

section GeneralizedEM

/-- The generalized EM **accumulator** starting from n.
    P(0) = n, P(k+1) = P(k) · minFac(P(k)+1). -/
def genProd (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => genProd n k * Nat.minFac (genProd n k + 1)

/-- The k-th prime in the generalized EM sequence from n:
    em_n(k) = minFac(P(k) + 1). -/
def genSeq (n k : Nat) : Nat := Nat.minFac (genProd n k + 1)

/-- Unfolding: genProd n (k+1) = genProd n k * genSeq n k. -/
@[simp] theorem genProd_succ (n k : Nat) :
    genProd n (k + 1) = genProd n k * genSeq n k := rfl

/-- Unfolding: genSeq n k = Nat.minFac (genProd n k + 1). -/
theorem genSeq_def (n k : Nat) : genSeq n k = Nat.minFac (genProd n k + 1) := rfl

/-- The generalized accumulator is positive when starting from n ≥ 1. -/
theorem genProd_pos {n : Nat} (hn : 1 ≤ n) (k : Nat) : 1 ≤ genProd n k := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    simp only [genProd_succ]
    have : 2 ≤ Nat.minFac (genProd n k + 1) :=
      (Nat.minFac_prime (by omega)).two_le
    calc 1 ≤ 1 * 2 := by omega
      _ ≤ genProd n k * Nat.minFac (genProd n k + 1) :=
          Nat.mul_le_mul ih this

/-- The k-th generalized EM prime is prime when n ≥ 1. -/
theorem genSeq_prime {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    Nat.Prime (genSeq n k) := by
  rw [genSeq_def]
  exact Nat.minFac_prime (by have := genProd_pos hn k; omega)

/-- The k-th generalized EM prime divides P(k) + 1. -/
theorem genSeq_dvd_genProd_succ (n k : Nat) :
    genSeq n k ∣ genProd n k + 1 :=
  Nat.minFac_dvd (genProd n k + 1)

/-- The k-th generalized EM prime is coprime to the accumulator P(k).
    Proof: genSeq n k ∣ P(k)+1, so gcd(genSeq n k, P(k)) ∣ gcd(P(k)+1, P(k)) = 1. -/
theorem genSeq_coprime_genProd {n : Nat} (_hn : 1 ≤ n) (k : Nat) :
    Nat.Coprime (genSeq n k) (genProd n k) := by
  rw [Nat.coprime_comm]
  exact (Nat.coprime_self_add_right.mpr
    ((Nat.coprime_one_right_iff _).mpr trivial)).coprime_dvd_right
    (genSeq_dvd_genProd_succ n k)

/-- **The generalized accumulator is squarefree** when the starting point is
    squarefree. Proof by induction: at each step, the new prime genSeq n k
    divides P(k)+1, hence is coprime to P(k), so the product of a squarefree
    number and a new coprime prime remains squarefree. -/
theorem genProd_squarefree {n : Nat} (hn : Squarefree n) (k : Nat) :
    Squarefree (genProd n k) := by
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (Squarefree.ne_zero hn)
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [genProd_succ]
    exact Nat.squarefree_mul_iff.mpr
      ⟨(genSeq_coprime_genProd hn_pos k).symm, ih,
       (genSeq_prime hn_pos k).squarefree⟩

/-- Every generalized Euclid number P(k)+1 belongs to the shifted squarefree
    population. This is the structural basis for the first moment argument. -/
theorem genProd_succ_in_shifted_squarefree {n : Nat} (hn : Squarefree n) (k : Nat) :
    genProd n k + 1 ∈ ShiftedSquarefree := by
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (Squarefree.ne_zero hn)
  exact ⟨by have := genProd_pos hn_pos k; omega,
         by rw [show genProd n k + 1 - 1 = genProd n k from by omega]
            exact genProd_squarefree hn k⟩

end GeneralizedEM

/-! ## Reciprocal Partial Sums -/

section ReciprocalPartialSums

/-- The partial reciprocal sum ∑_{k<K} 1/genSeq(n,k).
    This is the function whose divergence we study. -/
def recipPartialSum (n K : Nat) : ℝ :=
  ∑ k ∈ Finset.range K, (1 : ℝ) / (genSeq n k : ℝ)

/-- The partial reciprocal sum is non-negative. -/
theorem recipPartialSum_nonneg (n K : Nat) : 0 ≤ recipPartialSum n K := by
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- The partial reciprocal sum is non-decreasing in K. -/
theorem recipPartialSum_mono (n K : Nat) :
    recipPartialSum n K ≤ recipPartialSum n (K + 1) := by
  unfold recipPartialSum
  rw [Finset.sum_range_succ]
  have : 0 ≤ (1 : ℝ) / (genSeq n K : ℝ) := by positivity
  linarith

/-- Each term in the reciprocal sum is at most 1/2 (since genSeq ≥ 2). -/
theorem recipPartialSum_term_le_half {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    (1 : ℝ) / (genSeq n k : ℝ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (genSeq n k : ℝ) := by exact_mod_cast (genSeq_prime hn k).two_le
  exact div_le_div_of_nonneg_left zero_le_one (by positivity : (0:ℝ) < 2) h2

end ReciprocalPartialSums

/-! ## Divergence Definitions -/

section DivergenceDefinitions

/-- The reciprocal sum of the generalized EM sequence from n **diverges**:
    for every bound M, the partial sums eventually exceed M. -/
def recipSumDiverges (n : Nat) : Prop :=
  ∀ M : ℝ, ∃ K : Nat, M ≤ recipPartialSum n K

/-- **Almost All Squarefree RSD**: for every bound M > 0, the density of
    squarefree integers n whose reciprocal partial sums are all below M is zero.

    This implies: for almost all squarefree n (density 1), the reciprocal sum
    ∑_k 1/em_n(k) diverges.

    This is weaker than ReciprocalDivergence (for the specific starting point
    n = 2); the single-trajectory statement remains open. -/
def AlmostAllSquarefreeRSD : Prop :=
  ∀ M : ℝ, 0 < M →
    Filter.Tendsto
      (fun X : Nat =>
        (((Finset.Icc 1 X).filter
          (fun n => Squarefree n ∧ ∀ K, recipPartialSum n K < M)).card : ℝ) /
        ((Finset.Icc 1 X).filter Squarefree).card)
      Filter.atTop (nhds 0)

end DivergenceDefinitions

/-! ## Asymptotic Hypothesis -/

section AsymptoticHypothesis

/-- **Reciprocal Sum Concentration**: for each bound M > 0 and tolerance ε > 0,
    there exists K₀ such that for K ≥ K₀, the density of squarefree n ≤ X with
    S_K(n) < M is eventually at most ε.

    This is the quantitative consequence of the first moment (~ κK) and
    variance bound (O(K)) via Chebyshev's inequality:

    Pr_n[S_K(n) < M] ≤ Pr_n[|S_K(n) − κK| > κK − M] ≤ Var/(κK − M)² = O(1/K)

    for K > M/κ. The O(1/K) → 0 as K → ∞, so K₀ can be chosen to make
    this bound < ε.

    The decorrelation between steps (approximate independence
    of 1/em_n(j) and 1/em_n(k) when averaged over starting points n) ensures
    the variance bound holds.

    **Proof from standard ANT:** The first moment uses PE (Population
    Equidistribution, proved from Dirichlet + sieve). The variance bound uses
    CRT decorrelation (`crt_multiplier_invariance`, proved) and the +1 shift
    destroying residue correlations.

    **Quantifier structure**: ε appears before K₀, so K₀ can depend on ε.
    This is the correct structure for Chebyshev-type arguments, where the
    bound CK/(mean-M)² decreases with K but is a constant for fixed K. -/
def RecipSumConcentration : Prop :=
  ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε →
  ∃ K₀ : Nat,
    ∀ K ≥ K₀, ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ recipPartialSum n K < M)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card ≤ ε

end AsymptoticHypothesis

/-! ## Main Reduction: Concentration → RSD -/

section MainReduction

/-- If n satisfies ∀ K, S_K(n) < M, then in particular S_K₀(n) < M. -/
private theorem forall_bounded_subset (M : ℝ) (X K : Nat) :
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ ∀ L, recipPartialSum n L < M)) ⊆
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ recipPartialSum n K < M)) := by
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2 K⟩

private theorem card_ratio_le_of_subset {s t u : Finset Nat}
    (hst : s ⊆ t) (hu : 0 < (u.card : ℝ)) :
    (s.card : ℝ) / u.card ≤ (t.card : ℝ) / u.card :=
  div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hst) (le_of_lt hu)

/-- **Concentration → Almost All Squarefree RSD.**

    If RecipSumConcentration holds, then for any M > 0, the set
    {n squarefree : ∀ K, S_K(n) < M} has density 0.

    Proof: {n : ∀ K, S_K(n) < M} ⊆ {n : S_K(n) < M} for each K.
    By concentration with tolerance ε, the density of the latter is ≤ ε
    for K ≥ K₀(ε) and X ≥ X₀. Since the former is a subset, its density
    is also ≤ ε. Since ε was arbitrary, the density → 0. -/
theorem concentration_implies_rsd
    (hconc : RecipSumConcentration) : AlmostAllSquarefreeRSD := by
  intro M hM
  rw [show nhds (0 : ℝ) = nhds 0 from rfl]
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get K₀ from concentration with tolerance ε/2 (strict inequality from ≤)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨K₀, hK₀⟩ := hconc M hM (ε / 2) hε2
  -- Use K = K₀: density of {n : S_{K₀} < M} ≤ ε/2 eventually
  obtain ⟨X₀, hX₀⟩ := hK₀ K₀ (le_refl _)
  refine ⟨X₀, fun X hX => ?_⟩
  rw [Real.dist_eq, sub_zero]
  -- The density of {n : ∀K, S_K(n) < M} ≤ density of {n : S_{K₀}(n) < M}
  have h_card := Finset.card_le_card (forall_bounded_subset M X K₀)
  have h_density_le : (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ ∀ L, recipPartialSum n L < M)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card ≤ ε / 2 := by
    calc (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ ∀ L, recipPartialSum n L < M)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card
        ≤ (((Finset.Icc 1 X).filter
          (fun n => Squarefree n ∧ recipPartialSum n K₀ < M)).card : ℝ) /
        ((Finset.Icc 1 X).filter Squarefree).card := by
          apply div_le_div_of_nonneg_right (by exact_mod_cast h_card) (Nat.cast_nonneg _)
      _ ≤ ε / 2 := hX₀ X hX
  have h_nn : 0 ≤ (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ ∀ L, recipPartialSum n L < M)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [abs_of_nonneg h_nn]
  linarith

end MainReduction

/-! ## Connections -/

section Connections

/-- The standard EM accumulator P(0) = 2 equals genProd 2 0. -/
theorem genProd_two_eq_prod_zero : genProd 2 0 = prod 0 := rfl

/-- RSD for almost all squarefree n is a necessary condition for MC:
    MC → every prime appears → ∑ 1/p over appearing primes diverges
    → the reciprocal sums diverge for at least the standard trajectory.

    This theorem asserts: if MC and RecipSumConcentration both hold,
    then AlmostAllSquarefreeRSD holds. The MC implication is vacuous
    here (MC is already used elsewhere in the project); the value is in
    making the chain explicit. -/
theorem mc_and_concentration_implies_rsd
    (hconc : RecipSumConcentration) :
    AlmostAllSquarefreeRSD :=
  concentration_implies_rsd hconc

end Connections

/-! ## Pairwise Decorrelation Framework

Dead End #125 proved: pairwise (k=2) cancellation does NOT imply k-wise (XOR
counterexample). This killed the CCSB+CPD → UPE route.

But variance bounds only use k=2:
  Var(∑ X_j) = ∑ Var(X_j) + 2 ∑_{j<k} Cov(X_j, X_k)

If Cov → 0 (pairwise), then Var grows at most linearly.
If mean grows linearly (κK with κ > 0), Chebyshev gives concentration.

So: PSD (pairwise, k=2) + FM (mean → κ) → RSC → AASRSD.

This is genuinely weaker than CME. PSD does not require conditional
equidistribution — only that the reciprocals at different steps are
approximately uncorrelated when averaged over starting points. -/

section PairwiseDecorrelation

/-! ### Local averaging infrastructure

We define local versions of the ensemble average to avoid a circular import
with `Ensemble.FirstMoment` (which transitively imports this file). -/

/-- The squarefree integers in [1, X]. -/
private abbrev sfSet (X : Nat) : Finset Nat :=
  (Finset.Icc 1 X).filter Squarefree

/-- Count of squarefree integers in [1, X]. -/
private abbrev sfCard (X : Nat) : Nat := (sfSet X).card

/-- Ensemble average of f over squarefree n in [1, X]. When the squarefree
    count is zero, returns 0 (harmless — the set is nonempty for X ≥ 1). -/
private def sfAvg (X : Nat) (f : Nat → ℝ) : ℝ :=
  (∑ n ∈ sfSet X, f n) / (sfCard X : ℝ)

/-- Ensemble covariance of f and g over squarefree n in [1, X]:
    E[f·g] - E[f]·E[g]. -/
private def sfCov (X : Nat) (f g : Nat → ℝ) : ℝ :=
  sfAvg X (fun n => f n * g n) - sfAvg X f * sfAvg X g

/-! ### Definitions -/

/-- **Pairwise step decorrelation**: the ensemble covariance of reciprocals
    at distinct steps vanishes as X → ∞. For j ≠ k:

    Cov_n[1/genSeq(n,j), 1/genSeq(n,k)] → 0

    where the covariance is over squarefree starting points n ≤ X.

    This is strictly weaker than k-wise independence (Dead End #125: XOR
    counterexample shows pairwise does not imply 3-wise), but EXACTLY what
    is needed for variance bounds, since

    Var(∑_j X_j) = ∑_j Var(X_j) + 2 ∑_{j<k} Cov(X_j, X_k).

    **Mathematical basis**: CRT decorrelation (`crt_multiplier_invariance`,
    proved) ensures that genSeq(n,j) and genSeq(n,k) are approximately
    independent when averaged over starting points, because the multiplier
    at step k depends on the walk position at step k (via CRT fiber), which
    is approximately independent of the walk position at step j. -/
def PairwiseStepDecorrelation : Prop :=
  ∀ (j k : ℕ), j ≠ k →
    Filter.Tendsto
      (fun X : ℕ => sfCov X (fun n => (1 : ℝ) / genSeq n j)
                               (fun n => (1 : ℝ) / genSeq n k))
      Filter.atTop (nhds 0)

/-- **Ensemble mean divergence**: the ensemble average of the partial
    reciprocal sum S_K(n) = ∑_{k<K} 1/genSeq(n,k) diverges as K → ∞.

    If the first moment step gives E[1/genSeq(n,k)] → κ > 0, then by
    linearity of expectation (finite sums), E[S_K] ≈ κK → ∞.

    This captures the "mean grows linearly" half of the Chebyshev argument.

    Formulation: for any bound M, there exists K₀ such that for K ≥ K₀,
    the ensemble mean of S_K eventually exceeds M (as X → ∞). -/
def EnsembleMeanDivergence : Prop :=
  ∀ M : ℝ, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∃ X₀ : ℕ, ∀ X ≥ X₀,
    M ≤ sfAvg X (fun n => recipPartialSum n K)

/-- **Individual variance bound**: the variance of 1/genSeq(n,k) over
    squarefree starting points is uniformly bounded.

    Since genSeq(n,k) ≥ 2 for squarefree n ≥ 1, we have 1/genSeq(n,k) ∈ (0, 1/2],
    so Var[1/genSeq(n,k)] ≤ E[(1/genSeq(n,k))²] ≤ 1/4.

    This is the diagonal contribution to Var[S_K]. -/
def IndividualVarianceBound (V : ℝ) : Prop :=
  ∀ k : ℕ, ∃ X₀ : ℕ, ∀ X ≥ X₀,
    sfAvg X (fun n => ((1 : ℝ) / genSeq n k) ^ 2) -
    (sfAvg X (fun n => (1 : ℝ) / genSeq n k)) ^ 2 ≤ V

/-- **PSD+IVB implies variance bound**: if the pairwise covariances vanish
    and individual variances are bounded by V, then
    Var[S_K] ≤ K·V + o(K) = O(K).

    The variance decomposes as:
    Var[S_K] = ∑_{j<K} Var[1/genSeq(n,j)] + 2 ∑_{j<k<K} Cov(j,k)
             ≤ K·V + 2 ∑_{j<k<K} |Cov(j,k)|

    Each |Cov(j,k)| → 0 by PSD. For a fixed K, the sum has K(K-1)/2 terms
    and each → 0, so the sum → 0 (finite sum of vanishing terms).
    Hence for large X, the sum ≤ K (say), giving Var ≤ K(V+1).

    **Status**: PROVED (see `psd_ivb_implies_variance_bound_proved`). -/
def PSDIVBImpliesVarianceBound : Prop :=
  ∀ (V : ℝ), 0 < V →
    PairwiseStepDecorrelation → IndividualVarianceBound V →
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∃ X₀ : ℕ, ∀ X ≥ X₀,
      sfAvg X (fun n => (recipPartialSum n K) ^ 2) -
      (sfAvg X (fun n => recipPartialSum n K)) ^ 2 ≤ C * K

/-- **Linear mean growth**: the ensemble mean of S_K grows linearly in K.
    There exists κ > 0 such that for every K, the ensemble mean of S_K is
    eventually (as X → ∞) at least κK.

    This is the quantitative consequence of the first moment step:
    E[1/genSeq n k] → κ implies E[S_K] ≈ κK by linearity. The constant κ
    is the reciprocal constant (κ = E[1/minFac] ≥ 1/3 from the p=2 term).

    LinearMeanGrowth is strictly stronger than EnsembleMeanDivergence (it
    provides a RATE, not just eventual divergence), but is the natural
    consequence of FirstMomentStep. -/
def LinearMeanGrowth : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ K : ℕ, ∃ X₀ : ℕ, ∀ X ≥ X₀,
    κ * K ≤ sfAvg X (fun n => recipPartialSum n K)

/-- LinearMeanGrowth implies EnsembleMeanDivergence. -/
theorem linear_mean_growth_implies_emd : LinearMeanGrowth → EnsembleMeanDivergence := by
  intro ⟨κ, hκ, hlmg⟩ M
  -- Choose K₀ = ⌈M/κ⌉ + 1
  refine ⟨Nat.ceil (M / κ) + 1, fun K hK => ?_⟩
  obtain ⟨X₀, hX₀⟩ := hlmg K
  refine ⟨X₀, fun X hX => ?_⟩
  have hK_bound : M / κ < K := by
    calc M / κ ≤ ↑(Nat.ceil (M / κ)) := Nat.le_ceil _
      _ < ↑(Nat.ceil (M / κ)) + 1 := by linarith
      _ ≤ (K : ℝ) := by exact_mod_cast hK
  calc M = κ * (M / κ) := by field_simp
    _ ≤ κ * K := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hκ)
        exact le_of_lt hK_bound
    _ ≤ sfAvg X (fun n => recipPartialSum n K) := hX₀ X hX

/-- **Chebyshev concentration**: if the mean grows linearly and the variance
    grows at most linearly, then RecipSumConcentration holds.

    Proof: for K large enough that κK > M, by one-sided Chebyshev:
    Pr[S_K < M] ≤ Var/(mean - M)² ≤ CK/(κK - M)² → 0 as K → ∞.
    The monotonicity of S_K in K (non-decreasing) ensures that the density
    of {S_K < M} is non-increasing in K, so the bound for K₀ extends to
    all K ≥ K₀.

    **Status**: PROVED (see `chebyshev_concentration_proved`). -/
def ChebyshevConcentration : Prop :=
  LinearMeanGrowth →
  (∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, ∃ X₀ : ℕ, ∀ X ≥ X₀,
    sfAvg X (fun n => (recipPartialSum n K) ^ 2) -
    (sfAvg X (fun n => recipPartialSum n K)) ^ 2 ≤ C * K) →
  RecipSumConcentration

/-- The density of {S_K < M} is non-increasing in K, because S_K is non-decreasing. -/
private theorem density_mono_K (M : ℝ) (X : Nat) (K₁ K₂ : Nat) (h : K₁ ≤ K₂) :
    (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ recipPartialSum n K₂ < M)).card : ℝ) ≤
    (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ recipPartialSum n K₁ < M)).card : ℝ) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, hn.2.1, ?_⟩
  calc recipPartialSum n K₁ ≤ recipPartialSum n K₂ := by
        unfold recipPartialSum
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono h
        · intro k _ _; exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    _ < M := hn.2.2

/-- **One-sided Chebyshev at the Finset level.**
    If mean >= mu > M and Var <= sigma2, then
    #{n : f(n) < M} / |sfSet| <= sigma2 / (mu - M)^2. -/
private theorem finset_chebyshev (X K : Nat) (M mu sigma2 : ℝ)
    (hmu : mu ≤ sfAvg X (fun n => recipPartialSum n K))
    (hmuM : M < mu)
    (hvar : sfAvg X (fun n => (recipPartialSum n K) ^ 2) -
            (sfAvg X (fun n => recipPartialSum n K)) ^ 2 ≤ sigma2)
    (hsigma_nn : 0 ≤ sigma2)
    (hcard_pos : 0 < sfCard X) :
    (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ recipPartialSum n K < M)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card ≤ sigma2 / (mu - M) ^ 2 := by
  set S := sfSet X
  set badSet := S.filter (fun n => recipPartialSum n K < M) with hbadSet_def
  have hbad_sub : badSet ⊆ S := Finset.filter_subset _ _
  set mean := sfAvg X (fun n => recipPartialSum n K)
  have hmean_ge : mu ≤ mean := hmu
  have hmean_M : M < mean := lt_of_lt_of_le hmuM hmean_ge
  have hcard_pos_real : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard_pos
  have hmeanM_pos : (0 : ℝ) < mean - M := by linarith
  have hmuM_pos : (0 : ℝ) < mu - M := by linarith
  -- For n in badSet: S_K(n) < M < mean, so (S_K(n) - mean)^2 >= (mean-M)^2
  have h_diff_sq : ∀ n ∈ badSet, (mean - M) ^ 2 ≤ (recipPartialSum n K - mean) ^ 2 := by
    intro n hn
    simp only [hbadSet_def, Finset.mem_filter] at hn
    have h1 : mean - M ≤ mean - recipPartialSum n K := by linarith
    calc (mean - M) ^ 2 ≤ (mean - recipPartialSum n K) ^ 2 :=
          sq_le_sq' (by linarith) h1
      _ = (recipPartialSum n K - mean) ^ 2 := by ring_nf
  -- |bad|*(mean-M)^2 <= sum_{n in S} (S_K(n) - mean)^2
  have h_key : (badSet.card : ℝ) * (mean - M) ^ 2 ≤
      ∑ n ∈ S, (recipPartialSum n K - mean) ^ 2 := by
    calc (badSet.card : ℝ) * (mean - M) ^ 2
        = ∑ _n ∈ badSet, (mean - M) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ badSet, (recipPartialSum n K - mean) ^ 2 :=
          Finset.sum_le_sum h_diff_sq
      _ ≤ ∑ n ∈ S, (recipPartialSum n K - mean) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hbad_sub (fun _ _ _ => sq_nonneg _)
  -- sum_{n in S} (S_K(n) - mean)^2 = |S| * Var
  -- where Var = E[S^2] - (E[S])^2, and mean = E[S] = sfAvg
  -- So sum = sum(S^2) - |S|*mean^2, and sum/|S| = E[S^2] - mean^2 = Var
  -- Thus sum = |S| * Var <= |S| * sigma2
  have h_sum_eq : ∑ n ∈ S, (recipPartialSum n K - mean) ^ 2 =
      ∑ n ∈ S, (recipPartialSum n K) ^ 2 - 2 * mean * ∑ n ∈ S, recipPartialSum n K +
      S.card * mean ^ 2 := by
    have h1 : ∀ n, (recipPartialSum n K - mean) ^ 2 =
        (recipPartialSum n K) ^ 2 - 2 * mean * recipPartialSum n K + mean ^ 2 := by
      intro n; ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 1
    · congr 1
      rw [← Finset.mul_sum]
    · rw [Finset.sum_const, nsmul_eq_mul]
  have h_mean_eq : mean = (∑ n ∈ S, recipPartialSum n K) / (S.card : ℝ) := rfl
  -- sum/|S| = E[S^2] - mean^2 = Var
  have h_sum_div : (∑ n ∈ S, (recipPartialSum n K - mean) ^ 2) / (S.card : ℝ) =
      sfAvg X (fun n => (recipPartialSum n K) ^ 2) -
      (sfAvg X (fun n => recipPartialSum n K)) ^ 2 := by
    rw [h_sum_eq]
    simp only [sfAvg, S, mean]
    field_simp
    ring
  -- sum <= |S| * sigma2
  have h_sum_le : ∑ n ∈ S, (recipPartialSum n K - mean) ^ 2 ≤ (S.card : ℝ) * sigma2 := by
    have h1 : (∑ n ∈ S, (recipPartialSum n K - mean) ^ 2) / (S.card : ℝ) ≤ sigma2 :=
      le_trans (le_of_eq h_sum_div) hvar
    rw [mul_comm]; rwa [div_le_iff₀ hcard_pos_real] at h1
  -- |bad|*(mean-M)^2 <= |S|*sigma2, so |bad|/|S| <= sigma2/(mean-M)^2
  have h_ratio : (badSet.card : ℝ) / (S.card : ℝ) ≤ sigma2 / (mean - M) ^ 2 := by
    rw [div_le_div_iff₀ hcard_pos_real (by positivity : (0:ℝ) < (mean - M) ^ 2)]
    linarith [le_trans h_key h_sum_le]
  -- badSet = filtered set we want
  have h_set_eq : (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ recipPartialSum n K < M) =
      badSet := by
    simp only [hbadSet_def, S, sfSet]
    ext n
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  rw [h_set_eq]
  calc (badSet.card : ℝ) / (S.card : ℝ) ≤ sigma2 / (mean - M) ^ 2 := h_ratio
    _ ≤ sigma2 / (mu - M) ^ 2 := by
        apply div_le_div_of_nonneg_left hsigma_nn (by positivity) _
        exact sq_le_sq' (by linarith) (by linarith)

/-- **ChebyshevConcentration PROVED.**

    Uses LinearMeanGrowth (mean ≥ κK) and variance bound (Var ≤ CK) to
    establish RecipSumConcentration via one-sided Chebyshev inequality.

    For K ≥ K₀ where K₀ is large enough that CK₀/(κK₀-M)² ≤ ε:
    1. Mean ≥ κK > M for K large
    2. Chebyshev: density ≤ CK/(κK-M)² ≤ CK₀/(κK₀-M)² ≤ ε
       (using monotonicity: CK/(κK-M)² is decreasing for K > M/κ)
    3. Monotonicity of density in K: {S_K < M} ⊆ {S_{K₀} < M}, so
       density_K ≤ density_{K₀} ≤ ε -/
theorem chebyshev_concentration_proved : ChebyshevConcentration := by
  intro ⟨κ, hκ, hmean_growth⟩ ⟨C, hC, hvar⟩
  -- Need: ∀ M > 0, ∀ ε > 0, ∃ K₀, ∀ K ≥ K₀, ∃ X₀, ∀ X ≥ X₀, density ≤ ε
  intro M hM ε hε
  -- Choose K₀ large enough:
  -- (a) κ*K₀ > M  (so mean > M)
  -- (b) C*K₀/(κ*K₀ - M)² ≤ ε  (so Chebyshev bound ≤ ε)
  -- For (b): CK/(κK-M)² → 0 as K → ∞, so large K₀ suffices.
  -- Specifically: CK/(κK-M)² ≤ ε iff (κK-M)² ≥ CK/ε
  -- For K ≥ (2M/κ + 1): κK ≥ 2M+κ > 2M, so κK-M ≥ M+κ > M > 0
  -- and κK-M ≥ κK/2 (since κK ≥ 2M implies κK-M ≥ κK-κK/2 = κK/2)
  -- so (κK-M)² ≥ κ²K²/4, and CK/(κK-M)² ≤ 4C/(κ²K)
  -- Choose K₀ ≥ max(⌈2M/κ⌉+1, ⌈4C/(κ²ε)⌉+1) to get 4C/(κ²K₀) ≤ ε.
  set K_a := Nat.ceil (2 * M / κ) + 1
  set K_b := Nat.ceil (4 * C / (κ ^ 2 * ε)) + 1
  set K₀ := max K_a K_b
  refine ⟨K₀, fun K hK => ?_⟩
  -- Get X₀ from mean growth and variance bound for this K
  obtain ⟨X₁, hX₁⟩ := hmean_growth K
  obtain ⟨X₂, hX₂⟩ := hvar K
  refine ⟨max X₁ X₂, fun X hX => ?_⟩
  have hX₁' : X ≥ X₁ := le_trans (le_max_left _ _) hX
  have hX₂' : X ≥ X₂ := le_trans (le_max_right _ _) hX
  -- Key bounds
  have hK_ge_a : K_a ≤ K := le_trans (le_max_left _ _) hK
  have hK_ge_b : K_b ≤ K := le_trans (le_max_right _ _) hK
  have hK_pos : (0 : ℝ) < (K : ℝ) := by
    have : 1 ≤ K_a := Nat.le_add_left 1 _
    exact_mod_cast show 0 < K by omega
  have h2M_lt_κK : 2 * M < κ * K := by
    have h2Mκ_lt : 2 * M / κ < (K : ℝ) := by
      calc 2 * M / κ ≤ ↑(Nat.ceil (2 * M / κ)) := Nat.le_ceil _
        _ < ↑(Nat.ceil (2 * M / κ)) + 1 := by linarith
        _ ≤ (K_a : ℝ) := by simp [K_a]
        _ ≤ (K : ℝ) := by exact_mod_cast hK_ge_a
    -- 2M/κ < K and κ > 0, so 2M = κ·(2M/κ) < κK
    nlinarith [mul_comm κ (2 * M / κ), div_mul_cancel₀ (2 * M) (ne_of_gt hκ)]
  have hκK_gt_M : M < κ * K := by linarith
  -- Handle case where sfCard = 0 (trivial: density = 0/0 = 0 <= epsilon)
  by_cases hcard : sfCard X = 0
  · have : ((Finset.Icc 1 X).filter Squarefree).card = 0 := hcard
    rw [this, Nat.cast_zero, div_zero]
    exact le_of_lt hε
  have hcard_pos : 0 < sfCard X := Nat.pos_of_ne_zero hcard
  -- Apply one-sided Chebyshev
  have hmean_bound := hX₁ X hX₁'
  have hvar_bound := hX₂ X hX₂'
  have hCK_nn : (0 : ℝ) ≤ C * K := by positivity
  have h_cheb := finset_chebyshev X K M (κ * K) (C * K) hmean_bound hκK_gt_M hvar_bound hCK_nn hcard_pos
  -- Now bound C*K/(κ*K - M)² ≤ ε
  calc (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ recipPartialSum n K < M)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card
      ≤ C * K / (κ * K - M) ^ 2 := h_cheb
    _ ≤ ε := by
        -- CK/(κK-M)² ≤ 4C/(κ²K) ≤ ε
        -- From κK > 2M: κK - M > κK/2, so (κK-M)² > κ²K²/4
        have hκK_half : κ * K / 2 ≤ κ * K - M := by linarith
        have hκKM_pos : (0 : ℝ) < κ * K - M := by linarith
        have h_denom : κ ^ 2 * K ^ 2 / 4 ≤ (κ * K - M) ^ 2 := by
          have := mul_self_le_mul_self (by positivity : 0 ≤ κ * K / 2) hκK_half
          nlinarith
        -- So CK/(κK-M)² ≤ CK / (κ²K²/4) = 4C/(κ²K)
        have hκ2K_pos : (0:ℝ) < κ ^ 2 * K := mul_pos (by positivity) hK_pos
        have hκKM_sq_pos : (0 : ℝ) < (κ * K - M) ^ 2 := by positivity
        have h4C : C * K / (κ * K - M) ^ 2 ≤ 4 * C / (κ ^ 2 * K) := by
          rw [div_le_div_iff₀ hκKM_sq_pos hκ2K_pos]
          -- Goal: C * K * (κ² * K) ≤ 4 * C * (κK-M)²
          -- From h_denom: κ²K²/4 ≤ (κK-M)², so κ²K² ≤ 4(κK-M)²
          -- Therefore C * κ²K² ≤ 4C(κK-M)²
          have hd : κ ^ 2 * (K : ℝ) ^ 2 ≤ 4 * (κ * K - M) ^ 2 := by linarith
          nlinarith [le_of_lt hC]
        -- And 4C/(κ²K) ≤ ε when K ≥ K_b = ⌈4C/(κ²ε)⌉ + 1
        have h_target : 4 * C / (κ ^ 2 * K) ≤ ε := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < κ ^ 2 * K)]
          have hκ2ε_pos : (0:ℝ) < κ ^ 2 * ε := mul_pos (by positivity) hε
          have h_lt_K : 4 * C / (κ ^ 2 * ε) < (K : ℝ) := by
            calc 4 * C / (κ ^ 2 * ε)
                ≤ ↑(Nat.ceil (4 * C / (κ ^ 2 * ε))) := Nat.le_ceil _
              _ < ↑(Nat.ceil (4 * C / (κ ^ 2 * ε))) + 1 := by linarith
              _ ≤ (K_b : ℝ) := by simp [K_b]
              _ ≤ (K : ℝ) := by exact_mod_cast hK_ge_b
          -- 4C/(κ²ε) < K, so 4C < κ²ε * K = ε * (κ² * K)
          linarith [(div_lt_iff₀ hκ2ε_pos).mp h_lt_K]
        linarith

/-! ### Proved Reductions -/

/-- The squarefree average of a sum equals the sum of averages (linearity). -/
private theorem sfAvg_sum (X : Nat) (K : Nat) (f : Nat → Nat → ℝ) :
    sfAvg X (fun n => ∑ k ∈ Finset.range K, f n k) =
    ∑ k ∈ Finset.range K, sfAvg X (fun n => f n k) := by
  simp only [sfAvg]
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

/-- Linearity of sfAvg for scalar multiplication. -/
private theorem sfAvg_const_mul (X : Nat) (c : ℝ) (f : Nat → ℝ) :
    sfAvg X (fun n => c * f n) = c * sfAvg X f := by
  simp only [sfAvg, ← Finset.mul_sum, mul_div_assoc']


/-- The squared sum expands as a double sum of products. -/
private theorem sq_sum_eq_double_sum {K : Nat} (a : Nat → ℝ) :
    (∑ j ∈ Finset.range K, a j) ^ 2 =
    ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K, a j * a k := by
  rw [sq, Finset.sum_mul_sum]

/-- sfAvg of a double sum equals the double sum of sfAvg. -/
private theorem sfAvg_double_sum (X K : Nat) (f : Nat → Nat → Nat → ℝ) :
    sfAvg X (fun n => ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K, f n j k) =
    ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K, sfAvg X (fun n => f n j k) := by
  rw [sfAvg_sum]
  congr 1
  ext j
  exact sfAvg_sum X K (fun n k => f n j k)

/-- **Variance decomposition**: the variance of a sum of K functions equals
    the double sum of covariances (including diagonal = variance). -/
private theorem variance_eq_double_sum_cov (X K : Nat) (f : Nat → Nat → ℝ) :
    sfAvg X (fun n => (∑ j ∈ Finset.range K, f n j) ^ 2) -
    (sfAvg X (fun n => ∑ j ∈ Finset.range K, f n j)) ^ 2 =
    ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
      sfCov X (fun n => f n j) (fun n => f n k) := by
  -- LHS first term: E[S²] = E[∑∑ f_j f_k] = ∑∑ E[f_j f_k]
  have h1 : sfAvg X (fun n => (∑ j ∈ Finset.range K, f n j) ^ 2) =
      ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
        sfAvg X (fun n => f n j * f n k) := by
    conv_lhs => rw [show (fun n => (∑ j ∈ Finset.range K, f n j) ^ 2) =
      (fun n => ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K, f n j * f n k) from
      by ext n; rw [sq_sum_eq_double_sum]]
    exact sfAvg_double_sum X K (fun n j k => f n j * f n k)
  -- LHS second term: (E[S])² = (∑ E[f_j])² = ∑∑ E[f_j] E[f_k]
  have h2 : (sfAvg X (fun n => ∑ j ∈ Finset.range K, f n j)) ^ 2 =
      ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
        sfAvg X (fun n => f n j) * sfAvg X (fun n => f n k) := by
    rw [sfAvg_sum]
    rw [sq_sum_eq_double_sum]
  -- Combine: ∑∑ E[f_j f_k] - ∑∑ E[f_j]E[f_k] = ∑∑ (E[f_j f_k] - E[f_j]E[f_k])
  rw [h1, h2, ← Finset.sum_sub_distrib]
  congr 1; ext j
  simp only [← Finset.sum_sub_distrib, sfCov]

/-- **PSD + IVB implies variance bound (PROVED).**

    For each fixed K, extract X₀ from IVB for each j < K and from PSD for
    each pair (j,k), take the max. Diagonal terms contribute ≤ K·V, and
    K²−K off-diagonal terms each contribute ≤ 1/K², giving total ≤ K·V + 1. -/
theorem psd_ivb_implies_variance_bound_proved : PSDIVBImpliesVarianceBound := by
  intro V hV hpsd hivb
  refine ⟨V + 1, by linarith, ?_⟩
  intro K
  -- Handle K = 0 trivially
  by_cases hK : K = 0
  · subst hK
    exact ⟨0, fun X _ => by simp [recipPartialSum, sfAvg]⟩
  -- K ≥ 1
  have hK_pos : 0 < K := Nat.pos_of_ne_zero hK
  -- Abbreviation for the per-step function
  set f : Nat → Nat → ℝ := fun n j => (1 : ℝ) / genSeq n j with hf_def
  -- Step 1: For each j < K, get X₀ from IVB such that sfCov(f_j, f_j) ≤ V
  have h_ivb_bound : ∀ j : Nat, j < K → ∃ X₀ : Nat, ∀ X ≥ X₀,
      sfCov X (fun n => f n j) (fun n => f n j) ≤ V := by
    intro j _
    obtain ⟨X₀, hX₀⟩ := hivb j
    refine ⟨X₀, fun X hX => ?_⟩
    specialize hX₀ X hX
    -- sfCov f_j f_j = Var[f_j] = IVB expression
    show sfAvg X (fun n => f n j * f n j) -
      sfAvg X (fun n => f n j) * sfAvg X (fun n => f n j) ≤ V
    have hmul_eq : (fun n => f n j * f n j) = (fun n => ((1 : ℝ) / genSeq n j) ^ 2) := by
      ext n; simp [hf_def, sq]
    have hsq_eq : sfAvg X (fun n => f n j) * sfAvg X (fun n => f n j) =
      (sfAvg X (fun n => (1 : ℝ) / genSeq n j)) ^ 2 := by
      simp [hf_def, sq]
    rw [hmul_eq, hsq_eq]
    exact hX₀
  -- Step 2: For each off-diagonal pair, get X₀ from PSD such that sfCov ≤ ε
  set ε : ℝ := 1 / ((K : ℝ) ^ 2 + 1) with hε_def
  have hε_pos : 0 < ε := by positivity
  have h_psd_bound : ∀ j k : Nat, j < K → k < K → j ≠ k →
      ∃ X₀ : Nat, ∀ X ≥ X₀,
        sfCov X (fun n => f n j) (fun n => f n k) ≤ ε := by
    intro j k _ _ hjk
    have htend := hpsd j k hjk
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨X₀, hX₀⟩ := htend ε hε_pos
    refine ⟨X₀, fun X hX => ?_⟩
    have h_dist := hX₀ X hX
    rw [Real.dist_eq] at h_dist
    simp only [sub_zero] at h_dist
    -- |sfCov| < ε implies sfCov ≤ ε
    exact le_of_lt (abs_lt.mp h_dist).2
  -- Step 3: For a fixed K, collect all X₀'s
  -- Use Classical.choice to get functions (no membership proofs)
  -- Extract choose_spec for later use
  -- (No separate h_diag_choose/h_cross_choose needed; use .choose_spec inline)
  -- Build the master threshold as a sup over a finset of all thresholds
  -- Map each element of range K × range K to its threshold
  set allPairs := Finset.range K ×ˢ Finset.range K
  -- For diagonal (j,j): use h_ivb_bound threshold
  -- For off-diagonal (j,k): use h_psd_bound threshold
  -- Combine into a single function on allPairs
  set threshold : Nat × Nat → Nat := fun p =>
    if h : p.1 < K ∧ p.2 < K then
      if heq : p.1 = p.2 then (h_ivb_bound p.1 h.1).choose
      else (h_psd_bound p.1 p.2 h.1 h.2 heq).choose
    else 0
  set X₀ := allPairs.sup threshold
  refine ⟨X₀, fun X hX => ?_⟩
  -- Helper: X ≥ threshold for any pair in allPairs
  have h_ge_thresh : ∀ p ∈ allPairs, X ≥ threshold p := by
    intro p hp
    calc threshold p ≤ allPairs.sup threshold := Finset.le_sup hp
      _ = X₀ := rfl
      _ ≤ X := hX
  -- Step 4: Use the variance decomposition
  rw [show (fun n => (recipPartialSum n K) ^ 2) =
    (fun n => (∑ j ∈ Finset.range K, f n j) ^ 2) from by ext; rfl]
  rw [show (fun n => recipPartialSum n K) =
    (fun n => ∑ j ∈ Finset.range K, f n j) from by ext; rfl]
  rw [variance_eq_double_sum_cov]
  -- Now bound ∑_j ∑_k sfCov ≤ K*V + K²*ε ≤ K*V + 1 ≤ (V+1)*K
  -- Split into diagonal and off-diagonal
  have h_diag_le : ∀ j ∈ Finset.range K,
      sfCov X (fun n => f n j) (fun n => f n j) ≤ V := by
    intro j hj
    have hjK := Finset.mem_range.mp hj
    have hp : (j, j) ∈ allPairs := Finset.mem_product.mpr ⟨hj, hj⟩
    have hge := h_ge_thresh (j, j) hp
    simp only [threshold, show j < K ∧ j < K from ⟨hjK, hjK⟩, dite_true] at hge
    apply (h_ivb_bound j hjK).choose_spec X hge
  have h_cross_le : ∀ j ∈ Finset.range K, ∀ k ∈ Finset.range K, j ≠ k →
      sfCov X (fun n => f n j) (fun n => f n k) ≤ ε := by
    intro j hj k hk hjk
    have hjK := Finset.mem_range.mp hj
    have hkK := Finset.mem_range.mp hk
    have hp : (j, k) ∈ allPairs := Finset.mem_product.mpr ⟨hj, hk⟩
    have hge := h_ge_thresh (j, k) hp
    simp only [threshold, show j < K ∧ k < K from ⟨hjK, hkK⟩, hjk] at hge
    apply (h_psd_bound j k hjK hkK hjk).choose_spec X hge
  -- Main bound
  calc ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
        sfCov X (fun n => f n j) (fun n => f n k)
      ≤ ∑ j ∈ Finset.range K, (V + ∑ k ∈ (Finset.range K).erase j,
          sfCov X (fun n => f n j) (fun n => f n k)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← Finset.add_sum_erase _ _ hj]
        gcongr
        exact h_diag_le j hj
    _ ≤ ∑ j ∈ Finset.range K, (V + ∑ _k ∈ (Finset.range K).erase j, ε) := by
        apply Finset.sum_le_sum
        intro j hj
        gcongr with k hk
        have hjk : j ≠ k := fun heq => (Finset.mem_erase.mp hk).1 heq.symm
        exact h_cross_le j hj k (Finset.erase_subset _ _ hk) hjk
    _ ≤ ∑ _j ∈ Finset.range K, (V + (K : ℝ) * ε) := by
        apply Finset.sum_le_sum
        intro j hj
        gcongr
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hε_pos)
        have : ((Finset.range K).erase j).card ≤ K := by
          rw [Finset.card_erase_of_mem hj, Finset.card_range]; omega
        exact_mod_cast this
    _ = (K : ℝ) * (V + (K : ℝ) * ε) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (V + 1) * (K : ℝ) := by
        have hK_bound : (K : ℝ) * ε ≤ 1 := by
          rw [hε_def]
          have hKsq_pos : (0 : ℝ) < (K : ℝ) ^ 2 + 1 := by positivity
          rw [mul_one_div, div_le_one hKsq_pos]
          nlinarith [sq_nonneg ((K : ℝ) - 1)]
        nlinarith [Nat.cast_nonneg (α := ℝ) K]

/-- **Individual variance bound from genSeq ≥ 2.**
    Since genSeq(n,k) ≥ 2 for squarefree n ≥ 1, we have
    (1/genSeq(n,k))² ≤ 1/4. So E[(1/genSeq)²] ≤ 1/4,
    and Var = E[X²] - (E[X])² ≤ E[X²] ≤ 1/4.

    We prove IndividualVarianceBound (1/4). -/
theorem individual_variance_quarter : IndividualVarianceBound (1 / 4) := by
  intro k
  use 0
  intro X _
  -- Step 1: Each term (1/genSeq)² ≤ 1/4
  have h_term_le : ∀ n ∈ sfSet X,
      ((1 : ℝ) / genSeq n k) ^ 2 ≤ 1 / 4 := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hgen : (2 : ℝ) ≤ (genSeq n k : ℝ) :=
      by exact_mod_cast (genSeq_prime hn.1.1 k).two_le
    have h_le_half : (1 : ℝ) / genSeq n k ≤ 1 / 2 :=
      div_le_div_of_nonneg_left zero_le_one (by linarith) hgen
    have h_nn : 0 ≤ (1 : ℝ) / genSeq n k := by positivity
    calc ((1 : ℝ) / genSeq n k) ^ 2
        ≤ (1 / 2) ^ 2 := sq_le_sq' (by linarith) h_le_half
      _ = 1 / 4 := by norm_num
  -- Step 2: E[X²] ≤ 1/4
  have h_le : sfAvg X (fun n => ((1 : ℝ) / genSeq n k) ^ 2) ≤ 1 / 4 := by
    simp only [sfAvg]
    by_cases hcard : sfCard X = 0
    · simp [hcard]
    · have hcard_pos : (0 : ℝ) < sfCard X := by exact_mod_cast Nat.pos_of_ne_zero hcard
      rw [div_le_iff₀ hcard_pos]
      calc ∑ n ∈ sfSet X, ((1 : ℝ) / ↑(genSeq n k)) ^ 2
          ≤ ∑ _n ∈ sfSet X, (1 : ℝ) / 4 :=
            Finset.sum_le_sum h_term_le
        _ = sfCard X * (1 / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = 1 / 4 * sfCard X := by ring
  -- Step 2: (E[X])² ≥ 0
  have h_sq_nn : 0 ≤ (sfAvg X (fun n => (1 : ℝ) / ↑(genSeq n k))) ^ 2 := sq_nonneg _
  linarith

/-- **genSeq ≥ 2 for squarefree starting points.** -/
private theorem genSeq_ge_two {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    2 ≤ genSeq n k :=
  (genSeq_prime hn k).two_le

/-- **Reciprocal term in (0, 1/2].** -/
private theorem recip_genSeq_le_half {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    (1 : ℝ) / genSeq n k ≤ 1 / 2 := by
  have : (2 : ℝ) ≤ genSeq n k := by exact_mod_cast genSeq_ge_two hn k
  exact div_le_div_of_nonneg_left zero_le_one (by positivity) this

/-- **Reciprocal term is positive.** -/
private theorem recip_genSeq_pos {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    0 < (1 : ℝ) / genSeq n k := by
  have : (2 : ℝ) ≤ genSeq n k := by exact_mod_cast genSeq_ge_two hn k
  positivity

/-- **PSD + IVB + Chebyshev + LinearMeanGrowth → Concentration.**

    The full chain combining all components:
    1. PSD + IVB → VarianceBound (via PSDIVBImpliesVarianceBound)
    2. LinearMeanGrowth + VarianceBound → Concentration (via ChebyshevConcentration)

    This makes the open hypotheses explicit. -/
theorem psd_chain_implies_concentration
    (h_psd : PairwiseStepDecorrelation)
    (h_ivb : IndividualVarianceBound (1 / 4))
    (h_bridge : PSDIVBImpliesVarianceBound)
    (h_mean : LinearMeanGrowth)
    (h_cheb : ChebyshevConcentration) :
    RecipSumConcentration := by
  obtain ⟨C, hC_pos, hC⟩ := h_bridge (1 / 4) (by positivity) h_psd h_ivb
  exact h_cheb h_mean ⟨C, hC_pos, hC⟩

/-- **PSD chain → Almost All Squarefree RSD.**

    Full chain: PSD + IVB + bridges → Concentration → RSD. -/
theorem psd_chain_implies_rsd
    (h_psd : PairwiseStepDecorrelation)
    (h_ivb : IndividualVarianceBound (1 / 4))
    (h_bridge : PSDIVBImpliesVarianceBound)
    (h_mean : LinearMeanGrowth)
    (h_cheb : ChebyshevConcentration) :
    AlmostAllSquarefreeRSD :=
  concentration_implies_rsd
    (psd_chain_implies_concentration h_psd h_ivb h_bridge h_mean h_cheb)

/-- **PSD → RSD with standard hypotheses.**

    Simplified statement: PSD alone, together with the standard open bridges,
    implies AlmostAllSquarefreeRSD. Uses `individual_variance_quarter` (PROVED). -/
theorem psd_implies_rsd_with_bridges
    (h_psd : PairwiseStepDecorrelation)
    (h_bridge : PSDIVBImpliesVarianceBound)
    (h_mean : LinearMeanGrowth)
    (h_cheb : ChebyshevConcentration) :
    AlmostAllSquarefreeRSD :=
  psd_chain_implies_rsd h_psd individual_variance_quarter h_bridge h_mean h_cheb

/-- **PSD → Concentration (simplified).**

    Now that PSDIVBImpliesVarianceBound is PROVED, we can eliminate it
    as a hypothesis. Only PSD + LinearMeanGrowth + Chebyshev remain. -/
theorem psd_chain_implies_concentration'
    (h_psd : PairwiseStepDecorrelation)
    (h_mean : LinearMeanGrowth)
    (h_cheb : ChebyshevConcentration) :
    RecipSumConcentration :=
  psd_chain_implies_concentration h_psd individual_variance_quarter
    psd_ivb_implies_variance_bound_proved h_mean h_cheb

/-- **PSD → RSD (simplified).**

    With PSDIVBImpliesVarianceBound proved, only 3 hypotheses remain:
    PSD (number theory), LinearMeanGrowth (first moment), Chebyshev (pure analysis). -/
theorem psd_implies_rsd'
    (h_psd : PairwiseStepDecorrelation)
    (h_mean : LinearMeanGrowth)
    (h_cheb : ChebyshevConcentration) :
    AlmostAllSquarefreeRSD :=
  concentration_implies_rsd (psd_chain_implies_concentration' h_psd h_mean h_cheb)

/-- **PSD + LinearMeanGrowth → Concentration (fully simplified).**

    Now that ChebyshevConcentration AND PSDIVBImpliesVarianceBound are both PROVED,
    only 2 open hypotheses remain: PSD and LinearMeanGrowth. -/
theorem psd_lmg_implies_concentration
    (h_psd : PairwiseStepDecorrelation)
    (h_mean : LinearMeanGrowth) :
    RecipSumConcentration :=
  psd_chain_implies_concentration' h_psd h_mean chebyshev_concentration_proved

/-- **PSD + LinearMeanGrowth → RSD (fully simplified).**

    The ultimate 2-hypothesis chain: PSD (number theory) + LinearMeanGrowth (first moment)
    imply AlmostAllSquarefreeRSD. All three bridges (IVB, PSDIVBImpliesVarianceBound,
    ChebyshevConcentration) are now PROVED. -/
theorem psd_lmg_implies_rsd
    (h_psd : PairwiseStepDecorrelation)
    (h_mean : LinearMeanGrowth) :
    AlmostAllSquarefreeRSD :=
  concentration_implies_rsd (psd_lmg_implies_concentration h_psd h_mean)

end PairwiseDecorrelation

/-! ## Landscape: Revival of Dead End #125

Dead End #125 proved that pairwise (k=2) cancellation does NOT imply k-wise
cancellation (XOR counterexample). This killed the CCSB+CPD → UPE route.

However, variance bounds ONLY need pairwise decorrelation (k=2):
  Var(∑ X_j) = ∑ Var(X_j) + 2 ∑_{j<k} Cov(X_j, X_k)

So PairwiseStepDecorrelation is sufficient for the variance bound, and hence
for RecipSumConcentration, without needing k-wise independence.

PROVED components (all three bridges):
- **IndividualVarianceBound(1/4)**: from genSeq ≥ 2
- **PSDIVBImpliesVarianceBound**: variance decomposition + limit arithmetic
- **ChebyshevConcentration**: one-sided Chebyshev + monotonicity of partial sums

Remaining open hypotheses (only 2):
- **PairwiseStepDecorrelation**: pairwise covariances → 0 (from CRT + PE)
- **LinearMeanGrowth**: mean grows linearly (from FirstMomentStep κ, κ > 0) -/

section Landscape

/-- **Landscape theorem**: the PSD chain witnesses.

    All three bridges are now PROVED:
    - IndividualVarianceBound(1/4) from genSeq ≥ 2
    - PSDIVBImpliesVarianceBound from variance decomposition
    - ChebyshevConcentration from one-sided Chebyshev + monotonicity

    Only PSD and LinearMeanGrowth remain as open hypotheses. -/
theorem dead_end_125_pairwise_revival :
    (PairwiseStepDecorrelation →
     LinearMeanGrowth →
     AlmostAllSquarefreeRSD) ∧
    IndividualVarianceBound (1 / 4) ∧
    PSDIVBImpliesVarianceBound ∧
    ChebyshevConcentration :=
  ⟨psd_lmg_implies_rsd,
   individual_variance_quarter,
   psd_ivb_implies_variance_bound_proved,
   chebyshev_concentration_proved⟩

end Landscape

end
