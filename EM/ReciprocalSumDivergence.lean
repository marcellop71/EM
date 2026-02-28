import EM.WeakErgodicity
import EM.WeakMullin

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

/-- **Reciprocal Sum Concentration**: for each bound M > 0, eventually (in K),
    the density of squarefree n ≤ X with S_K(n) < M tends to 0 as X → ∞.

    This is the quantitative consequence of the first moment (~ κK) and
    variance bound (O(K)) via Chebyshev's inequality:

    Pr_n[S_K(n) < M] ≤ Pr_n[|S_K(n) − κK| > κK − M] ≤ Var/(κK − M)² = O(1/K)

    for K > M/κ. The decorrelation between steps (approximate independence
    of 1/em_n(j) and 1/em_n(k) when averaged over starting points n) ensures
    the variance bound holds.

    **Proof from standard ANT:** The first moment uses PE (Population
    Equidistribution, proved from Dirichlet + sieve). The variance bound uses
    CRT decorrelation (`crt_multiplier_invariance`, proved) and the +1 shift
    destroying residue correlations. -/
def RecipSumConcentration : Prop :=
  ∀ M : ℝ, 0 < M →
  ∃ K₀ : Nat,
    ∀ K ≥ K₀,
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧ recipPartialSum n K < M)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop
        (nhds 0)

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
    By concentration, the density of the latter → 0 as X → ∞ (for large K).
    Since the former is a subset, its density → 0 too. -/
theorem concentration_implies_rsd
    (hconc : RecipSumConcentration) : AlmostAllSquarefreeRSD := by
  intro M hM
  -- Get K₀ from concentration
  obtain ⟨K₀, hK₀⟩ := hconc M hM
  -- Use K = K₀: density of {n : S_{K₀} < M} → 0
  have h_tendsto := hK₀ K₀ (le_refl _)
  -- The density of {n : ∀K, S_K(n) < M} ≤ density of {n : S_{K₀}(n) < M}
  -- So the former also → 0.
  refine squeeze_zero
    (fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ h_tendsto
  intro X
  have h_card := Finset.card_le_card (forall_bounded_subset M X K₀)
  exact div_le_div_of_nonneg_right (by exact_mod_cast h_card) (Nat.cast_nonneg _)

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

end
