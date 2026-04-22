import EM.Reduction.TailIdentity
import EM.Reduction.SelfCorrecting

/-!
# Tail Window Decorrelation

This file formalizes the **Tail Window Decorrelation** (TWD) framework, which
decomposes the standard EM orbit's character sum into non-overlapping temporal
windows and reduces CCSB (hence MC) to a decorrelation statement between
consecutive windows.

## Mathematical Overview

Given the EM sequence `seq 1, seq 2, ...`, partition it into blocks (windows)
of length K:
  - Window 0: `seq 1, ..., seq K`
  - Window 1: `seq (K+1), ..., seq (2K)`
  - Window j: `seq (jK+1), ..., seq ((j+1)K)`

The character sum over window j is `S_j = sum_{k<K} chi(seq(jK+k+1) mod q)`.
By the tail identity (proved in TailIdentityAttack.lean), this equals the
generalized partial sum from starting point `prod(jK)`.

The total character sum decomposes as `sum_{k<N} chi(seq(k+1)) = sum_{j<J} S_j`
where J = N/K. The squared norm decomposes via the variance identity into
diagonal terms (energies) and off-diagonal terms (cross terms).

TWD asserts that the average absolute cross term vanishes, giving
|total sum|^2 = O(J*K^2 + eps*J^2*K^2) = O(NK + eps*N^2), hence CCSB.

## Main Results

### Definitions
* `windowCharSum`           -- character partial sum over the j-th window
* `windowCrossTerm`         -- Re(S_j * conj(S_l))
* `windowEnergy`            -- |S_j|^2
* `TailWindowDecorrelation` -- open hypothesis: average cross terms vanish
* `TWDImpliesCCSB`          -- open hypothesis: TWD => CCSB
* `TWDImpliesMC`            -- open hypothesis: TWD => MC

### Proved Theorems
* `windowCharSum_eq_genSeqCharPartialSum` -- window = tail identity (key structural)
* `windowEnergy_eq_genSeqCharEnergy`      -- window energy = tail energy
* `windowEnergy_nonneg`                   -- window energy >= 0
* `windowEnergy_le_sq`                    -- window energy <= K^2 (trivial bound)
* `windowCrossTerm_symm`                  -- cross term symmetry
* `windowCrossTerm_self`                  -- diagonal = energy
* `windowCrossTerm_abs_le`                -- |cross term| <= K^2
* `window_start_dvd`                      -- prod(jK) | prod((j+1)K)
* `norm_sq_sum_eq_diag_plus_cross`        -- variance identity for complex sums
* `charSum_eq_window_sum`                 -- total sum = sum of window sums
* `charEnergy_window_decomp`              -- total energy = diag + cross
* `diag_energy_le`                        -- diagonal <= J*K^2
* `cross_term_le_abs_cross`               -- triangle inequality on cross terms
* `abs_cross_trivial_bound`               -- cross terms <= J^2*K^2
* `twd_implies_mc_from_bridge`            -- TWDImpliesCCSB => TWD => MC
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Window Definitions -/

section WindowDefs

/-- The character partial sum over the j-th block of length K in the standard
    EM orbit. Window j covers steps jK+1 through (j+1)K of the sequence. -/
def windowCharSum (j K q : Nat) (χ : Nat → ℂ) : ℂ :=
  ∑ k ∈ Finset.range K, χ (seq (j * K + k + 1) % q)

/-- The cross term between windows j and l: Re(S_j * conj(S_l)). -/
def windowCrossTerm (j l K q : Nat) (χ : Nat → ℂ) : ℝ :=
  (windowCharSum j K q χ * starRingEnd ℂ (windowCharSum l K q χ)).re

/-- Energy of the j-th window: |S_j|^2 = normSq(S_j). -/
def windowEnergy (j K q : Nat) (χ : Nat → ℂ) : ℝ :=
  Complex.normSq (windowCharSum j K q χ)

end WindowDefs

/-! ## Window = Tail Identity

The key structural lemma: the j-th window character sum equals the generalized
character partial sum starting from prod(jK). This connects temporal blocks
of the standard EM orbit to the ensemble framework. -/

section WindowTailIdentity

/-- The j-th window character sum equals the generalized partial sum
    starting from prod(jK). This connects temporal blocks to the ensemble.

    Proof: unfold both sides and use genSeq_restart + genProd_two_eq_prod
    to show genSeq(prod(jK), k) = genSeq(2, jK+k) = seq(jK+k+1). -/
theorem windowCharSum_eq_genSeqCharPartialSum (j K q : Nat) (χ : Nat → ℂ) :
    windowCharSum j K q χ = genSeqCharPartialSum (prod (j * K)) K q χ := by
  unfold windowCharSum genSeqCharPartialSum
  congr 1; ext k
  congr 1; congr 1
  rw [← genProd_two_eq_prod, genSeq_restart, genSeq_two_eq_seq_succ]

/-- The j-th window energy equals the generalized character energy
    starting from prod(jK). -/
theorem windowEnergy_eq_genSeqCharEnergy (j K q : Nat) (χ : Nat → ℂ) :
    windowEnergy j K q χ = genSeqCharEnergy (prod (j * K)) K q χ := by
  unfold windowEnergy genSeqCharEnergy
  congr 1
  exact windowCharSum_eq_genSeqCharPartialSum j K q χ

end WindowTailIdentity

/-! ## Basic Window Properties -/

section WindowProperties

/-- Window energy is non-negative (it is a squared norm). -/
theorem windowEnergy_nonneg (j K q : Nat) (χ : Nat → ℂ) :
    0 ≤ windowEnergy j K q χ :=
  Complex.normSq_nonneg _

/-- Helper: norm of chi value is at most 1 when normSq(chi) <= 1. -/
private theorem norm_chi_le_one {χ : Nat → ℂ} (hχ : ∀ a, Complex.normSq (χ a) ≤ 1)
    (a : Nat) : ‖χ a‖ ≤ 1 := by
  have h := hχ a
  rw [Complex.normSq_eq_norm_sq] at h
  -- h : ‖χ a‖ ^ 2 ≤ 1
  -- Need: ‖χ a‖ ≤ 1
  exact le_of_sq_le_sq (by rwa [one_pow]) zero_le_one

/-- Helper: norm of window char sum is at most K when |chi| <= 1. -/
private theorem norm_windowCharSum_le (j K q : Nat) (χ : Nat → ℂ)
    (hχ : ∀ a, Complex.normSq (χ a) ≤ 1) :
    ‖windowCharSum j K q χ‖ ≤ (K : ℝ) := by
  unfold windowCharSum
  calc ‖∑ k ∈ Finset.range K, χ (seq (j * K + k + 1) % q)‖
      ≤ ∑ k ∈ Finset.range K, ‖χ (seq (j * K + k + 1) % q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        exact norm_chi_le_one hχ _
    _ = (K : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Each window has energy at most K^2. This follows from the triangle
    inequality: |S_j| = |sum chi(...)| <= sum |chi(...)| <= K when |chi| <= 1,
    so |S_j|^2 <= K^2. -/
theorem windowEnergy_le_sq (j K q : Nat) (χ : Nat → ℂ)
    (hχ : ∀ a, Complex.normSq (χ a) ≤ 1) :
    windowEnergy j K q χ ≤ (K : ℝ) ^ 2 := by
  unfold windowEnergy
  rw [Complex.normSq_eq_norm_sq]
  have h := norm_windowCharSum_le j K q χ hχ
  exact sq_le_sq' (by linarith [norm_nonneg (windowCharSum j K q χ)]) h

/-- The cross term between windows j and l is symmetric:
    Re(S_j * conj(S_l)) = Re(S_l * conj(S_j)). -/
theorem windowCrossTerm_symm (j l K q : Nat) (χ : Nat → ℂ) :
    windowCrossTerm j l K q χ = windowCrossTerm l j K q χ := by
  unfold windowCrossTerm
  have h : (windowCharSum j K q χ * starRingEnd ℂ (windowCharSum l K q χ)) =
      starRingEnd ℂ (windowCharSum l K q χ * starRingEnd ℂ (windowCharSum j K q χ)) := by
    simp only [map_mul, starRingEnd_self_apply]
    ring
  rw [h, Complex.conj_re]

/-- The diagonal cross term equals the window energy:
    Re(S_j * conj(S_j)) = |S_j|^2. -/
theorem windowCrossTerm_self (j K q : Nat) (χ : Nat → ℂ) :
    windowCrossTerm j j K q χ = windowEnergy j K q χ := by
  unfold windowCrossTerm windowEnergy
  -- normSq z = (conj z * z).re, and z * conj z has the same real part
  have h1 : Complex.normSq (windowCharSum j K q χ) =
      (starRingEnd ℂ (windowCharSum j K q χ) * windowCharSum j K q χ).re := by
    rw [← Complex.ofReal_re (Complex.normSq _)]
    congr 1
    exact Complex.normSq_eq_conj_mul_self
  rw [h1]
  congr 1
  ring

/-- The absolute value of the cross term is bounded by K^2. -/
theorem windowCrossTerm_abs_le (j l K q : Nat) (χ : Nat → ℂ)
    (hχ : ∀ a, Complex.normSq (χ a) ≤ 1) :
    |windowCrossTerm j l K q χ| ≤ (K : ℝ) ^ 2 := by
  unfold windowCrossTerm
  have h1 : |(windowCharSum j K q χ * starRingEnd ℂ (windowCharSum l K q χ)).re| ≤
      ‖windowCharSum j K q χ * starRingEnd ℂ (windowCharSum l K q χ)‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖windowCharSum j K q χ * starRingEnd ℂ (windowCharSum l K q χ)‖ =
      ‖windowCharSum j K q χ‖ * ‖windowCharSum l K q χ‖ := by
    rw [norm_mul, Complex.norm_conj]
  rw [h2] at h1
  have hj := norm_windowCharSum_le j K q χ hχ
  have hl := norm_windowCharSum_le l K q χ hχ
  calc |(windowCharSum j K q χ * starRingEnd ℂ (windowCharSum l K q χ)).re|
      ≤ ‖windowCharSum j K q χ‖ * ‖windowCharSum l K q χ‖ := h1
    _ ≤ (K : ℝ) * (K : ℝ) := mul_le_mul hj hl (norm_nonneg _) (Nat.cast_nonneg K)
    _ = (K : ℝ) ^ 2 := by ring

end WindowProperties

/-! ## Variance Identity

The algebraic identity: for complex numbers z_0, ..., z_{J-1},
  |sum z_j|^2 = sum |z_j|^2 + 2 * sum_{j<l} Re(z_j * conj(z_l))

This decomposes the squared norm of a sum into diagonal (energies) and
off-diagonal (cross terms) contributions. -/

section VarianceIdentity

/-- Helper: Re(z * conj(w)) = Re(w * conj(z)) for complex numbers. -/
private theorem re_mul_conj_comm (a b : ℂ) :
    (a * starRingEnd ℂ b).re = (b * starRingEnd ℂ a).re := by
  have : a * starRingEnd ℂ b = starRingEnd ℂ (b * starRingEnd ℂ a) := by
    simp only [map_mul, starRingEnd_self_apply]; ring
  rw [this, Complex.conj_re]

/-- Helper: normSq z = Re(z * conj z). -/
private theorem normSq_eq_re_mul_conj (z : ℂ) :
    Complex.normSq z = (z * starRingEnd ℂ z).re := by
  have h := Complex.normSq_eq_conj_mul_self (z := z)
  -- h : (normSq z : ℂ) = conj z * z
  rw [← Complex.ofReal_re (Complex.normSq z)]
  congr 1
  rw [h]; ring

/-- Helper: normSq(sum z_j) = sum_j sum_l Re(z_j * conj(z_l)). -/
private theorem normSq_sum_eq_double_sum (J : Nat) (z : Nat → ℂ) :
    Complex.normSq (∑ j ∈ Finset.range J, z j) =
    ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
      (z j * starRingEnd ℂ (z l)).re := by
  rw [normSq_eq_re_mul_conj, map_sum, Finset.sum_mul, Complex.re_sum]
  congr 1; ext j
  rw [Finset.mul_sum, Complex.re_sum]

/-- Variance identity: the squared norm of a sum of J complex numbers decomposes
    into diagonal terms (energies) and off-diagonal cross terms.

    |sum_{j<J} z_j|^2 = sum_{j<J} |z_j|^2 +
                         2 * sum_{j<J} sum_{l<J, j<l} Re(z_j * conj(z_l)) -/
theorem norm_sq_sum_eq_diag_plus_cross (J : Nat) (z : Nat → ℂ) :
    Complex.normSq (∑ j ∈ Finset.range J, z j) =
    ∑ j ∈ Finset.range J, Complex.normSq (z j) +
    2 * ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
      if j < l then (z j * starRingEnd ℂ (z l)).re else 0 := by
  rw [normSq_sum_eq_double_sum]
  -- Step 1: Split the inner sum for each j into: diagonal + upper + lower
  have hsplit : ∀ j ∈ Finset.range J,
      ∑ l ∈ Finset.range J, (z j * starRingEnd ℂ (z l)).re =
      Complex.normSq (z j) +
      ∑ l ∈ Finset.range J, (if j < l then (z j * starRingEnd ℂ (z l)).re else 0) +
      ∑ l ∈ Finset.range J, (if l < j then (z j * starRingEnd ℂ (z l)).re else 0) := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.mp hj
    -- Partition each term by comparing j and l
    have hterm : ∀ l, (z j * starRingEnd ℂ (z l)).re =
        (if j = l then (z j * starRingEnd ℂ (z l)).re else 0) +
        (if j < l then (z j * starRingEnd ℂ (z l)).re else 0) +
        (if l < j then (z j * starRingEnd ℂ (z l)).re else 0) := by
      intro l
      by_cases h1 : j = l
      · subst h1; simp only [lt_irrefl, ite_true, ite_false, add_zero]
      · by_cases h2 : j < l
        · simp only [h1, h2, not_lt.mpr (le_of_lt h2), ite_true, ite_false, zero_add, add_zero]
        · push Not at h2
          have h3 : l < j := lt_of_le_of_ne h2 (Ne.symm h1)
          simp only [h1, show ¬(j < l) from not_lt.mpr (le_of_lt h3), h3, ite_true, ite_false,
            zero_add]
    conv_lhs => arg 2; ext l; rw [hterm l]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1; congr 1
    -- The sum has `if j = l then ... else 0`; convert to `if l = j`
    have : ∀ l, (if j = l then (z j * starRingEnd ℂ (z l)).re else 0) =
        (if l = j then (z j * starRingEnd ℂ (z l)).re else 0) := by
      intro l; split_ifs with h1 h2 <;> first | rfl | omega
    simp_rw [this]
    rw [Finset.sum_ite_eq' (Finset.range J) j]
    simp only [Finset.mem_range, hjJ, ite_true]
    exact (normSq_eq_re_mul_conj (z j)).symm
  have : ∀ j ∈ Finset.range J,
      ∑ l ∈ Finset.range J, (z j * starRingEnd ℂ (z l)).re =
      (Complex.normSq (z j) +
        ∑ l ∈ Finset.range J, (if j < l then (z j * starRingEnd ℂ (z l)).re else 0)) +
      ∑ l ∈ Finset.range J, (if l < j then (z j * starRingEnd ℂ (z l)).re else 0) :=
    hsplit
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Step 2: The lower triangle sum = upper triangle sum by symmetry
  have hlower_eq_upper :
      ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
        (if l < j then (z j * starRingEnd ℂ (z l)).re else 0) =
      ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
        (if j < l then (z j * starRingEnd ℂ (z l)).re else 0) := by
    -- After swapping j,l: ∑ l ∑ j [l<j] Re(z_j conj z_l) = ∑ j ∑ l [j<l] Re(z_j conj z_l)
    -- which is exactly the RHS. But the LHS has Re(z_j conj z_l) while we need to
    -- match it to Re(z_l conj z_j) = Re(z_j conj z_l) by symmetry.
    conv_lhs =>
      arg 2; ext a; arg 2; ext b
      rw [show (if b < a then (z a * starRingEnd ℂ (z b)).re else (0 : ℝ)) =
        if b < a then (z b * starRingEnd ℂ (z a)).re else 0 from by
          split_ifs with h
          · exact re_mul_conj_comm (z a) (z b)
          · rfl]
    exact Finset.sum_comm
  rw [hlower_eq_upper]; ring

end VarianceIdentity

/-! ## Divisibility Infrastructure -/

section Divisibility

/-- Consecutive window starting points are related by divisibility:
    prod(jK) divides prod((j+1)K). This follows from prod_dvd_prod
    since jK <= (j+1)K. -/
theorem window_start_dvd (j K : Nat) :
    prod (j * K) ∣ prod ((j + 1) * K) := by
  apply prod_dvd_prod
  nlinarith

end Divisibility

/-! ## Open Hypotheses -/

section OpenHypotheses

/-- **TailWindowDecorrelation**: the average absolute cross term between
    non-overlapping windows vanishes as window size K grows.

    For J windows of size K:
      (1/J^2) * sum_{j<l<J} |crossTerm(j,l)| -> 0 as K -> inf

    This is a TEMPORAL decorrelation statement: windows far apart in the
    EM orbit should have nearly independent character sums, because the
    accumulator prod(jK) grows super-exponentially, so the starting points
    of consecutive windows are extremely different in magnitude.

    **Status**: open hypothesis. -/
def TailWindowDecorrelation : Prop :=
  ∀ q : Nat, q.Prime →
  ∀ χ : Nat → ℂ, (∀ a, Complex.normSq (χ a) ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      ∃ K₀ : Nat, 0 < K₀ ∧ ∀ K : Nat, K₀ ≤ K →
        ∀ J : Nat, 0 < J →
          (1 / (J : ℝ) ^ 2) *
            (∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
              if j < l then |windowCrossTerm j l K q χ| else (0 : ℝ))
          < ε

/-- **TWDImpliesCCSB**: Tail Window Decorrelation implies ComplexCharSumBound.

    Proof sketch: decompose the total character sum over N = J*K steps into
    J windows, apply the variance identity, control diagonal by J*K^2 and
    cross terms by eps*J^2*K^2 via TWD, giving
    |total sum|^2 <= N*K + 2*eps*N^2. Choose K = ceil(1/eps) to get
    |total sum|^2 <= eps*N^2 + 2*eps*N^2 = 3*eps*N^2, hence CCSB.

    **Status**: open hypothesis. -/
def TWDImpliesCCSB : Prop :=
  TailWindowDecorrelation → ComplexCharSumBound

/-- **TWDImpliesMC**: Tail Window Decorrelation implies Mullin's Conjecture.

    This composes TWDImpliesCCSB with the proved chain CCSB -> MC.

    **Status**: open hypothesis. -/
def TWDImpliesMC : Prop :=
  TailWindowDecorrelation → MullinConjecture

/-- TWD implies MC, given the bridge TWDImpliesCCSB (which is open)
    and the proved CCSB -> MC chain. -/
theorem twd_implies_mc_from_bridge (h1 : TWDImpliesCCSB) (h2 : TailWindowDecorrelation) :
    MullinConjecture :=
  complex_csb_mc' (h1 h2)

end OpenHypotheses

/-! ## Window Sum Decomposition

The total character sum over N steps decomposes into a sum of window
character sums when N = J * K. -/

section WindowDecomposition

/-- The character sum over J*K steps decomposes as a sum of J window
    character sums. This is the key decomposition identity.

    sum_{k < J*K} chi(seq(k+1) % q) = sum_{j < J} windowCharSum j K q chi -/
theorem charSum_eq_window_sum (J K q : Nat) (χ : Nat → ℂ) :
    ∑ k ∈ Finset.range (J * K), χ (seq (k + 1) % q) =
    ∑ j ∈ Finset.range J, windowCharSum j K q χ := by
  unfold windowCharSum
  -- Reindex: partition [0, J*K) into J blocks of K
  induction J with
  | zero => simp
  | succ J ih =>
    have hnotmem : J ∉ Finset.range J := by simp [Finset.mem_range]
    rw [show (J + 1) * K = J * K + K from by ring]
    rw [Finset.sum_range_add]
    rw [show Finset.range (J + 1) = insert J (Finset.range J) from
      (Finset.range_add_one).symm ▸ rfl]
    rw [Finset.sum_insert hnotmem, ih, add_comm]

/-- Applying the variance identity to the window decomposition gives a
    bound on the total character energy over J*K steps in terms of
    window energies and window cross terms. -/
theorem charEnergy_window_decomp (J K q : Nat) (χ : Nat → ℂ) :
    Complex.normSq (∑ k ∈ Finset.range (J * K), χ (seq (k + 1) % q)) =
    ∑ j ∈ Finset.range J, windowEnergy j K q χ +
    2 * ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
      if j < l then windowCrossTerm j l K q χ else 0 := by
  rw [charSum_eq_window_sum]
  exact norm_sq_sum_eq_diag_plus_cross J (fun j => windowCharSum j K q χ)

/-- The diagonal contribution is bounded by J * K^2 when |chi| <= 1. -/
theorem diag_energy_le (J K q : Nat) (χ : Nat → ℂ)
    (hχ : ∀ a, Complex.normSq (χ a) ≤ 1) :
    ∑ j ∈ Finset.range J, windowEnergy j K q χ ≤ (J : ℝ) * (K : ℝ) ^ 2 := by
  calc ∑ j ∈ Finset.range J, windowEnergy j K q χ
      ≤ ∑ _j ∈ Finset.range J, (K : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact windowEnergy_le_sq j K q χ hχ
    _ = (J : ℝ) * (K : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end WindowDecomposition

/-! ## Cross Term Bound from TWD

Infrastructure connecting the TWD hypothesis to bounds on the total
character energy. -/

section CrossTermBound

/-- The cross term sum is bounded in absolute value by the absolute cross
    term sum. This is the triangle inequality applied to the double sum. -/
theorem cross_term_le_abs_cross (J K q : Nat) (χ : Nat → ℂ) :
    |∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
      if j < l then windowCrossTerm j l K q χ else (0 : ℝ)| ≤
    ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
      if j < l then |windowCrossTerm j l K q χ| else (0 : ℝ) := by
  calc |∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
        if j < l then windowCrossTerm j l K q χ else 0|
      ≤ ∑ j ∈ Finset.range J, |∑ l ∈ Finset.range J,
        if j < l then windowCrossTerm j l K q χ else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
        |if j < l then windowCrossTerm j l K q χ else 0| := by
        apply Finset.sum_le_sum; intro j _
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
        if j < l then |windowCrossTerm j l K q χ| else 0 := by
        congr 1; ext j; congr 1; ext l
        split_ifs <;> simp

/-- The absolute cross term sum is trivially bounded by J^2 * K^2
    (there are at most J^2 pairs, each contributing at most K^2). -/
theorem abs_cross_trivial_bound (J K q : Nat) (χ : Nat → ℂ)
    (hχ : ∀ a, Complex.normSq (χ a) ≤ 1) :
    ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
      (if j < l then |windowCrossTerm j l K q χ| else (0 : ℝ)) ≤
    (J : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
  calc ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
        (if j < l then |windowCrossTerm j l K q χ| else (0 : ℝ))
      ≤ ∑ _j ∈ Finset.range J, ∑ _l ∈ Finset.range J, (K : ℝ) ^ 2 := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro l _
        split_ifs
        · exact windowCrossTerm_abs_le j l K q χ hχ
        · exact sq_nonneg _
    _ = (J : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end CrossTermBound

end
