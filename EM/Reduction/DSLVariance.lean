import EM.Ensemble.PT
import EM.Reduction.DSLInfra

/-!
# DSL Variance Route: Population-Level Second Moment Infrastructure

This file formalizes the **variance route** to the Deterministic Stability Lemma (DSL).
The key idea: instead of proving DSL for each starting point individually (which faces
the Four-Way Blocker), we prove that the second moment of character energy across
squarefree starting points is O(K), which implies DSL via Markov's inequality.

## Main Results

### Definitions
* `populationCharEnergy`      -- average character energy over squarefree n
* `populationCrossTermSum`    -- total cross-term sum
* `crossTermPair`             -- per-pair (j,k) cross-term
* `SecondMomentBound`         -- population energy <= C * K
* `PairwiseCrossTermVanishing` -- each cross-term pair -> 0

### Open Hypotheses
* `PairwiseVanishingImpliesSMB` -- cross-term vanishing -> second moment bound
* `SMBImpliesDSL`              -- second moment bound -> DSL
* `VarianceChainImpliesDSL`    -- full variance chain -> DSL

### Proved Theorems
* `populationCharEnergy_nonneg`                   -- population energy >= 0
* `populationCharEnergy_eq_ensembleAvg`           -- population energy = ensemble average
* `crossTermPair_comm`                            -- cross-term pair symmetry
* `charSumVarianceBound_implies_secondMomentBound` -- CharSumVarianceBound => SMB
* `stepDecorrelation_implies_pairwiseVanishing`   -- SD => PCV
* `variance_chain_from_bridges`                   -- PV2SMB + SMB2DSL => VC2DSL

## Mathematical Overview

The second moment decomposes as:
  E_2(K,X) = K + (2/|S(X)|) * sum_{j<k<K} C(j,k,X)

where C(j,k,X) = sum_{sqfree n <= X} Re(chi(m_j(n)) * conj(chi(m_k(n)))).

If each C(j,k,X) = o(|S(X)|), then E_2(K,X) = K + o(K^2), giving DSL.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Population Character Energy -/

section PopulationEnergy

/-- Population-averaged character energy: for each squarefree n in [1, X], compute the
    squared norm of the partial character sum sum_{k<K} chi(genSeq n k mod q), then
    average over squarefree n. When there are no squarefree numbers in [1,X], returns 0. -/
def populationCharEnergy (q : Nat) (χ : Nat → ℂ) (K X : Nat) : ℝ :=
  if sqfreeCount X = 0 then 0
  else (1 / (sqfreeCount X : ℝ)) *
    ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
      genSeqCharEnergy n K q χ

/-- The population character energy is non-negative. It is either zero (when no squarefree
    numbers exist) or an average of non-negative terms (each being a norm squared). -/
theorem populationCharEnergy_nonneg (q : Nat) (χ : Nat → ℂ) (K X : Nat) :
    0 ≤ populationCharEnergy q χ K X := by
  unfold populationCharEnergy
  split
  · exact le_rfl
  · exact mul_nonneg (div_nonneg one_pos.le (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun n _ => genSeqCharEnergy_nonneg n K q χ)

/-- Population energy equals the ensemble average of character energy (when sqfreeCount > 0). -/
theorem populationCharEnergy_eq_ensembleAvg (q : Nat) (χ : Nat → ℂ) (K X : Nat)
    (hX : 0 < sqfreeCount X) :
    populationCharEnergy q χ K X = ensembleAvg X (fun n => genSeqCharEnergy n K q χ) := by
  unfold populationCharEnergy
  rw [if_neg hX.ne']
  unfold ensembleAvg sqfreeCount; ring

/-- Population energy at K = 0 is zero (the partial sum over 0 steps is empty). -/
theorem populationCharEnergy_zero (q : Nat) (χ : Nat → ℂ) (X : Nat) :
    populationCharEnergy q χ 0 X = 0 := by
  unfold populationCharEnergy
  split
  · rfl
  · simp only [genSeqCharEnergy, genSeqCharPartialSum, Finset.range_zero, Finset.sum_empty,
      map_zero, Finset.sum_const_zero, mul_zero]

end PopulationEnergy

/-! ## Cross-Term Sums -/

section CrossTerms

/-- The per-pair cross-term: for fixed steps j, k and a character chi mod q,
    the population sum of Re(chi(genSeq n j mod q) * conj(chi(genSeq n k mod q)))
    over squarefree n in [1, X].

    This is the building block of the energy decomposition: the total energy
    is the sum of diagonal terms (= K) plus twice the sum of cross-term pairs. -/
def crossTermPair (q : Nat) (χ : Nat → ℂ) (j k X : Nat) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
    (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n k % q))).re

/-- The total cross-term sum: summing crossTermPair over all pairs j < k < K.
    The energy decomposition gives:
      sum_n |S_K(n)|^2 = sum_n K + 2 * sum_{j<k} crossTermPair(j,k,X)
    where the diagonal contribution is K per starting point. -/
def populationCrossTermSum (q : Nat) (χ : Nat → ℂ) (K X : Nat) : ℝ :=
  ∑ j ∈ Finset.range K, ∑ k ∈ Finset.Ico (j + 1) K,
    crossTermPair q χ j k X

/-- The cross-term pair is symmetric: swapping j and k gives the same value.
    This follows from Re(z * conj(w)) = Re(w * conj(z)) for all complex z, w. -/
theorem crossTermPair_comm (q : Nat) (χ : Nat → ℂ) (j k X : Nat) :
    crossTermPair q χ j k X = crossTermPair q χ k j X := by
  simp only [crossTermPair]
  congr 1; ext n
  rw [show (χ _ * starRingEnd ℂ (χ _)).re = (starRingEnd ℂ (χ _ * starRingEnd ℂ (χ _))).re
    from (Complex.conj_re _).symm, map_mul, starRingEnd_self_apply, mul_comm]

/-- The cross-term pair at j = k is the sum of normSq values. -/
private theorem re_mul_conj_eq_normSq (z : ℂ) :
    (z * starRingEnd ℂ z).re = Complex.normSq z := by
  rw [show starRingEnd ℂ z = Star.star z from rfl, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_re]

theorem crossTermPair_self (q : Nat) (χ : Nat → ℂ) (j X : Nat) :
    crossTermPair q χ j j X =
    ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
      Complex.normSq (χ (genSeq n j % q)) := by
  simp only [crossTermPair, re_mul_conj_eq_normSq]

end CrossTerms

/-! ## Second Moment Bound -/

section SecondMoment

/-- A **second moment bound** asserts that the population-averaged character
    energy grows at most linearly in K (not quadratically). This is the key
    hypothesis that would imply DSL.

    The statement: for every prime q and every bounded function chi, there
    exists a constant C > 0 such that for every K > 0, eventually in X,
    the population character energy is at most C * K.

    If chi is a nontrivial Dirichlet character mod q (so |chi(a)| <= 1),
    then the diagonal contribution to the energy is exactly K, so the bound
    C * K says the cross terms contribute at most (C-1) * K total -- i.e.,
    they do not grow quadratically. -/
def SecondMomentBound : Prop :=
  ∀ q : Nat, q.Prime →
  ∀ χ : Nat → ℂ, (∀ a, Complex.normSq (χ a) ≤ 1) →
    ∃ C : ℝ, 0 < C ∧ ∀ K : Nat, 0 < K → ∃ X₀ : Nat, ∀ X, X₀ ≤ X →
      populationCharEnergy q χ K X ≤ C * K

end SecondMoment

/-! ## Pairwise Cross-Term Vanishing -/

section PairwiseVanishing

/-- **Pairwise cross-term vanishing**: for each pair j < k and nontrivial chi,
    the population-averaged cross-term vanishes as X -> infinity.

    This is strictly stronger than StepDecorrelation (which only requires
    the ensemble average of |cross-term| to vanish), as it asks for the
    un-absolute-valued cross-term sum itself to vanish when normalized.

    However, the cross-term pair normalized by sqfreeCount X equals
    ensembleAvg X (fun n => Re(chi_j * conj(chi_k))), so if StepDecorrelation
    gives |ensembleAvg| -> 0, then ensembleAvg -> 0 as well.

    The nontrivial character condition (sum chi = 0) ensures that the
    diagonal (same-residue) contribution cancels in the average. -/
def PairwiseCrossTermVanishing : Prop :=
  ∀ q : Nat, q.Prime →
  ∀ χ : Nat → ℂ, (∀ a, Complex.normSq (χ a) ≤ 1) →
    (∑ a ∈ Finset.range q, χ a = 0) →
    ∀ j k : Nat, j < k →
      Filter.Tendsto (fun X => crossTermPair q χ j k X / sqfreeCount X)
        Filter.atTop (nhds 0)

end PairwiseVanishing

/-! ## Bridge Propositions -/

section Bridges

/-- **Pairwise vanishing implies second moment bound**: if every cross-term pair
    vanishes asymptotically, then the population character energy is O(K).

    Proof sketch: The energy decomposes into diagonal (= K) plus cross terms.
    The cross terms sum over K(K-1)/2 pairs, each <= eps * |S(X)| for X large enough.
    So total cross-term <= eps * K^2/2 * |S(X)|, giving energy <= K + eps * K^2/2.
    Choosing eps = 1/K gives energy <= K + K/2 = 3K/2 <= 2K.

    The difficulty: the epsilon-delta management requires choosing X_0 that works
    for ALL K(K-1)/2 pairs simultaneously, which requires a uniform rate of
    convergence across pairs -- a non-trivial analytic input.

    **Status**: open hypothesis. -/
def PairwiseVanishingImpliesSMB : Prop :=
  PairwiseCrossTermVanishing → SecondMomentBound

/-- **Second moment bound implies DSL**: if the population character energy
    is O(K), then by Markov's inequality, density-1 of starting points have
    character energy o(K^2), which is the content of DSL.

    Proof sketch: DSL requires PopulationEquidist -> ConditionalMultiplierEquidist.
    The second moment bound says E_n[|S_K|^2] <= C * K. By Markov,
    Pr[|S_K|^2 > eps^2 * K^2] <= C * K / (eps^2 * K^2) = C / (eps^2 * K) -> 0.
    This gives concentration, which (via the proved
    char_concentration_implies_cancellation) gives character sum cancellation
    for density-1 of starting points, which is CME.

    The gap: connecting this density-1 character cancellation (over the
    ensemble) to the pointwise CME statement (for the standard EM sequence
    starting at n = 2). This requires either:
    (a) showing n = 2 is in the density-1 good set, or
    (b) a transfer argument from density-1 to all starting points.

    **Status**: open hypothesis. -/
def SMBImpliesDSL : Prop :=
  SecondMomentBound → DeterministicStabilityLemma

/-- **The full variance chain**: pairwise vanishing implies DSL.
    Composition of PairwiseVanishingImpliesSMB and SMBImpliesDSL.

    This reduces DSL to a statement purely about pairwise cross-term
    cancellation in the squarefree population, which is the natural
    target for CRT-based decorrelation arguments. -/
def VarianceChainImpliesDSL : Prop :=
  PairwiseCrossTermVanishing → DeterministicStabilityLemma

/-- **The variance chain composes correctly**: given both bridge hypotheses,
    pairwise vanishing implies DSL. -/
theorem variance_chain_from_bridges
    (h1 : PairwiseVanishingImpliesSMB)
    (h2 : SMBImpliesDSL) :
    VarianceChainImpliesDSL :=
  fun hpv => h2 (h1 hpv)

end Bridges

/-! ## Relationship to Existing Infrastructure -/

section Connections

/-- The existing CharSumVarianceBound(C) implies SecondMomentBound.

    CharSumVarianceBound(C) states: for each q, chi, K, there exists X_0 such that
    for X >= X_0, ensembleAvg X (energy) <= C * K. Since populationCharEnergy
    equals ensembleAvg (when sqfreeCount > 0), this directly gives SecondMomentBound. -/
theorem charSumVarianceBound_implies_secondMomentBound (C : ℝ) (hC : 0 < C)
    (hvb : CharSumVarianceBound C) : SecondMomentBound := by
  intro q hq χ hχ
  exact ⟨C, hC, fun K hK => by
    obtain ⟨X₀, hX₀⟩ := hvb q hq χ hχ K
    use X₀
    intro X hX
    by_cases hsf : sqfreeCount X = 0
    · -- No squarefree numbers: energy is 0
      simp only [populationCharEnergy, if_pos hsf]
      exact mul_nonneg hC.le (Nat.cast_nonneg _)
    · -- sqfreeCount > 0: use ensemble average bound
      rw [populationCharEnergy_eq_ensembleAvg q χ K X (Nat.pos_of_ne_zero hsf)]
      exact hX₀ X hX⟩

/-- StepDecorrelation implies PairwiseCrossTermVanishing.

    StepDecorrelation gives |ensembleAvg X (cross-term)| -> 0 for each pair j < k.
    The crossTermPair / sqfreeCount equals ensembleAvg (cross-term) by definition.
    Since |f| -> 0 implies f -> 0 for real-valued functions, we get PCV.

    This connects the existing decorrelation hypothesis to the new variance route. -/
theorem stepDecorrelation_implies_pairwiseVanishing
    (hsd : StepDecorrelation) : PairwiseCrossTermVanishing := by
  intro q hq χ _hχ _hsum j k hjk
  have hsd_jk := hsd q hq χ j k hjk
  -- StepDecorrelation says |ensembleAvg X (cross-term)| -> 0
  -- crossTermPair / sqfreeCount = ensembleAvg (by definition)
  have heq : (fun X => crossTermPair q χ j k X / ↑(sqfreeCount X)) =
      (fun X => ensembleAvg X (fun n =>
        (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n k % q))).re)) := by
    ext X
    simp only [crossTermPair, ensembleAvg, sqfreeCount]
  rw [heq]
  -- |f(X)| -> 0 implies f(X) -> 0
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hsd_jk

end Connections

/-! ## Population Diagonal Sum -/

section DiagonalSum

/-- The population diagonal sum: the sum of normSq(chi(genSeq n k mod q))
    over squarefree n in [1,X] and steps k < K. This is the diagonal
    contribution to the total energy. -/
def populationDiagonalSum (q : Nat) (χ : Nat → ℂ) (K X : Nat) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
    ∑ k ∈ Finset.range K, Complex.normSq (χ (genSeq n k % q))

/-- The population diagonal sum is non-negative (sum of normSq values). -/
theorem populationDiagonalSum_nonneg (q : Nat) (χ : Nat → ℂ) (K X : Nat) :
    0 ≤ populationDiagonalSum q χ K X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- When chi is bounded (normSq <= 1), the population diagonal sum is at most
    K * sqfreeCount X. This is the natural upper bound: each of the sqfreeCount X
    starting points contributes at most K to the diagonal. -/
theorem populationDiagonalSum_le (q : Nat) (χ : Nat → ℂ) (K X : Nat)
    (hχ : ∀ a, Complex.normSq (χ a) ≤ 1) :
    populationDiagonalSum q χ K X ≤ K * sqfreeCount X := by
  unfold populationDiagonalSum sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree
  calc ∑ n ∈ S, ∑ k ∈ Finset.range K, Complex.normSq (χ (genSeq n k % q))
      ≤ ∑ n ∈ S, ∑ _k ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hχ _
    _ = ∑ _n ∈ S, (K : ℝ) := by
        simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    _ = ↑K * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end DiagonalSum

/-! ## SMB from CharSumVarianceBound (alternate route) -/

section AlternateRoute

/-- An alternate form of SecondMomentBound matching the CharSumVarianceBound quantifier
    structure (C comes first, then the universals).

    This is logically equivalent to SecondMomentBound but with the constant C
    stated up front rather than existentially quantified per (q, chi). -/
def SecondMomentBoundUniform (C : ℝ) : Prop :=
  ∀ q : Nat, q.Prime →
  ∀ χ : Nat → ℂ, (∀ a, Complex.normSq (χ a) ≤ 1) →
    ∀ K : Nat, 0 < K → ∃ X₀ : Nat, ∀ X, X₀ ≤ X →
      populationCharEnergy q χ K X ≤ C * K

/-- A uniform second moment bound implies the existential form. -/
theorem secondMomentBoundUniform_implies_smb (C : ℝ) (hC : 0 < C)
    (h : SecondMomentBoundUniform C) : SecondMomentBound := by
  intro q hq χ hχ
  exact ⟨C, hC, h q hq χ hχ⟩

/-- CharSumVarianceBound(C) implies SecondMomentBoundUniform(C). -/
theorem charSumVarianceBound_implies_uniform (C : ℝ)
    (hvb : CharSumVarianceBound C) : SecondMomentBoundUniform C := by
  intro q hq χ hχ K _hK
  obtain ⟨X₀, hX₀⟩ := hvb q hq χ hχ K
  use X₀
  intro X hX
  by_cases hsf : sqfreeCount X = 0
  · -- No squarefree numbers: population energy is 0, and 0 ≤ C * K
    simp only [populationCharEnergy, if_pos hsf]
    exact le_trans (ensembleAvg_nonneg fun n _ => genSeqCharEnergy_nonneg n K q χ) (hX₀ X hX)
  · rw [populationCharEnergy_eq_ensembleAvg q χ K X (Nat.pos_of_ne_zero hsf)]
    exact hX₀ X hX

end AlternateRoute

end
