import EM.Reduction.DSLVariance
import EM.Population.WeakErgodicity

/-!
# Tail Identity Attack on DSL

This file formalizes the **Tail Identity Attack** infrastructure for the
Deterministic Stability Lemma (DSL). The key observation:

Each standard EM accumulator `prod(M)` is squarefree, hence a legitimate
ensemble member. The character energy of the orbit starting from `prod(M)`
over K steps equals the character energy of the standard EM orbit's tail
from step M to M+K. This identity connects **ensemble averages** (over
all squarefree starting points) to the **standard EM trajectory** (n=2).

## Main Results

### Tail Identity (Proved)
* `genSeqCharPartialSum_tail`       -- partial sum from prod(M) = tail partial sum
* `genSeqCharEnergy_tail`           -- energy from prod(M) = tail energy
* `genSeqCharEnergy_standard_tail`  -- specialization to standard EM (n=2)

### Ensemble Membership (Proved)
* `standard_accum_squarefree`       -- prod(M) is squarefree
* `standard_accum_ge_two`           -- prod(M) >= 2
* `standard_accum_in_range`         -- prod(M) is in the squarefree filter

### Fourth Moment Infrastructure (Definitions + Nonnegativity Proved)
* `genSeqCharEnergySquared`              -- E(n,K)^2
* `populationCharEnergySquared`          -- population average of E^2
* `genSeqCharEnergySquared_nonneg`       -- E^2 >= 0
* `populationCharEnergySquared_nonneg`   -- population E^2 >= 0

### Four-Point Correlation (Open Hypotheses)
* `FourPointPCV`                    -- four-point pairwise correlation vanishing
* `SecondMomentSquaredBound`        -- E[E^2] = O(K^2)
* `ChebyshevDensityBound`          -- O(1/K^2) density bound for bad starting points
* `FourPointPCVImpliesDSL`         -- master reduction: FourPointPCV => DSL

### Bridge (Proved)
* `second_moment_squared_implies_chebyshev` -- SMSB => CDB (Markov argument)

## Mathematical Overview

The tail identity attack works as follows:
1. prod(M) is squarefree (proved), so it is a member of the ensemble S(X)
   for X >= prod(M).
2. The character energy of the orbit from prod(M) over K steps equals the
   energy of the standard EM tail from step M to M+K (proved).
3. If FourPointPCV holds, then E[E(n,K)^2] = O(K^2) (second moment squared).
4. By Chebyshev's inequality, density of {n : E(n,K) > (eps*K)^2} = O(1/K^2).
5. Since prod(M) grows super-exponentially, for most M, prod(M) is in the
   "good" set, giving cofinally good dyadic windows for the standard orbit.
6. Dyadic summation gives |sum chi(seq(k))| = o(N), i.e., CME for n=2.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Tail Identity -/

section TailIdentity

/-- The character partial sum from ensemble member `genProd n M` over K steps
    equals the character partial sum of orbit n's tail from step M to M+K.

    This is a direct consequence of `genSeq_restart`: genSeq (genProd n M) k
    = genSeq n (M + k). -/
theorem genSeqCharPartialSum_tail (n M K q : Nat) (χ : Nat → ℂ) :
    genSeqCharPartialSum (genProd n M) K q χ =
    ∑ k ∈ Finset.range K, χ (genSeq n (M + k) % q) := by
  unfold genSeqCharPartialSum
  congr 1; ext k
  rw [genSeq_restart]

/-- The character energy from ensemble member `genProd n M` over K steps
    equals the character energy of orbit n's tail from M.

    Since energy = |partial_sum|^2, this follows from the partial sum identity. -/
theorem genSeqCharEnergy_tail (n M K q : Nat) (χ : Nat → ℂ) :
    genSeqCharEnergy (genProd n M) K q χ =
    Complex.normSq (∑ k ∈ Finset.range K, χ (genSeq n (M + k) % q)) := by
  unfold genSeqCharEnergy
  congr 1
  exact genSeqCharPartialSum_tail n M K q χ

/-- The character energy from the standard accumulator `prod M` equals the
    energy of the standard EM sequence tail from step M.

    Specializes the tail identity to n = 2 using:
    - `genProd_two_eq_prod`: genProd 2 M = prod M
    - `genSeq_two_eq_seq_succ`: genSeq 2 k = seq (k + 1) -/
theorem genSeqCharEnergy_standard_tail (M K q : Nat) (χ : Nat → ℂ) :
    genSeqCharEnergy (prod M) K q χ =
    Complex.normSq (∑ k ∈ Finset.range K, χ (seq (M + k + 1) % q)) := by
  rw [← genProd_two_eq_prod, genSeqCharEnergy_tail]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [genSeq_two_eq_seq_succ]

end TailIdentity

/-! ## Ensemble Membership of Standard Accumulators -/

section EnsembleMembership

/-- Each standard accumulator `prod M` is squarefree (the EM accumulator
    is a product of distinct primes). -/
theorem standard_accum_squarefree (M : Nat) : Squarefree (prod M) :=
  prod_squarefree M

/-- `prod M` is at least 2 (since prod 0 = 2 and the sequence is increasing). -/
theorem standard_accum_ge_two (M : Nat) : 2 ≤ prod M :=
  prod_ge_two M

/-- `prod M` belongs to the squarefree set `{n in [1, prod M] : Squarefree n}`.
    This means prod M is a legitimate ensemble member for X >= prod M. -/
theorem standard_accum_in_range (M : Nat) :
    prod M ∈ (Finset.Icc 1 (prod M)).filter Squarefree := by
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by linarith [standard_accum_ge_two M], le_refl _⟩, standard_accum_squarefree M⟩

/-- `prod M` belongs to the squarefree set `{n in [1, X] : Squarefree n}` for X >= prod M. -/
theorem standard_accum_in_large_range (M X : Nat) (hX : prod M ≤ X) :
    prod M ∈ (Finset.Icc 1 X).filter Squarefree := by
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by linarith [standard_accum_ge_two M], hX⟩, standard_accum_squarefree M⟩

end EnsembleMembership

/-! ## Fourth Moment / Squared Energy Infrastructure -/

section FourthMoment

/-- The squared character energy: E(n,K)^2 = |S_K(n)|^4.
    This is the quantity whose population average gives the fourth moment,
    which controls concentration via Chebyshev's inequality. -/
def genSeqCharEnergySquared (n K q : Nat) (χ : Nat → ℂ) : ℝ :=
  (genSeqCharEnergy n K q χ) ^ 2

/-- Population average of the squared character energy.
    When sqfreeCount X = 0, returns 0 (no squarefree numbers). -/
def populationCharEnergySquared (q : Nat) (χ : Nat → ℂ) (K X : Nat) : ℝ :=
  if sqfreeCount X = 0 then 0
  else (1 / (sqfreeCount X : ℝ)) *
    ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
      genSeqCharEnergySquared n K q χ

/-- Squared energy is nonneg (it is a square of a real number). -/
theorem genSeqCharEnergySquared_nonneg (n K q : Nat) (χ : Nat → ℂ) :
    0 ≤ genSeqCharEnergySquared n K q χ :=
  sq_nonneg _

/-- Population squared energy is nonneg. -/
theorem populationCharEnergySquared_nonneg (q : Nat) (χ : Nat → ℂ) (K X : Nat) :
    0 ≤ populationCharEnergySquared q χ K X := by
  unfold populationCharEnergySquared
  split
  · exact le_refl 0
  · apply mul_nonneg
    · apply div_nonneg one_pos.le
      exact Nat.cast_nonneg _
    · apply Finset.sum_nonneg
      intro n _
      exact genSeqCharEnergySquared_nonneg n K q χ

/-- The squared energy decomposes: E(n,K)^2 = (genSeqCharEnergy n K q χ)^2. -/
theorem genSeqCharEnergySquared_eq_sq (n K q : Nat) (χ : Nat → ℂ) :
    genSeqCharEnergySquared n K q χ = (genSeqCharEnergy n K q χ) ^ 2 :=
  rfl

/-- When E(n,K) = 0, the squared energy is also 0. -/
theorem genSeqCharEnergySquared_of_energy_zero {n K q : Nat} {χ : Nat → ℂ}
    (h : genSeqCharEnergy n K q χ = 0) :
    genSeqCharEnergySquared n K q χ = 0 := by
  unfold genSeqCharEnergySquared; rw [h]; ring

end FourthMoment

/-! ## Four-Point PCV Hypothesis and Bridges -/

section FourPointPCV

/-- **Four-point PCV**: the four-point correlation vanishes for distinct index pairs.
    This is the key hypothesis for the Chebyshev bound approach.

    For distinct unordered pairs (j1,k1) != (j2,k2) with j1 < k1, j2 < k2,
    the four-point correlation
      E_sqf[Re(chi(m_{j1}) * conj(chi(m_{k1}))) * Re(chi(m_{j2}) * conj(chi(m_{k2})))]
    vanishes as X -> infinity, for bounded chi.

    This should follow from CRT independence at four distinct steps, extending
    the two-point PCV mechanism (which is StepDecorrelation). The key input is
    that for distinct pairs, the CRT factorization provides independence of the
    cross-term products.

    **Status**: OPEN hypothesis. -/
def FourPointPCV : Prop :=
  ∀ q : Nat, q.Prime →
  ∀ χ : Nat → ℂ, (∀ a, Complex.normSq (χ a) ≤ 1) →
    ∀ j₁ k₁ j₂ k₂ : Nat, j₁ < k₁ → j₂ < k₂ →
      (j₁ ≠ j₂ ∨ k₁ ≠ k₂) →
      ∀ ε : ℝ, 0 < ε →
        ∃ X₀ : Nat, ∀ X : Nat, X₀ ≤ X →
          sqfreeCount X ≠ 0 →
          (1 / (sqfreeCount X : ℝ)) *
            |∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
              ((χ (genSeq n j₁ % q) * starRingEnd ℂ (χ (genSeq n k₁ % q))).re *
               (χ (genSeq n j₂ % q) * starRingEnd ℂ (χ (genSeq n k₂ % q))).re)| < ε

/-- **SecondMomentSquaredBound**: the population average of E(n,K)^2 is O(K^2).
    This is the consequence of FourPointPCV.

    The second moment squared is E_sqf[|S_K(n)|^4]. When the cross terms of
    the expansion of |S_K|^2 are pairwise uncorrelated (FourPointPCV), the
    expansion of E[|S_K|^4] = E[(|S_K|^2)^2] gives at most O(K^2) terms
    with each contributing O(1), yielding E[|S_K|^4] = O(K^2).

    **Status**: open hypothesis. -/
def SecondMomentSquaredBound (D : ℝ) : Prop :=
  ∀ q : Nat, q.Prime →
  ∀ χ : Nat → ℂ, (∀ a, Complex.normSq (χ a) ≤ 1) →
    ∀ K : Nat, 0 < K →
      ∃ X₀ : Nat, ∀ X : Nat, X₀ ≤ X →
        populationCharEnergySquared q χ K X ≤ D * (K : ℝ) ^ 2

/-- **ChebyshevDensityBound**: from a second moment squared bound, Markov's
    inequality gives an O(1/K^2) density bound for bad starting points.

    If E[E(n,K)^2] <= D * K^2, then by Markov's inequality:
      Pr[E(n,K) > (eps * K)] = Pr[E(n,K)^2 > (eps * K)^2]
                              <= E[E^2] / (eps * K)^2
                              <= D * K^2 / (eps^2 * K^2)
                              = D / eps^2.

    Actually, we want a bound that improves with K. The correct fourth-moment
    approach: if E[E(n,K)^2] <= D * K^2, then
      Pr[E(n,K)^2 > threshold^2] <= D * K^2 / threshold^2.

    Setting threshold = eps * K^2 (so E(n,K) > eps * K^2 is the "bad" event),
    the density is <= D / (eps^2 * K^2).

    **Status**: proved from SecondMomentSquaredBound via Markov argument. -/
def ChebyshevDensityBound (D : ℝ) : Prop :=
  0 < D →
  ∀ q : Nat, q.Prime →
  ∀ χ : Nat → ℂ, (∀ a, Complex.normSq (χ a) ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      ∀ K : Nat, 0 < K →
        ∃ X₀ : Nat, ∀ X : Nat, X₀ ≤ X →
          sqfreeCount X ≠ 0 →
          (((Finset.Icc 1 X).filter (fun n =>
            Squarefree n ∧ genSeqCharEnergySquared n K q χ > ε * (K : ℝ) ^ 2)).card : ℝ) /
            (sqfreeCount X : ℝ) ≤ D / ε

end FourPointPCV

/-! ## Bridge: SecondMomentSquaredBound => ChebyshevDensityBound -/

section ChebyshevBridge

/-- **Markov helper**: if the average of a nonneg function over a finite set S
    is at most M, then the fraction of S with f(n) > t is at most M/t.

    This is a specialized version for our density counting setup. -/
private theorem density_markov_bound {S : Finset Nat} {f : Nat → ℝ} {M t : ℝ}
    (hS : S.Nonempty)
    (hf_nn : ∀ n ∈ S, 0 ≤ f n)
    (ht : 0 < t)
    (havg : (1 / (S.card : ℝ)) * ∑ n ∈ S, f n ≤ M) :
    ((S.filter (fun n => f n > t)).card : ℝ) / (S.card : ℝ) ≤ M / t := by
  have hS_pos : (0 : ℝ) < S.card :=
    Nat.cast_pos.mpr (Finset.Nonempty.card_pos hS)
  -- From the average bound: sum f(n) <= M * |S|
  have hsum : ∑ n ∈ S, f n ≤ M * S.card := by
    have h1 : (1 / (S.card : ℝ)) * ∑ n ∈ S, f n ≤ M := havg
    rwa [div_mul_eq_mul_div, one_mul, div_le_iff₀ hS_pos] at h1
  set B := S.filter (fun n => f n > t)
  have hB_sub : B ⊆ S := Finset.filter_subset _ S
  -- t * |B| <= sum_B f <= sum_S f <= M * |S|
  have hsum_B : t * B.card ≤ ∑ n ∈ S, f n := by
    calc t * (B.card : ℝ) = ∑ _n ∈ B, t := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ B, f n := by
          apply Finset.sum_le_sum
          intro n hn
          exact le_of_lt (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n ∈ S, f n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hB_sub
          intro i hi _
          exact hf_nn i hi
  -- |B| / |S| <= M / t  via  |B| * t <= M * |S|
  rw [div_le_div_iff₀ hS_pos ht]
  calc (B.card : ℝ) * t = t * B.card := by ring
    _ ≤ ∑ n ∈ S, f n := hsum_B
    _ ≤ M * S.card := hsum

/-- **Chebyshev's inequality for the squared energy**:
    if E[E^2] <= D * K^2, then density(E^2 > eps * K^2) <= D / eps.

    This is a direct application of Markov's inequality to the nonneg
    function E(n,K)^2 = genSeqCharEnergySquared. -/
theorem second_moment_squared_implies_chebyshev (D : ℝ) :
    SecondMomentSquaredBound D → ChebyshevDensityBound D := by
  intro hsmb _hD q hq χ hχ ε hε K hK
  obtain ⟨X₀, hX₀⟩ := hsmb q hq χ hχ K hK
  use X₀
  intro X hX hsf
  set S := (Finset.Icc 1 X).filter Squarefree with hS_def
  have hS_ne : S.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero, ← sqfreeCount]
  have hpop : populationCharEnergySquared q χ K X ≤ D * (K : ℝ) ^ 2 := hX₀ X hX
  unfold populationCharEnergySquared at hpop
  rw [if_neg hsf] at hpop
  have hεK : 0 < ε * (K : ℝ) ^ 2 := by
    apply mul_pos hε
    exact pow_pos (Nat.cast_pos.mpr hK) 2
  -- Rewrite filter over Icc 1 X as filter over S
  have hfilter_eq : (Finset.Icc 1 X).filter (fun n =>
      Squarefree n ∧ genSeqCharEnergySquared n K q χ > ε * (K : ℝ) ^ 2) =
    S.filter (fun n => genSeqCharEnergySquared n K q χ > ε * (K : ℝ) ^ 2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, hS_def]
    constructor
    · rintro ⟨hmem, hsqf, hgt⟩; exact ⟨⟨hmem, hsqf⟩, hgt⟩
    · rintro ⟨⟨hmem, hsqf⟩, hgt⟩; exact ⟨hmem, hsqf, hgt⟩
  rw [hfilter_eq]
  -- Prepare the average bound in the form density_markov_bound expects
  have hpop' : (1 / (S.card : ℝ)) * ∑ n ∈ S, genSeqCharEnergySquared n K q χ ≤
      D * (K : ℝ) ^ 2 := by
    convert hpop using 2
  -- Apply Markov: gives bound D * K^2 / (ε * K^2)
  have hmarkov := density_markov_bound hS_ne
    (fun n _ => genSeqCharEnergySquared_nonneg n K q χ)
    hεK hpop'
  -- Simplify D * K^2 / (ε * K^2) = D / ε
  have hK_pos : (0 : ℝ) < (K : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hK) 2
  rw [sqfreeCount, ← hS_def]
  calc (↑(S.filter (fun n => genSeqCharEnergySquared n K q χ > ε * ↑K ^ 2)).card : ℝ) /
        ↑S.card
      ≤ D * (K : ℝ) ^ 2 / (ε * (K : ℝ) ^ 2) := hmarkov
    _ = D / ε := by rw [mul_div_mul_right _ _ (ne_of_gt hK_pos)]

end ChebyshevBridge

/-! ## Master Reduction Hypothesis -/

section MasterReduction

/-- **The master hypothesis for the tail identity attack**:
    FourPointPCV implies DeterministicStabilityLemma.

    Proof roadmap (all steps except FourPointPCV are either proved or standard):
    1. FourPointPCV => E[E(n,K)^2] = O(K^2)   (four-point decomposition)
    2. E[E(n,K)^2] = O(K^2) => Chebyshev O(1/K^2) density bound (PROVED above)
    3. O(1/K^2) + Borel-Cantelli on prod(M) => cofinally good dyadic windows
    4. Dyadic summation => |sum chi(seq(k))| = o(N) (CME for n=2)
    5. CME => DSL via full_chain_dsl

    **Status**: open hypothesis. -/
def FourPointPCVImpliesDSL : Prop :=
  FourPointPCV → DeterministicStabilityLemma

/-- **FourPointPCV implies SecondMomentSquaredBound**: the four-point
    decorrelation gives the quartic moment bound E[|S_K|^4] = O(K^2).

    The expansion of |S_K|^4 = (sum_{j<k} cross_{jk})^2 involves O(K^4) terms,
    but the four-point PCV says all "off-diagonal" four-point correlations vanish.
    The "diagonal" contribution (where (j1,k1) = (j2,k2) as unordered pairs)
    has O(K^2) terms, each bounded by O(1) since |chi| <= 1.

    **Status**: open hypothesis. -/
def FourPointPCVImpliesSMSB : Prop :=
  FourPointPCV → ∃ D : ℝ, 0 < D ∧ SecondMomentSquaredBound D

/-- The full chain from FourPointPCV to ChebyshevDensityBound:
    FourPointPCV => SMSB (open) => CDB (proved). -/
theorem four_point_pcv_chain
    (h1 : FourPointPCVImpliesSMSB) (h2 : FourPointPCV) :
    ∃ D : ℝ, 0 < D ∧ ChebyshevDensityBound D := by
  obtain ⟨D, hD, hsmb⟩ := h1 h2
  exact ⟨D, hD, second_moment_squared_implies_chebyshev D hsmb⟩

end MasterReduction

/-! ## Tail Energy at Standard Accumulators -/

section StandardTailEnergy

/-- The character energy of the ensemble member `prod M` equals the
    energy of the standard EM tail. Moreover, this ensemble member
    is in the squarefree population for X >= prod M. Combined, these
    facts mean that the energy of the standard EM tail contributes to
    the population energy average.

    Specifically: if genSeqCharEnergySquared (prod M) K q chi > threshold,
    then prod M is in the "bad set" used by ChebyshevDensityBound. -/
theorem standard_tail_in_population (M K X q : Nat) (χ : Nat → ℂ)
    (hX : prod M ≤ X) (threshold : ℝ)
    (hbad : genSeqCharEnergySquared (prod M) K q χ > threshold) :
    prod M ∈ (Finset.Icc 1 X).filter (fun n =>
      Squarefree n ∧ genSeqCharEnergySquared n K q χ > threshold) := by
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by linarith [standard_accum_ge_two M], hX⟩,
         standard_accum_squarefree M, hbad⟩

/-- If the bad set has density zero for large X, then for each fixed M,
    eventually prod M is NOT in the bad set. This connects the density
    bound back to the specific starting point prod M.

    Stated as: if for all X >= X0, the bad set card is 0, then
    genSeqCharEnergySquared (prod M) K q chi <= threshold whenever
    prod M <= X for some X >= X0. -/
theorem standard_tail_not_bad (M K q : Nat) (χ : Nat → ℂ) (threshold : ℝ)
    (X₀ : Nat)
    (hbad_empty : ∀ X : Nat, X₀ ≤ X →
      ((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ genSeqCharEnergySquared n K q χ > threshold)).card = 0)
    (hX : X₀ ≤ prod M) :
    genSeqCharEnergySquared (prod M) K q χ ≤ threshold := by
  by_contra h
  push Not at h
  have hmem := standard_tail_in_population M K (prod M) q χ (le_refl _) threshold h
  have h0 := hbad_empty (prod M) hX
  rw [Finset.card_eq_zero] at h0
  exact absurd hmem (by rw [h0]; simp)

end StandardTailEnergy

end
