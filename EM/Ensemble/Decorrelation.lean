import EM.Ensemble.FirstMoment

/-!
# Ensemble Decorrelation and Equidistribution

This file formalizes the **ensemble decorrelation** framework (Steps 8–9 of
the master proof strategy). The key insight is that CRT decorrelation
(`crt_multiplier_invariance`, proved) implies approximate independence of
character values at different steps when averaged over starting points.

## Mathematical Background

For a non-trivial character χ mod q and steps j < k:
- χ(genSeq n j) depends on genProd n j mod q
- χ(genSeq n k) depends on genProd n k mod q
- Between steps j and k, the accumulator undergoes (k−j) multiplications
  by fresh primes and (k−j) additions of 1
- Each "+1" shift decorrelates the mod-q information (proved: `crt_multiplier_invariance`)
- Averaged over starting points: CRT independence gives decorrelation

The variance bound follows:
- Var[∑_{k<K} χ(genSeq n k)] = ∑_j ∑_k Cov(χ_j, χ_k)
- Diagonal: ∑_j |χ_j|² = K
- Off-diagonal: ∑_{j≠k} |Cov| ≤ K · ∑_{d≥1} ε(d) = O(K) if ∑ε(d) < ∞

## Main Results

### Definitions
* `genSeqCharPartialSum`       -- sum_{k<K} chi(genSeq n k) (multiplier char sum)
* `genSeqCharEnergy`           -- |sum_{k<K} chi(genSeq n k)|^2 (multiplier char energy)
* `genWalkCharPartialSum`      -- sum_{k<K} chi(genProd n k) (walk char sum)
* `genWalkCharEnergy`          -- |sum_{k<K} chi(genProd n k)|^2 (walk char energy)
* `MultCancelToWalkCancel`     -- walk cancellation for squarefree n (equiv. CCSB/CME, OPEN)
* `StepDecorrelation`          -- character values decorrelate when averaged over n
* `CharSumVarianceBound`       -- Var[sum chi] = O(K) (from decorrelation)
* `EnsembleCharSumConcentration` -- concentration for character sums

### Proved Theorems
* `genSeqCharEnergy_nonneg`    -- multiplier char energy is non-negative (PROVED)
* `genWalkCharEnergy_nonneg`   -- walk char energy is non-negative (PROVED)
* `finset_markov_density`      -- discrete Markov inequality in density form (PROVED)
* `char_variance_density_bound`-- Markov bound on bad density: <= C/(eps^2 K) (PROVED)
* `char_concentration_implies_cancellation` -- concentration -> cancellation (PROVED)

### Open Hypotheses
* `MultCancelToWalkCancel`     -- walk cancellation for squarefree n (equiv. CCSB/CME)
* `StepDecorrelation`          -- CRT-based decorrelation (provable from CRT + PE)
* `CharSumVarianceBound`       -- variance bound (follows from decorrelation)

### Proved Reductions
* `char_variance_implies_concentration_proved` -- VB -> concentration (PROVED, Markov + Metric.tendsto_atTop)
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter

/-! ## Character Sums over Generalized EM Sequences -/

section CharSums

/-- The character sum of the generalized EM sequence from starting point n,
    evaluated at character χ mod q, up to K steps.

    This is the analogue of the walk character sum ∑_{k<K} χ(w_k) but for
    the ensemble of EM sequences parametrized by starting point n. -/
def genSeqCharPartialSum (n K q : Nat) (χ : Nat → ℂ) : ℂ :=
  ∑ k ∈ Finset.range K, χ (genSeq n k % q)

/-- The squared modulus of the character sum. This is the quantity whose
    ensemble average gives the variance (up to a mean correction). -/
def genSeqCharEnergy (n K q : Nat) (χ : Nat → ℂ) : ℝ :=
  Complex.normSq (genSeqCharPartialSum n K q χ)

/-- The character sum of the walk positions (genProd) for the generalized EM
    sequence from starting point n, evaluated at function χ, up to K steps.

    Unlike `genSeqCharPartialSum` which sums χ over the multipliers (genSeq),
    this sums χ over the walk positions (genProd). The distinction matters:
    multiplier cancellation does NOT imply walk cancellation in general
    (see Dead End #58). -/
def genWalkCharPartialSum (n K q : Nat) (χ : Nat → ℂ) : ℂ :=
  ∑ k ∈ Finset.range K, χ (genProd n k % q)

/-- The squared modulus of the walk character sum. This is the quantity
    whose smallness (o(K²)) implies equidistribution of the walk
    in (Z/qZ) via the Weyl criterion. -/
def genWalkCharEnergy (n K q : Nat) (χ : Nat → ℂ) : ℝ :=
  Complex.normSq (genWalkCharPartialSum n K q χ)

/-- The walk character energy is non-negative (it is a norm squared). -/
theorem genWalkCharEnergy_nonneg (n K q : Nat) (χ : Nat → ℂ) :
    0 ≤ genWalkCharEnergy n K q χ :=
  Complex.normSq_nonneg _

/-- **Multiplier cancellation to walk cancellation transfer (pointwise).**

    This hypothesis states that for any squarefree starting point n and prime q
    not dividing n, if χ is a nontrivial character mod q, then the walk character
    energy genWalkCharEnergy n K q χ is eventually bounded by (ε·K)².

    The difficulty is that multiplier cancellation (genSeqCharEnergy = o(K²))
    does NOT imply walk cancellation (genWalkCharEnergy = o(K²)) in general:

    - Dead End #58 shows this is FALSE for abstract multiplicative walks
      (counterexample: multipliers cycling {-1,-1,+1,+1} on (Z/5Z)× give
      multiplier sums O(1) but walk sums Θ(N)).

    - Dead End #117 shows this remains false even for walks with ALL
      EM-specific structural properties (squarefree accumulator, coprime
      cascade, minFac selection, CRT invariance, super-exponential growth).

    This gap is equivalent in difficulty to CCSB/CME — the core open
    problem of the project. The Marginal/Joint Barrier manifests here:
    multiplier sums give marginal information, walk sums require joint
    information about all previous multipliers.

    Note: this is stated unconditionally (not conditional on multiplier
    cancellation) because the conditional form would require extracting
    pointwise multiplier cancellation for n=2 from the JSE density statement,
    which is not possible (density→0 does not imply pointwise bounds for
    any specific n). The JSE chain provides motivation but not a usable input.

    **Status**: OPEN — equivalent to CCSB/CME. -/
def MultCancelToWalkCancel : Prop :=
  ∀ (n : Nat), Squarefree n → 1 ≤ n →
  ∀ (q : Nat) (hq : Nat.Prime q), ¬ (q ∣ n) →
  ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
  (χ 0 = 0) →
  (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, χ (ZMod.val a) = 0) →
  ∀ (ε : ℝ), 0 < ε →
  ∃ K₀ : Nat, ∀ K : Nat, K₀ ≤ K → genWalkCharEnergy n K q χ ≤ (ε * K) ^ 2

end CharSums

/-! ## Step Decorrelation Hypothesis -/

section Decorrelation

/-- **Step Decorrelation**: character values at different steps are approximately
    uncorrelated when averaged over squarefree starting points.

    For a non-trivial character χ mod q and steps j < k:
    |E_n[χ(genSeq n j) · conj(χ(genSeq n k))]| → 0 as X → ∞.

    The structural basis:
    1. `crt_multiplier_invariance` (PROVED): genSeq n k mod q doesn't depend
       on genProd n k mod q (position-blindness).
    2. Between steps j and k, the accumulator undergoes (k−j) operations
       (multiply by fresh prime, then observe minFac of result + 1).
    3. Each operation involves a "+1" shift that decorrelates mod-q info.
    4. Averaged over n: CRT independence of the mod-q and non-mod-q coordinates
       gives approximate independence of χ(genSeq n j) and χ(genSeq n k).

    **Status**: open hypothesis, provable from CRT + PE. -/
def StepDecorrelation : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (χ : Nat → ℂ), -- a character mod q (nontrivial)
  ∀ (j k : Nat), j < k →
    Filter.Tendsto
      (fun X : Nat =>
        |ensembleAvg X (fun n =>
            (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n k % q))).re)|)
      Filter.atTop (nhds 0)

end Decorrelation

/-! ## Character Sum Variance Bound -/

section VarianceBound

/-- **Character Sum Variance Bound**: the ensemble average of |∑χ|² grows
    at most linearly in K.

    E_n[|∑_{k<K} χ(genSeq n k)|²] ≤ C · K

    This follows from expanding |∑χ|² = ∑_j ∑_k χ_j · conj(χ_k):
    - Diagonal (j = k): each |χ_j|² ≤ 1, contributes ≤ K
    - Off-diagonal (j ≠ k): controlled by StepDecorrelation
    - If the correlations decay summably: total ≤ K + K · ∑_{d≥1} ε(d) = O(K)

    **Status**: open hypothesis, follows from StepDecorrelation + summable decay. -/
def CharSumVarianceBound (C : ℝ) : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
  ∀ K : Nat, ∃ X₀ : Nat, ∀ X ≥ X₀,
    ensembleAvg X (fun n => genSeqCharEnergy n K q χ) ≤ C * K

end VarianceBound

/-! ## Character Sum Concentration -/

section CharConcentration

/-- **Ensemble Character Sum Concentration**: for each prime q, character χ,
    threshold ε > 0, and density target δ > 0, there exists K₀ such that
    for all K ≥ K₀, there exists X₀ such that for all X ≥ X₀, the density
    of squarefree n in [1,X] with |∑_{k<K} χ(genSeq n k)|² > (ε·K)² is at most δ.

    This is the pointwise Chebyshev/Markov consequence of `CharSumVarianceBound`:
    Pr[|∑χ|² > (εK)²] ≤ E[|∑χ|²]/(εK)² ≤ CK/(ε²K²) = C/(ε²K).
    Choosing K ≥ C/(ε²δ) makes this ≤ δ.

    The two-parameter (ε, δ) formulation separates the threshold from the
    density bound, allowing the downstream `char_concentration_implies_cancellation`
    to drive δ → 0 and recover Tendsto(nhds 0) for the "∀ K" deviant set. -/
def EnsembleCharSumConcentration : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
  ∀ (ε : ℝ), 0 < ε →
  ∀ (δ : ℝ), 0 < δ →
  ∃ K₀ : Nat,
    ∀ K ≥ K₀, ∃ X₀ : Nat, ∀ X ≥ X₀,
      (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧
          genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card ≤ δ

/-- **CharSumVarianceBound → EnsembleCharSumConcentration.** PROVED.

    By Chebyshev/Markov: if E[|∑χ|²] ≤ CK, then
    Pr[|∑χ|² > (εK)²] ≤ CK/(εK)² = C/(ε²K).

    For K ≥ ⌈C/(ε²δ)⌉ + 1, this bound is ≤ δ. The X₀ for each K comes
    from `char_variance_density_bound` (the proved Markov inequality). -/
def CharVarianceImpliesConcentration : Prop :=
  ∀ (C : ℝ), 0 < C →
    CharSumVarianceBound C → EnsembleCharSumConcentration

/-- The character energy `genSeqCharEnergy` is non-negative (it's a norm squared). -/
theorem genSeqCharEnergy_nonneg (n K q : Nat) (χ : Nat → ℂ) :
    0 ≤ genSeqCharEnergy n K q χ :=
  Complex.normSq_nonneg _

/-- **Markov density bound** (Finset version): if the average of a non-negative
    function f over squarefree n in [1,X] is at most M, and a subset B of those
    squarefree n has f(n) ≥ t for all n ∈ B (with t > 0), then |B|/|SF| ≤ M/t.

    This is the discrete Markov/Chebyshev inequality in density form. -/
theorem finset_markov_density {X : Nat} {f : Nat → ℝ} {M t : ℝ}
    (hf_nn : ∀ n ∈ (Finset.Icc 1 X).filter Squarefree, 0 ≤ f n)
    (ht : 0 < t)
    (hM_nn : 0 ≤ M)
    (havg : ensembleAvg X f ≤ M)
    (B : Finset Nat)
    (hB_sub : B ⊆ (Finset.Icc 1 X).filter Squarefree)
    (hB_threshold : ∀ n ∈ B, t ≤ f n) :
    (B.card : ℝ) / ((Finset.Icc 1 X).filter Squarefree).card ≤ M / t := by
  set S := (Finset.Icc 1 X).filter Squarefree
  by_cases hsf : S.card = 0
  · -- S is empty, so B is empty too
    have hB_empty : B = ∅ :=
      Finset.subset_empty.mp (Finset.card_eq_zero.mp hsf ▸ hB_sub)
    simp [hB_empty, hsf, div_nonneg hM_nn ht.le]
  · have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsf)
    -- Step 1: ∑_{n ∈ S} f(n) ≤ M * |S|
    have hsum_bound : ∑ n ∈ S, f n ≤ M * S.card := by
      unfold ensembleAvg sqfreeCount at havg
      rwa [div_le_iff₀ hS_pos] at havg
    -- Step 2: |B| * t ≤ ∑_{n ∈ B} f(n)
    have hB_lower : (B.card : ℝ) * t ≤ ∑ n ∈ B, f n :=
      calc (B.card : ℝ) * t = ∑ _ ∈ B, t := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ n ∈ B, f n := Finset.sum_le_sum hB_threshold
    -- Step 3: ∑_{n ∈ B} f(n) ≤ ∑_{n ∈ S} f(n)
    have hB_sum_le : ∑ n ∈ B, f n ≤ ∑ n ∈ S, f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hB_sub (fun n hn _ => hf_nn n hn)
    -- Combine: |B| * t ≤ M * |S|
    have : (B.card : ℝ) * t ≤ M * S.card := by linarith
    -- Conclude: |B|/|S| ≤ M/t
    exact (div_le_div_iff₀ hS_pos ht).mpr this

/-- **Markov bound on bad density**: for X ≥ X₀, the density of squarefree
    starting points with large character energy is bounded by C/(ε²K).

    This is the quantitative content of the Chebyshev/Markov inequality
    applied to the ensemble average from `CharSumVarianceBound`. -/
theorem char_variance_density_bound (C : ℝ) (hC : 0 < C)
    (hvb : CharSumVarianceBound C) (q : Nat) (hq : Nat.Prime q)
    (χ : Nat → ℂ) (hχ : ∀ a, Complex.normSq (χ a) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ K ≥ 1, ∃ X₀ : Nat, ∀ X ≥ X₀,
      (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧
          genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card ≤
      C * ↑K / (ε * ↑K) ^ 2 := by
  intro K hK
  obtain ⟨X₀, hX₀⟩ := hvb q hq χ hχ K
  refine ⟨X₀, fun X hX => ?_⟩
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hεK_sq_pos : (0 : ℝ) < (ε * ↑K) ^ 2 := sq_pos_of_pos (mul_pos hε hK_pos)
  exact finset_markov_density
    (fun _ _ => genSeqCharEnergy_nonneg _ _ _ _)
    hεK_sq_pos
    (mul_nonneg hC.le hK_pos.le)
    (hX₀ X hX)
    _
    (fun n hn => by simp only [Finset.mem_filter] at hn ⊢; exact ⟨hn.1, hn.2.1⟩)
    (fun n hn => by simp only [Finset.mem_filter] at hn; exact hn.2.2.le)

/-- **CharVarianceImpliesConcentration is PROVED.**

    The proof strategy: given CharSumVarianceBound C, for any ε, δ > 0,
    the Markov bound gives density ≤ C·K/(ε·K)² = C/(ε²·K) for X ≥ X₀(K).
    Choose K₀ so that C/(ε²·K₀) ≤ δ; then for K ≥ K₀, the bound C/(ε²·K) ≤ δ.
    The X₀ for each K comes from char_variance_density_bound. -/
theorem char_variance_implies_concentration_proved :
    CharVarianceImpliesConcentration := by
  intro C hC hvb q hq χ hχ ε hε δ hδ
  -- We need: ∃ K₀, ∀ K ≥ K₀, ∃ X₀, ∀ X ≥ X₀, density ≤ δ
  -- The Markov bound gives: for K ≥ 1, ∃ X₀(K), ∀ X ≥ X₀(K), density ≤ C·K/(ε·K)²
  -- C·K/(ε·K)² = C/(ε²·K), so we need C/(ε²·K) ≤ δ, i.e., K ≥ C/(ε²·δ)
  set K₀ := Nat.max 1 (Nat.ceil (C / (ε ^ 2 * δ)) + 1)
  refine ⟨K₀, fun K hK => ?_⟩
  -- K ≥ K₀ ≥ 1
  have hK_ge_one : K ≥ 1 := (Nat.le_max_left 1 _).trans hK
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Get X₀ from char_variance_density_bound and simplify C·K/(ε·K)² = C/(ε²·K)
  obtain ⟨X₀, hX₀⟩ := char_variance_density_bound C hC hvb q hq χ hχ ε hε K hK_ge_one
  refine ⟨X₀, fun X hX => ?_⟩
  have h_markov := hX₀ X hX
  have h_simplify : C * ↑K / (ε * ↑K) ^ 2 = C / (ε ^ 2 * ↑K) := by
    rw [mul_pow]; field_simp
  rw [h_simplify] at h_markov
  -- Show C/(ε²·K) ≤ δ: since K ≥ K₀ ≥ ⌈C/(ε²δ)⌉ + 1 > C/(ε²δ)
  have hε2δ_pos : (0 : ℝ) < ε ^ 2 * δ := mul_pos (sq_pos_of_pos hε) hδ
  have hK_large : (K : ℝ) ≥ C / (ε ^ 2 * δ) := by
    have : (K₀ : ℝ) ≥ Nat.ceil (C / (ε ^ 2 * δ)) + 1 := by exact_mod_cast Nat.le_max_right 1 _
    have : (K : ℝ) ≥ K₀ := by exact_mod_cast hK
    linarith [Nat.le_ceil (C / (ε ^ 2 * δ))]
  calc _ ≤ C / (ε ^ 2 * ↑K) := h_markov
    _ ≤ δ := by
        rw [div_le_iff₀ (mul_pos (sq_pos_of_pos hε) hK_pos)]
        calc C ≤ ε ^ 2 * δ * (C / (ε ^ 2 * δ)) := by rw [mul_div_cancel₀ C hε2δ_pos.ne']
          _ ≤ ε ^ 2 * δ * ↑K := mul_le_mul_of_nonneg_left hK_large hε2δ_pos.le
          _ = δ * (ε ^ 2 * ↑K) := by ring

end CharConcentration

/-! ## From Concentration to Equidistribution -/

section ConcentrationToEqd

/-- If n satisfies ∀ K, |∑χ|² > (εK)², then in particular at step K₀. -/
private theorem forall_char_deviant_subset (q : Nat) (χ : Nat → ℂ) (ε : ℝ) (X K : Nat) :
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ L, genSeqCharEnergy n L q χ > (ε * L) ^ 2)) ⊆
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        genSeqCharEnergy n K q χ > (ε * K) ^ 2)) :=
  Finset.monotone_filter_right _ fun _ _ ⟨hsf, hL⟩ => ⟨hsf, hL K⟩

/-- **Concentration → Almost All Character Sum Cancellation.**

    If EnsembleCharSumConcentration holds, then for almost all squarefree n,
    the character sums satisfy |∑_{k<K} χ(genSeq n k)| = o(K).

    Proof strategy: for any target δ > 0, the concentration hypothesis with
    density parameter δ/2 gives K₀ and X₀ such that for K ≥ K₀ and X ≥ X₀,
    density of the K-specific deviant set ≤ δ/2. The "∀ K" set is a subset
    of the K₀-specific set (by `forall_char_deviant_subset`), so its density
    ≤ δ/2 < δ. Since this works for all δ > 0, we get Tendsto(nhds 0)
    via Metric.tendsto_atTop. -/
theorem char_concentration_implies_cancellation
    (hconc : EnsembleCharSumConcentration) :
    ∀ (q : Nat), Nat.Prime q →
    ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
    ∀ (ε : ℝ), 0 < ε →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              ∀ K, genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop (nhds 0) := by
  intro q hq χ hχ ε hε
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Get K₀ from concentration with density target δ/2
  obtain ⟨K₀, hK₀⟩ := hconc q hq χ hχ ε hε (δ / 2) (by linarith)
  -- For K = K₀, get X₀
  obtain ⟨X₀, hX₀⟩ := hK₀ K₀ le_rfl
  refine ⟨X₀, fun X hX => ?_⟩
  -- The density of the K₀-specific set is ≤ δ/2
  have h_K₀_bound := hX₀ X hX
  -- The "∀ K" set is a subset of the K₀-specific set
  have h_card := Finset.card_le_card (forall_char_deviant_subset q χ ε X K₀)
  -- So density of "∀ K" set ≤ density of K₀-specific set ≤ δ/2
  have h_density_bound : (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ K, genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card ≤ δ / 2 :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr h_card) (Nat.cast_nonneg _)).trans
      h_K₀_bound
  -- dist f(X) 0 = |f(X)| = f(X) (since f ≥ 0) ≤ δ/2 < δ
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  linarith

end ConcentrationToEqd

/-! ## Full Decorrelation Chain

The ensemble decorrelation framework provides the following chain:

```
CRT decorrelation (crt_multiplier_invariance, PROVED)
  + PE (from ANT via pe_of_equidist, PROVED)
  → StepDecorrelation (character values decorrelate across steps)
  → CharSumVarianceBound (E[|∑χ|²] ≤ CK, expand square)
  → EnsembleCharSumConcentration (Chebyshev inequality)
  → Almost all squarefree n: |∑χ| = o(K) (squeeze_zero, PROVED)
  → AlmostAllSquarefreeEqd (character → residue via orthogonality)
```

This parallels the reciprocal sum chain from ReciprocalSumDivergence.lean:

```
PE + CRT → FirstMomentStep (E[1/genSeq] → κ)
         → VarianceBound (Var[S_K] ≤ CK)
         → RecipSumConcentration (Chebyshev)
         → AlmostAllSquarefreeRSD (squeeze_zero, PROVED)
```

Both chains ultimately reduce to:
1. PE (provable from Dirichlet + sieve, proved in PopulationEquidistProof.lean)
2. CRT decorrelation (proved: `crt_multiplier_invariance`)
3. A variance/concentration hypothesis bridging population to individual
-/

end
