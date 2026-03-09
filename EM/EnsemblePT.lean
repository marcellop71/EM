import EM.EnsembleCRT
import EM.EnsembleDecorrelation
import EM.EnsembleEM
import EM.MasterReduction

/-!
# Ensemble Population Transfer: MC for Almost All Starting Points

This file proves the **Ensemble Population Transfer theorem**: under CRT
equidistribution hypotheses, Mullin's Conjecture holds for density-1
squarefree starting points. It ties together all the ensemble infrastructure
from `EnsembleCRT.lean`, `EnsembleDecorrelation.lean`, `PopulationTransferStrategy.lean`,
and the master reduction chain.

## Mathematical Overview

The ensemble population transfer strategy proceeds in five layers:

1. **CRT Equidistribution** (from EnsembleCRT.lean):
   SRE + CRTPropagationStep => AccumulatorEquidistPropagation => EnsembleMultiplierEquidist

2. **Decorrelation Bridge** (new open hypothesis):
   EnsembleMultiplierEquidist => StepDecorrelation

3. **Variance and Concentration** (from EnsembleDecorrelation.lean):
   StepDecorrelation => CharSumVarianceBound => EnsembleCharSumConcentration

4. **Character Cancellation** (proved in EnsembleDecorrelation.lean):
   EnsembleCharSumConcentration => almost all character sums cancel

5. **Assembly**: combining the above into a single master theorem.

## Main Results

### Open Hypotheses
* `EnsembleEquidistImpliesDecorrelation` -- EME => StepDecorrelation
* `JointAccumulatorEquidist'`            -- genuine joint equidist of accumulator
* `JointStepEquidist`                    -- genuine joint equidist of genSeq
* `MultCancelToWalkCancel` (in EnsembleDecorrelation.lean) -- walk cancellation (equiv. CCSB/CME)

### Proved Theorems
* `equidist_implies_char_mean_vanishing_proved` -- EME => ensemble char means vanish (PROVED)
* `full_crt_chain_implies_cancellation`  -- SRE+CRT+bridges => char sum cancellation (a.a.)
* `ensemble_crt_equidist_chain`          -- SRE+CRT+bridge => EME (composition)
* `ensemble_decorrelation_chain`         -- EME+decorr+var+conc => char cancellation
* `sd_implies_cancellation`              -- SD alone => char cancellation (PROVED, composes 3 reductions)
* `ensemble_pt_master`                   -- all 6 hypotheses => char cancellation for a.a.
* `ensemble_pt_master_simplified`        -- 4 hypotheses => char cancellation (var+conc inlined, PROVED)
* `ensemble_pt_standard_em`              -- all hypotheses + DSL => MC for standard EM
* `gen_hitting_implies_gen_mc_proved`    -- cofinal walk hitting => gen. MC (PROVED)
* `gen_captures_target`                  -- generalized capture lemma (PROVED)
* `jse_implies_nontrivial_cancellation`  -- JSE + PCB => nontrivial cancellation (PROVED)
* `weyl_hitting_bridge_proved`           -- WeylHittingBridge (PROVED)
* `per_chi_cancellation_bridge_proved`   -- PerChiCancellationBridge (PROVED)
* `cancel_weyl_implies_mc`              -- walk cancellation => MC for n=2 (PROVED)
* `jse_transfer_implies_mc`             -- JSE + MultCancelToWalkCancel => MC (PROVED)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Section 1: Bridge from CRT Equidistribution to Decorrelation -/

section EquidistToDecorrelation

/-- **Ensemble multiplier equidistribution implies step decorrelation.**
    If genSeq n k equidistributes mod q for each fixed k (when averaged over
    squarefree starting points n), and the pair (genSeq n j, genSeq n k) is
    approximately independent via CRT propagation across the intervening steps,
    then the character values at different steps are decorrelated.

    The structural basis:
    1. EME gives equidistribution of each genSeq n k mod q individually.
    2. CRT independence (`crt_multiplier_invariance`, PROVED) means genSeq n k
       depends on genProd n k only through its non-mod-q coordinates.
    3. Between steps j and k, each "+1" shift decorrelates the mod-q information.
    4. The joint distribution of (genSeq n j, genSeq n k) is thus approximately
       product, giving E[chi(m_j) * conj(chi(m_k))] ~ E[chi(m_j)] * E[conj(chi(m_k))] ~ 0.

    **Status**: open hypothesis (requires quantitative CRT independence bounds). -/
def EnsembleEquidistImpliesDecorrelation : Prop :=
  EnsembleMultiplierEquidist → StepDecorrelation

/-- **Step decorrelation implies a character sum variance bound.**
    Expanding |sum_{k<K} chi(m_k)|^2 = sum_{j,k} chi(m_j) * conj(chi(m_k)):
    - Diagonal (j = k): each |chi|^2 <= 1, contributes <= K.
    - Off-diagonal (j != k): controlled by StepDecorrelation, which says
      the ensemble average of each cross-term vanishes.
    - If correlations decay summably: total <= K + K * sum_{d>=1} eps(d) = O(K).

    **Status**: open hypothesis (requires summable correlation decay from SD). -/
def DecorrelationImpliesVariance : Prop :=
  StepDecorrelation → ∃ C : ℝ, 0 < C ∧ CharSumVarianceBound C

/-- The partial character sum satisfies the recurrence:
    genSeqCharPartialSum n (K+1) q χ = genSeqCharPartialSum n K q χ + χ(genSeq n K % q). -/
private theorem genSeqCharPartialSum_succ (n K q : Nat) (χ : Nat → ℂ) :
    genSeqCharPartialSum n (K + 1) q χ =
    genSeqCharPartialSum n K q χ + χ (genSeq n K % q) := by
  simp [genSeqCharPartialSum, Finset.sum_range_succ]

/-- The character energy at K=0 is zero. -/
private theorem genSeqCharEnergy_zero (n q : Nat) (χ : Nat → ℂ) :
    genSeqCharEnergy n 0 q χ = 0 := by
  simp [genSeqCharEnergy, genSeqCharPartialSum]

/-- Energy recurrence: energy(K+1) = energy(K) + normSq(z_K) + 2·Re(S_K · conj(z_K)). -/
private theorem genSeqCharEnergy_succ (n K q : Nat) (χ : Nat → ℂ) :
    genSeqCharEnergy n (K + 1) q χ =
    genSeqCharEnergy n K q χ + Complex.normSq (χ (genSeq n K % q)) +
    2 * (genSeqCharPartialSum n K q χ * starRingEnd ℂ (χ (genSeq n K % q))).re := by
  unfold genSeqCharEnergy
  rw [genSeqCharPartialSum_succ]
  exact RCLike.normSq_add _ _

/-- The ensemble average of a pointwise-bounded function is bounded.
    If f(n) ≤ M for all squarefree n in [1,X], then ensembleAvg X f ≤ M (when M ≥ 0). -/
private theorem ensembleAvg_le_of_pointwise {X : Nat} {f : Nat → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hf : ∀ n ∈ (Finset.Icc 1 X).filter Squarefree, f n ≤ M) :
    ensembleAvg X f ≤ M := by
  unfold ensembleAvg sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree
  by_cases hS : S.card = 0
  · simp [hS, hM]
  · have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)
    rw [div_le_iff₀ hS_pos]
    calc ∑ n ∈ S, f n ≤ ∑ _ ∈ S, M := Finset.sum_le_sum hf
      _ = S.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = M * S.card := by ring

/-- Ensemble average of a sum equals the sum of ensemble averages. -/
private theorem ensembleAvg_sum {X : Nat} {s : Finset Nat} {f : Nat → Nat → ℝ} :
    ensembleAvg X (fun n => ∑ j ∈ s, f n j) = ∑ j ∈ s, ensembleAvg X (fun n => f n j) := by
  simp only [ensembleAvg, sqfreeCount, ← Finset.sum_div]
  congr 1; exact Finset.sum_comm

/-- Ensemble average distributes over addition. -/
private theorem ensembleAvg_add {X : Nat} {f g : Nat → ℝ} :
    ensembleAvg X (fun n => f n + g n) =
    ensembleAvg X f + ensembleAvg X g := by
  simp only [ensembleAvg, ← add_div]; congr 1; exact Finset.sum_add_distrib

/-- **Variance induction**: if normSq(χ a) ≤ 1 and each cross-term ensemble average
    tends to 0, then ensembleAvg X (genSeqCharEnergy · K q χ) ≤ 2·K eventually.

    This is the core induction used by both `decorrelation_implies_variance_proved`
    and `per_chi_cancellation_bridge_proved`. -/
private theorem variance_bound_induction (q : Nat) (χ : Nat → ℂ)
    (hχ : ∀ a, Complex.normSq (χ a) ≤ 1)
    (h_cross : ∀ j K : Nat, j < K →
      ∃ X₀ : Nat, ∀ X ≥ X₀,
        |ensembleAvg X (fun n =>
          (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n K % q))).re)| <
        1 / (2 * ((K : ℝ) + 1))) :
    ∀ K : Nat, ∃ X₀ : Nat, ∀ X ≥ X₀,
      ensembleAvg X (fun n => genSeqCharEnergy n K q χ) ≤ 2 * K := by
  intro K
  induction K with
  | zero =>
    refine ⟨0, fun X _ => ?_⟩
    simp only [Nat.cast_zero, mul_zero]
    exact ensembleAvg_le_of_pointwise (le_refl _)
      (fun n _ => le_of_eq (genSeqCharEnergy_zero n q χ))
  | succ K ih =>
    obtain ⟨X₀_K, hX₀_K⟩ := ih
    by_cases hK0 : K = 0
    · subst hK0
      refine ⟨0, fun X _ => ?_⟩
      show ensembleAvg X (fun n => genSeqCharEnergy n 1 q χ) ≤ 2 * (↑(1 : Nat) : ℝ)
      simp only [Nat.cast_one, mul_one]
      apply ensembleAvg_le_of_pointwise (by norm_num : (0:ℝ) ≤ 2)
      intro n _
      rw [genSeqCharEnergy_succ, genSeqCharEnergy_zero]
      simp only [genSeqCharPartialSum, Finset.sum_range_zero, zero_mul, Complex.zero_re,
        mul_zero, add_zero, zero_add]
      exact le_trans (hχ _) one_le_two
    · -- K ≥ 1. Collect cross-term witnesses.
      let X₀_fn : Nat → Nat := fun j =>
        if h : j < K then (h_cross j K h).choose else 0
      have hX₀_fn : ∀ j, j < K → ∀ X ≥ X₀_fn j,
          |ensembleAvg X (fun n =>
            (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n K % q))).re)| <
          1 / (2 * ((K : ℝ) + 1)) := by
        intro j hjK X hX
        have := (h_cross j K hjK).choose_spec X
        simp only [X₀_fn, dif_pos hjK] at hX
        exact this hX
      have h_all : ∃ X₀_cross : Nat, ∀ j ∈ Finset.range K, ∀ X ≥ X₀_cross,
          |ensembleAvg X (fun n =>
            (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n K % q))).re)| <
          1 / (2 * ((K : ℝ) + 1)) := by
        refine ⟨(Finset.range K).sup X₀_fn, fun j hj X hX => ?_⟩
        exact hX₀_fn j (Finset.mem_range.mp hj) X (le_trans (Finset.le_sup hj) hX)
      obtain ⟨X₀_cross, hX₀_cross⟩ := h_all
      refine ⟨Nat.max X₀_K X₀_cross, fun X hX => ?_⟩
      have hX_K : X ≥ X₀_K := le_trans (Nat.le_max_left _ _) hX
      have hX_cross : X ≥ X₀_cross := le_trans (Nat.le_max_right _ _) hX
      -- Decompose energy(K+1) = energy(K) + normSq(z_K) + 2·Re(S_K·conj(z_K))
      have h_avg_eq : ensembleAvg X (fun n => genSeqCharEnergy n (K + 1) q χ) =
          ensembleAvg X (fun n => genSeqCharEnergy n K q χ +
            Complex.normSq (χ (genSeq n K % q))) +
          ensembleAvg X (fun n =>
            2 * (genSeqCharPartialSum n K q χ *
              starRingEnd ℂ (χ (genSeq n K % q))).re) := by
        have : (fun n => genSeqCharEnergy n (K + 1) q χ) =
            (fun n => (genSeqCharEnergy n K q χ +
              Complex.normSq (χ (genSeq n K % q))) +
              2 * (genSeqCharPartialSum n K q χ *
                starRingEnd ℂ (χ (genSeq n K % q))).re) := by
          ext n; exact genSeqCharEnergy_succ n K q χ
        rw [this]; exact ensembleAvg_add
      rw [ensembleAvg_add] at h_avg_eq
      have h1 := hX₀_K X hX_K
      have h2 : ensembleAvg X (fun n => Complex.normSq (χ (genSeq n K % q))) ≤ 1 :=
        ensembleAvg_le_of_pointwise (by norm_num : (0:ℝ) ≤ 1) (fun n _ => hχ _)
      -- Cross-term bound: 2·|∑_j avg(cross(j,K))| < 1
      have h3 : ensembleAvg X (fun n =>
          2 * (genSeqCharPartialSum n K q χ *
            starRingEnd ℂ (χ (genSeq n K % q))).re) ≤ 1 := by
        have h_expand : (fun n => (genSeqCharPartialSum n K q χ *
            starRingEnd ℂ (χ (genSeq n K % q))).re) =
            (fun n => ∑ j ∈ Finset.range K,
              (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n K % q))).re) := by
          ext n; simp only [genSeqCharPartialSum, Finset.sum_mul, Complex.re_sum]
        have h_factor : ensembleAvg X (fun n =>
            2 * (genSeqCharPartialSum n K q χ *
              starRingEnd ℂ (χ (genSeq n K % q))).re) =
            2 * ensembleAvg X (fun n =>
              (genSeqCharPartialSum n K q χ *
                starRingEnd ℂ (χ (genSeq n K % q))).re) := by
          unfold ensembleAvg; rw [← mul_div_assoc]; congr 1; rw [Finset.mul_sum]
        rw [h_factor]
        have h_sum_form : ensembleAvg X (fun n =>
            (genSeqCharPartialSum n K q χ *
              starRingEnd ℂ (χ (genSeq n K % q))).re) =
            ∑ j ∈ Finset.range K, ensembleAvg X (fun n =>
              (χ (genSeq n j % q) *
                starRingEnd ℂ (χ (genSeq n K % q))).re) := by
          rw [show (fun n => (genSeqCharPartialSum n K q χ *
              starRingEnd ℂ (χ (genSeq n K % q))).re) =
              (fun n => ∑ j ∈ Finset.range K,
                (χ (genSeq n j % q) *
                  starRingEnd ℂ (χ (genSeq n K % q))).re) from h_expand]
          exact ensembleAvg_sum
        rw [h_sum_form]
        have h_each : ∀ j ∈ Finset.range K, |ensembleAvg X (fun n =>
            (χ (genSeq n j % q) *
              starRingEnd ℂ (χ (genSeq n K % q))).re)| <
            1 / (2 * ((K : ℝ) + 1)) :=
          fun j hj => hX₀_cross j hj X hX_cross
        have h_sum_bound : ∑ j ∈ Finset.range K, |ensembleAvg X (fun n =>
            (χ (genSeq n j % q) *
              starRingEnd ℂ (χ (genSeq n K % q))).re)| <
            K * (1 / (2 * ((K : ℝ) + 1))) :=
          calc ∑ j ∈ Finset.range K, |ensembleAvg X (fun n =>
                  (χ (genSeq n j % q) *
                    starRingEnd ℂ (χ (genSeq n K % q))).re)|
              < ∑ _ ∈ Finset.range K, (1 / (2 * ((K : ℝ) + 1))) :=
                Finset.sum_lt_sum_of_nonempty
                  (Finset.nonempty_range_iff.mpr (by omega)) h_each
            _ = K * (1 / (2 * ((K : ℝ) + 1))) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have h_frac : (K : ℝ) * (1 / (2 * ((K : ℝ) + 1))) ≤ 1 / 2 := by
          rw [mul_div, mul_one,
            div_le_div_iff₀ (mul_pos two_pos (Nat.cast_add_one_pos (n := K))) two_pos]
          nlinarith
        have h_cross_abs : |∑ j ∈ Finset.range K, ensembleAvg X (fun n =>
            (χ (genSeq n j % q) *
              starRingEnd ℂ (χ (genSeq n K % q))).re)| < 1 / 2 :=
          calc |∑ j ∈ Finset.range K, ensembleAvg X (fun n =>
                (χ (genSeq n j % q) *
                  starRingEnd ℂ (χ (genSeq n K % q))).re)|
              ≤ ∑ j ∈ Finset.range K, |ensembleAvg X (fun n =>
                  (χ (genSeq n j % q) *
                    starRingEnd ℂ (χ (genSeq n K % q))).re)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ < K * (1 / (2 * ((K : ℝ) + 1))) := h_sum_bound
            _ ≤ 1 / 2 := h_frac
        linarith [(abs_lt.mp h_cross_abs).1, (abs_lt.mp h_cross_abs).2]
      rw [h_avg_eq]; push_cast [Nat.cast_succ]; linarith

/-- The cross-term in StepDecorrelation matches the Re part of the energy recurrence.
    Specifically, for j < K:
    ensembleAvg X (fun n => (χ(genSeq n j % q) * conj(χ(genSeq n K % q))).re)
    is the quantity whose absolute value → 0 by StepDecorrelation. -/
private theorem cross_term_bound_from_sd
    (hsd : StepDecorrelation)
    (q : Nat) (hq : Nat.Prime q) (χ : Nat → ℂ) (j K : Nat) (hjK : j < K) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : Nat, ∀ X ≥ X₀,
      |ensembleAvg X (fun n =>
        (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n K % q))).re)| < ε := by
  have h := hsd q hq χ j K hjK
  rw [Metric.tendsto_atTop] at h
  obtain ⟨X₀, hX₀⟩ := h ε hε
  refine ⟨X₀, fun X hX => ?_⟩
  have := hX₀ X hX
  rwa [Real.dist_eq, sub_zero, abs_abs] at this

/-- **DecorrelationImpliesVariance is PROVED.**

    Choose C = 2. For fixed q, χ (bounded), and K, prove
    ∃ X₀, ∀ X ≥ X₀, ensembleAvg X (energy · K q χ) ≤ 2 * K
    by induction on K, using:
    - Base: energy(0) = 0 ≤ 0
    - Step: energy(K+1) = energy(K) + normSq(z_K) + 2·Re(S_K · conj(z_K))
      Diagonal: normSq(z_K) ≤ 1 (from |χ| ≤ 1)
      Off-diagonal: |E[Re(z_j · conj(z_K))]| → 0 by StepDecorrelation
      Combined: E[energy(K+1)] ≤ 2K + 1 + 2·K·(1/(2K)) = 2K + 2 = 2(K+1) -/
theorem decorrelation_implies_variance_proved : DecorrelationImpliesVariance := by
  intro hsd
  refine ⟨2, by norm_num, ?_⟩
  intro q hq χ hχ K
  -- Apply the extracted variance induction with cross-term bounds from SD
  exact variance_bound_induction q χ hχ (fun j K hjK => by
    have hε : (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) :=
      div_pos one_pos (mul_pos two_pos (Nat.cast_add_one_pos (n := K)))
    exact cross_term_bound_from_sd hsd q hq χ j K hjK _ hε) K

end EquidistToDecorrelation

/-! ## Section 1b: Joint Equidistribution and Step Decorrelation -/

section JointEquidist

/-- Count of squarefree n in [1,X] with genSeq n j in residue class a mod q
    AND genSeq n k in residue class b mod q simultaneously. -/
def sqfreeJointSeqCount (X j k q : Nat) (a b : ZMod q) : Nat :=
  ((Finset.Icc 1 X).filter (fun n =>
    Squarefree n ∧ (genSeq n j : ZMod q) = a ∧ (genSeq n k : ZMod q) = b)).card

/-- Joint density of squarefree n with genSeq n j ≡ a and genSeq n k ≡ b (mod q). -/
def sqfreeJointSeqDensity (X j k q : Nat) (a b : ZMod q) : ℝ :=
  (sqfreeJointSeqCount X j k q a b : ℝ) / (sqfreeCount X : ℝ)

/-- The joint count is bounded by the total squarefree count. -/
theorem sqfreeJointSeqCount_le_sqfreeCount (X j k q : Nat) (a b : ZMod q) :
    sqfreeJointSeqCount X j k q a b ≤ sqfreeCount X := by
  unfold sqfreeJointSeqCount sqfreeCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

/-- The joint density is non-negative. -/
theorem sqfreeJointSeqDensity_nonneg (X j k q : Nat) (a b : ZMod q) :
    0 ≤ sqfreeJointSeqDensity X j k q a b := by
  unfold sqfreeJointSeqDensity
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The joint density is at most 1. -/
theorem sqfreeJointSeqDensity_le_one (X j k q : Nat) (a b : ZMod q) :
    sqfreeJointSeqDensity X j k q a b ≤ 1 := by
  unfold sqfreeJointSeqDensity
  by_cases h : sqfreeCount X = 0
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sqfreeJointSeqCount_le_sqfreeCount X j k q a b))

/-- Count of squarefree n in [1,X] with genProd n j ≡ a AND genProd n k ≡ b (mod q)
    simultaneously. This is a GENUINE joint count at the same modulus q but different
    steps j, k. Unlike `sqfreeAccumDensity X j q a * sqfreeAccumDensity X k q b`
    (a product of marginals), this captures the actual joint distribution. -/
def sqfreeJointAccumCountSame (X j k q : Nat) (a b : ZMod q) : Nat :=
  ((Finset.Icc 1 X).filter (fun n : Nat =>
    Squarefree n ∧ (genProd n j : ZMod q) = a ∧ (genProd n k : ZMod q) = b)).card

/-- Density of squarefree n in [1,X] with genProd n j ≡ a AND genProd n k ≡ b (mod q). -/
def sqfreeJointAccumDensitySame (X j k q : Nat) (a b : ZMod q) : ℝ :=
  (sqfreeJointAccumCountSame X j k q a b : ℝ) / (sqfreeCount X : ℝ)

/-- The joint accumulator count (same modulus) is bounded by the total squarefree count. -/
theorem sqfreeJointAccumCountSame_le_sqfreeCount (X j k q : Nat) (a b : ZMod q) :
    sqfreeJointAccumCountSame X j k q a b ≤ sqfreeCount X := by
  unfold sqfreeJointAccumCountSame sqfreeCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

/-- The joint accumulator density (same modulus) is non-negative. -/
theorem sqfreeJointAccumDensitySame_nonneg (X j k q : Nat) (a b : ZMod q) :
    0 ≤ sqfreeJointAccumDensitySame X j k q a b := by
  unfold sqfreeJointAccumDensitySame
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The joint accumulator density (same modulus) is at most 1. -/
theorem sqfreeJointAccumDensitySame_le_one (X j k q : Nat) (a b : ZMod q) :
    sqfreeJointAccumDensitySame X j k q a b ≤ 1 := by
  unfold sqfreeJointAccumDensitySame
  by_cases h : sqfreeCount X = 0
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sqfreeJointAccumCountSame_le_sqfreeCount X j k q a b))

/-- The joint accumulator count (same modulus) is bounded by the marginal accumulator count
    (projecting to the first step j). -/
theorem sqfreeJointAccumCountSame_le_accumCount_first (X j k q : Nat) (a b : ZMod q) :
    sqfreeJointAccumCountSame X j k q a b ≤ sqfreeAccumCount X j q a := by
  unfold sqfreeJointAccumCountSame sqfreeAccumCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.1⟩

/-- **Partition identity for joint accumulator count (same modulus)**: summing over all
    residue classes b at step k gives the marginal count at step j.
    Every squarefree n with genProd n j ≡ a (mod q) falls into exactly one
    residue class for genProd n k mod q. -/
theorem sqfreeJointAccumCountSame_sum_eq_first (X j k q : Nat) [NeZero q]
    (a : ZMod q) :
    ∑ b : ZMod q, sqfreeJointAccumCountSame X j k q a b =
      sqfreeAccumCount X j q a := by
  unfold sqfreeJointAccumCountSame sqfreeAccumCount
  have hterm : ∀ b : ZMod q,
      ((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ (genProd n j : ZMod q) = a ∧
        (genProd n k : ZMod q) = b)).card =
      (((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ (genProd n j : ZMod q) = a)).filter
        (fun n => (genProd n k : ZMod q) = b)).card := by
    intro b; congr 1; ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, and_assoc]
  simp_rw [hterm]
  rw [← Finset.card_biUnion]
  · congr 1; ext n
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · intro ⟨_, hn, _⟩; exact hn
    · intro hn; exact ⟨(genProd n k : ZMod q), hn, rfl⟩
  · intro b₁ _ b₂ _ hb
    simp only [Finset.disjoint_filter]
    intro n _ h1 h2
    exact hb (h1.symm.trans h2)

/-- **Joint Accumulator Equidistribution (marginal product version)**: for prime q and
    steps j < k, the product of marginal densities sqfreeAccumDensity X j q a *
    sqfreeAccumDensity X k q b tends to 1/(q-1)^2 as X → ∞.

    **WARNING**: This is trivially implied by AccumulatorEquidistPropagation (AEP) —
    it is just the product of two independent marginals, each tending to 1/(q-1).
    Use `JointAccumulatorEquidist'` for the genuine joint version that captures
    the actual joint distribution at the same modulus.

    **Status**: trivially implied by AEP (see `aep_implies_jae_marginal`). -/
def JointAccumulatorEquidist_marginal : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (j k : Nat), j < k →
  ∀ (a b : ZMod q), a ≠ 0 → b ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeAccumDensity X j q a * sqfreeAccumDensity X k q b)
      Filter.atTop
      (nhds (1 / (((q : ℝ) - 1) ^ 2)))

/-- AEP trivially implies the marginal product version of JAE.
    Each marginal density → 1/(q-1), so the product → 1/(q-1)^2. -/
theorem aep_implies_jae_marginal (haep : AccumulatorEquidistPropagation) :
    JointAccumulatorEquidist_marginal := by
  intro q hq j k _ a b ha hb
  have hj := haep q hq j a ha
  have hk := haep q hq k b hb
  have : Filter.Tendsto
      (fun X : Nat => sqfreeAccumDensity X j q a * sqfreeAccumDensity X k q b)
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1) * (1 / ((q : ℝ) - 1)))) :=
    Filter.Tendsto.mul hj hk
  rwa [show (1 : ℝ) / ((q : ℝ) - 1) * (1 / ((q : ℝ) - 1)) =
    1 / (((q : ℝ) - 1) ^ 2) from by rw [one_div_mul_one_div_rev, sq]] at this

/-- **Genuine Joint Accumulator Equidistribution**: for prime q and steps j < k,
    the JOINT density of (genProd n j mod q, genProd n k mod q) — counting
    squarefree n where BOTH conditions hold simultaneously — tends to 1/(q-1)^2.

    Unlike `JointAccumulatorEquidist_marginal`, this is NOT trivial from AEP.
    It requires genuine independence/decorrelation between the mod-q coordinates
    of the accumulator at different steps.

    The structural basis: CRT independence of the mod-q coordinates at different
    steps. Between steps j and k, the accumulator undergoes (k-j) multiplications
    by fresh primes (genSeq) and (k-j) "+1" shifts. Each shift decorrelates
    the mod-q information via CRT.

    **Status**: open hypothesis (requires genuine CRT decorrelation argument). -/
def JointAccumulatorEquidist' : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (j k : Nat), j < k →
  ∀ (a b : ZMod q), a ≠ 0 → b ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeJointAccumDensitySame X j k q a b)
      Filter.atTop
      (nhds (1 / (((q : ℝ) - 1) ^ 2)))

/-- **Joint Step Equidistribution**: for prime q and steps j < k, the pair
    (genSeq n j mod q, genSeq n k mod q) is jointly uniform over nonzero residues
    when averaged over squarefree n in [1,X].

    The density of squarefree n with genSeq n j ≡ a and genSeq n k ≡ b (mod q)
    tends to 1/(q-1)^2 as X → ∞, for each nonzero pair (a, b).

    This is the multiplier-level version of `JointAccumulatorEquidist'`: it
    asserts joint uniformity of the *output primes* rather than the accumulators.
    The reduction JAE' → JSE goes through population transfer (PE) at each step.

    **Status**: open hypothesis (follows from JAE' + PE bridge). -/
def JointStepEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (j k : Nat), j < k →
  ∀ (a b : ZMod q), a ≠ 0 → b ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeJointSeqDensity X j k q a b)
      Filter.atTop
      (nhds (1 / (((q : ℝ) - 1) ^ 2)))

/-- The cross-term ensemble average decomposes as a density-weighted sum
    over residue class pairs.

    ensembleAvg X (fun n => (chi(genSeq n j % q) * conj(chi(genSeq n k % q))).re)
    = sum_{a,b : ZMod q} density(a,b) * (chi(a.val) * conj(chi(b.val))).re

    This is the joint analogue of `ensembleCharMean_eq_density_sum`. -/
private theorem cross_term_density_decomp (X j k q : Nat) [NeZero q]
    (chi : Nat → ℂ) :
    ensembleAvg X (fun n =>
      (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re) =
    ∑ a : ZMod q, ∑ b : ZMod q,
      sqfreeJointSeqDensity X j k q a b *
        (chi a.val * starRingEnd ℂ (chi b.val)).re := by
  unfold ensembleAvg sqfreeCount sqfreeJointSeqDensity sqfreeJointSeqCount
  set S := (Finset.Icc 1 X).filter Squarefree
  -- Key: genSeq n j % q = (genSeq n j : ZMod q).val
  have hmod_val : ∀ (m : Nat), m % q = (m : ZMod q).val := by
    intro m; rw [← ZMod.val_natCast (n := q) m]
  -- Step 1: partition by first coordinate using sum_fiberwise
  have hstep1 : ∑ n ∈ S,
      (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re =
      ∑ a : ZMod q, ∑ n ∈ S.filter (fun n => (genSeq n j : ZMod q) = a),
        (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re := by
    exact (Finset.sum_fiberwise S (fun n => (genSeq n j : ZMod q)) _).symm
  -- Step 2: for each a-fiber, partition by second coordinate
  have hstep2 : ∀ a : ZMod q,
      ∑ n ∈ S.filter (fun n => (genSeq n j : ZMod q) = a),
        (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re =
      ∑ b : ZMod q, ∑ n ∈ (S.filter (fun n => (genSeq n j : ZMod q) = a)).filter
          (fun n => (genSeq n k : ZMod q) = b),
        (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re := by
    intro a
    exact (Finset.sum_fiberwise _ (fun n => (genSeq n k : ZMod q)) _).symm
  -- Step 3: on each (a,b)-fiber, the function is constant
  have hstep3 : ∀ (a b : ZMod q),
      ∑ n ∈ (S.filter (fun n => (genSeq n j : ZMod q) = a)).filter
          (fun n => (genSeq n k : ZMod q) = b),
        (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re =
      ((S.filter (fun n => (genSeq n j : ZMod q) = a)).filter
          (fun n => (genSeq n k : ZMod q) = b)).card *
        (chi a.val * starRingEnd ℂ (chi b.val)).re := by
    intro a b
    rw [Finset.sum_congr rfl, Finset.sum_const, nsmul_eq_mul]
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [show genSeq n j % q = a.val from by rw [hmod_val, hn.1.2],
        show genSeq n k % q = b.val from by rw [hmod_val, hn.2]]
  -- Step 4: the double filter card equals the joint count
  have hstep4 : ∀ (a b : ZMod q),
      ((S.filter (fun n => (genSeq n j : ZMod q) = a)).filter
          (fun n => (genSeq n k : ZMod q) = b)).card =
      ((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ (genSeq n j : ZMod q) = a ∧
          (genSeq n k : ZMod q) = b)).card := by
    intro a b; congr 1; ext n
    simp only [Finset.mem_filter, S, and_assoc]
  -- Assemble: both sides = (∑ n ∈ S, f(n)) / |S|.
  -- RHS after unfolding = ∑_a ∑_b (count_ab / |S|) * g(a,b)
  --   = ∑_a ∑_b (count_ab * g(a,b)) / |S|  (rearrange)
  --   = (∑_a ∑_b count_ab * g(a,b)) / |S|   (pull division out)
  -- LHS = (∑ n ∈ S, f(n)) / |S|
  -- Need: ∑ n ∈ S, f(n) = ∑_a ∑_b count_ab * g(a,b)
  -- This follows from steps 1-4.
  -- Strategy: show both sides equal after dividing by |S|
  -- by showing numerators are equal.
  suffices h : ∑ n ∈ S,
      (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re =
      ∑ a : ZMod q, ∑ b : ZMod q,
        ↑((Finset.Icc 1 X |>.filter fun n =>
          Squarefree n ∧ (genSeq n j : ZMod q) = a ∧ (genSeq n k : ZMod q) = b).card) *
          (chi a.val * starRingEnd ℂ (chi b.val)).re by
    -- Pull out the division by |S| on both sides
    show (∑ n ∈ S,
        (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re) / ↑S.card =
      ∑ a : ZMod q, ∑ b : ZMod q,
        ↑((Finset.Icc 1 X |>.filter fun n =>
          Squarefree n ∧ (genSeq n j : ZMod q) = a ∧ (genSeq n k : ZMod q) = b).card) /
          ↑S.card *
          (chi a.val * starRingEnd ℂ (chi b.val)).re
    rw [h]
    -- Goal: (∑_a ∑_b count * g) / |S| = ∑_a ∑_b count / |S| * g
    -- Use Finset.sum_div twice to pull division into the sums
    rw [Finset.sum_div]
    congr 1; ext a
    rw [Finset.sum_div]
    congr 1; ext b
    ring
  -- Now prove the numerator identity
  rw [hstep1]; congr 1; ext a
  rw [hstep2 a]; congr 1; ext b
  rw [hstep3 a b, hstep4 a b]

/-- **Joint Step Equidistribution implies Step Decorrelation** for characters
    satisfying the nontriviality condition sum_a chi(a.val) = 0.

    Under JSE, for nontrivial chi (vanishing sum over residues mod q):
    E_n[chi(genSeq n j % q) * conj(chi(genSeq n k % q))] -> 0 as X -> infinity.

    The proof:
    1. Decompose the cross-term by residue class pairs (a, b) in (Z/qZ)^2.
    2. Under JSE, density(a,b) -> 1/(q-1)^2 for nonzero (a, b).
    3. The limit becomes (1/(q-1)^2) * sum_{a,b nonzero} (chi(a) * conj(chi(b))).re.
    4. Factor: sum_{a,b} f(a)*g(b) = (sum_a f(a))*(sum_b g(b)).
    5. For nontrivial chi: sum_a chi(a) = 0 implies the product = 0.
    6. The real part of 0 is 0. Hence the limit is 0.

    **Note**: This theorem requires nontriviality of chi (the sum-zero condition).
    For trivial characters, the cross-term does not vanish. This is appropriate
    because only nontrivial characters contribute to the equidistribution-to-MC
    reduction chain.

    **Status**: PROVED (from JSE + nontriviality). -/
theorem joint_step_equidist_implies_step_decorrelation
    (hjse : JointStepEquidist) :
    ∀ (q : Nat) (hq : Nat.Prime q),
    ∀ (chi : Nat → ℂ),
    -- Nontriviality: chi vanishes at 0 and sums to zero over ZMod q
    (chi 0 = 0) →
    (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, chi (ZMod.val a) = 0) →
    ∀ (j k : Nat), j < k →
      Filter.Tendsto
        (fun X : Nat =>
          |ensembleAvg X (fun n =>
              (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re)|)
        Filter.atTop (nhds 0) := by
  intro q hq chi hchi0 hchi_sum j k hjk
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- The target: |ensembleAvg X (cross-term)| -> 0
  -- Strategy: show the ensembleAvg itself -> 0, then |*| -> 0
  suffices h : Filter.Tendsto
      (fun X : Nat =>
        ensembleAvg X (fun n =>
          (chi (genSeq n j % q) * starRingEnd ℂ (chi (genSeq n k % q))).re))
      Filter.atTop (nhds 0) by
    have := h.abs
    simp only [abs_zero] at this
    exact this
  -- Rewrite using density decomposition
  simp_rw [cross_term_density_decomp _ j k q chi]
  -- The character value factor
  set f : ZMod q → ZMod q → ℝ :=
    fun a b => (chi a.val * starRingEnd ℂ (chi b.val)).re
  -- f(0, b) = 0 and f(a, 0) = 0 because chi(0) = 0
  have hf0a : ∀ b, f 0 b = 0 := by
    intro b; show (chi (0 : ZMod q).val * _).re = 0
    simp [ZMod.val_zero, hchi0]
  have hf0b : ∀ a, f a 0 = 0 := by
    intro a; show (chi a.val * starRingEnd ℂ (chi (0 : ZMod q).val)).re = 0
    simp [ZMod.val_zero, hchi0]
  -- Character orthogonality: sum_{a,b} f(a,b) = 0
  have h_sum_f_zero : ∑ a : ZMod q, ∑ b : ZMod q, f a b = 0 := by
    show ∑ a : ZMod q, ∑ b : ZMod q, (chi a.val * starRingEnd ℂ (chi b.val)).re = 0
    have hre : ∑ a : ZMod q, ∑ b : ZMod q, (chi a.val * starRingEnd ℂ (chi b.val)).re =
        (∑ a : ZMod q, ∑ b : ZMod q, chi a.val * starRingEnd ℂ (chi b.val)).re := by
      rw [Complex.re_sum]; congr 1; ext a; exact (Complex.re_sum _ _).symm
    rw [hre]
    have hfactor : ∑ a : ZMod q, ∑ b : ZMod q, chi a.val * starRingEnd ℂ (chi b.val) =
        (∑ a : ZMod q, chi a.val) * starRingEnd ℂ (∑ b : ZMod q, chi b.val) := by
      rw [map_sum, Finset.sum_mul]
      congr 1; ext a; rw [Finset.mul_sum]
    rw [hfactor, hchi_sum, zero_mul, Complex.zero_re]
  -- Each term density(a,b) * f(a,b) has a limit
  have h_term_tendsto : ∀ a : ZMod q, ∀ b : ZMod q,
      Filter.Tendsto
        (fun X => sqfreeJointSeqDensity X j k q a b * f a b)
        Filter.atTop
        (nhds (if a ≠ 0 ∧ b ≠ 0 then (1 / ((q : ℝ) - 1) ^ 2) * f a b else 0)) := by
    intro a b
    by_cases ha : a = 0
    · subst ha
      have hfab : f 0 b = 0 := hf0a b
      have hcond : ¬((0 : ZMod q) ≠ 0 ∧ b ≠ 0) := by tauto
      simp only [hfab, mul_zero, if_neg hcond]
      exact tendsto_const_nhds
    · by_cases hb : b = 0
      · subst hb
        have hfab : f a 0 = 0 := hf0b a
        have hcond : ¬(a ≠ 0 ∧ (0 : ZMod q) ≠ 0) := by tauto
        simp only [hfab, mul_zero, if_neg hcond]
        exact tendsto_const_nhds
      · rw [if_pos ⟨ha, hb⟩]
        exact (hjse q hq j k hjk a b ha hb).mul_const _
  -- The sum of limits equals 0
  have h_limit_sum :
      ∑ a : ZMod q, ∑ b : ZMod q,
        (if a ≠ 0 ∧ b ≠ 0 then (1 / ((q : ℝ) - 1) ^ 2) * f a b else 0) = 0 := by
    -- Replace each if-then-else with the unconditional product
    have h_ite_f : ∀ a b : ZMod q,
        (if a ≠ 0 ∧ b ≠ 0 then (1 / ((q : ℝ) - 1) ^ 2) * f a b else 0) =
        (1 / ((q : ℝ) - 1) ^ 2) * f a b := by
      intro a b
      by_cases ha : a = 0
      · subst ha; rw [if_neg (by simp : ¬((0 : ZMod q) ≠ 0 ∧ b ≠ 0)), hf0a b, mul_zero]
      · by_cases hb : b = 0
        · subst hb; rw [if_neg (by simp : ¬(a ≠ 0 ∧ (0 : ZMod q) ≠ 0)), hf0b a, mul_zero]
        · rw [if_pos ⟨ha, hb⟩]
    calc ∑ a : ZMod q, ∑ b : ZMod q,
            (if a ≠ 0 ∧ b ≠ 0 then (1 / ((q : ℝ) - 1) ^ 2) * f a b else 0)
        = ∑ a : ZMod q, ∑ b : ZMod q, (1 / ((q : ℝ) - 1) ^ 2) * f a b := by
            congr 1; ext a; congr 1; ext b; exact h_ite_f a b
      _ = ∑ a : ZMod q, (1 / ((q : ℝ) - 1) ^ 2) * ∑ b : ZMod q, f a b := by
            congr 1; ext a; rw [Finset.mul_sum]
      _ = (1 / ((q : ℝ) - 1) ^ 2) * ∑ a : ZMod q, ∑ b : ZMod q, f a b := by
            rw [Finset.mul_sum]
      _ = (1 / ((q : ℝ) - 1) ^ 2) * 0 := by rw [h_sum_f_zero]
      _ = 0 := mul_zero _
  -- Tendsto of finite sum
  have h_sum_tendsto : Filter.Tendsto
      (fun X => ∑ a : ZMod q, ∑ b : ZMod q,
        sqfreeJointSeqDensity X j k q a b * f a b)
      Filter.atTop
      (nhds (∑ a : ZMod q, ∑ b : ZMod q,
        (if a ≠ 0 ∧ b ≠ 0 then (1 / ((q : ℝ) - 1) ^ 2) * f a b else 0))) := by
    apply tendsto_finset_sum
    intro a _
    apply tendsto_finset_sum
    intro b _
    exact h_term_tendsto a b
  rw [h_limit_sum] at h_sum_tendsto
  exact h_sum_tendsto

end JointEquidist

/-! ## Section 2: Ensemble Character Mean Vanishing from Equidistribution -/

section CharMeanVanishing

/-- **Equidistribution implies ensemble character means are small** for
    nontrivial characters.

    If genSeq n k equidistributes mod q (density 1/(q-1) for each nonzero residue),
    then for any chi : ZMod q -> C satisfying chi(0) = 0 and ∑ a, chi(a) = 0
    (nontrivial character conditions), the density decomposition
    `ensembleCharMean_eq_density_sum` gives:

    E_n[chi(genSeq n k)] = ∑_a density(a) * chi(a) -> (1/(q-1)) * ∑_{a≠0} chi(a) = 0.

    This is a direct consequence of `EnsembleMultEquidistImpliesCharMeanZero`
    (PROVED in EnsembleCRT.lean). The statement is identical. -/
def EquidistImpliesCharMeanVanishing : Prop :=
  EnsembleMultiplierEquidist →
    ∀ (q : Nat) (hq : Nat.Prime q), ∀ (k : Nat),
    ∀ (chi : ZMod q → ℂ),
      chi (0 : ZMod q) = 0 →
      (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, chi a = 0) →
      Filter.Tendsto
        (fun X : Nat => ‖ensembleCharMean X k q chi‖)
        Filter.atTop
        (nhds 0)

/-- `EquidistImpliesCharMeanVanishing` is identical to
    `EnsembleMultEquidistImpliesCharMeanZero` and therefore PROVED. -/
theorem equidist_implies_char_mean_vanishing_proved :
    EquidistImpliesCharMeanVanishing :=
  ensemble_mult_equidist_implies_char_mean_zero

end CharMeanVanishing

/-! ## Section 3: The CRT-to-Cancellation Chain -/

section CRTToCancellation

/-- **The full CRT equidistribution chain**: SRE + CRTPropagationStep + bridge
    gives EnsembleMultiplierEquidist. This is a re-export of
    `sre_crt_bridge_implies_mult_equidist` for convenient reference. -/
theorem ensemble_crt_equidist_chain
    (hsre : SquarefreeResidueEquidist)
    (hcrt : CRTPropagationStep)
    (hbridge : AccumEquidistImpliesMultEquidist) :
    EnsembleMultiplierEquidist :=
  sre_crt_bridge_implies_mult_equidist hsre hcrt hbridge

/-- **The decorrelation chain**: EME + decorrelation bridge + variance bridge
    + concentration bridge gives character sum cancellation for almost all
    squarefree starting points.

    Chain:
    EME -> StepDecorrelation (by decorrelation bridge)
    -> CharSumVarianceBound C (by variance bridge)
    -> EnsembleCharSumConcentration (by concentration bridge)
    -> almost all char sums cancel (PROVED: char_concentration_implies_cancellation) -/
theorem ensemble_decorrelation_chain
    (heme : EnsembleMultiplierEquidist)
    (hdecorr : EnsembleEquidistImpliesDecorrelation)
    (hvar : DecorrelationImpliesVariance)
    (hconc : CharVarianceImpliesConcentration) :
    ∀ (q : Nat), Nat.Prime q →
    ∀ (chi : Nat → ℂ), (∀ a, Complex.normSq (chi a) ≤ 1) →
    ∀ (eps : ℝ), 0 < eps →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              ∀ K, genSeqCharEnergy n K q chi > (eps * K) ^ 2)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop (nhds 0) := by
  -- Step 1: EME -> StepDecorrelation
  have hsd : StepDecorrelation := hdecorr heme
  -- Step 2: StepDecorrelation -> CharSumVarianceBound C
  obtain ⟨C, hCpos, hvb⟩ := hvar hsd
  -- Step 3: CharSumVarianceBound C -> EnsembleCharSumConcentration
  have hconcentration : EnsembleCharSumConcentration := hconc C hCpos hvb
  -- Step 4: Concentration -> cancellation (PROVED)
  exact char_concentration_implies_cancellation hconcentration

end CRTToCancellation

/-! ## Section 3b: SD Alone Implies Cancellation -/

section SDToCancellation

/-- **StepDecorrelation alone implies character sum cancellation.**

    This theorem composes the three proved reductions in the concentration chain:
    1. `decorrelation_implies_variance_proved`: SD → ∃ C, CharSumVarianceBound C
    2. `char_variance_implies_concentration_proved`: CharSumVarianceBound C → EnsembleCharSumConcentration
    3. `char_concentration_implies_cancellation`: EnsembleCharSumConcentration → cancellation

    **StepDecorrelation is the SOLE remaining gap in the concentration chain.**
    Once SD is proved, the entire chain from decorrelation to almost-all
    character sum cancellation is complete with zero open hypotheses. -/
theorem sd_implies_cancellation (hsd : StepDecorrelation) :
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
  -- Step 1: SD → ∃ C, CharSumVarianceBound C
  obtain ⟨C, hCpos, hvb⟩ := decorrelation_implies_variance_proved hsd
  -- Step 2: CharSumVarianceBound C → EnsembleCharSumConcentration
  have hconc := char_variance_implies_concentration_proved C hCpos hvb
  -- Step 3: EnsembleCharSumConcentration → cancellation (PROVED)
  exact char_concentration_implies_cancellation hconc

/-- **Simplified Ensemble PT Master Theorem (4 hypotheses).**

    This is `ensemble_pt_master` with the two proved reductions
    (`DecorrelationImpliesVariance` and `CharVarianceImpliesConcentration`)
    inlined. Only 4 open hypotheses remain:
    1. `SquarefreeResidueEquidist` — standard ANT
    2. `CRTPropagationStep` — CRT independence
    3. `AccumEquidistImpliesMultEquidist` — population transfer bridge
    4. `EnsembleEquidistImpliesDecorrelation` — EME → SD bridge

    The chain: SRE + CRT + AccumBridge → EME → (DecorrBridge) → SD
    → (PROVED: variance) → (PROVED: concentration) → cancellation. -/
theorem ensemble_pt_master_simplified
    (hsre : SquarefreeResidueEquidist)
    (hcrt : CRTPropagationStep)
    (hbridge : AccumEquidistImpliesMultEquidist)
    (hdecorr : EnsembleEquidistImpliesDecorrelation) :
    ∀ (q : Nat), Nat.Prime q →
    ∀ (chi : Nat → ℂ), (∀ a, Complex.normSq (chi a) ≤ 1) →
    ∀ (eps : ℝ), 0 < eps →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              ∀ K, genSeqCharEnergy n K q chi > (eps * K) ^ 2)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop (nhds 0) :=
  -- Chain: SRE+CRT+bridge → EME → (decorr) → SD → (proved) → cancellation
  sd_implies_cancellation (hdecorr (ensemble_crt_equidist_chain hsre hcrt hbridge))

end SDToCancellation

/-! ## Section 4: Generalized MC from Walk Hitting -/

section GenMC

/-- **Generalized Mullin Conjecture for starting point n**: every prime
    appears in the generalized EM sequence from n. -/
def GenMullinConjecture (n : Nat) : Prop :=
  ∀ q : Nat, Nat.Prime q → ∃ k : Nat, genSeq n k = q

/-- **Walk hitting (cofinal) implies generalized MC.**
    If the generalized walk hits -1 mod q cofinally for every prime q
    (meaning for every N, there exists k >= N with q | genProd n k + 1),
    then every prime q appears in the generalized EM sequence from n.

    This is the generalized analogue of `conjectureA_implies_mullin`.
    The cofinal hitting hypothesis is necessary: a single hit might occur
    before all smaller primes have appeared, preventing the captures_target
    argument. With cofinal hitting, we can choose a hit past the "sieve gap"
    (after all smaller primes have appeared), making the argument work.

    **Status**: PROVED (gen_hitting_implies_gen_mc_proved). -/
def GenHittingImpliesGenMC : Prop :=
  ∀ (n : Nat), Squarefree n → 1 ≤ n →
    (∀ q : Nat, Nat.Prime q → ∀ N : Nat, ∃ k : Nat, N ≤ k ∧ genWalkZ n q k = -1) →
    GenMullinConjecture n

/-- Helper: if every prime below q appears in genSeq n, there exists a
    uniform bound N such that they all appear by step N.
    This is the generalized analogue of `exists_bound`. -/
private theorem gen_exists_bound (n : Nat) (q : Nat)
    (h : ∀ p, Nat.Prime p → p < q → ∃ k, genSeq n k = p) :
    ∃ N, ∀ p, Nat.Prime p → p < q → ∃ m, m < N ∧ genSeq n m = p := by
  induction q with
  | zero => exact ⟨0, fun p _ hp => absurd hp (by omega)⟩
  | succ q' ih =>
    have h' : ∀ p, Nat.Prime p → p < q' → ∃ k, genSeq n k = p :=
      fun p hp hpq => h p hp (by omega)
    obtain ⟨N', hN'⟩ := ih h'
    if hprime : Nat.Prime q' then
      obtain ⟨m, hm⟩ := h q' hprime (by omega)
      refine ⟨Nat.max N' (m + 1), fun p hp hpq => ?_⟩
      match Nat.lt_or_ge p q' with
      | .inl hlt =>
        obtain ⟨j, hj, hjseq⟩ := hN' p hp hlt
        exact ⟨j, lt_of_lt_of_le hj (Nat.le_max_left N' (m + 1)), hjseq⟩
      | .inr hge =>
        have : p = q' := by omega
        subst this
        exact ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right N' (m + 1)), hm⟩
    else
      refine ⟨N', fun p hp hpq => ?_⟩
      match Nat.lt_or_ge p q' with
      | .inl hlt => exact hN' p hp hlt
      | .inr hge =>
        exfalso
        have : p = q' := by omega
        subst this
        exact hprime hp

/-- **Generalized captures_target**: if q divides genProd n k + 1 and all
    primes p < q have appeared in genSeq n at steps < k, then genSeq n k = q.

    This parallels `captures_target` from MullinConjectures.lean. The proof:
    - genSeq n k = Nat.minFac(genProd n k + 1) <= q (minimality of minFac)
    - If genSeq n k < q, it appeared at some earlier step j < k (by hypothesis)
    - Then genSeq n j divides genProd n k (via genSeq_dvd_genProd_later)
    - But genSeq n k = genSeq n j also divides genProd n k + 1
    - A prime dividing both genProd n k and genProd n k + 1 divides 1: contradiction -/
theorem gen_captures_target {n : Nat} (hn : Squarefree n)
    {q : Nat} (hq : Nat.Prime q) {k : Nat}
    (hdvd : q ∣ genProd n k + 1)
    (hall : ∀ p, Nat.Prime p → p < q → ∃ j, j < k ∧ genSeq n j = p) :
    genSeq n k = q := by
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (Squarefree.ne_zero hn)
  -- genSeq n k = Nat.minFac(genProd n k + 1), so genSeq n k divides genProd n k + 1
  -- Upper bound: genSeq n k <= q
  have hpn : 2 ≤ genProd n k + 1 := by have := genProd_pos hn_pos k; omega
  have hle : genSeq n k ≤ q := by
    rw [genSeq_def]
    exact Nat.minFac_le_of_dvd hq.two_le hdvd
  -- genSeq n k is prime
  have hprime_s := genSeq_prime hn_pos k
  -- Lower bound: q <= genSeq n k
  have hge : q ≤ genSeq n k := by
    match Nat.lt_or_ge (genSeq n k) q with
    | .inr hge => exact hge
    | .inl hlt =>
      exfalso
      -- genSeq n k < q and is prime, so by hall it appeared at some step j < k
      obtain ⟨j, hjk, hseqj⟩ := hall (genSeq n k) hprime_s hlt
      -- genSeq n j = genSeq n k, so genSeq n j divides genProd n k
      have h_dvd_prod : genSeq n j ∣ genProd n k := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hjk)
        rw [hd]; exact genSeq_dvd_genProd_later n j d
      -- genSeq n k divides genProd n k (substituting genSeq n j = genSeq n k)
      rw [hseqj] at h_dvd_prod
      -- genSeq n k divides genProd n k + 1
      have h_dvd_succ := genSeq_dvd_genProd_succ n k
      -- A number >= 2 can't divide both a and a+1
      exact not_dvd_consec hprime_s.two_le h_dvd_prod h_dvd_succ
  omega

/-- **Cofinal walk hitting implies generalized MC.** PROVED.

    The proof follows the same pattern as `conjectureA_implies_mullin`:
    strong induction on q, collecting witnesses into a uniform bound,
    choosing a hit past the bound, and applying gen_captures_target. -/
theorem gen_hitting_implies_gen_mc_proved : GenHittingImpliesGenMC := by
  intro n hn hn_pos hhit
  -- Prove ∀ q, Nat.Prime q → ∃ k, genSeq n k = q by strong induction on q
  unfold GenMullinConjecture
  suffices ∀ B q, q ≤ B → Nat.Prime q → ∃ k, genSeq n k = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro B
  induction B with
  | zero => intro q hle hq; exact absurd hq.two_le (by omega)
  | succ B ih =>
    intro q hle hq
    match Nat.lt_or_ge q (B + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      -- q = B + 1. By IH, every prime p < q appears in genSeq n.
      have appears : ∀ p, Nat.Prime p → p < q → ∃ k, genSeq n k = p :=
        fun p hp hpq => ih p (by omega) hp
      -- Collect witnesses into a uniform bound N
      obtain ⟨N, hN⟩ := gen_exists_bound n q appears
      -- By cofinal hitting, get k >= N with q | genProd n k + 1
      obtain ⟨k, hk_ge, hhit_k⟩ := hhit q hq N
      rw [genWalkZ_eq_neg_one_iff] at hhit_k
      -- All primes < q appeared at steps < k (since k >= N >= each witness)
      have hall : ∀ p, Nat.Prime p → p < q → ∃ j, j < k ∧ genSeq n j = p := by
        intro p hp hpq
        obtain ⟨m, hm, hseqm⟩ := hN p hp hpq
        exact ⟨m, by omega, hseqm⟩
      -- gen_captures_target: genSeq n k = q. Done!
      exact ⟨k, gen_captures_target hn hq hhit_k hall⟩

/-- **Standard EM is a special case of generalized EM.**
    GenMullinConjecture 2 is equivalent to MullinConjecture
    (modulo the index shift genSeq 2 k = seq (k+1)). -/
theorem gen_mc_two_implies_mc
    (h : GenMullinConjecture 2) : MullinConjecture := by
  intro q hq
  obtain ⟨k, hk⟩ := h q (IsPrime.toNatPrime hq)
  exact ⟨k + 1, by rwa [← genSeq_two_eq_seq_succ]⟩

end GenMC

/-! ## Section 4b: JSE → GenMC Master Chain

The full chain from JointStepEquidist to GenMullinConjecture requires two bridges:

1. **Per-chi cancellation bridge**: JSE gives per-chi decorrelation for nontrivial
   characters (PROVED: `joint_step_equidist_implies_step_decorrelation`). The
   existing `sd_implies_cancellation` works with *universal* StepDecorrelation
   (quantified over ALL chi, including trivial), but JSE only gives decorrelation
   for nontrivial chi. A per-chi version of the variance-concentration-cancellation
   chain is needed. This is mathematically straightforward (identical proofs
   restricted to one chi) and captured by `PerChiCancellationBridge` (PROVED).

2. **Weyl hitting bridge**: Character cancellation for all nontrivial chi implies
   equidistribution of the walk (Weyl criterion), hence cofinal hitting of -1.
   This is captured by `WeylHittingBridge`.

Together: JSE + PerChiCancellationBridge (PROVED) + WeylHittingBridge → GenMC for all
squarefree n ≥ 1, completing the ensemble chain.
-/

section JSEToGenMC

/-- **Per-chi cancellation bridge**: per-chi step decorrelation implies
    per-chi character sum cancellation.

    This captures the mathematical content that the variance-concentration-cancellation
    chain (`decorrelation_implies_variance_proved`, `char_variance_implies_concentration_proved`,
    `char_concentration_implies_cancellation`) works per-chi, not just for universal SD.

    The proof is identical to the existing chain but with the SD hypothesis
    restricted to a single character χ. Specifically:
    - Per-chi SD → per-chi variance bound (C=2, by the same induction on K)
    - Per-chi variance → per-chi concentration (same Markov argument)
    - Per-chi concentration → per-chi cancellation (same squeeze argument)

    **Status**: PROVED (`per_chi_cancellation_bridge_proved`). -/
def PerChiCancellationBridge : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
  -- Per-chi decorrelation hypothesis (not universal SD)
  (∀ j k : Nat, j < k →
    Filter.Tendsto
      (fun X : Nat =>
        |ensembleAvg X (fun n =>
            (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n k % q))).re)|)
      Filter.atTop (nhds 0)) →
  -- Conclusion: per-chi cancellation
  ∀ (ε : ℝ), 0 < ε →
    Filter.Tendsto
      (fun X : Nat =>
        (((Finset.Icc 1 X).filter
          (fun n => Squarefree n ∧
            ∀ K, genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card : ℝ) /
        ((Finset.Icc 1 X).filter Squarefree).card)
      Filter.atTop (nhds 0)

/-- **PerChiCancellationBridge is PROVED.**

    The proof inlines the three-step chain (variance → concentration → cancellation)
    with the character χ fixed throughout. Each step is identical to its universal
    counterpart (`decorrelation_implies_variance_proved`,
    `char_variance_implies_concentration_proved`,
    `char_concentration_implies_cancellation`) but uses the per-chi decorrelation
    hypothesis instead of universal `StepDecorrelation`.

    **Step 1** (per-chi variance, C=2): By induction on K. Base: energy(0)=0≤0.
    Step: energy(K+1) = energy(K) + normSq(z_K) + 2·Re(S_K·conj(z_K)).
    The diagonal contributes ≤1. The cross-term is a sum of K terms, each
    with ensemble average → 0 by per-chi decorrelation. Choose X₀ so each
    cross-term average < 1/(2(K+1)), giving total cross ≤ 1.
    So E[energy(K+1)] ≤ 2K + 1 + 1 = 2(K+1).

    **Step 2** (per-chi concentration): Markov/Chebyshev. The variance bound
    gives density ≤ 2K/(εK)² = 2/(ε²K). Choose K₀ ≥ ⌈2/(ε²δ)⌉+1.

    **Step 3** (per-chi cancellation): The "∀ K" deviant set is a subset of
    the K₀-specific deviant set, so its density → 0 via Metric.tendsto_atTop. -/
theorem per_chi_cancellation_bridge_proved : PerChiCancellationBridge := by
  intro q hq χ hχ h_decorr ε hε
  -- ===== Step 1: Per-chi variance bound with C=2 (via extracted helper) =====
  have h_variance : ∀ K : Nat, ∃ X₀ : Nat, ∀ X ≥ X₀,
      ensembleAvg X (fun n => genSeqCharEnergy n K q χ) ≤ 2 * K :=
    variance_bound_induction q χ hχ (fun j K hjK => by
      have hε_cross : (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) :=
        div_pos one_pos (mul_pos two_pos (Nat.cast_add_one_pos (n := K)))
      have h := h_decorr j K hjK
      rw [Metric.tendsto_atTop] at h
      obtain ⟨X₀, hX₀⟩ := h _ hε_cross
      refine ⟨X₀, fun X hX => ?_⟩
      have := hX₀ X hX
      rwa [Real.dist_eq, sub_zero, abs_abs] at this)
  -- ===== Step 2: Per-chi concentration =====
  -- For any δ > 0, ∃ K₀, ∀ K ≥ K₀, ∃ X₀, ∀ X ≥ X₀, density ≤ δ
  have h_concentration : ∀ (δ : ℝ), 0 < δ →
      ∃ K₀ : Nat, ∀ K ≥ K₀, ∃ X₀ : Nat, ∀ X ≥ X₀,
        (((Finset.Icc 1 X).filter
          (fun n => Squarefree n ∧
            genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
        ((Finset.Icc 1 X).filter Squarefree).card ≤ δ := by
    intro δ hδ
    -- Markov: density ≤ 2K/(εK)² = 2/(ε²K). Need K ≥ 2/(ε²δ).
    set K₀ := Nat.max 1 (Nat.ceil (2 / (ε ^ 2 * δ)) + 1)
    refine ⟨K₀, fun K hK => ?_⟩
    have hK_ge_one : K ≥ 1 := le_trans (Nat.le_max_left 1 _) hK
    have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
    obtain ⟨X₀, hX₀⟩ := h_variance K
    refine ⟨X₀, fun X hX => ?_⟩
    have hεK_sq_pos : (0 : ℝ) < (ε * ↑K) ^ 2 := sq_pos_of_pos (mul_pos hε hK_pos)
    -- Apply Markov inequality
    have h_markov : (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧
          genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card ≤
      2 * ↑K / (ε * ↑K) ^ 2 := by
      exact finset_markov_density
        (fun n hn => genSeqCharEnergy_nonneg _ _ _ _)
        hεK_sq_pos
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hK_pos))
        (hX₀ X hX)
        _
        (fun n hn => by
          simp only [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1, hn.2.1⟩)
        (fun n hn => by
          simp only [Finset.mem_filter] at hn
          exact le_of_lt hn.2.2)
    -- Simplify: 2K/(εK)² = 2/(ε²K)
    have h_simplify : 2 * ↑K / (ε * ↑K) ^ 2 = 2 / (ε ^ 2 * ↑K) := by
      rw [mul_pow]; field_simp
    rw [h_simplify] at h_markov
    -- Show 2/(ε²K) ≤ δ
    have h_bound : 2 / (ε ^ 2 * ↑K) ≤ δ := by
      rw [div_le_iff₀ (mul_pos (sq_pos_of_pos hε) hK_pos)]
      have hε2δ_pos : (0 : ℝ) < ε ^ 2 * δ := mul_pos (sq_pos_of_pos hε) hδ
      have hK_large : (K : ℝ) ≥ 2 / (ε ^ 2 * δ) := by
        have hK₀_large : (K₀ : ℝ) ≥ Nat.ceil (2 / (ε ^ 2 * δ)) + 1 := by
          exact_mod_cast Nat.le_max_right 1 _
        have : (K : ℝ) ≥ K₀ := by exact_mod_cast hK
        have hceil : (Nat.ceil (2 / (ε ^ 2 * δ)) : ℝ) ≥ 2 / (ε ^ 2 * δ) := Nat.le_ceil _
        linarith
      have hkey : ε ^ 2 * δ * ↑K ≥ 2 := by
        calc ε ^ 2 * δ * ↑K
            ≥ ε ^ 2 * δ * (2 / (ε ^ 2 * δ)) :=
              mul_le_mul_of_nonneg_left hK_large (le_of_lt hε2δ_pos)
          _ = 2 := by field_simp
      linarith
    linarith
  -- ===== Step 3: Per-chi cancellation (squeeze to zero) =====
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Get K₀ from concentration with density target δ/2
  obtain ⟨K₀, hK₀⟩ := h_concentration (δ / 2) (by linarith)
  -- For K = K₀, get X₀
  obtain ⟨X₀, hX₀⟩ := hK₀ K₀ (le_refl _)
  refine ⟨X₀, fun X hX => ?_⟩
  -- The density of the K₀-specific set is ≤ δ/2
  have h_K₀_bound := hX₀ X hX
  -- The "∀ K" set is a subset of the K₀-specific set
  have h_card : ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ K, genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card ≤
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        genSeqCharEnergy n K₀ q χ > (ε * K₀) ^ 2)).card := by
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2 K₀⟩
  -- So density of "∀ K" set ≤ density of K₀-specific set ≤ δ/2
  have h_density_bound : (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ K, genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card ≤ δ / 2 :=
    le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h_card) (Nat.cast_nonneg _))
      h_K₀_bound
  -- dist f(X) 0 = |f(X)| = f(X) (since f ≥ 0) ≤ δ/2 < δ
  rw [Real.dist_eq]
  have h_nn : 0 ≤ (((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ K, genSeqCharEnergy n K q χ > (ε * ↑K) ^ 2)).card : ℝ) /
    ((Finset.Icc 1 X).filter Squarefree).card :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Nontrivial character cancellation from JSE + PerChiCancellationBridge.**

    Under JSE, every nontrivial character χ mod q (chi(0)=0, ∑chi=0, normSq≤1)
    has its character sums cancel for almost all squarefree starting points.

    This composes:
    1. JSE → per-chi decorrelation (joint_step_equidist_implies_step_decorrelation, PROVED)
    2. Per-chi decorrelation → per-chi cancellation (PerChiCancellationBridge, PROVED)

    **Status**: PROVED (from JSE + PerChiCancellationBridge, both proved). -/
theorem jse_implies_nontrivial_cancellation
    (hjse : JointStepEquidist) (hbridge : PerChiCancellationBridge) :
    ∀ (q : Nat) (hq : Nat.Prime q),
    ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
    (χ 0 = 0) →
    (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, χ (ZMod.val a) = 0) →
    ∀ (ε : ℝ), 0 < ε →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              ∀ K, genSeqCharEnergy n K q χ > (ε * K) ^ 2)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop (nhds 0) := by
  intro q hq χ hχ_bound hχ0 hχ_sum ε hε
  -- Step 1: JSE → per-chi decorrelation for this nontrivial χ
  have h_decorr : ∀ j k : Nat, j < k →
      Filter.Tendsto
        (fun X : Nat =>
          |ensembleAvg X (fun n =>
              (χ (genSeq n j % q) * starRingEnd ℂ (χ (genSeq n k % q))).re)|)
        Filter.atTop (nhds 0) :=
    joint_step_equidist_implies_step_decorrelation hjse q hq χ hχ0 hχ_sum
  -- Step 2: per-chi decorrelation → per-chi cancellation (PerChiCancellationBridge)
  exact hbridge q hq χ hχ_bound h_decorr ε hε

/-- **Weyl hitting bridge**: walk character cancellation (strong Weyl form)
    for primes not dividing the starting point implies either the prime
    appeared in the generalized sequence or the walk hits -1 cofinally.

    The mathematical content is the Weyl equidistribution criterion applied
    to the walk positions genProd n k mod q. The hypothesis uses genWalkCharEnergy
    (walk character energy) with the strong form: for all K >= K0, the energy
    is bounded by (eps*K)^2. The guard q does not divide n ensures the walk
    starts in (Z/qZ)x.

    **Status**: PROVED (weyl_hitting_bridge_proved). -/
def WeylHittingBridge : Prop :=
  ∀ (n : Nat), Squarefree n → 1 ≤ n →
  ∀ (q : Nat) (hq : Nat.Prime q),
  ¬ (q ∣ n) →
  (∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
    (χ 0 = 0) →
    (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, χ (ZMod.val a) = 0) →
    ∀ (ε : ℝ), 0 < ε →
      ∃ K₀ : Nat, ∀ K : Nat, K₀ ≤ K → genWalkCharEnergy n K q χ ≤ (ε * K) ^ 2) →
  (∃ j : Nat, genSeq n j = q) ∨
  (∀ N : Nat, ∃ k : Nat, N ≤ k ∧ genWalkZ n q k = -1)

/-- If q is prime, does not divide n, and never appears as genSeq n j,
    then q does not divide genProd n k for any k. -/
private theorem genProd_not_dvd_of_not_appeared {n : Nat} {q : Nat} (hq : Nat.Prime q)
    (hndvd : ¬ (q ∣ n)) (hnot : ∀ j, genSeq n j ≠ q) (k : Nat) :
    ¬ (q ∣ genProd n k) := by
  induction k with
  | zero => simpa [genProd]
  | succ k ih =>
    rw [genProd_succ]; intro hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h2
    · exact ih h1
    · have hn_pos : 1 ≤ n := by
        by_contra h; push_neg at h; interval_cases n; exact hndvd (dvd_zero q)
      rcases (genSeq_prime hn_pos k).eq_one_or_self_of_dvd q h2 with h | h
      · exact absurd h (by have := hq.one_lt; omega)
      · exact absurd h.symm (hnot k)

/-- If no hits at -1 occur at steps >= N0, hits in any range are bounded
    by hits in range N0. -/
private theorem hit_filter_bounded {n q N₀ : Nat}
    (hno : ∀ k, N₀ ≤ k → genProd n k % q ≠ q - 1) (K : Nat) :
    ((Finset.range K).filter (fun k => genProd n k % q = q - 1)).card ≤
    ((Finset.range N₀).filter (fun k => genProd n k % q = q - 1)).card := by
  apply Finset.card_le_card; intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨by_contra fun h => hno k (by push_neg at h; exact h) hk.2, hk.2⟩

/-- The Weyl test function: centered indicator of -1 among units mod q. -/
private noncomputable def weylTestFn (q : Nat) : Nat → ℂ := fun x =>
  if x % q = 0 then (0 : ℂ)
  else if x % q = q - 1 then (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ)
  else (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ)

private theorem weylTestFn_zero (q : Nat) : weylTestFn q 0 = 0 := by
  simp [weylTestFn]

private theorem weylTestFn_bound (q : Nat) (hq2 : 2 ≤ q) (a : Nat) :
    Complex.normSq (weylTestFn q a) ≤ 1 := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqr_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  simp only [weylTestFn]
  split_ifs with h0 h1
  · simp [Complex.normSq]
  · rw [show (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ) =
      Complex.ofReal (((q : ℝ) - 2) / ((q : ℝ) - 1)) from by push_cast; ring]
    rw [Complex.normSq_ofReal, div_mul_div_comm, div_le_one (by positivity)]
    exact mul_self_le_mul_self (by linarith) (by linarith)
  · rw [show (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ) =
      Complex.ofReal ((-1 : ℝ) / ((q : ℝ) - 1)) from by push_cast; ring]
    rw [Complex.normSq_ofReal, div_mul_div_comm, div_le_one (by positivity)]
    nlinarith

/-- The Weyl test function sums to zero over ZMod q.
    Sum = 0 (at val=0) + (q-2)/(q-1) (at val=q-1) + (q-2)*(-1/(q-1)) (rest) = 0. -/
private theorem weylTestFn_sum_zero (q : Nat) (hq : Nat.Prime q) :
    (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, weylTestFn q (ZMod.val a) = 0) := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hq2 := hq.two_le
  have hval_mod : ∀ a : ZMod q, ZMod.val a % q = ZMod.val a :=
    fun a => Nat.mod_eq_of_lt (ZMod.val_lt a)
  simp_rw [weylTestFn, hval_mod]
  -- Decompose: each summand = B·(if val≠0 then 1 else 0) + (A-B)·(if val=q-1 then 1 else 0)
  -- Sum = B·(q-1) + (A-B)·1 = A + (q-2)·B = 0.
  set A : ℂ := (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ) with hAdef
  set B : ℂ := (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ) with hBdef
  have hdecomp : ∀ a : ZMod q,
      (if ZMod.val a = 0 then (0 : ℂ) else if ZMod.val a = q - 1 then A else B) =
      B * (if ZMod.val a = 0 then 0 else 1) + (A - B) * (if ZMod.val a = q - 1 then 1 else 0) := by
    intro a; split_ifs with h0 h1
    · exfalso; omega
    · simp
    · ring
    · ring
  simp_rw [hdecomp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Need: B·card{val≠0} + (A-B)·card{val=q-1} = 0 where card{val≠0}=q-1, card{val=q-1}=1
  have hval_inj : Function.Injective (fun a : ZMod q => ZMod.val a) := ZMod.val_injective q
  have hcard_ne0 : ((Finset.univ.filter (fun a : ZMod q => ¬ZMod.val a = 0)).card : ℂ) =
      (q : ℂ) - 1 := by
    have htotal : Finset.card (Finset.univ : Finset (ZMod q)) = q := ZMod.card q
    have hone : (Finset.univ.filter (fun a : ZMod q => ZMod.val a = 0)).card = 1 := by
      have : Finset.univ.filter (fun a : ZMod q => ZMod.val a = 0) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => hval_inj (by simp [h]), fun h => by simp [h]⟩
      rw [this, Finset.card_singleton]
    have hnat := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun a : ZMod q => ZMod.val a = 0)
    rw [htotal, hone] at hnat
    rw [show (Finset.univ.filter (fun a : ZMod q => ¬ZMod.val a = 0)).card = q - 1 from by omega,
        Nat.cast_sub (by omega : 1 ≤ q)]; simp
  -- Second: card{a : ZMod q | val a = q-1}
  have hcard_qm1 : ((Finset.univ.filter (fun a : ZMod q => ZMod.val a = q - 1)).card : ℂ) = 1 := by
    have : Finset.univ.filter (fun a : ZMod q => ZMod.val a = q - 1) = {((q - 1 : Nat) : ZMod q)} := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; apply hval_inj; simp only; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [this, Finset.card_singleton]; simp
  rw [hcard_ne0, hcard_qm1]
  rw [hAdef, hBdef]; push_cast; field_simp; ring

/-- **WeylHittingBridge is true.** PROVED.

    Proof by contradiction using the Weyl test function. If q never appeared
    and the walk stops hitting -1, the hit count is bounded. The test function's
    partial sum grows as K/(q-1), giving energy ~ K^2/(q-1)^2 which contradicts
    the hypothesis for eps = 1/(2(q-1)). -/
theorem weyl_hitting_bridge_proved : WeylHittingBridge := by
  intro n hn hn_pos q hq hndvd hcancel
  by_cases happeared : ∃ j, genSeq n j = q
  · exact Or.inl happeared
  · push_neg at happeared; right
    have hndvd_prod := fun k => genProd_not_dvd_of_not_appeared hq hndvd happeared k
    have hwalk_nz : ∀ k, genProd n k % q ≠ 0 :=
      fun k h => hndvd_prod k (Nat.dvd_of_mod_eq_zero h)
    by_contra hf; push_neg at hf
    obtain ⟨N₀, hN₀⟩ := hf
    have hno : ∀ k, N₀ ≤ k → genProd n k % q ≠ q - 1 := by
      intro k hk h; apply hN₀ k hk; rw [genWalkZ_eq_neg_one_iff]
      have hq2 := hq.two_le
      rw [Nat.dvd_iff_mod_eq_zero]
      conv_lhs => rw [show genProd n k + 1 = genProd n k + 1 from rfl]
      rw [Nat.add_mod, h]
      have : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
      rw [this, Nat.sub_add_cancel (by omega : 1 ≤ q), Nat.mod_self]
    set C := ((Finset.range N₀).filter (fun k => genProd n k % q = q - 1)).card
    have hbd := hit_filter_bounded hno
    -- Apply hypothesis with Weyl test function
    set χ := weylTestFn q
    have hχ_bound := weylTestFn_bound q hq.two_le
    have hχ0 := weylTestFn_zero q
    have hχ_sum := weylTestFn_sum_zero q hq
    have hqr_pos : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
      linarith
    set ε := 1 / (2 * ((q : ℝ) - 1))
    have hε_pos : 0 < ε := div_pos one_pos (mul_pos two_pos hqr_pos)
    obtain ⟨K₀, hK₀⟩ := hcancel χ hχ_bound hχ0 hχ_sum ε hε_pos
    -- Choose K large enough
    set K := Nat.max K₀ (2 * C * q + 1)
    have hK_ge : K₀ ≤ K := Nat.le_max_left _ _
    have hK_big : 2 * C * q + 1 ≤ K := Nat.le_max_right _ _
    have hE := hK₀ K hK_ge
    -- Compute partial sum, show energy = (hitK - K/(q-1))², derive contradiction
    set hitK := ((Finset.range K).filter (fun k => genProd n k % q = q - 1)).card
    set A : ℂ := (((q : ℝ) - 2) / ((q : ℝ) - 1) : ℂ)
    set B : ℂ := (((-1 : ℝ) / ((q : ℝ) - 1)) : ℂ)
    -- Each summand: since walk is never 0 mod q, χ(genProd n k % q) is A or B
    have hterm : ∀ k, k ∈ Finset.range K →
        χ (genProd n k % q) = if genProd n k % q = q - 1 then A else B := by
      intro k _
      simp only [χ, weylTestFn]
      -- weylTestFn applies % q to its arg, giving (genProd n k % q) % q = genProd n k % q
      rw [Nat.mod_mod_of_dvd _ (dvd_refl q)]
      rw [if_neg (hwalk_nz k)]
    have hpartial : genWalkCharPartialSum n K q χ = ↑hitK * A + (↑K - ↑hitK) * B := by
      simp only [genWalkCharPartialSum]; rw [Finset.sum_congr rfl hterm]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      -- Goal: ↑hitK * A + ↑compl * B = ↑hitK * A + (↑K - ↑hitK) * B
      -- where compl = filter (¬P).card
      -- We need: ↑compl = ↑K - ↑hitK
      have hle : hitK ≤ K := by
        have := Finset.card_filter_le (Finset.range K) (fun k => genProd n k % q = q - 1)
        rw [Finset.card_range] at this; exact this
      have hcomp := Finset.card_filter_add_card_filter_not
        (s := Finset.range K) (fun k => genProd n k % q = q - 1)
      rw [Finset.card_range] at hcomp
      -- hcomp: hitK + compl = K, so compl = K - hitK
      set compl := ((Finset.range K).filter (fun k => ¬genProd n k % q = q - 1)).card
      have hcompl_eq : compl = K - hitK := by omega
      rw [hcompl_eq, Nat.cast_sub hle]
    -- A and B simplify: hitK*A + (K-hitK)*B = (hitK - K/(q-1))
    have hAB_val : ↑hitK * A + (↑K - ↑hitK) * B =
        (↑(hitK : ℕ) - ↑(K : ℕ) / ((q : ℝ) - 1) : ℝ) := by
      simp only [A, B]; push_cast
      have hqc : ((-1 : ℂ) + (q : ℂ)) ≠ 0 := by
        rw [show (-1 : ℂ) + (q : ℂ) = ((q : ℤ) - 1 : ℤ) from by push_cast; ring]
        exact_mod_cast (show (q : ℤ) - 1 ≠ 0 from by have := hq.two_le; omega)
      set r := ((-1 : ℂ) + (↑↑q : ℂ))⁻¹
      have hqr1 : ((-1 : ℂ) + ↑↑q) * r = 1 := mul_inv_cancel₀ hqc
      linear_combination ↑↑hitK * hqr1
    -- So energy = normSq of a real number
    have henergy_eq : genWalkCharEnergy n K q χ =
        ((hitK : ℝ) - (K : ℝ) / ((q : ℝ) - 1)) ^ 2 := by
      simp only [genWalkCharEnergy]; rw [hpartial, hAB_val]
      rw [show ((↑hitK - ↑K / ((q : ℝ) - 1) : ℝ) : ℂ) =
        Complex.ofReal (↑hitK - ↑K / ((q : ℝ) - 1)) from by push_cast; ring]
      rw [Complex.normSq_ofReal]; ring
    -- Step 2: Energy lower bound
    -- hitK ≤ C (bounded by early hits)
    have hhit_le : hitK ≤ C := hbd K
    -- Energy ≥ (K/(q-1) - C)^2 when K/(q-1) ≥ C
    have hKr : (K : ℝ) / ((q : ℝ) - 1) ≥ (C : ℝ) := by
      rw [ge_iff_le, le_div_iff₀ hqr_pos]
      have hq2 := hq.two_le
      have : (q : ℝ) - 1 ≤ (q : ℝ) := by linarith
      calc (C : ℝ) * ((q : ℝ) - 1) ≤ (C : ℝ) * (q : ℝ) := by
            apply mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ (2 * C * q : ℕ) := by
            push_cast
            have : (0 : ℝ) ≤ (C : ℝ) * (q : ℝ) := mul_nonneg (Nat.cast_nonneg' C) (Nat.cast_nonneg' q)
            linarith
        _ ≤ (2 * C * q + 1 : ℕ) := by push_cast; linarith
        _ ≤ K := by exact_mod_cast hK_big
    have henergy_lb : ((K : ℝ) / ((q : ℝ) - 1) - (C : ℝ)) ^ 2 ≤ genWalkCharEnergy n K q χ := by
      rw [henergy_eq]
      have hhitR : (hitK : ℝ) ≤ (C : ℝ) := by exact_mod_cast hhit_le
      -- (K/(q-1) - C)^2 ≤ (hitK - K/(q-1))^2
      -- = (K/(q-1) - hitK)^2 (squaring removes sign)
      rw [show ((hitK : ℝ) - (K : ℝ) / ((q : ℝ) - 1)) ^ 2 =
        ((K : ℝ) / ((q : ℝ) - 1) - (hitK : ℝ)) ^ 2 from by ring]
      apply sq_le_sq'
      · -- -(K/(q-1) - hitK) ≤ K/(q-1) - C, i.e., C ≤ 2K/(q-1) - hitK
        -- True since C ≤ K/(q-1) and hitK ≤ K/(q-1)
        linarith
      · -- K/(q-1) - C ≤ K/(q-1) - hitK, i.e., hitK ≤ C
        linarith
    -- Step 3: Energy upper bound from hypothesis
    -- energy ≤ (ε * K)^2 = (K / (2*(q-1)))^2
    have hε_val : ε = 1 / (2 * ((q : ℝ) - 1)) := rfl
    have henergy_ub : genWalkCharEnergy n K q χ ≤ ((K : ℝ) / (2 * ((q : ℝ) - 1))) ^ 2 := by
      calc genWalkCharEnergy n K q χ ≤ (ε * K) ^ 2 := hE
        _ = ((K : ℝ) / (2 * ((q : ℝ) - 1))) ^ 2 := by rw [hε_val]; ring
    -- Combined: (K/(q-1) - C)^2 ≤ (K/(2(q-1)))^2
    have hcombined : ((K : ℝ) / ((q : ℝ) - 1) - (C : ℝ)) ^ 2 ≤
        ((K : ℝ) / (2 * ((q : ℝ) - 1))) ^ 2 := le_trans henergy_lb henergy_ub
    -- Since both sides ≥ 0, take square root: lhs ≤ rhs
    have hrhs_nn : (0 : ℝ) ≤ (K : ℝ) / (2 * ((q : ℝ) - 1)) := by positivity
    have hsqrt := (abs_le_of_sq_le_sq' hcombined hrhs_nn).2
    -- K/(q-1) - C ≤ K/(2(q-1)), so K/(2(q-1)) ≤ C
    -- From hsqrt: K/(q-1) - C ≤ K/(2(q-1))
    -- Hence: K/(q-1) - K/(2(q-1)) ≤ C
    -- K/(q-1) - K/(2(q-1)) = K * (1/(q-1) - 1/(2(q-1))) = K * 1/(2(q-1)) = K/(2(q-1))
    have hdiff : (K : ℝ) / ((q : ℝ) - 1) - (K : ℝ) / (2 * ((q : ℝ) - 1)) =
        (K : ℝ) / (2 * ((q : ℝ) - 1)) := by
      field_simp; ring
    have hKC : (K : ℝ) / (2 * ((q : ℝ) - 1)) ≤ (C : ℝ) := by linarith
    -- K ≤ 2*C*(q-1)
    have hK_le : (K : ℝ) ≤ 2 * (C : ℝ) * ((q : ℝ) - 1) := by
      have h2qr := show (0 : ℝ) < 2 * ((q : ℝ) - 1) from by positivity
      calc (K : ℝ) = (K : ℝ) / (2 * ((q : ℝ) - 1)) * (2 * ((q : ℝ) - 1)) :=
            (div_mul_cancel₀ _ (ne_of_gt h2qr)).symm
        _ ≤ (C : ℝ) * (2 * ((q : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hKC (le_of_lt h2qr)
        _ = 2 * (C : ℝ) * ((q : ℝ) - 1) := by ring
    -- But K ≥ 2*C*q + 1 > 2*C*(q-1) (since C ≥ 0)
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    have hCnn : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg'  _
    have hKbig : (2 * C * q + 1 : ℕ) ≤ K := hK_big
    have : (K : ℝ) ≥ 2 * (C : ℝ) * (q : ℝ) + 1 := by exact_mod_cast hKbig
    -- K ≤ 2C(q-1) = 2Cq - 2C ≤ 2Cq < 2Cq + 1 ≤ K, contradiction
    nlinarith [mul_nonneg hCnn (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)]

/-- Helper: gen_exists_bound for odd primes only.
    Same as gen_exists_bound but with the extra 3 ≤ p condition. -/
private theorem gen_exists_bound_odd (q : Nat)
    (h : ∀ p, Nat.Prime p → 3 ≤ p → p < q → ∃ k, genSeq 2 k = p) :
    ∃ N, ∀ p, Nat.Prime p → 3 ≤ p → p < q → ∃ m, m < N ∧ genSeq 2 m = p := by
  induction q with
  | zero => exact ⟨0, fun p _ _ hp => absurd hp (by omega)⟩
  | succ q' ih =>
    have h' : ∀ p, Nat.Prime p → 3 ≤ p → p < q' → ∃ k, genSeq 2 k = p :=
      fun p hp hp3 hpq => h p hp hp3 (by omega)
    obtain ⟨N', hN'⟩ := ih h'
    if hprime : Nat.Prime q' then
      if hge3 : 3 ≤ q' then
        obtain ⟨m, hm⟩ := h q' hprime hge3 (by omega)
        refine ⟨Nat.max N' (m + 1), fun p hp hp3 hpq => ?_⟩
        match Nat.lt_or_ge p q' with
        | .inl hlt =>
          obtain ⟨j, hj, hjseq⟩ := hN' p hp hp3 hlt
          exact ⟨j, lt_of_lt_of_le hj (Nat.le_max_left _ _), hjseq⟩
        | .inr hge_p =>
          have : p = q' := by omega
          subst this
          exact ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right _ _), hm⟩
      else
        refine ⟨N', fun p hp hp3 hpq => ?_⟩
        have : p < q' := by omega
        exact hN' p hp hp3 this
    else
      refine ⟨N', fun p hp hp3 hpq => ?_⟩
      match Nat.lt_or_ge p q' with
      | .inl hlt => exact hN' p hp hp3 hlt
      | .inr hge_p =>
        exfalso; have : p = q' := by omega
        subst this; exact hprime hp

/-- **Weyl + walk cancellation → MC for standard EM (n=2).**

    For the standard EM sequence (n=2), seq 0 = 2 handles q=2.
    For q >= 3, q does not divide 2, so WeylHittingBridge gives either
    appearance (genSeq 2 j = q, hence seq(j+1) = q) or cofinal hitting.
    Cofinal hitting gives appearance via the gen_captures_target induction
    (modified: all primes in the gen sequence from 2 are odd, so the induction
    only needs primes >= 3, which all don't divide 2).

    **Status**: PROVED (from weyl_hitting_bridge_proved). -/
theorem cancel_weyl_implies_mc
    -- Walk character cancellation for n=2 (strong Weyl form, for q coprime to 2):
    (hcancel : ∀ (q : Nat) (hq : Nat.Prime q), ¬ (q ∣ 2) →
      ∀ (χ : Nat → ℂ), (∀ a, Complex.normSq (χ a) ≤ 1) →
      (χ 0 = 0) →
      (letI : NeZero q := ⟨hq.ne_zero⟩; ∑ a : ZMod q, χ (ZMod.val a) = 0) →
      ∀ (ε : ℝ), 0 < ε →
        ∃ K₀ : Nat, ∀ K : Nat, K₀ ≤ K → genWalkCharEnergy 2 K q χ ≤ (ε * K) ^ 2) :
    MullinConjecture := by
  -- Strong induction: suffices to show MC for all primes q ≤ B
  suffices ∀ B q, IsPrime q → q ≤ B → ∃ k, seq k = q by
    intro q hq; exact this q q hq (le_refl q)
  intro B
  induction B with
  | zero => intro q hq hle; exact absurd (Nat.Prime.one_lt (IsPrime.toNatPrime hq)) (by omega)
  | succ B ih =>
    intro q hq hle
    match Nat.lt_or_ge q (B + 1) with
    | .inl hlt => exact ih q hq (by omega)
    | .inr hge =>
      -- q = B + 1
      have hqp := IsPrime.toNatPrime hq
      by_cases hq2 : q = 2
      · exact ⟨0, by subst hq2; rfl⟩
      · have hndvd : ¬ (q ∣ 2) := by
          intro h; have hle := Nat.le_of_dvd (by norm_num) h
          have hge := hqp.two_le; omega
        have h_weyl := weyl_hitting_bridge_proved 2 Nat.squarefree_two (by norm_num)
          q hqp hndvd (hcancel q hqp hndvd)
        rcases h_weyl with ⟨j, hj⟩ | h_cofinal
        · exact ⟨j + 1, by rwa [← genSeq_two_eq_seq_succ]⟩
        · -- Cofinal hitting. Extract appearance.
          suffices ∃ k, genSeq 2 k = q by
            obtain ⟨k, hk⟩ := this
            exact ⟨k + 1, by rwa [← genSeq_two_eq_seq_succ]⟩
          -- By IH, every odd prime p < q appears as genSeq 2 _
          have ih_odd : ∀ p, Nat.Prime p → 3 ≤ p → p < q → ∃ k, genSeq 2 k = p := by
            intro p hp hp3 hpq
            obtain ⟨m, hm⟩ := ih p hp.toIsPrime (by omega)
            -- seq m = p, and seq 0 = 2 ≠ p (since p ≥ 3), so m ≥ 1
            have hm_pos : 0 < m := by
              by_contra h_zero; push_neg at h_zero
              have : m = 0 := by omega
              subst this; change seq 0 = p at hm; rw [seq_zero] at hm; omega
            -- genSeq 2 (m-1) = seq m = p
            refine ⟨m - 1, ?_⟩
            rw [genSeq_two_eq_seq_succ, show m - 1 + 1 = m from by omega, hm]
          -- genSeq 2 k ≥ 3 always (genProd 2 k is even, so genProd 2 k + 1 is odd)
          have hgen_ge3 : ∀ k, 3 ≤ genSeq 2 k := by
            intro k
            have hprime := genSeq_prime (by norm_num : 1 ≤ 2) k
            have heven : 2 ∣ genProd 2 k := start_dvd_genProd 2 k
            have hodd : ¬ 2 ∣ genProd 2 k + 1 := by omega
            have h2ne : genSeq 2 k ≠ 2 := by
              intro heq; rw [genSeq_def] at heq
              have := Nat.minFac_dvd (genProd 2 k + 1)
              rw [heq] at this; exact hodd this
            have := hprime.two_le; omega
          -- Bound the odd prime witnesses
          obtain ⟨N, hN⟩ := gen_exists_bound_odd q ih_odd
          obtain ⟨k, hk_ge, hhit_k⟩ := h_cofinal N
          rw [genWalkZ_eq_neg_one_iff] at hhit_k
          -- Key: genSeq 2 k ≤ q (from minFac ≤ q since q | genProd 2 k + 1)
          have hle_q : genSeq 2 k ≤ q := by
            rw [genSeq_def]; exact Nat.minFac_le_of_dvd hqp.two_le hhit_k
          -- Key: genSeq 2 k ≥ q (all odd primes < q already taken at steps < k)
          have hge_q : q ≤ genSeq 2 k := by
            by_contra hlt; push_neg at hlt
            have hprime_s := genSeq_prime (by norm_num : 1 ≤ 2) k
            have hge3_k := hgen_ge3 k
            obtain ⟨j, hjk, hseqj⟩ := hN (genSeq 2 k) hprime_s hge3_k hlt
            have hinj := (genSeq_injective Nat.squarefree_two) hseqj
            -- j < N ≤ k and j = k: contradiction
            omega
          -- genSeq 2 k = q
          exact ⟨k, by omega⟩

/-- **Full JSE to MC chain (honest version with explicit gap).**

    This composes all links in the JSE → MC chain:
    - JSE → multiplier cancellation for a.a. squarefree n (PROVED)
    - MultCancelToWalkCancel → walk cancellation for all squarefree n (open)
    - cancel_weyl_implies_mc → MC (PROVED)

    The two open hypotheses are:
    1. JointStepEquidist (JSE) — hard, requires BV/Siegel-Walfisz infrastructure
    2. MultCancelToWalkCancel — hard, equivalent to CCSB/CME (Dead End #117)

    Note: JSE is included for documentation (it motivates why multiplier
    cancellation should hold) but is logically redundant here —
    MultCancelToWalkCancel alone suffices since it gives walk cancellation
    unconditionally. The density-based multiplier cancellation from JSE
    cannot be extracted to pointwise bounds for specific n=2, so the
    conditional form (multiplier→walk transfer) would require an additional
    pointwise hypothesis. The unconditional form avoids this subtlety.

    WeylHittingBridge and PerChiCancellationBridge are both PROVED. -/
theorem jse_transfer_implies_mc
    (_hjse : JointStepEquidist)
    (htransfer : MultCancelToWalkCancel) :
    MullinConjecture :=
  cancel_weyl_implies_mc (fun q hq hndvd χ hχb hχ0 hχs ε hε =>
    htransfer 2 Nat.squarefree_two (by norm_num) q hq hndvd χ hχb hχ0 hχs ε hε)

end JSEToGenMC

/-! ## Section 5: The Ensemble PT Master Theorem -/

section MasterTheorem

/-- **Ensemble PT Master Theorem (character version).**
    Under the full chain of CRT equidistribution hypotheses plus the
    decorrelation and concentration bridges, for almost all squarefree
    starting points, the generalized EM character sums cancel:

    SRE + CRTPropStep + AccumBridge + DecorrBridge + VarBridge + ConcBridge
    => for a.a. squarefree n, |sum_{k<K} chi(genSeq n k)| = o(K).

    This is assembled from:
    1. `ensemble_crt_equidist_chain`: SRE+CRT+bridge => EME
    2. `ensemble_decorrelation_chain`: EME+decorr+var+conc => cancellation -/
theorem ensemble_pt_master
    (hsre : SquarefreeResidueEquidist)
    (hcrt : CRTPropagationStep)
    (hbridge : AccumEquidistImpliesMultEquidist)
    (hdecorr : EnsembleEquidistImpliesDecorrelation)
    (hvar : DecorrelationImpliesVariance)
    (hconc : CharVarianceImpliesConcentration) :
    ∀ (q : Nat), Nat.Prime q →
    ∀ (chi : Nat → ℂ), (∀ a, Complex.normSq (chi a) ≤ 1) →
    ∀ (eps : ℝ), 0 < eps →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              ∀ K, genSeqCharEnergy n K q chi > (eps * K) ^ 2)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop (nhds 0) :=
  ensemble_decorrelation_chain
    (ensemble_crt_equidist_chain hsre hcrt hbridge)
    hdecorr hvar hconc

/-- **Ensemble PT: standard EM via DSL.**
    Under the ensemble hypotheses plus DSL, MC holds for the standard
    Euclid-Mullin sequence (starting from n=2). The DSL provides
    the trajectory-level analogue of the ensemble decorrelation for
    the specific starting point n=2.

    Chain: DSL gives PE -> CME -> MC directly (proved in MasterReduction.lean).
    The ensemble framework shows this is part of a broader picture where
    MC holds for *almost all* starting points even without DSL. -/
theorem ensemble_pt_standard_em
    (h_equidist : ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q)
    (hdsl : DeterministicStabilityLemma) :
    MullinConjecture :=
  full_chain_dsl h_equidist hdsl

end MasterTheorem

/-! ## Section 6: Consistency and Cross-Connections -/

section Consistency

/-- **Ensemble equidistribution consistency**: the residue-counting version
    (`AlmostAllSquarefreeEqd`) and the character-sum version (from
    `char_concentration_implies_cancellation`) are both consequences of
    their respective concentration hypotheses. This theorem shows both
    reductions compose with the same CRT equidistribution source. -/
theorem ensemble_dual_consistency
    (hconc_res : EnsembleConcentration)
    (hconc_char : EnsembleCharSumConcentration) :
    AlmostAllSquarefreeEqd ∧
    (∀ (q : Nat), Nat.Prime q →
      ∀ (chi : Nat → ℂ), (∀ a, Complex.normSq (chi a) ≤ 1) →
      ∀ (eps : ℝ), 0 < eps →
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              ∀ K, genSeqCharEnergy n K q chi > (eps * K) ^ 2)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop (nhds 0)) :=
  ⟨ensemble_concentration_implies_eqd hconc_res,
   char_concentration_implies_cancellation hconc_char⟩

/-- **The ensemble framework subsumes the reciprocal sum chain.**
    Both the reciprocal sum divergence (from FM+VB) and the ensemble
    equidistribution (from EnsembleConcentration) are proved reductions
    from their respective concentration hypotheses. This combines them
    into a single consistency statement. -/
theorem ensemble_subsumes_reciprocal
    (h_recip : RecipSumConcentration)
    (h_ens : EnsembleConcentration) :
    AlmostAllSquarefreeRSD ∧ AlmostAllSquarefreeEqd :=
  ensemble_chains_consistent h_recip h_ens

/-- **DSL closes everything.** Under standard ANT (MinFacResidueEquidist)
    plus DSL, both MC and all ensemble conclusions hold:
    - MC (standard EM, via full_chain_dsl)
    - CCSB (complex character sum bound, via pe_dsl_implies_ccsb)
    All open ensemble hypotheses become vacuously satisfiable once MC holds. -/
theorem dsl_closes_all
    (h_equidist : ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q)
    (hdsl : DeterministicStabilityLemma) :
    MullinConjecture ∧ ComplexCharSumBound :=
  ⟨full_chain_dsl h_equidist hdsl,
   pe_dsl_implies_ccsb (pe_of_equidist h_equidist) hdsl⟩

end Consistency

/-! ## Summary of Proof Chain

The Ensemble Population Transfer framework establishes:

```
Layer 1: CRT Equidistribution
  SquarefreeResidueEquidist (standard ANT)
    + CRTPropagationStep (CRT independence)
    => AccumulatorEquidistPropagation (induction, PROVED)
    + AccumEquidistImpliesMultEquidist (PE bridge, open)
    => EnsembleMultiplierEquidist

Layer 2: Decorrelation
  EnsembleMultiplierEquidist
    + EnsembleEquidistImpliesDecorrelation (open)
    => StepDecorrelation

Layer 3: Variance and Concentration (ALL PROVED)
  StepDecorrelation
    => CharSumVarianceBound C (decorrelation_implies_variance_proved, PROVED)
    => EnsembleCharSumConcentration (char_variance_implies_concentration_proved, PROVED)

Layer 4: Cancellation (PROVED)
  EnsembleCharSumConcentration
    => a.a. squarefree n: character sums cancel
    (char_concentration_implies_cancellation, PROVED)

Direct composition (sd_implies_cancellation, PROVED):
  StepDecorrelation alone => a.a. character sum cancellation
  (composes all three Layer 3-4 reductions, zero open hypotheses)

Assembly (PROVED):
  Layers 1-4 compose to give `ensemble_pt_master_simplified` (4 hypotheses):
    SRE + CRT + AccumBridge + DecorrBridge => char cancellation for a.a.
  Original `ensemble_pt_master` (6 hypotheses) still available.

Standard EM (PROVED):
  DSL alone => MC for the standard sequence starting from n=2
  (full_chain_dsl, via PE from ANT)

JSE → MC (Section 4b):
  JointStepEquidist
    => per-chi decorrelation for nontrivial chi (PROVED)
    + PerChiCancellationBridge (PROVED, per_chi_cancellation_bridge_proved)
    => nontrivial MULTIPLIER cancellation (jse_implies_nontrivial_cancellation, PROVED)
    ... gap: MultCancelToWalkCancel (OPEN, equiv. to CCSB/CME, Dead End #117) ...
    => walk cancellation for n=2
    + WeylHittingBridge (PROVED, weyl_hitting_bridge_proved)
    => cofinal hitting
    + gen_hitting_implies_gen_mc_proved (PROVED)
    => MullinConjecture (cancel_weyl_implies_mc, PROVED)

  The explicit gap is MultCancelToWalkCancel (EnsembleDecorrelation.lean):
  multiplier character energy (genSeqCharEnergy) does NOT imply walk character
  energy (genWalkCharEnergy). This is the Marginal/Joint Barrier — multiplier
  sums give marginal information, walk sums require joint information about
  all previous multipliers. Dead Ends #58 and #117 show this fails for abstract
  and even EM-structured walks.

  Composition: jse_transfer_implies_mc (JSE + MultCancelToWalkCancel => MC).
  Note: JSE is logically redundant (MultCancelToWalkCancel alone suffices)
  but included to document the intended chain.
```

### Definitions in This File
* `sqfreeJointSeqCount`              -- joint count: genSeq at two steps (same modulus)
* `sqfreeJointSeqDensity`            -- joint density: genSeq at two steps
* `sqfreeJointAccumCountSame`        -- joint count: genProd at two steps (same modulus)
* `sqfreeJointAccumDensitySame`      -- joint density: genProd at two steps
* `JointAccumulatorEquidist_marginal`-- product of marginals (trivially from AEP)
* `JointAccumulatorEquidist'`        -- genuine joint density (open hypothesis)
* `JointStepEquidist`                -- genuine joint density for genSeq (open hypothesis)
* `PerChiCancellationBridge`         -- per-chi SD => per-chi cancellation (PROVED)
* `WeylHittingBridge`                -- walk char cancellation => cofinal hitting (PROVED)

### Open Hypotheses in This File
1. `EnsembleEquidistImpliesDecorrelation` -- EME => StepDecorrelation
2. `JointAccumulatorEquidist'`       -- genuine joint equidist of accumulator (not trivial from AEP)
3. `JointStepEquidist`               -- genuine joint equidist of genSeq (follows from JAE' + PE)

### Open Hypotheses in EnsembleDecorrelation.lean
4. `MultCancelToWalkCancel`          -- walk cancellation for all squarefree n
                                        (equivalent to CCSB/CME, Dead Ends #58/#117)

### Proved in This File
* `aep_implies_jae_marginal`              -- AEP => JAE_marginal (PROVED, trivial by Filter.Tendsto.mul)
* `sqfreeJointAccumCountSame_le_sqfreeCount`    -- count bound (PROVED)
* `sqfreeJointAccumDensitySame_nonneg`          -- density >= 0 (PROVED)
* `sqfreeJointAccumDensitySame_le_one`          -- density <= 1 (PROVED)
* `sqfreeJointAccumCountSame_le_accumCount_first` -- joint <= marginal (PROVED)
* `sqfreeJointAccumCountSame_sum_eq_first`      -- partition identity (PROVED)
* `DecorrelationImpliesVariance` -- SD => CharSumVarianceBound (PROVED, C=2)
* `EquidistImpliesCharMeanVanishing` -- EME => vanishing char means (PROVED)
* `GenHittingImpliesGenMC` -- cofinal walk hitting => gen. MC (PROVED)
* `sd_implies_cancellation` -- SD alone => char cancellation (PROVED, 3-step composition)
* `ensemble_pt_master_simplified` -- 4 hypotheses => char cancellation (PROVED)
* `joint_step_equidist_implies_step_decorrelation` -- JSE => per-chi SD (PROVED)
* `per_chi_cancellation_bridge_proved` -- PerChiCancellationBridge (PROVED, per-chi chain)
* `weyl_hitting_bridge_proved` -- WeylHittingBridge (PROVED, test function contradiction)
* `jse_implies_nontrivial_cancellation` -- JSE + PCB => nontrivial cancellation (PROVED)
* `cancel_weyl_implies_mc` -- walk cancellation => MC for n=2 (PROVED)
* `jse_transfer_implies_mc` -- JSE + MultCancelToWalkCancel => MC (PROVED, composition)

### What Would Close the Ensemble Gap

**Route A (universal SD)**: `EnsembleEquidistImpliesDecorrelation` is the sole
remaining open hypothesis for universal StepDecorrelation. Once SD holds (for all
chi, including trivial), `sd_implies_cancellation` gives character sum cancellation
for almost all squarefree starting points.

**Route B (JSE + MultCancelToWalkCancel)**: The JSE chain gives multiplier
character cancellation for a.a. squarefree n (PROVED). WeylHittingBridge is
PROVED (`weyl_hitting_bridge_proved`). PerChiCancellationBridge is PROVED
(`per_chi_cancellation_bridge_proved`). The sole remaining gap is
`MultCancelToWalkCancel` — transferring from multiplier energy (genSeqCharEnergy)
to walk energy (genWalkCharEnergy). This is equivalent to CCSB/CME and is the
core open problem of the project (see Dead Ends #58, #117).
Composition: `jse_transfer_implies_mc` (JSE + MultCancelToWalkCancel => MC).

**Route C (DSL)**: The DSL (from `PopulationTransferStrategy.lean`) provides a
stronger, trajectory-level version that gives MC for the specific starting point
n=2 without needing the ensemble averaging (`full_chain_dsl`). The ensemble
framework shows MC holds more broadly for density-1 starting points.
-/

end
