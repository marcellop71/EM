import EM.Ensemble.PT
import EM.Reduction.TailWindow

/-!
# The uncentered ensemble character layer is false: Dead Ends #156 and #157, witnessed

Session 307 recorded (Dead End #156) that the ensemble character-sum hypotheses
`StepDecorrelation`, `CharSumVarianceBound`, `EnsembleCharSumConcentration`, `FourPointPCV`,
`SecondMomentSquaredBound` and `TailWindowDecorrelation` quantify over *every* `χ : ℕ → ℂ` with
at most `‖χ‖ ≤ 1` — no `χ 0 = 0`, no `∑ χ = 0`, no nontriviality — so the constant character
`χ ≡ 1` falsifies each of them (the correlation is `1`, the energy of a window of length `K` is
`K²`, the fourth moment `K⁴`).  Dead End #157 recorded that `EnsembleMultiplierEquidist` fails
at step `0` by small-prime domination: for odd squarefree seeds `n`, `genSeq n 0 = minFac (n+1)
= 2`, and odd seeds are at least half of all squarefree seeds.  Both were "documented, not
witnessed".  This file supplies the witnesses; every proof is a two-line argument.

Consequences: the open points `StepDecorrelation`, `FourPointPCV`, `TailWindowDecorrelation`
are retired as FALSE, and the bridges `TWDImpliesCCSB`, `EnsembleEquidistImpliesDecorrelation`,
`DecorrelationImpliesVariance`, `FourPointPCVImpliesSMSB` hold vacuously (proved below).  The
proved chain theorems that consume these hypotheses (`decorrelation_implies_variance_proved`,
`char_variance_implies_concentration_proved`, `sd_implies_cancellation`, `four_point_pcv_chain`,
`second_moment_squared_implies_chebyshev`, the tail-window chain) remain valid conditionals with
false antecedents.  A *centered* repair (nontrivial Dirichlet characters, `∑ χ = 0`) is the
statement one would want; at fixed steps `j, k` it is of the head-dominated fixed-step type of
#157 and is not pursued here.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup

namespace UncenteredRefutations

/-- The constant character. -/
def one : ℕ → ℂ := fun _ => 1

theorem one_normSq (a : ℕ) : Complex.normSq (one a) ≤ 1 := by simp [one]

theorem sqfreeCount_ne_zero {X : ℕ} (hX : 1 ≤ X) : sqfreeCount X ≠ 0 :=
  (sqfreeCount_pos_of_pos hX).ne'

/-- The ensemble average of a constant is that constant. -/
theorem ensembleAvg_const {X : ℕ} (hX : 1 ≤ X) (c : ℝ) : ensembleAvg X (fun _ => c) = c := by
  unfold ensembleAvg sqfreeCount
  rw [Finset.sum_const, nsmul_eq_mul]
  have : ((((Finset.Icc 1 X).filter Squarefree).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (sqfreeCount_pos_of_pos hX).ne'
  field_simp

/-- For the constant character, a window of length `K` has character sum `K`. -/
theorem genSeqCharPartialSum_one (n K q : ℕ) : genSeqCharPartialSum n K q one = K := by
  simp [genSeqCharPartialSum, one]

theorem genSeqCharEnergy_one (n K q : ℕ) : genSeqCharEnergy n K q one = (K : ℝ) ^ 2 := by
  unfold genSeqCharEnergy
  rw [genSeqCharPartialSum_one]
  simp [Complex.normSq_natCast, sq]

/-! ## Dead End #156 -/

/-- **`StepDecorrelation` is false**: at `χ ≡ 1` the ensemble correlation is identically `1`. -/
theorem not_stepDecorrelation : ¬ StepDecorrelation := by
  intro h
  have := h 2 Nat.prime_two one 0 1 (by norm_num)
  have h1 : Filter.Tendsto (fun X : ℕ =>
      |ensembleAvg X (fun n => (one (genSeq n 0 % 2) * starRingEnd ℂ (one (genSeq n 1 % 2))).re)|)
      Filter.atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with X hX
    simp only [one, map_one, mul_one, Complex.one_re]
    rw [ensembleAvg_const hX]; simp
  have := tendsto_nhds_unique this h1
  norm_num at this

/-- **`FourPointPCV` is false**: at `χ ≡ 1` every four-point correlation is `1`. -/
theorem not_fourPointPCV : ¬ FourPointPCV := by
  intro h
  obtain ⟨X₀, hX₀⟩ := h 2 Nat.prime_two one one_normSq 0 1 0 2 (by norm_num) (by norm_num)
    (Or.inr (by norm_num)) (1 / 2) (by norm_num)
  have hX := hX₀ (max X₀ 1) (le_max_left _ _) (sqfreeCount_ne_zero (le_max_right _ _))
  simp only [one, map_one, mul_one, Complex.one_re, Finset.sum_const, nsmul_eq_mul, mul_one] at hX
  have hpos : (0 : ℝ) < sqfreeCount (max X₀ 1) := by
    exact_mod_cast sqfreeCount_pos_of_pos (le_max_right _ _)
  unfold sqfreeCount at hpos hX
  rw [abs_of_pos hpos, one_div, inv_mul_cancel₀ hpos.ne'] at hX
  norm_num at hX

/-- **`TailWindowDecorrelation` is false**: at `χ ≡ 1` two windows of length `K` have cross
term `K²`. -/
theorem not_tailWindowDecorrelation : ¬ TailWindowDecorrelation := by
  intro h
  obtain ⟨K₀, hK₀, hK⟩ := h 2 Nat.prime_two one one_normSq (1 / 4) (by norm_num)
  have := hK K₀ le_rfl 2 (by norm_num)
  have hcross : windowCrossTerm 0 1 K₀ 2 one = (K₀ : ℝ) ^ 2 := by
    unfold windowCrossTerm windowCharSum
    simp [one, sq]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at this
  norm_num [hcross] at this
  have hK1 : (1 : ℝ) ≤ K₀ := by exact_mod_cast hK₀
  nlinarith

/-- **`CharSumVarianceBound C` is false for every `C`**: at `χ ≡ 1` the ensemble energy is
`K²`, not `O(K)`. -/
theorem not_charSumVarianceBound (C : ℝ) : ¬ CharSumVarianceBound C := by
  intro h
  set K := ⌈C⌉₊ + 1 with hK
  obtain ⟨X₀, hX₀⟩ := h 2 Nat.prime_two one one_normSq K
  have := hX₀ (max X₀ 1) (le_max_left _ _)
  simp only [genSeqCharEnergy_one] at this
  rw [ensembleAvg_const (le_max_right _ _)] at this
  have hKC : C < K := by
    have := Nat.le_ceil C; rw [hK]; push_cast; linarith
  have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
  nlinarith

/-- **`EnsembleCharSumConcentration` is false**: at `χ ≡ 1` every seed is bad. -/
theorem not_ensembleCharSumConcentration : ¬ EnsembleCharSumConcentration := by
  intro h
  obtain ⟨K₀, hK₀⟩ := h 2 Nat.prime_two one one_normSq (1 / 2) (by norm_num) (1 / 2) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := hK₀ (max K₀ 1) (le_max_left _ _)
  have := hX₀ (max X₀ 1) (le_max_left _ _)
  set K : ℕ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_max_right K₀ 1
  have hall : (Finset.Icc 1 (max X₀ 1)).filter (fun n => Squarefree n ∧
      genSeqCharEnergy n K 2 one > (1 / 2 * (K : ℝ)) ^ 2) =
      (Finset.Icc 1 (max X₀ 1)).filter Squarefree := by
    apply Finset.filter_congr
    intro n _
    rw [genSeqCharEnergy_one]
    constructor
    · exact fun h => h.1
    · intro h; refine ⟨h, ?_⟩; nlinarith
  rw [hall] at this
  have hpos : (0 : ℝ) < ((Finset.Icc 1 (max X₀ 1)).filter Squarefree).card := by
    exact_mod_cast sqfreeCount_pos_of_pos (le_max_right X₀ 1)
  rw [div_self hpos.ne'] at this
  norm_num at this

/-- **`SecondMomentSquaredBound D` is false for every `D`**: at `χ ≡ 1` the fourth moment is
`K⁴`, not `O(K²)`. -/
theorem not_secondMomentSquaredBound (D : ℝ) : ¬ SecondMomentSquaredBound D := by
  intro h
  set K := ⌈D⌉₊ + 1 with hK
  obtain ⟨X₀, hX₀⟩ := h 2 Nat.prime_two one one_normSq K (by omega)
  have := hX₀ (max X₀ 1) (le_max_left _ _)
  unfold populationCharEnergySquared at this
  rw [if_neg (sqfreeCount_ne_zero (le_max_right _ _))] at this
  simp only [genSeqCharEnergySquared, genSeqCharEnergy_one, Finset.sum_const, nsmul_eq_mul] at this
  have hpos : (0 : ℝ) < sqfreeCount (max X₀ 1) := by
    exact_mod_cast sqfreeCount_pos_of_pos (le_max_right _ _)
  unfold sqfreeCount at this hpos
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at this
  have hKD : D < K := by
    have := Nat.le_ceil D; rw [hK]; push_cast; linarith
  have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈D⌉₊]
  have hK2 : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  nlinarith

/-! ## Dead End #157 -/

/-- **`EnsembleMultiplierEquidist` is false**: at step `0`, the odd squarefree seeds — at least
half of all seeds — all have multiplier `2`, so the class `2 mod 5` has density `≥ 1/2 > 1/4`. -/
theorem not_ensembleMultiplierEquidist : ¬ EnsembleMultiplierEquidist := by
  intro h
  have hprime : Nat.Prime 5 := by decide
  have h5 := h 5 hprime 0 (2 : ZMod 5) (by decide)
  have hlow : ∀ X : ℕ, 1 ≤ X → (1 / 2 : ℝ) ≤ sqfreeSeqDensity X 0 5 (2 : ZMod 5) := by
    intro X hX
    unfold sqfreeSeqDensity sqfreeSeqCount
    have hsub : (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n) ⊆
        (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ (genSeq n 0 : ZMod 5) = 2) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨hn.1, hn.2.1, ?_⟩
      rw [genSeq_zero_of_odd hn.1.1 hn.2.2]; rfl
    have h1 := Finset.card_le_card hsub
    have h2 := odd_sf_card_ge_half X
    have hpos : (0 : ℝ) < (sqfreeCount X : ℝ) := by exact_mod_cast sqfreeCount_pos_of_pos hX
    rw [le_div_iff₀ hpos]
    unfold sqfreeCount at hpos ⊢
    have h1' : (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)).card : ℝ) ≤
        (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ (genSeq n 0 : ZMod 5) = 2)).card : ℝ) := by
      exact_mod_cast h1
    have h2' : (((Finset.Icc 1 X).filter Squarefree).card : ℝ) ≤
        2 * (((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)).card : ℝ) := by
      exact_mod_cast h2
    linarith
  have hge : (1 / 2 : ℝ) ≤ 1 / ((5 : ℝ) - 1) := by
    refine ge_of_tendsto h5 ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with X hX using hlow X hX
  norm_num at hge

/-! ## Vacuous bridges -/

theorem twdImpliesCCSB_vacuous : TWDImpliesCCSB :=
  fun h => (not_tailWindowDecorrelation h).elim

theorem ensembleEquidistImpliesDecorrelation_vacuous : EnsembleEquidistImpliesDecorrelation :=
  fun h => (not_ensembleMultiplierEquidist h).elim

theorem decorrelationImpliesVariance_vacuous : DecorrelationImpliesVariance :=
  fun h => (not_stepDecorrelation h).elim

theorem fourPointPCVImpliesSMSB_vacuous : FourPointPCVImpliesSMSB :=
  fun h => (not_fourPointPCV h).elim

end UncenteredRefutations

end
