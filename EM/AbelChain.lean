import EM.OneSidedTauberian

/-!
# Abel summation: from `(log p)/p` to `1/p`

This file proves `PrimeLogToReciprocal`: that `PrimeLogSumEquidist` implies
`PrimesEquidistributedInAP`, using discrete Abel summation (summation by parts)
to convert `sum (log p)/p` equidistribution into `sum 1/p` equidistribution.

## Main results

* `hasDerivAt_log_log` : derivative of `log(log t)` is `1/(t * log t)` for `t > 1`
* `hasDerivAt_neg_inv_log` : derivative of `-(log t)^{-1}` is `(t * (log t)^2)^{-1}` for `t > 1`
* `integral_inv_mul_log` : `integral 1/(t * log t) dt = log(log b) - log(log a)` (FTC)
* `integral_inv_mul_log_sq` : `integral (t * (log t)^2)^{-1} dt = (log a)^{-1} - (log b)^{-1}`
* `log_ratio_le` : `(log b - log a)/log b <= log(log b) - log(log a)`
* `loglog_le_ratio` : `log(log b) - log(log a) <= (log b - log a)/log a`
* `prime_log_to_reciprocal_proved` : `PrimeLogSumEquidist -> PrimesEquidistributedInAP`
-/

noncomputable section
open Classical

namespace IK

open Nat Finset BigOperators Filter MeasureTheory

/-! ### Derivative computations -/

/-- Derivative of `log(log t)` is `1/(t * log t)` for `t > 1`. -/
theorem hasDerivAt_log_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => Real.log (Real.log t)) (1 / (t * Real.log t)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hd := (Real.hasDerivAt_log hlt).comp t (Real.hasDerivAt_log ht0)
  simp only [Function.comp_def] at hd
  convert hd using 1; field_simp

/-- Derivative of `-(log t)^{-1}` is `(t * (log t)^2)^{-1}` for `t > 1`. -/
theorem hasDerivAt_neg_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) ((t * (Real.log t) ^ 2)⁻¹) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  convert ((Real.hasDerivAt_log ht0).inv hlt).neg using 1; field_simp

/-! ### Integral computations via FTC -/

/-- `integral 1/(t * log t) dt = log(log b) - log(log a)` for `1 < a <= b`. -/
theorem integral_inv_mul_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (1 / (t * Real.log t)) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  have hmem : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht; rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · exact ContinuousOn.mul continuousOn_id
        (Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [ht.1])))
    · intro t ht
      exact mul_ne_zero (ne_of_gt (by linarith [ht.1]))
        (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_log_log (hmem t ht)) hint

/-- `integral (t * (log t)^2)^{-1} dt = (log a)^{-1} - (log b)^{-1}` for `1 < a <= b`. -/
theorem integral_inv_mul_log_sq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (t * (Real.log t) ^ 2)⁻¹ =
      (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hmem : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht; rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]
  have hint : IntervalIntegrable (fun t => (t * (Real.log t) ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    simp_rw [inv_eq_one_div]
    apply ContinuousOn.div continuousOn_const
    · exact ContinuousOn.mul continuousOn_id
        ((Real.continuousOn_log.mono (fun t ht =>
          ne_of_gt (by linarith [ht.1]))).pow 2)
    · intro t ht
      exact mul_ne_zero (ne_of_gt (by linarith [ht.1]))
        (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [ht.1]))))
  linarith [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_neg_inv_log (hmem t ht)) hint]

/-! ### Key inequalities from `log x <= x - 1` -/

/-- `(log b - log a) / log b <= log(log b) - log(log a)` for `1 < a <= b`. -/
theorem log_ratio_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (Real.log b - Real.log a) / Real.log b ≤
    Real.log (Real.log b) - Real.log (Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogb : 0 < Real.log b := Real.log_pos (lt_of_lt_of_le ha hab)
  have h := Real.log_le_sub_one_of_pos (div_pos hloga hlogb)
  rw [Real.log_div hloga.ne' hlogb.ne'] at h
  have hrw : (Real.log b - Real.log a) / Real.log b =
      1 - Real.log a / Real.log b := by
    rw [sub_div, div_self hlogb.ne']
  rw [hrw]; linarith

/-- `log(log b) - log(log a) <= (log b - log a) / log a` for `1 < a <= b`. -/
theorem loglog_le_ratio {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Real.log (Real.log b) - Real.log (Real.log a) ≤
    (Real.log b - Real.log a) / Real.log a := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogb : 0 < Real.log b := Real.log_pos (lt_of_lt_of_le ha hab)
  have h := Real.log_le_sub_one_of_pos (div_pos hlogb hloga)
  rw [Real.log_div hlogb.ne' hloga.ne'] at h
  linarith [show Real.log b / Real.log a - 1 =
    (Real.log b - Real.log a) / Real.log a from by rw [sub_div, div_self hloga.ne']]

/-! ### PrimeLogToReciprocal via discrete Abel summation -/

section PrimeLogToReciprocal

/-- `log(1 + y) <= y` for `y >= 0`. -/
private theorem log_one_add_le {y : ℝ} (hy : 0 ≤ y) :
    Real.log (1 + y) ≤ y := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + y)]

/-- For `m <= x < m + 1` with `m >= 3`, `|loglog x - loglog m| <= 1`. -/
private theorem loglog_floor_close {x : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (hmx : (m : ℝ) ≤ x) (hxm : x < m + 1) :
    |Real.log (Real.log x) - Real.log (Real.log (m : ℝ))| ≤ 1 := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  rw [abs_of_nonneg (by linarith [Real.log_le_log hlogm (Real.log_le_log hm_pos hmx)])]
  have step1 := loglog_le_ratio hm1 (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
  have step2 : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / m := by
    rw [← Real.log_div (by positivity) hm_pos.ne']
    have : ((m : ℝ) + 1) / m = 1 + 1 / m := by field_simp
    rw [this]; exact log_one_add_le (by positivity)
  have h_upper : Real.log (Real.log x) ≤ Real.log (Real.log ((m : ℝ) + 1)) :=
    Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) hxm.le)
  have hlog3_gt_one : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have step3 : 1 / (m : ℝ) / Real.log (m : ℝ) ≤ 1 := by
    rw [div_div, div_le_one (mul_pos hm_pos hlogm)]
    calc (1 : ℝ) ≤ 1 * Real.log 3 := by rw [one_mul]; exact hlog3_gt_one.le
      _ ≤ 3 * Real.log 3 := by nlinarith
      _ ≤ m * Real.log (m : ℝ) := by
          apply mul_le_mul (by exact_mod_cast hm)
            (Real.log_le_log (by norm_num : (0:ℝ) < 3) (by exact_mod_cast hm))
            (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3))
            (by exact_mod_cast (show 0 ≤ m by omega))
  calc Real.log (Real.log x) - Real.log (Real.log (m : ℝ))
      ≤ Real.log (Real.log ((m : ℝ) + 1)) - Real.log (Real.log (m : ℝ)) := by linarith
    _ ≤ (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) / Real.log (m : ℝ) := step1
    _ ≤ (1 / (m : ℝ)) / Real.log (m : ℝ) :=
        div_le_div_of_nonneg_right step2 hlogm.le
    _ ≤ 1 := step3

/-! #### Discrete Abel summation identity -/

/-- Discrete Abel summation (summation by parts):
    `sum_{Ico lo (hi+1)} a(k) * g(k) = A(hi) * g(hi) +
      sum_{Ico lo hi} A(j) * (g(j) - g(j+1))`
    where `A(j) = sum_{Ico lo (j+1)} a(k)`. -/
private theorem discrete_abel (a g : ℕ → ℝ) (lo hi : ℕ) (hlo : lo ≤ hi) :
    ∑ k ∈ Ico lo (hi + 1), a k * g k =
      (∑ k ∈ Ico lo (hi + 1), a k) * g hi +
      ∑ j ∈ Ico lo hi, (∑ k ∈ Ico lo (j + 1), a k) * (g j - g (j + 1)) := by
  induction hi with
  | zero =>
    have hlo0 : lo = 0 := by omega
    subst hlo0
    simp only [Finset.Ico_self, Finset.sum_empty]
    rw [Nat.Ico_succ_singleton]; simp [Finset.sum_singleton]
  | succ n ih =>
    by_cases hlon : lo ≤ n
    · have h1 : lo ≤ n + 1 := by omega
      rw [Finset.sum_Ico_succ_top h1 (fun k => a k * g k),
        ih hlon, Finset.sum_Ico_succ_top h1 a,
        Finset.sum_Ico_succ_top hlon
          (fun j => (∑ k ∈ Ico lo (j + 1), a k) * (g j - g (j + 1)))]
      ring
    · have hlon1 : lo = n + 1 := by omega
      subst hlon1
      simp only [Finset.Ico_self, Finset.sum_empty]
      rw [Nat.Ico_succ_singleton]; simp [Finset.sum_singleton]

/-- `log(k+1) - log(k) <= 1/k` for `k >= 1`. -/
private theorem log_succ_sub_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) ≤ 1 / k := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [← Real.log_div (by positivity) hk_pos.ne']
  have : ((k : ℝ) + 1) / k = 1 + 1 / k := by field_simp
  rw [this]; exact log_one_add_le (by positivity)

/-- Telescoping: `sum_{Ico 2 m} (1/log k - 1/log(k+1)) = 1/log 2 - 1/log m` for `m >= 2`. -/
private theorem sum_inv_log_telescope (m : ℕ) (hm : 2 ≤ m) :
    ∑ k ∈ Ico 2 m, (1 / Real.log (k : ℝ) - 1 / Real.log ((k : ℝ) + 1)) =
    1 / Real.log 2 - 1 / Real.log (m : ℝ) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn2 : n = 1
    · subst hn2
      rw [show Ico 2 2 = ∅ from by decide, Finset.sum_empty]; push_cast; ring
    · rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n), ih (by omega)]; push_cast; ring

/-- `(log(k+1) - log k) / log(k+1) <= loglog(k+1) - loglog k` for `k >= 2`. -/
private theorem main_term_upper {k : ℕ} (hk : 2 ≤ k) :
    (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) ≤
    Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) :=
  log_ratio_le (by exact_mod_cast (show 1 < k by omega))
    (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)

/-- The correction between `loglog(k+1) - loglog(k)` and
    `(log(k+1) - log(k)) / log(k+1)` is bounded by `1/(k^2 * (log 2)^2)`. -/
private theorem main_term_correction {k : ℕ} (hk : 2 ≤ k) :
    Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
      (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) ≤
    1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hk_pos : (0 : ℝ) < k := by linarith
  have hlogk : (0 : ℝ) < Real.log k := Real.log_pos hk1
  have hlogk1 : (0 : ℝ) < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hub := loglog_le_ratio hk1 (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
  set δ := Real.log ((k : ℝ) + 1) - Real.log k with hδ_def
  have hδ_nonneg : 0 ≤ δ := by linarith [Real.log_le_log hk_pos (by linarith : (k:ℝ) ≤ k + 1)]
  have hδ_le : δ ≤ 1 / k := log_succ_sub_le (by omega : 1 ≤ k)
  have step1 : Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
        (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1)
      ≤ δ / Real.log k - δ / Real.log ((k : ℝ) + 1) := by linarith
  have step2 : δ / Real.log k - δ / Real.log ((k : ℝ) + 1) =
      δ ^ 2 / (Real.log k * Real.log ((k : ℝ) + 1)) := by
    rw [div_sub_div _ _ hlogk.ne' hlogk1.ne', hδ_def]; ring
  have hlog2_le_logk : Real.log 2 ≤ Real.log ↑k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ k by omega))
  have hlog2_le_logk1 : Real.log 2 ≤ Real.log (↑k + 1) :=
    Real.log_le_log (by norm_num) (by
      have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      linarith)
  have step3 : δ ^ 2 / (Real.log k * Real.log ((k : ℝ) + 1)) ≤
      (1 / k) ^ 2 / (Real.log 2 * Real.log 2) := by
    have hnum : δ ^ 2 ≤ (1 / k) ^ 2 := pow_le_pow_left₀ hδ_nonneg hδ_le 2
    have hden : Real.log 2 * Real.log 2 ≤ Real.log k * Real.log ((k : ℝ) + 1) :=
      mul_le_mul hlog2_le_logk hlog2_le_logk1 hlog2.le hlogk.le
    calc δ ^ 2 / (Real.log ↑k * Real.log (↑k + 1))
        ≤ (1 / ↑k) ^ 2 / (Real.log ↑k * Real.log (↑k + 1)) :=
          div_le_div_of_nonneg_right hnum (mul_nonneg hlogk.le hlogk1.le)
      _ ≤ (1 / ↑k) ^ 2 / (Real.log 2 * Real.log 2) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hlog2 hlog2) hden
  linarith [step1, step2, step3,
    show (1 / (k : ℝ)) ^ 2 / (Real.log 2 * Real.log 2) =
      1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2) from by ring]

/-- Telescope: `sum_{Ico 2 m} (1/(k-1) - 1/k) = 1 - 1/(m-1)` for `m >= 3`. -/
private theorem sum_telescope_inv (m : ℕ) (hm : 3 ≤ m) :
    ∑ k ∈ Ico 2 m, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 - 1 / ((m : ℝ) - 1) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 2
    · subst hn
      rw [show Ico 2 3 = {2} from by decide, Finset.sum_singleton]; push_cast; norm_num
    · rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n), ih (by omega)]
      have : (↑(n + 1) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
      rw [this]; linarith

/-- `sum_{Ico 2 m} 1/(k * (k-1)) <= 1` by telescoping. -/
private theorem sum_inv_mul_pred_le (m : ℕ) :
    ∑ k ∈ Ico 2 m, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 := by
  have key : ∀ k ∈ Ico 2 m, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) =
      1 / ((k : ℝ) - 1) - 1 / k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      linarith
    rw [div_sub_div _ _ hk1_pos.ne' hk_pos.ne']; congr 1 <;> ring
  rw [Finset.sum_congr rfl key]
  by_cases hm : m ≤ 2
  · have : Ico 2 m = ∅ := by ext k; simp [Finset.mem_Ico]; omega
    simp [this]
  · push_neg at hm
    rw [sum_telescope_inv m (by omega)]
    have hm_pos : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    linarith [div_nonneg (by positivity : (0 : ℝ) ≤ 1) hm_pos.le]

/-- `sum_{Ico 2 m} 1/k^2 <= 1` by comparison with `1/(k*(k-1))` telescope. -/
private theorem sum_inv_sq_le (m : ℕ) :
    ∑ k ∈ Ico 2 m, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by
  calc ∑ k ∈ Ico 2 m, (1 : ℝ) / (k : ℝ) ^ 2
      ≤ ∑ k ∈ Ico 2 m, 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
        apply Finset.sum_le_sum; intro k hk
        rw [Finset.mem_Ico] at hk
        have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
          linarith
        rw [div_le_div_iff₀ (sq_pos_of_pos hk_pos) (mul_pos hk_pos hk1_pos)]
        rw [one_mul, one_mul, sq]
        exact mul_le_mul_of_nonneg_left (by linarith) hk_pos.le
    _ ≤ 1 := sum_inv_mul_pred_le m

/-- Telescoping loglog sum: `sum_{Ico 2 m} (loglog(k+1) - loglog k) =
    loglog m - loglog 2` for `m >= 3`. -/
private theorem sum_loglog_telescope (m : ℕ) (hm : 3 ≤ m) :
    ∑ k ∈ Ico 2 m,
      (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) =
      Real.log (Real.log ↑m) - Real.log (Real.log 2) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn3 : n = 2
    · subst hn3
      rw [show Ico 2 3 = {2} from by decide, Finset.sum_singleton]; push_cast; ring_nf
    · rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n), ih (by omega)]; push_cast; ring_nf

/-- The main sum `sum_{Ico 2 m} (log(k+1) - log k) / log(k+1)` is within
    `1/(log 2)^2` of `loglog m - loglog 2`. -/
private theorem main_sum_sandwich (m : ℕ) (hm : 3 ≤ m) :
    let σ := ∑ k ∈ Ico 2 m,
      (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1)
    0 ≤ Real.log (Real.log m) - Real.log (Real.log 2) - σ ∧
    Real.log (Real.log m) - Real.log (Real.log 2) - σ ≤ 1 / (Real.log 2) ^ 2 := by
  intro σ
  constructor
  · -- Lower bound: sigma <= loglog(m) - loglog(2) by telescoping main_term_upper
    have hle : σ ≤ ∑ k ∈ Ico 2 m,
        (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) :=
      Finset.sum_le_sum fun k hk => main_term_upper (by rw [Finset.mem_Ico] at hk; omega)
    linarith [sum_loglog_telescope m hm]
  · -- Upper bound: each correction <= 1/(k^2 * (log 2)^2), and sum 1/k^2 <= 1
    have htel_eq : Real.log (Real.log m) - Real.log (Real.log 2) - σ =
        ∑ k ∈ Ico 2 m, (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
          (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1)) := by
      rw [Finset.sum_sub_distrib]; congr 1; exact (sum_loglog_telescope m hm).symm
    rw [htel_eq]
    calc ∑ k ∈ Ico 2 m, (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
            (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1))
        ≤ ∑ k ∈ Ico 2 m, (1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2)) :=
          Finset.sum_le_sum fun k hk => main_term_correction (by rw [Finset.mem_Ico] at hk; omega)
      _ = (∑ k ∈ Ico 2 m, (1 : ℝ) / (k : ℝ) ^ 2) / (Real.log 2) ^ 2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ 1 / (Real.log 2) ^ 2 :=
          div_le_div_of_nonneg_right (sum_inv_sq_le m) (sq_nonneg _)

/-! #### Abel summation applied to prime reciprocal sums -/

/-- Abel summation for primes in a residue class: expresses `sum 1/p` in terms
    of partial sums `sum (log p)/p` and telescoping `1/log j - 1/log(j+1)`. -/
private theorem abel_filtered_sum (q : ℕ) (a_mod : ℕ) (m : ℕ) (hm : 2 ≤ m) :
    let PCS : ℕ → Finset ℕ := fun n =>
      ((Icc 2 n).filter Nat.Prime).filter (fun p => p % q = a_mod % q)
    ∑ p ∈ PCS m, (1 : ℝ) / p =
      (∑ p ∈ PCS m, Real.log p / p) * (1 / Real.log m) +
      ∑ j ∈ Ico 2 m,
        (∑ p ∈ PCS j, Real.log p / p) *
        (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) := by
  intro PCS
  set af : ℕ → ℝ := fun k => if k ∈ PCS m then Real.log k / k else 0
  set gf : ℕ → ℝ := fun k => 1 / Real.log (k : ℝ)
  have habel := discrete_abel af gf 2 m hm
  have icc_ico : Icc 2 m = Ico 2 (m + 1) := by
    ext k; simp [Finset.mem_Icc, Finset.mem_Ico]
  -- LHS of Abel = sum 1/p
  have lhs_eq : ∑ k ∈ Ico 2 (m + 1), af k * gf k = ∑ p ∈ PCS m, (1 : ℝ) / p := by
    rw [icc_ico.symm]
    have hsub : PCS m ⊆ Icc 2 m := fun p hp =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 m) (fun k => k ∈ PCS m)]
    have hzero : ∑ k ∈ (Icc 2 m).filter (fun k => k ∉ PCS m), af k * gf k = 0 :=
      Finset.sum_eq_zero fun k hk => by
        simp only [Finset.mem_filter] at hk; simp only [af, if_neg hk.2, zero_mul]
    rw [hzero, add_zero]
    have hfilter : (Icc 2 m).filter (fun k => k ∈ PCS m) = PCS m := by
      ext k; simp only [Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hsub h, h⟩⟩
    rw [hfilter]
    apply Finset.sum_congr rfl; intro k hk
    simp only [af, gf, if_pos hk]
    have hk_prime : Nat.Prime k :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk_prime.pos
    have hlogk : Real.log (k : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hk_prime.one_lt))
    field_simp
  -- PCS monotonicity
  have pcs_mono : ∀ j, j ≤ m → PCS j ⊆ PCS m := fun j hjm p hp => by
    simp only [Finset.mem_filter, Finset.mem_Icc, PCS] at hp ⊢
    exact ⟨⟨⟨hp.1.1.1, hp.1.1.2.trans hjm⟩, hp.1.2⟩, hp.2⟩
  have pcs_sub_icc : ∀ j, PCS j ⊆ Icc 2 j := fun j p hp =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  -- sum af(k) over Ico 2 (j+1) = S(j)
  have sum_af_eq : ∀ j, 2 ≤ j → j ≤ m →
      ∑ k ∈ Ico 2 (j + 1), af k = ∑ p ∈ PCS j, Real.log p / p := by
    intro j hj hjm
    have icc_eq : Ico 2 (j + 1) = Icc 2 j := by
      ext k; simp [Finset.mem_Icc, Finset.mem_Ico]
    rw [icc_eq]
    trans ∑ p ∈ PCS j, af p
    · symm
      apply Finset.sum_subset (pcs_sub_icc j)
      intro k hk hk_not
      simp only [af]; rw [if_neg]
      intro hk_mem
      exact hk_not (by
        simp only [Finset.mem_filter, Finset.mem_Icc, PCS] at hk_mem ⊢
        exact ⟨⟨⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2⟩, hk_mem.1.2⟩, hk_mem.2⟩)
    · exact Finset.sum_congr rfl fun k hk => by simp only [af, if_pos (pcs_mono j hjm hk)]
  -- Assemble
  rw [lhs_eq] at habel; rw [habel]
  have eq1 : (∑ k ∈ Ico 2 (m + 1), af k) * gf m =
      (∑ p ∈ PCS m, Real.log p / p) * (1 / Real.log m) := by
    congr 1; exact sum_af_eq m hm le_rfl
  have eq2 : ∑ j ∈ Ico 2 m, (∑ k ∈ Ico 2 (j + 1), af k) * (gf j - gf (j + 1)) =
      ∑ j ∈ Ico 2 m, (∑ p ∈ PCS j, Real.log p / p) *
        (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) := by
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.mem_Ico] at hj
    rw [sum_af_eq j hj.1 hj.2.le]; simp only [gf, Nat.cast_add, Nat.cast_one]
  rw [eq1, eq2]

/-- `log j * (1/log j - 1/log(j+1)) = (log(j+1) - log j) / log(j+1)` for `j >= 2`. -/
private theorem main_term_alg {j : ℕ} (hj : 2 ≤ j) :
    Real.log (j : ℝ) * (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) =
    (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) / Real.log ((j : ℝ) + 1) := by
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hlogj : Real.log (j : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hj1)
  have hlogj1 : Real.log ((j : ℝ) + 1) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  field_simp

/-- `1/log j - 1/log(j+1) >= 0` for `j >= 2`. -/
private theorem inv_log_diff_nonneg {j : ℕ} (hj : 2 ≤ j) :
    0 ≤ 1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1) := by
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hlogj : 0 < Real.log (j : ℝ) := Real.log_pos hj1
  have hlogj1 : 0 < Real.log ((j : ℝ) + 1) := Real.log_pos (by linarith)
  rw [div_sub_div _ _ hlogj.ne' hlogj1.ne']
  exact div_nonneg
    (by linarith [Real.log_le_log (by linarith : (0:ℝ) < j) (by linarith : (j:ℝ) ≤ j + 1)])
    (mul_nonneg hlogj.le hlogj1.le)

/-- `|1 - log(log 2)| <= 1 + 1/(log 2)^2`. -/
private theorem loglog2_bound :
    |1 - Real.log (Real.log 2)| ≤ 1 + 1 / (Real.log 2) ^ 2 := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 2)]
    exact Real.exp_one_gt_d9.trans' (by norm_num)
  have hloglog2_neg : Real.log (Real.log 2) < 0 := by
    rw [Real.log_neg_iff hlog2_pos]; exact hlog2_lt1
  rw [show (1 : ℝ) - Real.log (Real.log 2) = 1 + (-Real.log (Real.log 2)) from by ring,
    abs_of_pos (by linarith)]
  suffices h : -Real.log (Real.log 2) ≤ 1 / (Real.log 2) ^ 2 by linarith
  have h1 : -Real.log (Real.log 2) = Real.log (1 / Real.log 2) := by
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) hlog2_pos.ne', Real.log_one, zero_sub]
  rw [h1]
  have h2 := Real.log_le_sub_one_of_pos (div_pos one_pos hlog2_pos)
  have h4 : 1 / Real.log 2 ≤ 1 / (Real.log 2) ^ 2 := by
    rw [div_le_div_iff₀ hlog2_pos (sq_pos_of_pos hlog2_pos), sq, one_mul, one_mul]
    exact mul_le_of_le_one_left hlog2_pos.le hlog2_lt1.le
  linarith

/-- **PrimeLogToReciprocal**: `PrimeLogSumEquidist -> PrimesEquidistributedInAP`.

Uses discrete Abel summation to convert `sum (log p)/p` equidistribution
into `sum 1/p` equidistribution. -/
theorem prime_log_to_reciprocal_proved : PrimeLogToReciprocal := by
  intro hPLS q a hq hcop
  obtain ⟨C, hC_pos, hC_bound⟩ := hPLS q a hq hcop
  set φq := (Nat.totient q : ℝ) with hφq_def
  have hφq_pos : 0 < φq := by
    show (0 : ℝ) < (Nat.totient q : ℝ)
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set C' := C / Real.log 2 + C / Real.log 3 + (1 + 2 / (Real.log 2) ^ 2) / φq + 1 + 1
    with hC'_def
  refine ⟨C', by positivity, ?_⟩
  intro x hx
  set m := Nat.floor x with hm_def
  have hm3 : 3 ≤ m := by rw [hm_def]; exact Nat.le_floor hx
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have floor_nat : ∀ k : ℕ, Nat.floor (k : ℝ) = k := Nat.floor_natCast
  -- S(k) bound at naturals
  have hS_nat : ∀ k : ℕ, 2 ≤ k →
      |∑ p ∈ ((Icc 2 k).filter Nat.Prime).filter (fun p => p % q = a % q),
        Real.log p / p - Real.log (k : ℝ) / φq| ≤ C := by
    intro k hk; have := hC_bound k (by exact_mod_cast hk); rwa [floor_nat] at this
  set PCS : ℕ → Finset ℕ := fun n =>
    ((Icc 2 n).filter Nat.Prime).filter (fun p => p % q = a % q) with hPCS_def
  set S' : ℕ → ℝ := fun j => ∑ p ∈ PCS j, Real.log p / p with hS'_def
  -- Phase 1: Integer bound using Abel summation
  suffices habel_int : ∀ (m' : ℕ), 3 ≤ m' →
      |∑ p ∈ PCS m', (1 : ℝ) / p - Real.log (Real.log (m' : ℝ)) / φq| ≤
        C / Real.log 2 + C / Real.log 3 + (1 + 2 / (Real.log 2) ^ 2) / φq by
    -- Phase 2: Extend to real x using loglog_floor_close
    show |∑ p ∈ ((Icc 2 (⌊x⌋₊)).filter Nat.Prime).filter (fun p => p % q = a % q),
        (1 : ℝ) / p - Real.log (Real.log x) / φq| ≤ C'
    change |∑ p ∈ PCS m, (1 : ℝ) / p - Real.log (Real.log x) / φq| ≤ C'
    calc |∑ p ∈ PCS m, (1 : ℝ) / p - Real.log (Real.log x) / φq|
        ≤ |∑ p ∈ PCS m, (1 : ℝ) / p - Real.log (Real.log (m : ℝ)) / φq| +
          |Real.log (Real.log (m : ℝ)) / φq - Real.log (Real.log x) / φq| := by
            rw [show ∑ p ∈ PCS m, (1 : ℝ) / p - Real.log (Real.log x) / φq =
              (∑ p ∈ PCS m, (1 : ℝ) / p - Real.log (Real.log (m : ℝ)) / φq) +
              (Real.log (Real.log (m : ℝ)) / φq - Real.log (Real.log x) / φq) from by ring]
            exact abs_add_le _ _
      _ ≤ (C / Real.log 2 + C / Real.log 3 + (1 + 2 / (Real.log 2) ^ 2) / φq) +
          1 / φq := by
            apply _root_.add_le_add
            · exact habel_int m hm3
            · rw [← sub_div, abs_div, abs_of_pos hφq_pos]
              exact div_le_div_of_nonneg_right
                (by rw [abs_sub_comm]; exact loglog_floor_close hm3 hmx (Nat.lt_floor_add_one x))
                hφq_pos.le
      _ ≤ C' := by
            rw [hC'_def]
            have hφq_ge1 : (1 : ℝ) ≤ φq := by
              show (1 : ℝ) ≤ (Nat.totient q : ℝ)
              exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
            linarith [(div_le_one₀ hφq_pos).mpr hφq_ge1]
  -- Prove the integer bound
  intro m' hm'
  have hm'2 : 2 ≤ m' := by omega
  have hm'1 : (1 : ℝ) < m' := by exact_mod_cast (show 1 < m' by omega)
  have hlogm'_pos : 0 < Real.log (m' : ℝ) := Real.log_pos hm'1
  rw [abel_filtered_sum q a m' hm'2]
  set σ := ∑ j ∈ Ico 2 m',
    (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) / Real.log ((j : ℝ) + 1)
  set error_rem := ∑ j ∈ Ico 2 m',
    (S' j - Real.log (j : ℝ) / φq) *
    (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1))
  -- The remainder decomposes as sigma/phi(q) + error_rem
  have remainder_decomp :
      ∑ j ∈ Ico 2 m', S' j * (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) =
      σ / φq + error_rem := by
    have hstep : ∀ j ∈ Ico 2 m',
        S' j * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) =
        (Real.log (↑j + 1) - Real.log ↑j) / Real.log (↑j + 1) / φq +
        (S' j - Real.log ↑j / φq) * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have : S' j * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) =
          Real.log ↑j / φq * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) +
          (S' j - Real.log ↑j / φq) *
            (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) := by ring
      rw [this, div_mul_eq_mul_div, main_term_alg hj.1]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_div]
  -- Bound the error term
  have error_bound : |error_rem| ≤ C / Real.log 2 := by
    calc |error_rem|
        ≤ ∑ j ∈ Ico 2 m', |(S' j - Real.log (j : ℝ) / φq) *
            (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Ico 2 m', |S' j - Real.log (j : ℝ) / φq| *
            (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) := by
          apply Finset.sum_congr rfl; intro j hj
          rw [Finset.mem_Ico] at hj
          rw [abs_mul, abs_of_nonneg (inv_log_diff_nonneg hj.1)]
      _ ≤ ∑ j ∈ Ico 2 m', C *
            (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) :=
          Finset.sum_le_sum fun j hj => by
            rw [Finset.mem_Ico] at hj
            exact mul_le_mul_of_nonneg_right (hS_nat j hj.1) (inv_log_diff_nonneg hj.1)
      _ = C * (1 / Real.log 2 - 1 / Real.log (m' : ℝ)) := by
          rw [← Finset.mul_sum, sum_inv_log_telescope m' hm'2]
      _ ≤ C * (1 / Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ hC_pos.le
          linarith [div_nonneg (by linarith : (0:ℝ) ≤ 1) hlogm'_pos.le]
      _ = C / Real.log 2 := by ring
  -- Bound S(m')/log(m') - 1/phi(q)
  have s_over_log_bound :
      |S' m' * (1 / Real.log (m' : ℝ)) - 1 / φq| ≤ C / Real.log 3 := by
    rw [show S' m' * (1 / Real.log (m' : ℝ)) - 1 / φq =
      (S' m' - Real.log (m' : ℝ) / φq) / Real.log (m' : ℝ) from by field_simp,
      abs_div, abs_of_pos hlogm'_pos]
    have hlog3_le : Real.log 3 ≤ Real.log (m' : ℝ) :=
      Real.log_le_log (by norm_num : (0:ℝ) < 3) (by exact_mod_cast (show 3 ≤ m' by omega))
    calc |S' m' - Real.log ↑m' / φq| / Real.log ↑m'
        ≤ C / Real.log ↑m' :=
          div_le_div_of_nonneg_right (hS_nat m' hm'2) hlogm'_pos.le
      _ ≤ C / Real.log 3 :=
          div_le_div_of_nonneg_left hC_pos.le hlog3_pos hlog3_le
  -- Use main_sum_sandwich for sigma
  obtain ⟨hσ_lower, hσ_upper⟩ := main_sum_sandwich m' hm'
  have sigma_bound :
      |σ / φq - (Real.log (Real.log (m' : ℝ)) - Real.log (Real.log 2)) / φq| ≤
      1 / (Real.log 2) ^ 2 / φq := by
    rw [← sub_div, abs_div, abs_of_pos hφq_pos]
    apply div_le_div_of_nonneg_right _ hφq_pos.le
    rw [show σ - (Real.log (Real.log ↑m') - Real.log (Real.log 2)) =
      -(Real.log (Real.log ↑m') - Real.log (Real.log 2) - σ) from by ring,
      abs_neg, abs_of_nonneg hσ_lower]
    exact hσ_upper
  -- Assemble via triangle inequality
  have key_eq :
      S' m' * (1 / Real.log ↑m') + (σ / φq + error_rem) -
        Real.log (Real.log ↑m') / φq =
      (S' m' * (1 / Real.log ↑m') - 1 / φq) +
      (σ / φq - (Real.log (Real.log ↑m') - Real.log (Real.log 2)) / φq) +
      error_rem +
      (1 - Real.log (Real.log 2)) / φq := by ring
  rw [remainder_decomp, key_eq]
  set a_term := S' m' * (1 / Real.log ↑m') - 1 / φq
  set b_term := σ / φq - (Real.log (Real.log ↑m') - Real.log (Real.log 2)) / φq
  set c_term := error_rem
  set d_term := (1 - Real.log (Real.log 2)) / φq
  have hd_bound : |d_term| ≤ (1 + 1 / (Real.log 2) ^ 2) / φq := by
    simp only [d_term]
    rw [abs_div, abs_of_pos hφq_pos]
    exact div_le_div_of_nonneg_right loglog2_bound hφq_pos.le
  have tri := abs_add_le a_term b_term
  have tri2 := abs_add_le (a_term + b_term) c_term
  have tri3 := abs_add_le (a_term + b_term + c_term) d_term
  linarith [s_over_log_bound, sigma_bound, error_bound, hd_bound,
    show C / Real.log 3 + 1 / (Real.log 2) ^ 2 / φq + (C / Real.log 2) +
        (1 + 1 / (Real.log 2) ^ 2) / φq =
      C / Real.log 2 + C / Real.log 3 + (1 + 2 / (Real.log 2) ^ 2) / φq from by ring]

end PrimeLogToReciprocal

/-! ### Full WPNT -> PrimesEquidist chain -/

/-- The full chain `WeightedPNTinAP -> PrimesEquidistributedInAP`,
    via `PrimePowerStripping` and `PrimeLogToReciprocal`. -/
theorem wpnt_implies_primes_equidist_proved :
    WeightedPNTinAP → PrimesEquidistributedInAP :=
  wpnt_implies_primes_equidist prime_power_stripping_proved prime_log_to_reciprocal_proved

/-- Both sub-results of the WPNT -> PrimesEquidist chain are proved:
    `PrimePowerStripping` (OneSidedTauberian.lean) and
    `PrimeLogToReciprocal` (this file). -/
theorem ant_chain_both_proved :
    (PrimePowerStripping) ∧ (PrimeLogToReciprocal) ∧
    (WeightedPNTinAP → PrimesEquidistributedInAP) :=
  ⟨prime_power_stripping_proved, prime_log_to_reciprocal_proved,
   wpnt_implies_primes_equidist_proved⟩

end IK
