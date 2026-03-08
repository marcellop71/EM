import EM.OneSidedTauberian

/-!
# PrimeLogToReciprocal: Abel summation from (log p)/p to 1/p

This file provides infrastructure for `PrimeLogToReciprocal`:
that `PrimeLogSumEquidist` implies `PrimesEquidistributedInAP`.

## Proved infrastructure

- `hasDerivAt_log_log`: derivative of `log(log(t))` is `1/(t·log(t))`
- `hasDerivAt_neg_inv_log`: derivative of `-(log t)⁻¹` is `(t·(log t)²)⁻¹`
- `integral_inv_mul_log`: `∫_a^b 1/(t·log t) dt = log(log b) - log(log a)` (FTC)
- `integral_inv_mul_log_sq`: `∫_a^b 1/(t·(log t)²) dt = 1/log(a) - 1/log(b)` (FTC)
- `log_ratio_le`: `(log b - log a)/log b ≤ log(log b) - log(log a)` (from `log x ≤ x-1`)
- `loglog_le_ratio`: `log(log b) - log(log a) ≤ (log b - log a)/log a` (converse)
- `prime_log_to_reciprocal_proved`: PrimeLogSumEquidist → PrimesEquidistributedInAP
-/

noncomputable section
open Classical

namespace IK

open Nat Finset BigOperators Filter MeasureTheory

/-! ### Derivative computations -/

/-- `HasDerivAt (fun t => log (log t)) (1 / (t * log t)) t` for `t > 1`. -/
theorem hasDerivAt_log_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => Real.log (Real.log t)) (1 / (t * Real.log t)) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hd := (Real.hasDerivAt_log hlt).comp t (Real.hasDerivAt_log ht0)
  simp only [Function.comp_def] at hd
  convert hd using 1; field_simp

/-- `HasDerivAt (fun t => -(log t)⁻¹) ((t * (log t)^2)⁻¹) t` for `t > 1`. -/
theorem hasDerivAt_neg_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) ((t * (Real.log t) ^ 2)⁻¹) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hd' := ((Real.hasDerivAt_log ht0).inv hlt).neg
  convert hd' using 1; field_simp

/-! ### Integral computations via FTC -/

/-- `∫ t in a..b, 1/(t * log t) = log(log b) - log(log a)` for `1 < a ≤ b`. -/
theorem integral_inv_mul_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (1 / (t * Real.log t)) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  have hmem : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht; rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t)) MeasureTheory.MeasureSpace.volume a b := by
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

/-- `∫ t in a..b, (t * (log t)^2)⁻¹ = (log a)⁻¹ - (log b)⁻¹` for `1 < a ≤ b`. -/
theorem integral_inv_mul_log_sq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (t * (Real.log t) ^ 2)⁻¹ =
      (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hmem : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht; rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]
  have hint : IntervalIntegrable (fun t => (t * (Real.log t) ^ 2)⁻¹) MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    have heq : (fun t => (t * (Real.log t) ^ 2)⁻¹) = (fun t => 1 / (t * (Real.log t) ^ 2)) := by
      ext t; rw [one_div]
    rw [heq]
    apply ContinuousOn.div continuousOn_const
    · exact ContinuousOn.mul continuousOn_id
        ((Real.continuousOn_log.mono (fun t ht =>
          ne_of_gt (by linarith [ht.1]))).pow 2)
    · intro t ht
      exact mul_ne_zero (ne_of_gt (by linarith [ht.1]))
        (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [ht.1]))))
  have key : ∫ t in a..b, (t * (Real.log t) ^ 2)⁻¹ =
      -(Real.log b)⁻¹ - (-(Real.log a)⁻¹) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_neg_inv_log (hmem t ht)) hint
  linarith

/-! ### Key inequalities from log x ≤ x - 1 -/

/-- `(log b - log a) / log b ≤ log(log b) - log(log a)` for `1 < a ≤ b`.
    From `log(x) ≤ x - 1` applied to `x = log(a)/log(b)`. -/
theorem log_ratio_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (Real.log b - Real.log a) / Real.log b ≤
    Real.log (Real.log b) - Real.log (Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogb : 0 < Real.log b := Real.log_pos (lt_of_lt_of_le ha hab)
  -- log(log a / log b) ≤ log a / log b - 1 (from log x ≤ x - 1)
  have h := Real.log_le_sub_one_of_pos (div_pos hloga hlogb)
  -- log(log a / log b) = log(log a) - log(log b)
  rw [Real.log_div hloga.ne' hlogb.ne'] at h
  -- So log(log a) - log(log b) ≤ log a / log b - 1
  -- i.e., 1 - log a / log b ≤ log(log b) - log(log a)
  -- and (log b - log a) / log b = 1 - log a / log b
  have hrw : (Real.log b - Real.log a) / Real.log b = 1 - Real.log a / Real.log b := by
    rw [sub_div, div_self hlogb.ne']
  rw [hrw]
  linarith

/-- `log(log b) - log(log a) ≤ (log b - log a) / log a` for `1 < a ≤ b`.
    From `log(x) ≤ x - 1` applied to `x = log(b)/log(a)`. -/
theorem loglog_le_ratio {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Real.log (Real.log b) - Real.log (Real.log a) ≤
    (Real.log b - Real.log a) / Real.log a := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogb : 0 < Real.log b := Real.log_pos (lt_of_lt_of_le ha hab)
  -- log(log b / log a) ≤ log b / log a - 1 (from log x ≤ x - 1)
  have h := Real.log_le_sub_one_of_pos (div_pos hlogb hloga)
  -- log(log b / log a) = log(log b) - log(log a)
  rw [Real.log_div hlogb.ne' hloga.ne'] at h
  -- So log(log b) - log(log a) ≤ log b / log a - 1 = (log b - log a) / log a
  have hrw : Real.log b / Real.log a - 1 = (Real.log b - Real.log a) / Real.log a := by
    rw [sub_div, div_self hloga.ne']
  linarith

/-! ### PrimeLogToReciprocal via discrete Abel summation -/

section PrimeLogToReciprocal

/-- `log(1+y) ≤ y` for `y ≥ 0`, via `log x ≤ x - 1`. -/
private theorem log_one_add_le {y : ℝ} (hy : 0 ≤ y) :
    Real.log (1 + y) ≤ y := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + y)
  linarith

/-- For `m ≤ x < m + 1` with `m ≥ 3`, `|loglog x - loglog m| ≤ 1`. -/
private theorem loglog_floor_close {x : ℝ} {m : ℕ} (hm : 3 ≤ m)
    (hmx : (m : ℝ) ≤ x) (hxm : x < m + 1) :
    |Real.log (Real.log x) - Real.log (Real.log (m : ℝ))| ≤ 1 := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have h_lower : Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogm (Real.log_le_log hm_pos hmx)
  rw [abs_of_nonneg (by linarith)]
  have step1 : Real.log (Real.log ((m : ℝ) + 1)) - Real.log (Real.log (m : ℝ)) ≤
      (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) / Real.log (m : ℝ) :=
    loglog_le_ratio hm1 (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
  have step2 : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / m := by
    rw [← Real.log_div (by positivity) hm_pos.ne']
    have heq : ((m : ℝ) + 1) / m = 1 + 1 / m := by field_simp
    rw [heq]
    exact log_one_add_le (by positivity)
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

/-- Discrete Abel summation (summation by parts).
    `∑_{k ∈ Ico lo (hi+1)} a(k)·g(k) = A(hi)·g(hi) + ∑_{j ∈ Ico lo hi} A(j)·(g(j)-g(j+1))`
    where `A(j) = ∑_{k ∈ Ico lo (j+1)} a(k)`. -/
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
    · -- Inductive step: hi = n + 1
      have h1 : lo ≤ n + 1 := by omega
      -- Peel LHS sum: Ico lo (n+1+1) → Ico lo (n+1) + top
      have lhs_eq := Finset.sum_Ico_succ_top h1 (fun k => a k * g k)
      have sum_eq := Finset.sum_Ico_succ_top h1 a
      have rhs_eq := Finset.sum_Ico_succ_top hlon
        (fun j => (∑ k ∈ Ico lo (j + 1), a k) * (g j - g (j + 1)))
      rw [lhs_eq, ih hlon, sum_eq, rhs_eq]
      ring
    · -- lo > n, so lo = n + 1
      have hlon1 : lo = n + 1 := by omega
      subst hlon1
      simp only [Finset.Ico_self, Finset.sum_empty]
      rw [Nat.Ico_succ_singleton]; simp [Finset.sum_singleton]

/-- `log(k+1) - log(k) ≤ 1/k` for `k ≥ 1`. From `log(1+1/k) ≤ 1/k`. -/
private theorem log_succ_sub_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) ≤ 1 / k := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [← Real.log_div (by positivity) hk_pos.ne']
  have : ((k : ℝ) + 1) / k = 1 + 1 / k := by field_simp
  rw [this]
  exact log_one_add_le (by positivity)

/-- Telescoping: `∑_{k=2}^{m-1} (1/log(k) - 1/log(k+1)) = 1/log(2) - 1/log(m)` for m ≥ 2. -/
private theorem sum_inv_log_telescope (m : ℕ) (hm : 2 ≤ m) :
    ∑ k ∈ Ico 2 m, (1 / Real.log (k : ℝ) - 1 / Real.log ((k : ℝ) + 1)) =
    1 / Real.log 2 - 1 / Real.log (m : ℝ) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn2 : n = 1
    · subst hn2
      rw [show Ico 2 2 = ∅ from by decide, Finset.sum_empty]
      push_cast; ring
    · have hn : 2 ≤ n := by omega
      rw [Finset.sum_Ico_succ_top hn]
      rw [ih hn]; push_cast; ring

/-- Each term of the main sum satisfies the sandwich:
    `(log(k+1) - log(k))/log(k+1) ≤ loglog(k+1) - loglog(k)` for `k ≥ 2`.
    This is `log_ratio_le` instantiated at naturals. -/
private theorem main_term_upper {k : ℕ} (hk : 2 ≤ k) :
    (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) ≤
    Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  exact log_ratio_le hk1 (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)

/-- The correction between `loglog(k+1) - loglog(k)` and `(log(k+1)-log(k))/log(k+1)`
    is bounded by `1/(k² · (log 2)²)` for `k ≥ 2`. -/
private theorem main_term_correction {k : ℕ} (hk : 2 ≤ k) :
    Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
      (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) ≤
    1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hk_pos : (0 : ℝ) < k := by linarith
  have hlogk : (0 : ℝ) < Real.log k := Real.log_pos hk1
  have hlogk1 : (0 : ℝ) < Real.log ((k : ℝ) + 1) :=
    Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Upper bound on loglog(k+1) - loglog(k): (log(k+1)-log(k))/log(k)
  have hub := loglog_le_ratio hk1 (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
  -- So the correction ≤ (log(k+1)-log(k))/log(k) - (log(k+1)-log(k))/log(k+1)
  --    = (log(k+1)-log(k)) · (1/log(k) - 1/log(k+1))
  --    = (log(k+1)-log(k))² / (log(k) · log(k+1))
  set δ := Real.log ((k : ℝ) + 1) - Real.log k with hδ_def
  have hδ_nonneg : 0 ≤ δ := by
    have : Real.log ↑k ≤ Real.log (↑k + 1) :=
      Real.log_le_log hk_pos (by linarith)
    linarith [hδ_def]
  have hδ_le : δ ≤ 1 / k := log_succ_sub_le (by omega : 1 ≤ k)
  -- correction ≤ δ/log(k) - δ/log(k+1) = δ² / (log(k) · log(k+1))
  have step1 : Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
        (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1)
      ≤ δ / Real.log k - δ / Real.log ((k : ℝ) + 1) := by linarith
  have step2 : δ / Real.log k - δ / Real.log ((k : ℝ) + 1) =
      δ ^ 2 / (Real.log k * Real.log ((k : ℝ) + 1)) := by
    rw [div_sub_div _ _ hlogk.ne' hlogk1.ne']
    rw [hδ_def]; ring
  have hlog2_le_logk : Real.log 2 ≤ Real.log ↑k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ k by omega))
  have hlog2_le_logk1 : Real.log 2 ≤ Real.log (↑k + 1) :=
    Real.log_le_log (by norm_num) (by
      have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      linarith)
  have step3 : δ ^ 2 / (Real.log k * Real.log ((k : ℝ) + 1)) ≤
      (1 / k) ^ 2 / (Real.log 2 * Real.log 2) := by
    -- numerator: δ² ≤ (1/k)²
    have hnum : δ ^ 2 ≤ (1 / k) ^ 2 := pow_le_pow_left₀ hδ_nonneg hδ_le 2
    -- denominator: log 2 * log 2 ≤ log k * log(k+1)
    have hden : Real.log 2 * Real.log 2 ≤ Real.log k * Real.log ((k : ℝ) + 1) :=
      mul_le_mul hlog2_le_logk hlog2_le_logk1 hlog2.le hlogk.le
    calc δ ^ 2 / (Real.log ↑k * Real.log (↑k + 1))
        ≤ (1 / ↑k) ^ 2 / (Real.log ↑k * Real.log (↑k + 1)) :=
          div_le_div_of_nonneg_right hnum (mul_nonneg hlogk.le hlogk1.le)
      _ ≤ (1 / ↑k) ^ 2 / (Real.log 2 * Real.log 2) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hlog2 hlog2) hden
  linarith [step1, step2, step3, show (1 / (k : ℝ)) ^ 2 / (Real.log 2 * Real.log 2) =
      1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2) from by ring]

/-- Telescope identity: `∑_{k=2}^{m-1} (1/(k-1) - 1/k) = 1 - 1/(m-1)` for `m ≥ 3`. -/
private theorem sum_telescope_inv (m : ℕ) (hm : 3 ≤ m) :
    ∑ k ∈ Ico 2 m, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 - 1 / ((m : ℝ) - 1) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 2
    · subst hn
      rw [show Ico 2 3 = {2} from by decide, Finset.sum_singleton]
      push_cast; norm_num
    · have hn3 : 3 ≤ n := by omega
      rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n)]
      rw [ih hn3]
      -- Goal: 1 - 1/(↑n-1) + (1/(↑(n+1)-1-1) - 1/(↑(n+1)-1)) = 1 - 1/(↑(n+1)-1-1)
      -- = 1 - 1/(↑n-1) + (1/(↑n-1) - 1/↑n) = 1 - 1/↑n
      -- But the RHS is 1 - 1/(↑(n+1) - 1) = 1 - 1/↑n
      -- The last summand is 1/(↑n - 1) - 1/↑n
      -- So: (1 - 1/(↑n-1)) + (1/(↑n-1) - 1/↑n) = 1 - 1/↑n. True by ring.
      -- Issue: Lean represents ↑(n+1) as ↑n + 1, and ↑(n+1) - 1 = ↑n
      -- Let's help with simp lemmas
      have : (↑(n + 1) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
      rw [this]
      have : (n : ℝ) - 1 - 1 = (n : ℝ) - 2 := by ring
      -- The term at index n is: 1/(↑n - 1) - 1/↑n (when the target is ↑m - 1 for m = n+1)
      -- But wait, m = n + 1 in the outer statement, so Ico 2 (n+1) and the peeled term
      -- is at k = n: 1/(↑n - 1) - 1/↑n
      -- After rw [ih hn3]: goal is
      --   1 - 1/(↑n - 1) + (1/(↑n - 1) - 1/↑n) = 1 - 1/↑n
      -- This is linarith-provable
      linarith

/-- `∑_{k=2}^{m-1} 1/(k*(k-1)) ≤ 1` by telescoping. -/
private theorem sum_inv_mul_pred_le (m : ℕ) :
    ∑ k ∈ Ico 2 m, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 := by
  -- Partial fractions: 1/(k(k-1)) = 1/(k-1) - 1/k
  have key : ∀ k ∈ Ico 2 m, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) =
      1 / ((k : ℝ) - 1) - 1 / k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk2 : 2 ≤ k := hk.1
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      linarith
    rw [div_sub_div _ _ hk1_pos.ne' hk_pos.ne']
    congr 1
    · ring
    · ring
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

/-- `∑_{k=2}^{m-1} 1/k² ≤ 1` (by comparison with 1/(k(k-1)) telescope). -/
private theorem sum_inv_sq_le (m : ℕ) :
    ∑ k ∈ Ico 2 m, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by
  calc ∑ k ∈ Ico 2 m, (1 : ℝ) / (k : ℝ) ^ 2
      ≤ ∑ k ∈ Ico 2 m, 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hk_pos : (0 : ℝ) < k := by
          have : 2 ≤ k := hk.1; exact_mod_cast (show 0 < k by omega)
        have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
          linarith
        -- 1/k² ≤ 1/(k*(k-1)) because k*(k-1) ≤ k²
        rw [div_le_div_iff₀ (sq_pos_of_pos hk_pos) (mul_pos hk_pos hk1_pos)]
        rw [one_mul, one_mul, sq]
        exact mul_le_mul_of_nonneg_left (by linarith) hk_pos.le
    _ ≤ 1 := sum_inv_mul_pred_le m

/-- The main sum `∑_{k=2}^{m-1} (log(k+1)-log(k))/log(k+1)` is within `1/(log 2)²`
    of `loglog(m) - loglog(2)`. More precisely:
    `0 ≤ loglog(m) - loglog(2) - ∑ ≤ 1/(log 2)²`. -/
private theorem main_sum_sandwich (m : ℕ) (hm : 3 ≤ m) :
    let σ := ∑ k ∈ Ico 2 m,
      (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1)
    0 ≤ Real.log (Real.log m) - Real.log (Real.log 2) - σ ∧
    Real.log (Real.log m) - Real.log (Real.log 2) - σ ≤ 1 / (Real.log 2) ^ 2 := by
  intro σ
  constructor
  · -- Lower bound: σ ≤ loglog(m) - loglog(2) by telescoping main_term_upper
    have : σ ≤ ∑ k ∈ Ico 2 m,
        (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact main_term_upper (by omega)
    have htel : ∑ k ∈ Ico 2 m,
        (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) =
        Real.log (Real.log m) - Real.log (Real.log 2) := by
      -- Telescope by induction on m
      have : ∀ (m' : ℕ), 3 ≤ m' → ∑ k ∈ Ico 2 m',
          (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) =
          Real.log (Real.log ↑m') - Real.log (Real.log 2) := by
        intro m' hm'
        induction m' with
        | zero => omega
        | succ n ih =>
          by_cases hn3 : n = 2
          · subst hn3
            rw [show Ico 2 3 = {2} from by decide, Finset.sum_singleton]
            push_cast; ring
          · have hn : 3 ≤ n := by omega
            rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n)]
            rw [ih hn]; push_cast; ring
      exact this m hm
    linarith
  · -- Upper bound: each correction ≤ 1/(k² · (log 2)²), and ∑ 1/k² ≤ 1
    have hcorr : ∀ k ∈ Ico 2 m,
        Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
          (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1) ≤
        1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact main_term_correction (by omega)
    -- The total correction = loglog(m) - loglog(2) - σ
    -- It equals ∑ [loglog(k+1) - loglog(k) - (log(k+1)-log(k))/log(k+1)]
    have htel_eq : Real.log (Real.log m) - Real.log (Real.log 2) - σ =
        ∑ k ∈ Ico 2 m, (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
          (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1)) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      -- Telescope the loglog sum (same as htel above)
      have : ∀ (m' : ℕ), 3 ≤ m' → ∑ k ∈ Ico 2 m',
          (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k)) =
          Real.log (Real.log ↑m') - Real.log (Real.log 2) := by
        intro m' hm'
        induction m' with
        | zero => omega
        | succ n ih =>
          by_cases hn3 : n = 2
          · subst hn3
            rw [show Ico 2 3 = {2} from by decide, Finset.sum_singleton]
            push_cast; ring
          · have hn : 3 ≤ n := by omega
            rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ n)]
            rw [ih hn]; push_cast; ring
      exact (this m hm).symm
    rw [htel_eq]
    calc ∑ k ∈ Ico 2 m, (Real.log (Real.log ((k : ℝ) + 1)) - Real.log (Real.log k) -
            (Real.log ((k : ℝ) + 1) - Real.log k) / Real.log ((k : ℝ) + 1))
        ≤ ∑ k ∈ Ico 2 m, (1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2)) :=
          Finset.sum_le_sum hcorr
      _ = (∑ k ∈ Ico 2 m, (1 : ℝ) / (k : ℝ) ^ 2) / (Real.log 2) ^ 2 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ 1 / (Real.log 2) ^ 2 := by
          apply div_le_div_of_nonneg_right (sum_inv_sq_le m)
          exact sq_nonneg _

/-! #### Abel summation applied to prime reciprocal sums -/

/-- Abel summation applied to the indicator coefficient sequence for primes in a class.
    Expresses `∑ 1/p` in terms of the partial sums `∑ (log p)/p` and the
    telescoping differences `1/log(j) - 1/log(j+1)`. -/
private theorem abel_filtered_sum (q : ℕ) (a_mod : ℕ) (m : ℕ) (hm : 2 ≤ m) :
    let PCS : ℕ → Finset ℕ := fun n =>
      ((Icc 2 n).filter Nat.Prime).filter (fun p => p % q = a_mod % q)
    ∑ p ∈ PCS m, (1 : ℝ) / p =
      (∑ p ∈ PCS m, Real.log p / p) * (1 / Real.log m) +
      ∑ j ∈ Ico 2 m,
        (∑ p ∈ PCS j, Real.log p / p) *
        (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) := by
  intro PCS
  -- For each prime p in PCS(m), 1/p = (log p/p) * (1/log p)
  -- We use discrete Abel summation via a direct algebraic route
  -- instead of going through indicator functions
  -- Key insight: ∑_{p ∈ PCS(m)} 1/p = ∑_{p ∈ PCS(m)} (log p / p) * (1/log p)
  -- Step 1: Split ∑_{p ∈ PCS(m)} (log p / p) * (1/log p) using Abel
  -- Define partial sums S(j) = ∑_{p ∈ PCS(j)} (log p)/p
  -- Then ∑_{p ∈ PCS(m)} 1/p = S(m)/log(m) + ∑_{j=2}^{m-1} S(j) * (1/log(j) - 1/log(j+1))

  -- We prove this by constructing indicator functions on Icc 2 m
  -- af(k) = (log k)/k if k ∈ PCS(m), else 0
  -- gf(k) = 1/log(k)
  -- Then ∑_k af(k)*gf(k) = ∑_{p ∈ PCS(m)} 1/p

  -- Direct proof: use Finset.sum_comm-style manipulation
  -- Actually, for simplicity, let's use a direct telescoping argument
  -- S(m)/log(m) + ∑ S(j)·Δg(j) = ∑ 1/p is equivalent to Abel's identity

  -- LHS/RHS match by Abel identity applied to the prime counting sets
  -- This is purely algebraic given the PCS definition

  -- For each j ∈ [2, m), let D(j) = PCS(j+1) \ PCS(j) = primes p with p = j+1 and p in class
  -- Then S(j+1) - S(j) = ∑_{p ∈ D(j)} (log p)/p
  -- And ∑_{p ∈ PCS(m)} 1/p = ∑_{j=2}^{m} (∑_{p ∈ D(j-1)} 1/p)

  -- For now, prove by sorry-free but indirect route:
  -- Express both sides in terms of the same partial sums and show equality

  -- We'll use a clean indicator-free approach
  -- For each k ∈ Icc 2 m that is in PCS(m):
  --   1/k = (log k / k) * (1/log k)
  -- Apply discrete_abel with a(k) = (log k)/k · 1_{k ∈ PCS(m)}, g(k) = 1/log(k)

  -- Set up the indicator coefficient
  set af : ℕ → ℝ := fun k => if k ∈ PCS m then Real.log k / k else 0
  set gf : ℕ → ℝ := fun k => 1 / Real.log (k : ℝ)
  -- Abel identity
  have habel := discrete_abel af gf 2 m hm

  -- Key: Icc 2 m = Ico 2 (m+1)
  have icc_ico : Icc 2 m = Ico 2 (m + 1) := by
    ext k; simp [Finset.mem_Icc, Finset.mem_Ico]

  -- LHS of Abel = ∑ 1/p
  have lhs_eq : ∑ k ∈ Ico 2 (m + 1), af k * gf k = ∑ p ∈ PCS m, (1 : ℝ) / p := by
    rw [icc_ico.symm]
    -- Split into PCS(m) part and non-PCS(m) part
    have hsub : PCS m ⊆ Icc 2 m := by
      intro p hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 m) (fun k => k ∈ PCS m)]
    have hzero : ∑ k ∈ (Icc 2 m).filter (fun k => k ∉ PCS m), af k * gf k = 0 := by
      apply Finset.sum_eq_zero; intro k hk
      simp only [Finset.mem_filter] at hk
      simp only [af, if_neg hk.2, zero_mul]
    rw [hzero, add_zero]
    have hfilter : (Icc 2 m).filter (fun k => k ∈ PCS m) = PCS m := by
      ext k; simp only [Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hsub h, h⟩⟩
    rw [hfilter]
    apply Finset.sum_congr rfl; intro k hk
    simp only [af, gf, if_pos hk]
    have hk_prime : Nat.Prime k :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk_prime.pos
    have hlogk : Real.log (k : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hk_prime.one_lt))
    field_simp

  -- PCS monotonicity: j ≤ m → PCS j ⊆ PCS m
  have pcs_mono : ∀ j, j ≤ m → PCS j ⊆ PCS m := by
    intro j hjm p hp
    simp only [Finset.mem_filter, Finset.mem_Icc, PCS] at hp ⊢
    exact ⟨⟨⟨hp.1.1.1, hp.1.1.2.trans hjm⟩, hp.1.2⟩, hp.2⟩

  -- PCS is contained in Icc
  have pcs_sub_icc : ∀ j, PCS j ⊆ Icc 2 j := by
    intro j p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

  -- ∑ af(k) over Ico 2 (j+1) = S(j)
  have sum_af_eq : ∀ j, 2 ≤ j → j ≤ m →
      ∑ k ∈ Ico 2 (j + 1), af k = ∑ p ∈ PCS j, Real.log p / p := by
    intro j hj hjm
    -- Ico 2 (j+1) = Icc 2 j
    have icc_eq : Ico 2 (j + 1) = Icc 2 j := by
      ext k; simp [Finset.mem_Icc, Finset.mem_Ico]
    rw [icc_eq]
    -- Split Icc 2 j into PCS(j) and non-PCS(j)
    -- Key: k ∈ Icc 2 j, k ∈ PCS(m) iff k ∈ PCS(j) (since Icc 2 j ∩ PCS(m) = PCS(j))
    -- For k ∉ PCS(m), af(k) = 0
    -- For k ∈ PCS(m), af(k) = log k / k, and k ∈ Icc 2 j ∩ PCS(m) iff k ∈ PCS(j)
    trans ∑ p ∈ PCS j, af p
    · -- ∑_{Icc 2 j} af = ∑_{PCS(j)} af (zero outside PCS(m) ⊇ PCS(j))
      symm
      apply Finset.sum_subset (pcs_sub_icc j)
      intro k hk hk_not
      simp only [af]
      rw [if_neg]
      intro hk_mem
      exact hk_not (by
        simp only [Finset.mem_filter, Finset.mem_Icc, PCS] at hk_mem ⊢
        exact ⟨⟨⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2⟩, hk_mem.1.2⟩, hk_mem.2⟩)
    · -- ∑_{PCS(j)} af = ∑_{PCS(j)} log p / p
      apply Finset.sum_congr rfl; intro k hk
      simp only [af, if_pos (pcs_mono j hjm hk)]

  -- Assemble
  rw [lhs_eq] at habel; rw [habel]
  -- LHS: (∑ af) * gf m + ∑ (∑ af) * (gf j - gf (j+1))
  -- RHS: (∑ log p / p) * (1/log m) + ∑ (∑ log p / p) * (1/log j - 1/log(j+1))
  -- Use sum_af_eq to convert ∑ af to ∑ log p / p
  have eq1 : (∑ k ∈ Ico 2 (m + 1), af k) * gf m =
      (∑ p ∈ PCS m, Real.log p / p) * (1 / Real.log m) := by
    congr 1; exact sum_af_eq m hm le_rfl
  have eq2 : ∑ j ∈ Ico 2 m, (∑ k ∈ Ico 2 (j + 1), af k) * (gf j - gf (j + 1)) =
      ∑ j ∈ Ico 2 m, (∑ p ∈ PCS j, Real.log p / p) *
        (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) := by
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.mem_Ico] at hj
    rw [sum_af_eq j hj.1 hj.2.le]
    simp only [gf, Nat.cast_add, Nat.cast_one]
  rw [eq1, eq2]

/-- Key algebraic identity: `log(j) * (1/log(j) - 1/log(j+1)) =
    (log(j+1) - log(j))/log(j+1)` for `j ≥ 2`. -/
private theorem main_term_alg {j : ℕ} (hj : 2 ≤ j) :
    Real.log (j : ℝ) * (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) =
    (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) / Real.log ((j : ℝ) + 1) := by
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hlogj : Real.log (j : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hj1)
  have hlogj1 : Real.log ((j : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  field_simp

/-- Each term `1/log(j) - 1/log(j+1)` is nonneg for `j ≥ 2`. -/
private theorem inv_log_diff_nonneg {j : ℕ} (hj : 2 ≤ j) :
    0 ≤ 1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1) := by
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hlogj : 0 < Real.log (j : ℝ) := Real.log_pos hj1
  have hlogj1 : 0 < Real.log ((j : ℝ) + 1) := Real.log_pos (by linarith)
  rw [div_sub_div _ _ hlogj.ne' hlogj1.ne']
  apply div_nonneg
  · linarith [Real.log_le_log (by linarith : (0:ℝ) < j)
      (by linarith : (j:ℝ) ≤ (j:ℝ) + 1)]
  · exact mul_nonneg hlogj.le hlogj1.le

/-- Bound on `|1 - log(log 2)|`: since `log 2 < 1`, we have `log(log 2) < 0`,
    so `|1 - log(log 2)| = 1 - log(log 2) ≤ 1 + 1/(log 2)^2`. -/
private theorem loglog2_bound :
    |1 - Real.log (Real.log 2)| ≤ 1 + 1 / (Real.log 2) ^ 2 := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 2)]
    exact Real.exp_one_gt_d9.trans' (by norm_num)
  have hloglog2_neg : Real.log (Real.log 2) < 0 := by
    rw [Real.log_neg_iff hlog2_pos]; exact hlog2_lt1
  rw [show (1 : ℝ) - Real.log (Real.log 2) = 1 + (-Real.log (Real.log 2)) from by ring]
  rw [abs_of_pos (by linarith)]
  -- Need: -log(log 2) ≤ 1/(log 2)^2
  -- -log(log 2) = log(1/log 2)
  -- log(1/log 2) ≤ 1/log 2 - 1 (from log x ≤ x-1)
  -- 1/log 2 - 1 ≤ 1/log 2 ≤ 1/(log 2)^2 (since log 2 ≤ 1)
  suffices h : -Real.log (Real.log 2) ≤ 1 / (Real.log 2) ^ 2 by linarith
  have h1 : -Real.log (Real.log 2) = Real.log (1 / Real.log 2) := by
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) hlog2_pos.ne', Real.log_one, zero_sub]
  rw [h1]
  have h2 : Real.log (1 / Real.log 2) ≤ 1 / Real.log 2 - 1 :=
    Real.log_le_sub_one_of_pos (div_pos one_pos hlog2_pos)
  have h3 : 1 / Real.log 2 - 1 ≤ 1 / Real.log 2 := by linarith
  have h4 : 1 / Real.log 2 ≤ 1 / (Real.log 2) ^ 2 := by
    rw [div_le_div_iff₀ hlog2_pos (sq_pos_of_pos hlog2_pos)]
    rw [sq, one_mul, one_mul]
    exact mul_le_of_le_one_left hlog2_pos.le hlog2_lt1.le
  linarith

/-- `PrimeLogToReciprocal`: `PrimeLogSumEquidist → PrimesEquidistributedInAP`.

    Uses discrete Abel summation to convert `∑ (log p)/p` equidistribution
    into `∑ 1/p` equidistribution. -/
theorem prime_log_to_reciprocal_proved : PrimeLogToReciprocal := by
  intro hPLS q a hq hcop
  obtain ⟨C, hC_pos, hC_bound⟩ := hPLS q a hq hcop
  set φq := (Nat.totient q : ℝ) with hφq_def
  have hφq_pos : 0 < φq := by
    show (0 : ℝ) < (Nat.totient q : ℝ)
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  -- Generous bound constant
  set C' := C / Real.log 2 + C / Real.log 3 + (1 + 2 / (Real.log 2) ^ 2) / φq + 1 + 1
    with hC'_def
  refine ⟨C', by positivity, ?_⟩
  intro x hx
  set m := Nat.floor x with hm_def
  have hm3 : 3 ≤ m := by rw [hm_def]; exact Nat.le_floor hx
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have floor_nat : ∀ k : ℕ, Nat.floor (k : ℝ) = k := fun k => Nat.floor_natCast k
  -- S(k) bound at naturals: |S(k) - log(k)/φ(q)| ≤ C
  have hS_nat : ∀ k : ℕ, 2 ≤ k →
      |∑ p ∈ ((Icc 2 k).filter Nat.Prime).filter (fun p => p % q = a % q),
        Real.log p / p - Real.log (k : ℝ) / φq| ≤ C := by
    intro k hk
    have := hC_bound k (by exact_mod_cast hk)
    rwa [floor_nat] at this
  -- Abbreviation for the prime counting set
  set PCS : ℕ → Finset ℕ := fun n =>
    ((Icc 2 n).filter Nat.Prime).filter (fun p => p % q = a % q) with hPCS_def
  set S' : ℕ → ℝ := fun j => ∑ p ∈ PCS j, Real.log p / p with hS'_def
  -- Phase 1: Prove integer bound using Abel summation
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
            have : ∑ p ∈ PCS m, (1 : ℝ) / p - Real.log (Real.log x) / φq =
              (∑ p ∈ PCS m, (1 : ℝ) / p - Real.log (Real.log (m : ℝ)) / φq) +
              (Real.log (Real.log (m : ℝ)) / φq - Real.log (Real.log x) / φq) := by ring
            rw [this]; exact abs_add_le _ _
      _ ≤ (C / Real.log 2 + C / Real.log 3 + (1 + 2 / (Real.log 2) ^ 2) / φq) +
          1 / φq := by
            apply _root_.add_le_add
            · exact habel_int m hm3
            · rw [← sub_div, abs_div, abs_of_pos hφq_pos]
              apply div_le_div_of_nonneg_right _ hφq_pos.le
              rw [abs_sub_comm]
              exact loglog_floor_close hm3 hmx (Nat.lt_floor_add_one x)
      _ ≤ C' := by
            rw [hC'_def]
            have hφq_ge1 : (1 : ℝ) ≤ φq := by
              show (1 : ℝ) ≤ (Nat.totient q : ℝ)
              exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
            have : 1 / φq ≤ 1 := (div_le_one₀ hφq_pos).mpr hφq_ge1
            linarith
  -- Prove the integer bound
  intro m' hm'
  have hm'2 : 2 ≤ m' := by omega
  have hm'1 : (1 : ℝ) < m' := by exact_mod_cast (show 1 < m' by omega)
  have hm'_pos : (0 : ℝ) < m' := by linarith
  have hlogm'_pos : 0 < Real.log (m' : ℝ) := Real.log_pos hm'1
  -- Apply Abel summation identity
  have habel := abel_filtered_sum q a m' hm'2
  -- T(m') = S(m')/log(m') + ∑_{j=2}^{m'-1} S(j) · (1/log(j) - 1/log(j+1))
  rw [habel]
  -- Decompose remainder: ∑ S(j)·diff = (1/φq)·σ + error
  set σ := ∑ j ∈ Ico 2 m',
    (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) / Real.log ((j : ℝ) + 1)
  set error_rem := ∑ j ∈ Ico 2 m',
    (S' j - Real.log (j : ℝ) / φq) *
    (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1))
  -- The remainder decomposes as σ/φq + error_rem
  have remainder_decomp :
      ∑ j ∈ Ico 2 m', S' j * (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) =
      σ / φq + error_rem := by
    -- Split each term: S'(j) * diff = log(j)/φq * diff + (S'(j)-log(j)/φq) * diff
    -- The first part: log(j) * diff = (log(j+1)-log(j))/log(j+1) (main_term_alg)
    -- So: ∑ S'(j)*diff = ∑ [(log(j+1)-log j)/log(j+1)]/φq + ∑ (S'j-logj/φq)*diff
    --                   = σ/φq + error_rem
    have hstep : ∀ j ∈ Ico 2 m',
        S' j * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) =
        (Real.log (↑j + 1) - Real.log ↑j) / Real.log (↑j + 1) / φq +
        (S' j - Real.log ↑j / φq) * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have halg := main_term_alg hj.1
      have : S' j * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) =
          Real.log ↑j / φq * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) +
          (S' j - Real.log ↑j / φq) * (1 / Real.log ↑j - 1 / Real.log (↑j + 1)) := by ring
      rw [this, div_mul_eq_mul_div, halg]
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
            (1 / Real.log (j : ℝ) - 1 / Real.log ((j : ℝ) + 1)) := by
          apply Finset.sum_le_sum; intro j hj
          rw [Finset.mem_Ico] at hj
          exact mul_le_mul_of_nonneg_right (hS_nat j hj.1) (inv_log_diff_nonneg hj.1)
      _ = C * (1 / Real.log 2 - 1 / Real.log (m' : ℝ)) := by
          rw [← Finset.mul_sum, sum_inv_log_telescope m' hm'2]
      _ ≤ C * (1 / Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ hC_pos.le
          linarith [div_nonneg (by linarith : (0:ℝ) ≤ 1) hlogm'_pos.le]
      _ = C / Real.log 2 := by ring
  -- Bound S(m')/log(m') - 1/φq
  have s_over_log_bound :
      |S' m' * (1 / Real.log (m' : ℝ)) - 1 / φq| ≤ C / Real.log 3 := by
    have hrw : S' m' * (1 / Real.log (m' : ℝ)) - 1 / φq =
        (S' m' - Real.log (m' : ℝ) / φq) / Real.log (m' : ℝ) := by field_simp
    rw [hrw, abs_div, abs_of_pos hlogm'_pos]
    have hlog3_le_logm' : Real.log 3 ≤ Real.log (m' : ℝ) :=
      Real.log_le_log (by norm_num : (0:ℝ) < 3) (by exact_mod_cast (show 3 ≤ m' by omega))
    calc |S' m' - Real.log ↑m' / φq| / Real.log ↑m'
        ≤ C / Real.log ↑m' := by
          apply div_le_div_of_nonneg_right (hS_nat m' hm'2) hlogm'_pos.le
      _ ≤ C / Real.log 3 := by
          apply div_le_div_of_nonneg_left hC_pos.le hlog3_pos hlog3_le_logm'
  -- Use main_sum_sandwich for σ
  have hsandwich := main_sum_sandwich m' hm'
  obtain ⟨hσ_lower, hσ_upper⟩ := hsandwich
  -- |σ/φq - (loglog(m') - loglog(2))/φq| ≤ 1/(log 2)² / φq
  have sigma_bound :
      |σ / φq - (Real.log (Real.log (m' : ℝ)) - Real.log (Real.log 2)) / φq| ≤
      1 / (Real.log 2) ^ 2 / φq := by
    rw [← sub_div, abs_div, abs_of_pos hφq_pos]
    apply div_le_div_of_nonneg_right _ hφq_pos.le
    rw [show σ - (Real.log (Real.log ↑m') - Real.log (Real.log 2)) =
      -(Real.log (Real.log ↑m') - Real.log (Real.log 2) - σ) from by ring,
      abs_neg, abs_of_nonneg hσ_lower]
    exact hσ_upper
  -- Assemble: decompose the difference T(m') - loglog(m')/φq
  have key_eq :
      S' m' * (1 / Real.log ↑m') + (σ / φq + error_rem) -
        Real.log (Real.log ↑m') / φq =
      (S' m' * (1 / Real.log ↑m') - 1 / φq) +
      (σ / φq - (Real.log (Real.log ↑m') - Real.log (Real.log 2)) / φq) +
      error_rem +
      (1 - Real.log (Real.log 2)) / φq := by ring
  rw [remainder_decomp, key_eq]
  -- Triangle inequality: bound |a + b + c + d| ≤ |a| + |b| + |c| + |d|
  set a_term := S' m' * (1 / Real.log ↑m') - 1 / φq
  set b_term := σ / φq - (Real.log (Real.log ↑m') - Real.log (Real.log 2)) / φq
  set c_term := error_rem
  set d_term := (1 - Real.log (Real.log 2)) / φq
  have htri : |a_term + b_term + c_term + d_term| ≤
      |a_term| + |b_term| + |c_term| + |d_term| := by
    calc |a_term + b_term + c_term + d_term|
        ≤ |a_term + b_term + c_term| + |d_term| := abs_add_le _ _
      _ ≤ (|a_term + b_term| + |c_term|) + |d_term| := by
          linarith [abs_add_le (a_term + b_term) c_term]
      _ ≤ ((|a_term| + |b_term|) + |c_term|) + |d_term| := by
          linarith [abs_add_le a_term b_term]
  have hd_bound : |d_term| ≤ (1 + 1 / (Real.log 2) ^ 2) / φq := by
    simp only [d_term]
    rw [abs_div, abs_of_pos hφq_pos]
    exact div_le_div_of_nonneg_right loglog2_bound hφq_pos.le
  calc |a_term + b_term + c_term + d_term|
      ≤ |a_term| + |b_term| + |c_term| + |d_term| := htri
    _ ≤ C / Real.log 3 + (1 / (Real.log 2) ^ 2 / φq) +
        (C / Real.log 2) + ((1 + 1 / (Real.log 2) ^ 2) / φq) := by
          linarith [s_over_log_bound, sigma_bound, error_bound, hd_bound]
    _ = C / Real.log 2 + C / Real.log 3 + (1 + 2 / (Real.log 2) ^ 2) / φq := by ring

end PrimeLogToReciprocal

end IK
