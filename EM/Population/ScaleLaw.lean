import EM.Population.HeadDomination
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The scale of the least prime factor

2026-11-22.

`HeadDomination.lean` gives the law of `minFac` on the integers: the density of
`{m : minFac m = p}` is `w p = (1/p) ∏_{r<p} (1 − 1/r)` and the density of the `y`-rough
integers is `cfun (y+1) = ∏_{r ≤ y} (1 − 1/r)`. Those results were used for the residue of
`minFac`. This file is about its size.

## Results

Unconditional:

* `cfun_eq_prod`, `cfun_succ_eq_prod_primesLE` — `cfun` as a product over primes.
* `tendsto_rough_ratio` — **the exact conditional law.** Among the `y`-rough integers, the
  proportion of `z`-rough ones is `cfun (z+1) / cfun (y+1) = ∏_{y < r ≤ z} (1 − 1/r)`.

Under statements quoted from the Tau Ceti library (`TauCeti/NumberTheory/Mertens.lean`,
Mathlib-only statements; not in Mathlib; not re-proved here):

* `scale_law` — under `MertensThird`
  (`TauCeti.exists_abs_prod_primesLE_one_sub_inv_sub_exp_neg_div_log_le`):
  `|cfun (z+1) / cfun (y+1) − log y / log z| ≤ C / log y` for `y₀ ≤ y ≤ z`.
  So for a `y`-rough integer `m`, `log y / log (minFac m)` is uniform on `(0,1)` up to
  `O(1/log y)`, whatever `y` is: in logarithmic scale the least prime factor has a Pareto law
  of index `1`, and the law is scale invariant.
* `sum_w_log_tendsto`, `mean_log_minFac_unbounded` — under `MertensProductBounds`
  (`TauCeti.exists_pos_prod_primesLE_one_sub_inv_bounds`): `∑_p w p · log p = ∞`, and the mean
  of `log (minFac m)` over `2 ≤ m ≤ X` is unbounded as `X → ∞`. A Pareto law of index `1` has
  no mean.

## Reading

The greedy step adds `log (minFac (P + 1))` to `log P`. The increment has a scale-invariant
heavy tail with infinite mean, truncated at `log (P + 1)`; the truncation is attained exactly
when `P + 1` is prime. These are statements about the integers (and, with the selection law,
about seed populations). Nothing here concerns an individual orbit.
-/

noncomputable section
open Classical Finset

namespace ScaleLaw

open HeadDomination

/-! ## 1. `cfun` as a product -/

theorem cfun_eq_prod (n : ℕ) :
    cfun n = ∏ r ∈ (range n).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := by
  unfold cfun Apr Npr
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hp : r.Prime := (Finset.mem_filter.mp hr).2
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Nat.cast_sub hp.one_le]
  field_simp
  simp

theorem cfun_succ_eq_prod_primesLE (n : ℕ) :
    cfun (n + 1) = ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ)⁻¹) := by
  rw [cfun_eq_prod, Nat.primesLE_eq_filter_range]

/-! ## 2. The exact conditional law -/

/-- **The exact conditional law.** Among the integers with least prime factor `> y`, the
proportion with least prime factor `> z` tends to `cfun (z+1) / cfun (y+1)`, which is
`∏_{y < r ≤ z} (1 − 1/r)` over primes (`cfun_eq_prod`). -/
theorem tendsto_rough_ratio (y z : ℕ) :
    Filter.Tendsto (fun X : ℕ => (roughCount z X : ℝ) / roughCount y X) Filter.atTop
      (nhds (cfun (z + 1) / cfun (y + 1))) := by
  have h := (tendsto_roughCount_div z).div (tendsto_roughCount_div y) (cfun_pos (y + 1)).ne'
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with X hX
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hX0]

/-! ## 3. The scale law, from Mertens' third theorem -/

/-- **Quoted (Tau Ceti, `TauCeti.exists_abs_prod_primesLE_one_sub_inv_sub_exp_neg_div_log_le`).**
Mertens' third theorem, reciprocal form, uniform on `[2, ∞)`:
`|∏_{p ≤ x} (1 − 1/p) − e^{−γ} / log x| ≤ C / log² x`. -/
def MertensThird : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |(∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) -
        Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤ C / Real.log x ^ 2

/-- **Quoted (Tau Ceti, `TauCeti.exists_pos_prod_primesLE_one_sub_inv_bounds`).** Two-sided
bounds for the partial Euler product: `c₁ / log y ≤ ∏_{p ≤ y} (1 − 1/p) ≤ c₂ / log y`. -/
def MertensProductBounds : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ y : ℝ, 2 ≤ y →
    c₁ / Real.log y ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)) ∧
      (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)) ≤ c₂ / Real.log y

/-- **The scale law.** Under Mertens' third theorem there are `C, y₀` such that for all
integers `y₀ ≤ y ≤ z`,

  `|cfun (z+1) / cfun (y+1) − log y / log z| ≤ C / log y`.

The left quotient is the proportion of `z`-rough integers among the `y`-rough ones
(`tendsto_rough_ratio`). -/
theorem scale_law (h : MertensThird) :
    ∃ C y₀ : ℝ, ∀ y z : ℕ, y₀ ≤ (y : ℝ) → y ≤ z →
      |cfun (z + 1) / cfun (y + 1) - Real.log y / Real.log z| ≤ C / Real.log y := by
  obtain ⟨C₀, hC₀⟩ := h
  set κ : ℝ := Real.exp (-Real.eulerMascheroniConstant) with hκ
  have hκpos : 0 < κ := Real.exp_pos _
  set C : ℝ := |C₀| + 1 with hC
  have hCpos : 0 < C := by positivity
  -- `u n = cfun (n+1) · log n` is within `C / log n` of `κ`
  have hu : ∀ n : ℕ, 2 ≤ n → |cfun (n + 1) * Real.log n - κ| ≤ C / Real.log n := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hL : 0 < Real.log n := Real.log_pos (by linarith)
    have h1 := hC₀ n hn2
    rw [Nat.floor_natCast, ← cfun_succ_eq_prod_primesLE] at h1
    have h2 : |cfun (n + 1) - κ / Real.log n| ≤ C / Real.log n ^ 2 :=
      h1.trans (div_le_div_of_nonneg_right (by rw [hC]; linarith [le_abs_self C₀]) (by positivity))
    have h3 : cfun (n + 1) * Real.log n - κ = (cfun (n + 1) - κ / Real.log n) * Real.log n := by
      field_simp
    rw [h3, abs_mul, abs_of_pos hL]
    calc |cfun (n + 1) - κ / Real.log n| * Real.log n
        ≤ C / Real.log n ^ 2 * Real.log n := mul_le_mul_of_nonneg_right h2 hL.le
      _ = C / Real.log n := by field_simp
  refine ⟨4 * C / κ, max 2 (Real.exp (2 * C / κ)), fun y z hy hyz => ?_⟩
  have hy2 : (2 : ℝ) ≤ y := le_trans (le_max_left _ _) hy
  have hyn : 2 ≤ y := by exact_mod_cast hy2
  have hzn : 2 ≤ z := le_trans hyn hyz
  have hLy : 0 < Real.log y := Real.log_pos (by linarith)
  have hyz' : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hLyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz'
  have hLz : 0 < Real.log z := lt_of_lt_of_le hLy hLyz
  have hLbig : 2 * C / κ ≤ Real.log y := by
    have : Real.exp (2 * C / κ) ≤ y := le_trans (le_max_right _ _) hy
    calc 2 * C / κ = Real.log (Real.exp (2 * C / κ)) := (Real.log_exp _).symm
      _ ≤ Real.log y := Real.log_le_log (Real.exp_pos _) this
  have huy := hu y hyn
  have huz := hu z hzn
  set uy := cfun (y + 1) * Real.log y with huy_def
  set uz := cfun (z + 1) * Real.log z with huz_def
  have hCy : C / Real.log y ≤ κ / 2 := by
    rw [div_le_iff₀ hLy]
    have := (div_le_iff₀ hκpos).mp hLbig
    linarith
  have huy_lb : κ / 2 ≤ uy := by
    have := (abs_le.mp huy).1
    linarith
  have huy_pos : 0 < uy := by linarith
  have hCz : C / Real.log z ≤ C / Real.log y :=
    div_le_div_of_nonneg_left hCpos.le hLy hLyz
  have hdiff : |uz - uy| ≤ 2 * (C / Real.log y) := by
    have h1 : uz - uy = (uz - κ) - (uy - κ) := by ring
    rw [h1]
    calc |(uz - κ) - (uy - κ)| ≤ |uz - κ| + |uy - κ| := abs_sub _ _
      _ ≤ C / Real.log z + C / Real.log y := add_le_add huz huy
      _ ≤ 2 * (C / Real.log y) := by linarith
  have hcy : cfun (y + 1) = uy / Real.log y := by rw [huy_def]; field_simp
  have hcz : cfun (z + 1) = uz / Real.log z := by rw [huz_def]; field_simp
  have hid : cfun (z + 1) / cfun (y + 1) - Real.log y / Real.log z =
      Real.log y / Real.log z * ((uz - uy) / uy) := by
    rw [hcy, hcz]; field_simp
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg hLy.le hLz.le), abs_div (uz - uy) uy,
    abs_of_pos huy_pos]
  have hratio : Real.log y / Real.log z ≤ 1 := (div_le_one hLz).mpr hLyz
  calc Real.log y / Real.log z * (|uz - uy| / uy)
      ≤ 1 * (|uz - uy| / uy) :=
        mul_le_mul_of_nonneg_right hratio (div_nonneg (abs_nonneg _) huy_pos.le)
    _ = |uz - uy| / uy := one_mul _
    _ ≤ 2 * (C / Real.log y) / (κ / 2) :=
        div_le_div₀ (by positivity) hdiff (by positivity) huy_lb
    _ = 4 * C / κ / Real.log y := by field_simp; ring

/-! ## 4. No mean -/

/-- Under the two-sided Mertens bounds, `w p · log p ≥ c₁ / p` for every prime `p`. -/
theorem w_mul_log_ge (h : MertensProductBounds) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p.Prime → c / p ≤ w p * Real.log p := by
  obtain ⟨c₁, c₂, hc₁, -, hb⟩ := h
  refine ⟨c₁, hc₁, fun p hp => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hL : 0 < Real.log p := Real.log_pos (by linarith)
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 := (hb p hp2).1
  rw [Nat.floor_natCast, ← cfun_succ_eq_prod_primesLE] at h1
  have h2 : cfun (p + 1) ≤ cfun p := cfun_antitone (Nat.le_succ p)
  have h3 : c₁ / Real.log p ≤ cfun p := h1.trans h2
  have h4 : c₁ ≤ cfun p * Real.log p := (div_le_iff₀ hL).mp h3
  rw [w, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h4 hp0.le

/-- Under the two-sided Mertens bounds, `∑_{p < N} w p · log p → ∞`. -/
theorem sum_w_log_tendsto (h : MertensProductBounds) :
    Filter.Tendsto (fun N => ∑ p ∈ (range N).filter Nat.Prime, w p * Real.log p)
      Filter.atTop Filter.atTop := by
  obtain ⟨c, hc, hw⟩ := w_mul_log_ge h
  have h1 : Filter.Tendsto
      (fun N => c * ∑ r ∈ (range N).filter Nat.Prime, (1 : ℝ) / r) Filter.atTop Filter.atTop :=
    tendsto_sum_inv_primes.const_mul_atTop hc
  refine Filter.tendsto_atTop_mono (fun N => ?_) h1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have := hw p (Finset.mem_filter.mp hp).2
  rwa [mul_one_div]

/-- The sum of `log (minFac m)` over `2 ≤ m ≤ X` dominates the contribution of the primes
below `N`. -/
theorem sum_log_minFac_ge (N X : ℕ) :
    ∑ p ∈ (range N).filter Nat.Prime,
        Real.log p * (((Icc 2 X).filter fun m => Nat.minFac m = p).card : ℝ) ≤
      ∑ m ∈ Icc 2 X, Real.log (Nat.minFac m) := by
  have hstep : ∀ p ∈ (range N).filter Nat.Prime,
      Real.log p * (((Icc 2 X).filter fun m => Nat.minFac m = p).card : ℝ) =
        ∑ m ∈ Icc 2 X, if Nat.minFac m = p then Real.log p else 0 := by
    intro p _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_le_sum fun m _ => ?_
  have hnn : (0 : ℝ) ≤ Real.log (Nat.minFac m) := Real.log_natCast_nonneg _
  rw [Finset.sum_ite_eq]
  split_ifs
  · exact le_rfl
  · exact hnn

/-- **The mean of `log minFac` is unbounded.** Under the two-sided Mertens bounds, for every
`M` and all large `X`, `∑_{2 ≤ m ≤ X} log (minFac m) ≥ M · X`. -/
theorem mean_log_minFac_unbounded (h : MertensProductBounds) (M : ℝ) :
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → M * (X : ℝ) ≤ ∑ m ∈ Icc 2 X, Real.log (Nat.minFac m) := by
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp (sum_w_log_tendsto h) (M + 1)).exists
  set S := (range N).filter Nat.Prime with hS
  set K : ℝ := ∑ p ∈ S, Real.log p * (Apr p : ℝ) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun p _ =>
    mul_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨⌈K⌉₊, fun X hX => ?_⟩
  have hXK : K ≤ (X : ℝ) := (Nat.le_ceil K).trans (by exact_mod_cast hX)
  have hterm : ∀ p ∈ S, (X : ℝ) * (w p * Real.log p) - Real.log p * (Apr p : ℝ) ≤
      Real.log p * (((Icc 2 X).filter fun m => Nat.minFac m = p).card : ℝ) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hd : 0 < p * Npr p := Nat.mul_pos hpp.pos (Npr_pos p)
    have hd' : (0 : ℝ) < (p : ℝ) * (Npr p : ℝ) := by exact_mod_cast hd
    have hlog : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg _
    have hA : (0 : ℝ) ≤ (Apr p : ℝ) := Nat.cast_nonneg _
    have hcard : (((X / (p * Npr p) : ℕ) : ℝ)) * (Apr p : ℝ) ≤
        (((Icc 2 X).filter fun m => Nat.minFac m = p).card : ℝ) := by
      exact_mod_cast card_minFac_eq_ge hpp X
    have hfloor := (nat_div_bounds X (p * Npr p) hd).1
    rw [Nat.cast_mul] at hfloor
    have h1 : ((X : ℝ) / ((p : ℝ) * (Npr p : ℝ)) - 1) * (Apr p : ℝ) ≤
        (((Icc 2 X).filter fun m => Nat.minFac m = p).card : ℝ) :=
      (mul_le_mul_of_nonneg_right hfloor hA).trans hcard
    have h2 : (X : ℝ) * (w p * Real.log p) - Real.log p * (Apr p : ℝ) =
        Real.log p * (((X : ℝ) / ((p : ℝ) * (Npr p : ℝ)) - 1) * (Apr p : ℝ)) := by
      rw [w_eq]; field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hlog
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hfinal := hsum.trans (sum_log_minFac_ge N X)
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  nlinarith [mul_le_mul_of_nonneg_left hN hX0]

end ScaleLaw

end
