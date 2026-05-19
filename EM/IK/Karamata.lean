import EM.IK.AbelChain
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Karamata's Tauberian theorem, and `WeightedPNTinAPAsymp` unconditionally

`EM/IK/Tauberian.lean §6` and `EM/Population/AlladiDensity.lean` reduce the ANT entry point of
the Alladi chain to the *asymptotic* statement

  `WeightedPNTinAPAsymp`:  `∑_{n ≤ x, n ≡ a (q)} Λ(n)/n = (log x)/φ(q) + o(log x)`,

and the repository already proves the Dirichlet-series input unconditionally
(`IK.residueClass_tsum_both_bounds`, from Mathlib's non-vanishing of Dirichlet `L`-functions
on `Re s ≥ 1`):

  `∑' n, Λ_a(n)/n^σ = (1/φ(q))/(σ − 1) + O(1)`  for `σ ∈ (1, 2]`.

The bridge between the two is a Tauberian theorem.  This file proves it and applies it.

## Part 1: Karamata for Dirichlet series with nonnegative coefficients

For `c : ℕ → ℝ` with `c n ≥ 0` and `c 0 = 0`, write `F(s) = ∑' n, c n · n^{−s}` and
`A(x) = ∑_{1 ≤ n ≤ x} c n`.  **If `s · F(s) → C` as `s → 0⁺`, then `A(x)/log x → C`.**

The proof is the classical one (Karamata 1931), with the Laplace–Stieltjes transform replaced
by the Dirichlet series and `t = log n`:

* monomials — `s · ∑' c n · n^{−s} (n^{−s})^k = s · F((k+1)s) → C/(k+1) = C ∫₀¹ y^k dy`;
* polynomials `P` — by linearity, `s · ∑' c n · n^{−s} P(n^{−s}) → C ∫₀¹ P`;
* the cutoff — `n^{−s} ≥ e^{−1}` iff `n ≤ e^{1/s}`, so `s · A(e^{1/s})` is
  `s · ∑' c n · n^{−s} g₀(n^{−s})` for `g₀(y) = 𝟙[e^{−1} ≤ y]/y`;
* sandwich — continuous `g⁻ ≤ g₀ ≤ g⁺` built from a piecewise-linear ramp, then Weierstrass
  polynomials `P⁻ ≤ g⁻`, `P⁺ ≥ g⁺` on `[0,1]`, all with integrals within `η` of
  `∫₀¹ g₀ = 1`.  Nonnegativity of `c` is what makes the pointwise sandwich sum;
* reparametrise `s = 1/log x`.

Only the *qualitative* limit is extracted; no rate.  That is exactly why the `O(1)`
strengthening was scoped out first (`asymptotic_entry_point_status`): Karamata cannot give it,
and nothing downstream needs it.

## Part 2: application

With `c n = Λ_a(n)/n`, `s · F(s) → 1/φ(q)` follows from `residueClass_tsum_both_bounds` at
`σ = 1 + s`.  Hence `weightedPNTinAP_asymp_proved : WeightedPNTinAPAsymp`, and with the
proved asymptotic chain of `EM/IK/AbelChain.lean`, `primesEquidistInAP_asymp_proved`.

## Main results

* `Karamata.karamata` — the Tauberian theorem.
* `weightedPNTinAP_asymp_proved`, `primesEquidistInAP_asymp_proved` — the ANT entry point of
  the Alladi chain, unconditional.
-/

noncomputable section
open Classical

namespace IK

open Nat Finset Filter Topology

namespace Karamata

open Polynomial

/-- The Dirichlet series `∑' n, c n · n^{−s}`. -/
def dser (c : ℕ → ℝ) (s : ℝ) : ℝ := ∑' n, c n * (n : ℝ) ^ (-s)

/-- The partial sums `∑_{1 ≤ n ≤ x} c n`. -/
def psum (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 (Nat.floor x), c n

variable {c : ℕ → ℝ} {C : ℝ}

/-! ### The weight `n^{−s}` -/

theorem weight_nonneg (n : ℕ) (s : ℝ) : 0 ≤ (n : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem weight_le_one (n : ℕ) {s : ℝ} (hs : 0 < s) : (n : ℝ) ^ (-s) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]; exact zero_le_one
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

theorem weight_mem_Icc (n : ℕ) {s : ℝ} (hs : 0 < s) : (n : ℝ) ^ (-s) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨weight_nonneg n s, weight_le_one n hs⟩

/-- `n^{−s} · (n^{−s})^k = n^{−(k+1)s}`. -/
theorem weight_mul_pow (n : ℕ) (s : ℝ) (k : ℕ) :
    (n : ℝ) ^ (-s) * ((n : ℝ) ^ (-s)) ^ k = (n : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * s)) := by
  rw [show (n : ℝ) ^ (-s) * ((n : ℝ) ^ (-s)) ^ k = ((n : ℝ) ^ (-s)) ^ (k + 1) from
    (pow_succ' _ _).symm, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1; push_cast; ring

/-! ### Step 1: monomials -/

/-- `s · ∑' c n · n^{−s} (n^{−s})^k → C/(k+1)`. -/
theorem tendsto_monomial (hlim : Tendsto (fun s => s * dser c s) (𝓝[>] 0) (𝓝 C)) (k : ℕ) :
    Tendsto (fun s => s * ∑' n, c n * (n : ℝ) ^ (-s) * ((n : ℝ) ^ (-s)) ^ k)
      (𝓝[>] 0) (𝓝 (C / (k + 1))) := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hmap : Tendsto (fun s : ℝ => ((k + 1 : ℕ) : ℝ) * s) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun s : ℝ => ((k + 1 : ℕ) : ℝ) * s) (𝓝 0)
          (𝓝 (((k + 1 : ℕ) : ℝ) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos (by positivity) (Set.mem_Ioi.mp hs)
  have h2 := (hlim.comp hmap).const_mul (1 / ((k + 1 : ℕ) : ℝ))
  have heq : ∀ s : ℝ,
      (1 / ((k + 1 : ℕ) : ℝ)) *
        ((((k + 1 : ℕ) : ℝ) * s) * dser c (((k + 1 : ℕ) : ℝ) * s)) =
      s * ∑' n, c n * (n : ℝ) ^ (-s) * ((n : ℝ) ^ (-s)) ^ k := by
    intro s
    have : dser c (((k + 1 : ℕ) : ℝ) * s) =
        ∑' n, c n * (n : ℝ) ^ (-s) * ((n : ℝ) ^ (-s)) ^ k := by
      unfold dser
      exact tsum_congr fun n => by rw [mul_assoc, weight_mul_pow]
    rw [this]; field_simp
  have hval : (1 / ((k + 1 : ℕ) : ℝ)) * C = C / (k + 1) := by push_cast; ring
  rw [← hval]
  exact h2.congr heq

/-! ### Step 2: polynomials -/

/-- Polynomials are bounded on `[0,1]`. -/
theorem poly_bdd (P : ℝ[X]) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, |P.eval y| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    P.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  have := hM y hy
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Summability of the polynomially weighted series. -/
theorem summable_poly (hc : ∀ n, 0 ≤ c n)
    (hsum : ∀ s : ℝ, 0 < s → Summable (fun n => c n * (n : ℝ) ^ (-s)))
    {s : ℝ} (hs : 0 < s) (P : ℝ[X]) :
    Summable (fun n => c n * (n : ℝ) ^ (-s) * P.eval ((n : ℝ) ^ (-s))) := by
  obtain ⟨M, _, hM⟩ := poly_bdd P
  refine Summable.of_norm_bounded ((hsum s hs).mul_left M) (fun n => ?_)
  have hnn : 0 ≤ c n * (n : ℝ) ^ (-s) := mul_nonneg (hc n) (weight_nonneg n s)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  calc c n * (n : ℝ) ^ (-s) * |P.eval ((n : ℝ) ^ (-s))|
      ≤ c n * (n : ℝ) ^ (-s) * M :=
        mul_le_mul_of_nonneg_left (hM _ (weight_mem_Icc n hs)) hnn
    _ = M * (c n * (n : ℝ) ^ (-s)) := by ring

/-- `s · ∑' c n · n^{−s} P(n^{−s}) → C ∫₀¹ P`. -/
theorem tendsto_poly (hc : ∀ n, 0 ≤ c n)
    (hsum : ∀ s : ℝ, 0 < s → Summable (fun n => c n * (n : ℝ) ^ (-s)))
    (hlim : Tendsto (fun s => s * dser c s) (𝓝[>] 0) (𝓝 C)) (P : ℝ[X]) :
    Tendsto (fun s => s * ∑' n, c n * (n : ℝ) ^ (-s) * P.eval ((n : ℝ) ^ (-s)))
      (𝓝[>] 0) (𝓝 (C * ∫ y in (0 : ℝ)..1, P.eval y)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have hint : ∫ y in (0 : ℝ)..1, (p + q).eval y =
        (∫ y in (0 : ℝ)..1, p.eval y) + ∫ y in (0 : ℝ)..1, q.eval y := by
      simp only [Polynomial.eval_add]
      exact intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
        (q.continuous.intervalIntegrable _ _)
    rw [hint, mul_add]
    refine (hp.add hq).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← mul_add, ← (summable_poly hc hsum hs p).tsum_add (summable_poly hc hsum hs q)]
    congr 1
    exact tsum_congr fun n => by simp only [Polynomial.eval_add]; ring
  | monomial k a =>
    have hint : ∫ y in (0 : ℝ)..1, (monomial k a).eval y = a * (1 / (k + 1)) := by
      simp only [Polynomial.eval_monomial]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp
    rw [hint]
    have h := (tendsto_monomial hlim k).const_mul a
    have heq : ∀ s : ℝ,
        a * (s * ∑' n, c n * (n : ℝ) ^ (-s) * ((n : ℝ) ^ (-s)) ^ k) =
        s * ∑' n, c n * (n : ℝ) ^ (-s) * (monomial k a).eval ((n : ℝ) ^ (-s)) := by
      intro s
      simp only [Polynomial.eval_monomial]
      have : ∑' n, c n * (n : ℝ) ^ (-s) * (a * ((n : ℝ) ^ (-s)) ^ k) =
          a * ∑' n, c n * (n : ℝ) ^ (-s) * ((n : ℝ) ^ (-s)) ^ k := by
        rw [← tsum_mul_left]; exact tsum_congr fun n => by ring
      rw [this]; ring
    have hval : C * (a * (1 / (k + 1))) = a * (C / (k + 1)) := by ring
    rw [hval]
    exact h.congr heq

/-! ### Step 3: the cutoff `n^{−s} ≥ e^{−1}` -/

/-- For `n ≥ 1`, `e^{−1} ≤ n^{−s}` iff `n ≤ e^{1/s}`. -/
theorem weight_ge_iff {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    Real.exp (-1) ≤ (n : ℝ) ^ (-s) ↔ (n : ℝ) ≤ Real.exp (1 / s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn0, Real.exp_le_exp, ← Real.log_le_iff_le_exp hn0, le_div_iff₀ hs]
  constructor <;> intro h <;> linarith [show Real.log n * (-s) = -(Real.log n * s) by ring]

/-- The indicator-weighted coefficient vanishes off `[1, ⌊e^{1/s}⌋]`. -/
theorem ind_eq_zero (hc0 : c 0 = 0) {s : ℝ} (hs : 0 < s) (n : ℕ)
    (hn : n ∉ Icc 1 (Nat.floor (Real.exp (1 / s)))) :
    c n * (if Real.exp (-1) ≤ (n : ℝ) ^ (-s) then (1 : ℝ) else 0) = 0 := by
  rw [Finset.mem_Icc] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [hc0]
  · have : ¬ Real.exp (-1) ≤ (n : ℝ) ^ (-s) := by
      rw [weight_ge_iff hpos hs]
      intro h
      exact hn ⟨hpos, Nat.le_floor h⟩
    simp [this]

theorem summable_ind (hc0 : c 0 = 0) {s : ℝ} (hs : 0 < s) :
    Summable (fun n => c n * (if Real.exp (-1) ≤ (n : ℝ) ^ (-s) then (1 : ℝ) else 0)) :=
  summable_of_ne_finset_zero (ind_eq_zero hc0 hs)

/-- The indicator-weighted series is the partial sum up to `e^{1/s}`. -/
theorem tsum_ind (hc0 : c 0 = 0) {s : ℝ} (hs : 0 < s) :
    ∑' n, c n * (if Real.exp (-1) ≤ (n : ℝ) ^ (-s) then (1 : ℝ) else 0) =
      psum c (Real.exp (1 / s)) := by
  unfold psum
  rw [tsum_eq_sum (ind_eq_zero hc0 hs)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have : Real.exp (-1) ≤ (n : ℝ) ^ (-s) :=
    (weight_ge_iff hn.1 hs).mpr ((Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2)
  simp [this]

/-- **The sandwich.**  Polynomials `Pl, Pu` with `y·Pl(y) ≤ 𝟙[e^{−1} ≤ y] ≤ y·Pu(y)` on
`[0,1]` squeeze the partial sum `A(e^{1/s})` between the two polynomially weighted series. -/
theorem sandwich_tsum (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 = 0)
    (hsum : ∀ s : ℝ, 0 < s → Summable (fun n => c n * (n : ℝ) ^ (-s)))
    {s : ℝ} (hs : 0 < s) (Pl Pu : ℝ[X])
    (hl : ∀ y ∈ Set.Icc (0 : ℝ) 1, y * Pl.eval y ≤ (if Real.exp (-1) ≤ y then 1 else 0))
    (hu : ∀ y ∈ Set.Icc (0 : ℝ) 1, (if Real.exp (-1) ≤ y then (1 : ℝ) else 0) ≤ y * Pu.eval y) :
    (∑' n, c n * (n : ℝ) ^ (-s) * Pl.eval ((n : ℝ) ^ (-s))) ≤ psum c (Real.exp (1 / s)) ∧
    psum c (Real.exp (1 / s)) ≤ ∑' n, c n * (n : ℝ) ^ (-s) * Pu.eval ((n : ℝ) ^ (-s)) := by
  rw [← tsum_ind hc0 hs]
  constructor
  · refine (summable_poly hc hsum hs Pl).tsum_le_tsum (fun n => ?_) (summable_ind hc0 hs)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hl _ (weight_mem_Icc n hs)) (hc n)
  · refine (summable_ind hc0 hs).tsum_le_tsum (fun n => ?_) (summable_poly hc hsum hs Pu)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hu _ (weight_mem_Icc n hs)) (hc n)

/-! ### Step 4: the sandwich functions

`ramp a b` rises linearly from `0` at `a` to `1` at `b`.  Then

* `gplus δ y = ramp(e^{−1−δ}, e^{−1})(y) / max y e^{−1−δ}` — equals `1/y` on `[e^{−1}, 1]`,
  vanishes below `e^{−1−δ}`, and `y · gplus ≥ 𝟙[e^{−1} ≤ y]`;
* `gminus δ y = ramp(e^{−1}, e^{−1+δ})(y) / max y e^{−1}` — equals `1/y` on `[e^{−1+δ}, 1]`,
  vanishes below `e^{−1}`, and `y · gminus ≤ 𝟙[e^{−1} ≤ y]`.

Both are continuous, with `∫₀¹ gplus ≤ 1 + δ` and `∫₀¹ gminus ≥ 1 − δ`. -/

/-- Piecewise-linear ramp from `0` at `a` to `1` at `b`. -/
def ramp (a b y : ℝ) : ℝ := min 1 (max 0 ((y - a) / (b - a)))

theorem ramp_continuous (a b : ℝ) : Continuous (ramp a b) := by
  unfold ramp; fun_prop

theorem ramp_nonneg (a b y : ℝ) : 0 ≤ ramp a b y :=
  le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (a b y : ℝ) : ramp a b y ≤ 1 := min_le_left _ _

theorem ramp_eq_zero {a b y : ℝ} (hab : a < b) (hy : y ≤ a) : ramp a b y = 0 := by
  unfold ramp
  have : (y - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [max_eq_left this, min_eq_right zero_le_one]

theorem ramp_eq_one {a b y : ℝ} (hab : a < b) (hy : b ≤ y) : ramp a b y = 1 := by
  unfold ramp
  have h1 : 1 ≤ (y - a) / (b - a) := by rw [le_div_iff₀ (by linarith)]; linarith
  rw [max_eq_right (by linarith), min_eq_left h1]

/-- The upper sandwich function. -/
def gplus (δ y : ℝ) : ℝ := ramp (Real.exp (-1 - δ)) (Real.exp (-1)) y / max y (Real.exp (-1 - δ))

/-- The lower sandwich function. -/
def gminus (δ y : ℝ) : ℝ := ramp (Real.exp (-1)) (Real.exp (-1 + δ)) y / max y (Real.exp (-1))

theorem gplus_continuous (δ : ℝ) : Continuous (gplus δ) := by
  unfold gplus
  exact (ramp_continuous _ _).div (continuous_id.max continuous_const)
    fun y => (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)).ne'

theorem gminus_continuous (δ : ℝ) : Continuous (gminus δ) := by
  unfold gminus
  exact (ramp_continuous _ _).div (continuous_id.max continuous_const)
    fun y => (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)).ne'

theorem gplus_nonneg (δ y : ℝ) : 0 ≤ gplus δ y :=
  div_nonneg (ramp_nonneg _ _ _) (le_trans (Real.exp_pos _).le (le_max_right _ _))

theorem gminus_nonneg (δ y : ℝ) : 0 ≤ gminus δ y :=
  div_nonneg (ramp_nonneg _ _ _) (le_trans (Real.exp_pos _).le (le_max_right _ _))

/-- `𝟙[e^{−1} ≤ y] ≤ y · gplus δ y` on `[0,1]`. -/
theorem gplus_sandwich {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (if Real.exp (-1) ≤ y then (1 : ℝ) else 0) ≤ y * gplus δ y := by
  have hab : Real.exp (-1 - δ) < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
  split_ifs with h
  · have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) h
    unfold gplus
    rw [ramp_eq_one hab h, max_eq_left (le_trans hab.le h), mul_one_div_cancel hy0.ne']
  · exact mul_nonneg hy.1 (gplus_nonneg δ y)

/-- `y · gminus δ y ≤ 𝟙[e^{−1} ≤ y]` on `[0,1]`. -/
theorem gminus_sandwich {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (_hy : y ∈ Set.Icc (0 : ℝ) 1) :
    y * gminus δ y ≤ (if Real.exp (-1) ≤ y then (1 : ℝ) else 0) := by
  have hab : Real.exp (-1) < Real.exp (-1 + δ) := Real.exp_lt_exp.mpr (by linarith)
  split_ifs with h
  · have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) h
    unfold gminus
    rw [max_eq_left h, mul_div_cancel₀ _ hy0.ne']
    exact ramp_le_one _ _ _
  · push Not at h
    unfold gminus
    rw [ramp_eq_zero hab h.le, zero_div, mul_zero]

/-- `gplus δ` vanishes on `[0, e^{−1−δ}]`. -/
theorem gplus_eq_zero {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : y ≤ Real.exp (-1 - δ)) :
    gplus δ y = 0 := by
  have hab : Real.exp (-1 - δ) < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
  unfold gplus; rw [ramp_eq_zero hab hy, zero_div]

/-- `gplus δ y ≤ 1/y` for `y ≥ e^{−1−δ}`. -/
theorem gplus_le_inv {δ y : ℝ} (hy : Real.exp (-1 - δ) ≤ y) : gplus δ y ≤ 1 / y := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  unfold gplus
  rw [max_eq_left hy]
  exact div_le_div_of_nonneg_right (ramp_le_one _ _ _) hy0.le

/-- `gminus δ y = 1/y` for `y ≥ e^{−1+δ}`. -/
theorem gminus_eq_inv {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : Real.exp (-1 + δ) ≤ y) :
    gminus δ y = 1 / y := by
  have hab : Real.exp (-1) < Real.exp (-1 + δ) := Real.exp_lt_exp.mpr (by linarith)
  unfold gminus
  rw [ramp_eq_one hab hy, max_eq_left (le_trans hab.le hy)]

/-- `∫₀¹ gplus δ ≤ 1 + δ`. -/
theorem integral_gplus_le {δ : ℝ} (hδ : 0 < δ) :
    ∫ y in (0 : ℝ)..1, gplus δ y ≤ 1 + δ := by
  set a := Real.exp (-1 - δ) with ha_def
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := by rw [ha_def, Real.exp_lt_one_iff]; linarith
  have hcont := gplus_continuous δ
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 a)
    (hcont.intervalIntegrable a 1)]
  have h1 : ∫ y in (0 : ℝ)..a, gplus δ y = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro y hy
    rw [Set.uIcc_of_le ha0.le] at hy
    exact gplus_eq_zero hδ hy.2
  have h2 : ∫ y in a..1, gplus δ y ≤ ∫ y in a..1, 1 / y := by
    apply intervalIntegral.integral_mono_on ha1.le (hcont.intervalIntegrable _ _)
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ha1.le]
      exact continuousOn_const.div continuousOn_id fun y hy => (lt_of_lt_of_le ha0 hy.1).ne'
    · intro y hy; exact gplus_le_inv hy.1
  have h3 : ∫ y in a..1, 1 / y = 1 + δ := by
    rw [integral_one_div, one_div, Real.log_inv, ha_def, Real.log_exp]
    · ring
    · rw [Set.uIcc_of_le ha1.le]; intro h; exact (not_le.mpr ha0) h.1
  linarith

/-- `1 − δ ≤ ∫₀¹ gminus δ` for `0 < δ ≤ 1`. -/
theorem integral_gminus_ge {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ ∫ y in (0 : ℝ)..1, gminus δ y := by
  set b := Real.exp (-1 + δ) with hb_def
  have hb0 : 0 < b := Real.exp_pos _
  have hb1 : b ≤ 1 := by rw [hb_def, Real.exp_le_one_iff]; linarith
  have hcont := gminus_continuous δ
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 b)
    (hcont.intervalIntegrable b 1)]
  have h1 : 0 ≤ ∫ y in (0 : ℝ)..b, gminus δ y :=
    intervalIntegral.integral_nonneg hb0.le fun y _ => gminus_nonneg δ y
  have h2 : ∫ y in b..1, gminus δ y = ∫ y in b..1, 1 / y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hb1] at hy
    exact gminus_eq_inv hδ hy.1
  have h3 : ∫ y in b..1, 1 / y = 1 - δ := by
    rw [integral_one_div, one_div, Real.log_inv, hb_def, Real.log_exp]
    · ring
    · rw [Set.uIcc_of_le hb1]; intro h; exact (not_le.mpr hb0) h.1
  linarith

/-! ### Step 5: Weierstrass polynomials and the sandwich polynomials -/

/-- Weierstrass on `[0,1]`, in the form used below. -/
theorem exists_poly_near (g : ℝ → ℝ) (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ y ∈ Set.Icc (0 : ℝ) 1, |p.eval y - g y| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1
    ⟨fun y : Set.Icc (0 : ℝ) 1 => g y, hg.comp continuous_subtype_val⟩ ε hε
  refine ⟨p, fun y hy => ?_⟩
  have := (ContinuousMap.norm_lt_iff _ hε).mp hp ⟨y, hy⟩
  simpa [Real.norm_eq_abs] using this

/-- **The sandwich polynomials.**  For every `0 < η ≤ 1` there are polynomials `Pl ≤ Pu` with
`y·Pl(y) ≤ 𝟙[e^{−1} ≤ y] ≤ y·Pu(y)` on `[0,1]` and `∫₀¹ Pl ≥ 1 − η`, `∫₀¹ Pu ≤ 1 + η`. -/
theorem exists_sandwich {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ Pl Pu : ℝ[X],
      (∀ y ∈ Set.Icc (0 : ℝ) 1, y * Pl.eval y ≤ (if Real.exp (-1) ≤ y then 1 else 0)) ∧
      (∀ y ∈ Set.Icc (0 : ℝ) 1, (if Real.exp (-1) ≤ y then (1 : ℝ) else 0) ≤ y * Pu.eval y) ∧
      1 - η ≤ (∫ y in (0 : ℝ)..1, Pl.eval y) ∧
      (∫ y in (0 : ℝ)..1, Pu.eval y) ≤ 1 + η := by
  set δ := η / 2 with hδ_def
  set ε := η / 4 with hε_def
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by linarith
  have hε : 0 < ε := by positivity
  obtain ⟨pu, hpu⟩ := exists_poly_near (gplus δ) (gplus_continuous δ) hε
  obtain ⟨pl, hpl⟩ := exists_poly_near (gminus δ) (gminus_continuous δ) hε
  refine ⟨pl - Polynomial.C ε, pu + Polynomial.C ε, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [Polynomial.eval_sub, Polynomial.eval_C]
    have h1 : pl.eval y - ε ≤ gminus δ y := by
      have := hpl y hy; rw [abs_lt] at this; linarith
    calc y * (pl.eval y - ε) ≤ y * gminus δ y := mul_le_mul_of_nonneg_left h1 hy.1
      _ ≤ _ := gminus_sandwich hδ hy
  · intro y hy
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    have h1 : gplus δ y ≤ pu.eval y + ε := by
      have := hpu y hy; rw [abs_lt] at this; linarith
    calc (if Real.exp (-1) ≤ y then (1 : ℝ) else 0) ≤ y * gplus δ y := gplus_sandwich hδ hy
      _ ≤ y * (pu.eval y + ε) := mul_le_mul_of_nonneg_left h1 hy.1
  · -- `∫ (pl − ε) = ∫ pl − ε ≥ (∫ gminus − ε) − ε ≥ 1 − δ − 2ε = 1 − η`
    have hI : ∫ y in (0 : ℝ)..1, (pl - Polynomial.C ε).eval y =
        (∫ y in (0 : ℝ)..1, pl.eval y) - ε := by
      simp only [Polynomial.eval_sub, Polynomial.eval_C]
      rw [intervalIntegral.integral_sub (pl.continuous.intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    have hmono : ∫ y in (0 : ℝ)..1, (gminus δ y - ε) ≤ ∫ y in (0 : ℝ)..1, pl.eval y := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (((gminus_continuous δ).sub continuous_const).intervalIntegrable _ _)
        (pl.continuous.intervalIntegrable _ _)
      intro y hy
      have := hpl y hy; rw [abs_lt] at this
      show gminus δ y - ε ≤ pl.eval y
      linarith
    have hsplit : ∫ y in (0 : ℝ)..1, (gminus δ y - ε) =
        (∫ y in (0 : ℝ)..1, gminus δ y) - ε := by
      rw [intervalIntegral.integral_sub ((gminus_continuous δ).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    have := integral_gminus_ge hδ hδ1
    rw [hI]; linarith
  · have hI : ∫ y in (0 : ℝ)..1, (pu + Polynomial.C ε).eval y =
        (∫ y in (0 : ℝ)..1, pu.eval y) + ε := by
      simp only [Polynomial.eval_add, Polynomial.eval_C]
      rw [intervalIntegral.integral_add (pu.continuous.intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    have hmono : ∫ y in (0 : ℝ)..1, pu.eval y ≤ ∫ y in (0 : ℝ)..1, (gplus δ y + ε) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (pu.continuous.intervalIntegrable _ _)
        (((gplus_continuous δ).add continuous_const).intervalIntegrable _ _)
      intro y hy
      have := hpu y hy; rw [abs_lt] at this
      show pu.eval y ≤ gplus δ y + ε
      linarith
    have hsplit : ∫ y in (0 : ℝ)..1, (gplus δ y + ε) =
        (∫ y in (0 : ℝ)..1, gplus δ y) + ε := by
      rw [intervalIntegral.integral_add ((gplus_continuous δ).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    have := integral_gplus_le hδ
    rw [hI]; linarith

/-! ### Step 6: assembly -/

/-- **Karamata, exponential parametrisation**: `s · A(e^{1/s}) → C` as `s → 0⁺`. -/
theorem tendsto_psum_exp (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 = 0)
    (hsum : ∀ s : ℝ, 0 < s → Summable (fun n => c n * (n : ℝ) ^ (-s)))
    (hlim : Tendsto (fun s => s * dser c s) (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun s => s * psum c (Real.exp (1 / s))) (𝓝[>] 0) (𝓝 C) := by
  have hC : 0 ≤ C := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_nonneg (le_of_lt hs)
      (tsum_nonneg fun n => mul_nonneg (hc n) (weight_nonneg n s))
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := min 1 (ε / (2 * (C + 1))) with hη_def
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hCη : C * η ≤ ε / 2 := by
    have h1 : C * η ≤ C * (ε / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    have h2 : C * (ε / (2 * (C + 1))) = (ε / 2) * (C / (C + 1)) := by
      field_simp
    have h3 : C / (C + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc C * η ≤ (ε / 2) * (C / (C + 1)) := h1.trans (le_of_eq h2)
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ε / 2 := mul_one _
  obtain ⟨Pl, Pu, hl, hu, hIl, hIu⟩ := exists_sandwich hη hη1
  have htl := tendsto_poly hc hsum hlim Pl
  have htu := tendsto_poly hc hsum hlim Pu
  rw [Metric.tendsto_nhds] at htl htu
  filter_upwards [htl (ε / 2) (by positivity), htu (ε / 2) (by positivity),
    self_mem_nhdsWithin] with s hsl hsu hs
  have hs_pos : (0 : ℝ) < s := hs
  obtain ⟨hlow, hup⟩ := sandwich_tsum hc hc0 hsum hs_pos Pl Pu hl hu
  rw [Real.dist_eq, abs_lt] at hsl hsu ⊢
  have hlow' := mul_le_mul_of_nonneg_left hlow hs_pos.le
  have hup' := mul_le_mul_of_nonneg_left hup hs_pos.le
  have hIl' : C * (1 - η) ≤ C * ∫ y in (0 : ℝ)..1, Pl.eval y :=
    mul_le_mul_of_nonneg_left hIl hC
  have hIu' : C * ∫ y in (0 : ℝ)..1, Pu.eval y ≤ C * (1 + η) :=
    mul_le_mul_of_nonneg_left hIu hC
  constructor <;> nlinarith [hsl.1, hsl.2, hsu.1, hsu.2, hlow', hup', hIl', hIu', hCη]

/-- **Karamata's Tauberian theorem for Dirichlet series with nonnegative coefficients.**

If `c n ≥ 0`, `c 0 = 0`, `∑' n, c n · n^{−s}` converges for every `s > 0`, and
`s · ∑' n, c n · n^{−s} → C` as `s → 0⁺`, then `(∑_{n ≤ x} c n) / log x → C` as `x → ∞`. -/
theorem karamata (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 = 0)
    (hsum : ∀ s : ℝ, 0 < s → Summable (fun n => c n * (n : ℝ) ^ (-s)))
    (hlim : Tendsto (fun s => s * dser c s) (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun x : ℝ => psum c x / Real.log x) atTop (𝓝 C) := by
  have h := tendsto_psum_exp hc hc0 hsum hlim
  have hmap : Tendsto (fun x : ℝ => 1 / Real.log x) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
      exact this.congr fun x => by simp [one_div]
    · filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx
      exact one_div_pos.mpr hx
  refine (h.comp hmap).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  simp only [Function.comp]
  rw [one_div_one_div, Real.exp_log (by linarith)]
  ring

end Karamata

/-! ## Part 2: `WeightedPNTinAPAsymp`, unconditionally

Apply Karamata to `c n = Λ_a(n)/n`.  The Dirichlet series is `∑' n, Λ_a(n)/n^{1+s}`, and
`residueClass_tsum_both_bounds` at `σ = 1 + s ∈ (1, 2]` gives `s · F(s) = 1/φ(q) + O(s)`. -/

section Application

open ArithmeticFunction ArithmeticFunction.vonMangoldt

variable {q : ℕ}

/-- The coefficient sequence `Λ_a(n)/n`. -/
def wcoef (a : ZMod q) (n : ℕ) : ℝ := residueClass a n / n

theorem wcoef_nonneg (a : ZMod q) (n : ℕ) : 0 ≤ wcoef a n :=
  div_nonneg (residueClass_nonneg a n) (Nat.cast_nonneg n)

theorem wcoef_zero (a : ZMod q) : wcoef a 0 = 0 := by simp [wcoef]

/-- `wcoef a n · n^{−s} = Λ_a(n) / n^{1+s}`. -/
theorem wcoef_mul_weight (a : ZMod q) (n : ℕ) (s : ℝ) :
    wcoef a n * (n : ℝ) ^ (-s) = residueClass a n / (n : ℝ) ^ (1 + s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wcoef]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs0 : (n : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos hn0 s).ne'
    rw [wcoef, Real.rpow_add hn0, Real.rpow_one, Real.rpow_neg hn0.le]
    field_simp

/-- Summability of `Λ_a(n)/n^{1+s}` for `s > 0`, by `Λ(n) ≤ log n ≤ (2/s) n^{s/2}`. -/
theorem wcoef_summable (a : ZMod q) {s : ℝ} (hs : 0 < s) :
    Summable (fun n => wcoef a n * (n : ℝ) ^ (-s)) := by
  have hsum : Summable (fun n : ℕ => (2 / s) * (n : ℝ) ^ (-1 - s / 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (wcoef_nonneg a n) (Karamata.weight_nonneg n s)) (fun n => ?_) hsum
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wcoef, Real.zero_rpow (by linarith : (-1 - s / 2 : ℝ) ≠ 0)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [wcoef_mul_weight]
    have h1 : residueClass a n ≤ (2 / s) * (n : ℝ) ^ (s / 2) := by
      calc residueClass a n ≤ vonMangoldt n := residueClass_le a n
        _ ≤ Real.log n := vonMangoldt_le_log
        _ ≤ (n : ℝ) ^ (s / 2) / (s / 2) := Real.log_le_rpow_div hn0.le (by positivity)
        _ = (2 / s) * (n : ℝ) ^ (s / 2) := by field_simp
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
    calc residueClass a n ≤ (2 / s) * (n : ℝ) ^ (s / 2) := h1
      _ = (2 / s) * (n : ℝ) ^ (-1 - s / 2) * (n : ℝ) ^ (1 + s) := by
          rw [mul_assoc, ← Real.rpow_add hn0]
          congr 2; ring

/-- The Tauberian input: `s · ∑' n, Λ_a(n)/n^{1+s} → 1/φ(q)` as `s → 0⁺`.  This is
`residueClass_tsum_both_bounds` at `σ = 1 + s`. -/
theorem wcoef_tendsto [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun s => s * Karamata.dser (wcoef a) s) (𝓝[>] 0)
      (𝓝 ((Nat.totient q : ℝ)⁻¹)) := by
  obtain ⟨M, hM0, hM⟩ := residueClass_tsum_both_bounds ha
  have hdser : ∀ s : ℝ, Karamata.dser (wcoef a) s =
      ∑' n, residueClass a n / (n : ℝ) ^ (1 + s) := by
    intro s; unfold Karamata.dser; exact tsum_congr fun n => wcoef_mul_weight a n s
  have hbound : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      |s * Karamata.dser (wcoef a) s - (Nat.totient q : ℝ)⁻¹| ≤ s * M := by
    intro s hs
    have h := hM (show 1 + s ∈ Set.Ioc 1 2 by constructor <;> linarith [hs.1, hs.2])
    rw [show (1 + s) - 1 = s by ring] at h
    rw [hdser]
    have h2 : |s * ((∑' n, residueClass a n / (n : ℝ) ^ (1 + s)) -
        (Nat.totient q : ℝ)⁻¹ / s)| ≤ s * M := by
      rw [abs_mul, abs_of_pos hs.1]; exact mul_le_mul_of_nonneg_left h hs.1.le
    have h3 : s * ((Nat.totient q : ℝ)⁻¹ / s) = (Nat.totient q : ℝ)⁻¹ := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hs.1.ne']
    rwa [mul_sub, h3] at h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : Set.Ioc (0 : ℝ) (min 1 (ε / (M + 1))) ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (lt_min one_pos (by positivity))
  filter_upwards [hev] with s hs
  rw [Real.dist_eq]
  have hs1 : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  calc |s * Karamata.dser (wcoef a) s - (Nat.totient q : ℝ)⁻¹| ≤ s * M := hbound s hs1
    _ ≤ (ε / (M + 1)) * M :=
        mul_le_mul_of_nonneg_right (hs.2.trans (min_le_right _ _)) hM0.le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- `psum (wcoef a) x` is the residue-class-restricted sum `∑_{n ≤ x, n ≡ a (q)} Λ(n)/n`. -/
theorem psum_wcoef (a : ℕ) (x : ℝ) :
    Karamata.psum (wcoef (a : ZMod q)) x =
      ∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q), vonMangoldt n / n := by
  unfold Karamata.psum wcoef
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, ZMod.natCast_eq_natCast_iff']
  split_ifs <;> simp

/-- **`WeightedPNTinAPAsymp` is a theorem.**  Karamata applied to `Λ_a(n)/n`, with the
Dirichlet-series input `residueClass_tsum_both_bounds` (from Mathlib's `L(1,χ) ≠ 0`). -/
theorem weightedPNTinAP_asymp_proved : WeightedPNTinAPAsymp := by
  intro q a hq hcop ε hε
  have : NeZero q := ⟨by omega⟩
  have ha : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hkar := Karamata.karamata (wcoef_nonneg (a : ZMod q)) (wcoef_zero _)
    (fun s hs => wcoef_summable _ hs) (wcoef_tendsto ha)
  rw [Metric.tendsto_nhds] at hkar
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp ((hkar ε hε).and (eventually_ge_atTop 2))
  refine ⟨max x₀ 2, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  rw [Real.dist_eq, psum_wcoef] at h1
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  set S : ℝ := ∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q),
    vonMangoldt n / (n : ℝ) with hS
  have heq : |S - Real.log x / Nat.totient q| =
      Real.log x * |S / Real.log x - (Nat.totient q : ℝ)⁻¹| := by
    rw [← abs_of_pos hlog, ← abs_mul, abs_of_pos hlog]
    congr 1
    field_simp
  rw [heq]
  calc Real.log x * |S / Real.log x - (Nat.totient q : ℝ)⁻¹|
      ≤ Real.log x * ε := mul_le_mul_of_nonneg_left h1.le hlog.le
    _ = ε * Real.log x := mul_comm _ _

/-- **`PrimesEquidistInAPAsymp` is a theorem**: `∑_{p ≤ x, p ≡ a (q)} 1/p ~ (log log x)/φ(q)`,
via the proved asymptotic chain of `EM/IK/AbelChain.lean`. -/
theorem primesEquidistInAP_asymp_proved : PrimesEquidistInAPAsymp :=
  wpnt_asymp_implies_primes_equidist_asymp weightedPNTinAP_asymp_proved

end Application

end IK
