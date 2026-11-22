import EM.FunctionField.QuadCharBridge
import EM.FunctionField.StableDensity
import EM.IK.GRHBridge

/-!
# Stable primes under GRH: the chain assembled

The stable primes are the `p` for which the function-field Mullin conjecture over `𝔽_p` is
false among those where it is not the dichotomy (`TowerClassification.lean`). This file
composes the three steps

1. explicit formula + zero count + zeros on the line `⟹ |ψ(x, χ)| ≤ C √x log²(N x)`
   (`IK.grhPsiBound_of_explicitFormula`, `EM/IK/GRHBridge.lean`);
2. that bound `⟹ |∑_{p ≤ x} (D / p)| ≤ C' √x log²(|D| x)` for non-square `D`
   (`QuadCharBridge.quadPrimeSumBound_of_grhPsiBound`);
3. that bound `⟹ #{stable p ≤ x} ≤ x / 2^K + C' √x log²(4^{2^K} x)`
   (`StableCount.card_stable_le`),

and makes the choice `2^K ≈ x^{1/6}`.

## Main results

* `card_stable_le_of_grh` — the count for every `K`, from the three statements quoted from
  `leanprover-community/riemann-hypothesis`.
* `card_stable_le_rpow` — `#{stable p ≤ x} ≤ C x^{5/6}` under `QuadPrimeSumBound`.
* `card_stable_le_rpow_of_grh` — the same from the three quoted statements.

The three hypotheses are theorems of that repository (`truncated_explicit_formula`,
`zeroCount_holds`, `LFunction_eq_zero_re`), stated here with Mathlib's definitions only. The
repository is not a dependency; nothing here is an axiom.
-/

namespace FunctionFieldAnalog

namespace StableGRH

open Finset StableCount

/-- The prime-sum bound is monotone in the constant. -/
theorem quadPrimeSumBound_mono {C C' : ℝ} (hCC : C ≤ C') (h : QuadPrimeSumBound C) :
    QuadPrimeSumBound C' := fun D hD x hx =>
  (h D hD x hx).trans (by gcongr)

/-- The `ψ` bound is monotone in the constant. -/
theorem grhPsiBound_mono {C C' : ℝ} (hCC : C ≤ C') (h : IK.GRHPsiBound C) :
    IK.GRHPsiBound C' := fun N _ χ hχ x hx =>
  (h N χ hχ x hx).trans (by gcongr)

/-- **The prime-sum bound from the quoted statements.** -/
theorem exists_quadPrimeSumBound_of_grh (hE : IK.TruncatedExplicitFormula)
    (hZ : IK.ZeroCountUnitWindow) (hG : IK.DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ QuadPrimeSumBound C := by
  obtain ⟨C₀, h₀⟩ := IK.grhPsiBound_of_explicitFormula hE hZ hG
  obtain ⟨C₁, h₁⟩ := QuadCharBridge.quadPrimeSumBound_of_grhPsiBound (le_max_right C₀ 0)
    (grhPsiBound_mono (le_max_left C₀ 0) h₀)
  exact ⟨max C₁ 0, le_max_right _ _, quadPrimeSumBound_mono (le_max_left _ _) h₁⟩

/-- **Stable primes under GRH, every `K`.** -/
theorem card_stable_le_of_grh (hE : IK.TruncatedExplicitFormula)
    (hZ : IK.ZeroCountUnitWindow) (hG : IK.DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K x : ℕ, 2 ≤ x →
      ((stableLE x).card : ℝ) ≤
        (x : ℝ) / 2 ^ K + C * Real.sqrt x * Real.log ((4 : ℝ) ^ 2 ^ K * x) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_quadPrimeSumBound_of_grh hE hZ hG
  exact ⟨C, hC, fun K x hx => card_stable_le hC h K x hx⟩

/-- **The power saving.** Under the prime-sum bound, `#{stable p ≤ x} ≤ (2 + 81 C) x^{5/6}`. -/
theorem card_stable_le_rpow {C : ℝ} (hC : 0 ≤ C) (h : QuadPrimeSumBound C) (x : ℕ)
    (hx : 2 ≤ x) : ((stableLE x).card : ℝ) ≤ (2 + 81 * C) * (x : ℝ) ^ (5 / 6 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  -- `y = x^{1/6}`
  set y : ℝ := (x : ℝ) ^ (1 / 6 : ℝ) with hy
  have hy6 : y ^ 6 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy5 : y ^ 5 = (x : ℝ) ^ (5 / 6 : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hy0 : 0 < y := by linarith
  -- `K` with `64^K ≤ x < 64^{K+1}`, `t = 2^K`
  set K := Nat.log 64 x with hK
  have hlo : (64 : ℕ) ^ K ≤ x := Nat.pow_log_le_self 64 (by omega)
  have hhi : x < 64 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  set t : ℝ := 2 ^ K with ht
  have ht0 : 0 < t := by positivity
  have ht6 : t ^ 6 ≤ y ^ 6 := by
    rw [hy6, ht, ← pow_mul, mul_comm, pow_mul]
    exact_mod_cast hlo
  have hty : t ≤ y := le_of_pow_le_pow_left₀ (by norm_num) hy0.le ht6
  have hyt : y < 2 * t := by
    have h1 : y ^ 6 < (2 * t) ^ 6 := by
      rw [hy6, ht, ← pow_succ', ← pow_mul, mul_comm, pow_mul]
      exact_mod_cast hhi
    exact lt_of_pow_lt_pow_left₀ 6 (by positivity) h1
  have hmain := card_stable_le hC h K x hx
  -- first term: `x / t ≤ 2 y^5`
  have h1 : (x : ℝ) / 2 ^ K ≤ 2 * y ^ 5 := by
    rw [← ht, div_le_iff₀ ht0, ← hy6]
    nlinarith [pow_pos hy0 5]
  -- `√x = y^3`
  have hsqrt : Real.sqrt x = y ^ 3 := by
    rw [← hy6, show y ^ 6 = (y ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  -- `log(4^t x) ≤ 9 y`
  have hlog : Real.log ((4 : ℝ) ^ 2 ^ K * x) ≤ 9 * y := by
    have hpow : (0 : ℝ) < (4 : ℝ) ^ 2 ^ K := by positivity
    rw [Real.log_mul hpow.ne' (by linarith), Real.log_pow]
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have hlx : Real.log x ≤ 6 * y := by
      rw [← hy6, Real.log_pow]
      have := Real.log_le_sub_one_of_pos hy0
      push_cast; nlinarith
    have hcast : ((2 ^ K : ℕ) : ℝ) = t := by rw [ht]; push_cast; ring
    rw [hcast]
    have h4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hlog0 : 0 ≤ Real.log ((4 : ℝ) ^ 2 ^ K * x) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (4 : ℝ) ^ 2 ^ K := one_le_pow₀ (by norm_num)
      nlinarith)
  have h2 : C * Real.sqrt x * Real.log ((4 : ℝ) ^ 2 ^ K * x) ^ 2 ≤ 81 * C * y ^ 5 := by
    rw [hsqrt]
    have hsq : Real.log ((4 : ℝ) ^ 2 ^ K * x) ^ 2 ≤ (9 * y) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    calc C * y ^ 3 * Real.log ((4 : ℝ) ^ 2 ^ K * x) ^ 2
        ≤ C * y ^ 3 * (9 * y) ^ 2 := by gcongr
      _ = 81 * C * y ^ 5 := by ring
  rw [← hy5]
  linarith

/-- **Stable primes are `O(x^{5/6})` under GRH**, from the three quoted statements. -/
theorem card_stable_le_rpow_of_grh (hE : IK.TruncatedExplicitFormula)
    (hZ : IK.ZeroCountUnitWindow) (hG : IK.DirichletLZerosOnLine) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → ((stableLE x).card : ℝ) ≤ C * (x : ℝ) ^ (5 / 6 : ℝ) := by
  obtain ⟨C, hC, h⟩ := exists_quadPrimeSumBound_of_grh hE hZ hG
  exact ⟨2 + 81 * C, fun x hx => card_stable_le_rpow hC h x hx⟩

end StableGRH

end FunctionFieldAnalog
