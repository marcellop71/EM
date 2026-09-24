import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The Mertens function and its divisor-sum recursion (Mathlib-only)

`mertens N = ∑_{n ≤ N} μ(n)`.  The content of this file is the pair of identities obtained by
summing `ζ * μ = 1` and `μ * ζ = 1` over `n ≤ N`:

* `sum_mertens_div` : `∑_{n ≤ N} M(⌊N/n⌋) = 1`     (`N ≥ 1`),
* `sum_moebius_mul_div` : `∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1` (`N ≥ 1`),

and the recursion `mertens_eq_one_sub` : `M(N) = 1 - ∑_{2 ≤ n ≤ N} M(⌊N/n⌋)` which every
sub-linear algorithm for `M` (Meissel–Lehmer style, Deléglise–Rivat) is an organisation of:
`⌊N/n⌋` takes only `O(√N)` distinct values.

The second identity isolates the archimedean content of `M`: replacing `⌊N/n⌋` by `N/n` would
give `N · ∑ μ(n)/n = 1`.  Over `𝔽_q[X]` the corresponding count of multiples in a degree box is
exact and the recursion collapses (`∑_{deg f = n} μ(f) = 0` for `n ≥ 2`); see
`docs/analysis/mertens_function_2026-09-17.md`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The Mertens function `M(N) = ∑_{1 ≤ n ≤ N} μ(n)`. -/
def mertens (N : ℕ) : ℤ := ∑ n ∈ Ioc 0 N, μ n

@[simp] theorem mertens_zero : mertens 0 = 0 := by simp [mertens]

theorem mertens_succ (N : ℕ) : mertens (N + 1) = mertens N + μ (N + 1) := by
  simp [mertens, Finset.sum_Ioc_succ_top]

@[simp] theorem mertens_one : mertens 1 = 1 := by simp [mertens_succ]

/-- The trivial bound `|M(N)| ≤ N`. -/
theorem abs_mertens_le (N : ℕ) : |mertens N| ≤ N := by
  calc |mertens N| ≤ ∑ n ∈ Ioc 0 N, |μ n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℤ) := sum_le_sum fun _ _ ↦ abs_moebius_le_one
    _ = N := by simp

/-- Summing `ζ * μ = 1` over `n ≤ N`. -/
private theorem sum_Ioc_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, (1 : ArithmeticFunction ℤ) n = 1 := by
  rw [Finset.sum_eq_single 1]
  · simp
  · intro n _ hn; simp [one_apply_ne hn]
  · intro h; exact absurd (mem_Ioc.mpr ⟨Nat.one_pos, hN⟩) h

/-- **The divisor-sum identity** `∑_{n ≤ N} M(⌊N/n⌋) = 1`. -/
theorem sum_mertens_div {N : ℕ} (hN : 1 ≤ N) : ∑ n ∈ Ioc 0 N, mertens (N / n) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum (ζ : ArithmeticFunction ℤ) μ N
  rw [coe_zeta_mul_moebius, sum_Ioc_one hN] at h
  rw [h]
  refine sum_congr rfl fun n hn ↦ ?_
  have : n ≠ 0 := by simp only [mem_Ioc] at hn; omega
  simp [mertens, natCoe_apply, zeta_apply, this]

/-- `∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1`: all of `M` is in the floors. -/
theorem sum_moebius_mul_div {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, μ n * ((N / n : ℕ) : ℤ) = 1 := by
  have h := sum_Ioc_mul_zeta_eq_sum (μ : ArithmeticFunction ℤ) N
  rw [moebius_mul_coe_zeta, sum_Ioc_one hN] at h
  exact h.symm

/-- **The recursion** `M(N) = 1 - ∑_{2 ≤ n ≤ N} M(⌊N/n⌋)`. -/
theorem mertens_eq_one_sub {N : ℕ} (hN : 1 ≤ N) :
    mertens N = 1 - ∑ n ∈ Ioc 1 N, mertens (N / n) := by
  have h := sum_mertens_div hN
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN] at h
  simp only [Nat.Ioc_succ_singleton, zero_add, sum_singleton, Nat.div_one] at h
  linarith
