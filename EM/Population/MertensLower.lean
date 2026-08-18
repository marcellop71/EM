import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Analysis.Complex.ExponentialBounds
import EM.Population.LargeStepRoughness

/-!
# Mertens' first theorem: the **lower** bound

Group 7 / **C4 tail estimate** of the verified statement list
(`agents/state/findings_ls_verification.md` §2.10; Session 310).

The repository already carries the *upper* Mertens estimate
`LargeStepRoughness.mertens_upper`, obtained by discrete summation by parts against
Chebyshev's `θ`.  The tail estimate of Group 7 needs the matching *lower* bound

```
log n - 13  ≤  ∑_{p ≤ n, p prime} (log p)/p            (`mertens_lower`)
```

which is **not** in Mathlib (Mathlib only has qualitative divergence of `∑ 1/p`,
`Mathlib.NumberTheory.SumPrimeReciprocals`).  We prove it from scratch, by the
classical elementary route of Mertens / Chebyshev:

1. **C0** — `n^n ≤ e^n · n!` (elementary induction on `(1+1/k)^k ≤ e`), hence
   `n log n - n ≤ log (n!)`.
2. **C1** — Legendre's factorisation identity, in logarithmic form:
   `log (n!) = ∑_{p ≤ n} ν_p(n!) · log p`.
3. **C2** — the exponent bound `ν_p(n!) ≤ n/p + 2n/p²` (Legendre's formula plus a
   geometric tail).
4. **C3** — the convergent constant `∑_{2 ≤ k ≤ n} (log k)/k² ≤ 6`, by the
   comparison `log k ≤ 2√k` and a telescoping `k^{-3/2} ≤ 2/√(k-1) - 2/√k`.
5. **C4** — assembling: `n log n - n ≤ n·∑ (log p)/p + 12 n`, divide by `n`.
6. **C5** — the *windowed* consequence `log log Y - log log z - 16 ≤ ∑_{z<r≤Y} 1/r`
   for `16 ≤ z ≤ Y` (`window_recip_lower`), by discrete summation by parts of
   `∑ (log r/r)·(1/log r)` against the two-sided control
   `log t - 13 ≤ M(t) ≤ 2 log 4 (2 + log t)` (the upper half is
   `LargeStepRoughness.mertens_upper`).

Everything is finitary and elementary: no integrals, no analytic number theory,
no computation on specific integers.
-/

namespace MertensLower

open Finset

/-! ## C0.  A factorial lower bound: `n^n ≤ e^n · n!` -/

/-- `(k+1)^k ≤ e · k^k` for `k ≥ 1`: the classical `(1 + 1/k)^k ≤ e`. -/
private theorem succ_pow_le_exp_mul (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) + 1) ^ k ≤ Real.exp 1 * (k : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hstep : (k : ℝ) + 1 ≤ (k : ℝ) * Real.exp (1 / (k : ℝ)) := by
    have h := Real.add_one_le_exp (1 / (k : ℝ))
    have h2 : (k : ℝ) * (1 / (k : ℝ) + 1) ≤ (k : ℝ) * Real.exp (1 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left h hk0.le
    have h3 : (k : ℝ) * (1 / (k : ℝ) + 1) = 1 + (k : ℝ) := by
      field_simp
    linarith [h2, h3.symm.le, h3.le]
  have hpow : ((k : ℝ) + 1) ^ k ≤ ((k : ℝ) * Real.exp (1 / (k : ℝ))) ^ k := by
    gcongr
  have hexp : ((k : ℝ) * Real.exp (1 / (k : ℝ))) ^ k = Real.exp 1 * (k : ℝ) ^ k := by
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp]
    ring
  linarith [hpow, hexp.le, hexp.symm.le]

/-- **C0.**  `n^n ≤ e^n · n!` for every `n`. -/
theorem pow_self_le_exp_mul_factorial (n : ℕ) :
    (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
      have hs := succ_pow_le_exp_mul k hk
      have hkey : ((k : ℝ) + 1) ^ k ≤ Real.exp 1 * (Real.exp k * (k.factorial : ℝ)) := by
        calc ((k : ℝ) + 1) ^ k ≤ Real.exp 1 * (k : ℝ) ^ k := hs
          _ ≤ Real.exp 1 * (Real.exp k * (k.factorial : ℝ)) := by
              exact mul_le_mul_of_nonneg_left ih (Real.exp_pos 1).le
      have hfacs : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hexpsum : Real.exp ((k : ℝ) + 1) = Real.exp 1 * Real.exp k := by
        rw [Real.exp_add]; ring
      have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      calc (((k + 1 : ℕ) : ℝ)) ^ (k + 1)
          = ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ k) := by push_cast; ring
        _ ≤ ((k : ℝ) + 1) * (Real.exp 1 * (Real.exp k * (k.factorial : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hkey hpos.le
        _ = Real.exp ((k : ℝ) + 1) * (((k : ℝ) + 1) * (k.factorial : ℝ)) := by
            rw [hexpsum]; ring
        _ = Real.exp (((k + 1 : ℕ) : ℝ)) * (((k + 1).factorial : ℕ) : ℝ) := by
            rw [hfacs]; push_cast; ring

/-- **C0, logarithmic form.**  `n log n - n ≤ log (n!)` for `1 ≤ n`. -/
theorem log_factorial_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hpow : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hn0 n
  have h := pow_self_le_exp_mul_factorial n
  have hlog := Real.log_le_log hpow h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hfac.ne', Real.log_exp] at hlog
  linarith

/-! ## C1.  Legendre's factorisation identity in logarithmic form -/

/-- **C1.**  `log (n!) = ∑_{p ≤ n, p prime} ν_p(n!) · log p`. -/
theorem log_factorial_eq_sum (n : ℕ) :
    Real.log (n.factorial : ℝ)
      = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
          ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  have hne : n.factorial ≠ 0 := n.factorial_ne_zero
  have hprod : n.factorial = ∏ p ∈ n.factorial.primeFactors, p ^ n.factorial.factorization p :=
    Nat.prod_primeFactors_pow_factorization hne
  have hR : (n.factorial : ℝ)
      = ∏ p ∈ n.factorial.primeFactors, ((p : ℝ) ^ n.factorial.factorization p) := by
    rw [show ((n.factorial : ℕ) : ℝ)
        = ((∏ p ∈ n.factorial.primeFactors, p ^ n.factorial.factorization p : ℕ) : ℝ) from
      congrArg _ hprod]
    push_cast
    rfl
  have hne' : ∀ p ∈ n.factorial.primeFactors, ((p : ℝ) ^ n.factorial.factorization p) ≠ 0 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    positivity
  have hsub : n.factorial.primeFactors ⊆ (Finset.range (n + 1)).filter Nat.Prime := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n.factorial := Nat.dvd_of_mem_primeFactors hp
    have hle : p ≤ n := (Nat.Prime.dvd_factorial hpp).mp hdvd
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp⟩
  have hzero : ∀ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      p ∉ n.factorial.primeFactors →
      ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p = 0 := by
    intro p _ hp
    have : n.factorial.factorization p = 0 := by
      rw [← Nat.support_factorization] at hp
      exact Finsupp.notMem_support_iff.mp hp
    rw [this]
    simp
  have hcongr : ∀ i ∈ n.factorial.primeFactors,
      Real.log ((i : ℝ) ^ n.factorial.factorization i)
        = ((n.factorial.factorization i : ℕ) : ℝ) * Real.log i := by
    intro i _
    rw [Real.log_pow]
  rw [hR, Real.log_prod hne', Finset.sum_congr rfl hcongr]
  exact Finset.sum_subset hsub hzero

/-! ## C2.  The exponent bound `ν_p(n!) ≤ n/p + 2n/p²` -/

/-- A finite geometric sum with ratio at most `1/2` is at most `2`. -/
private theorem geom_range_le_two (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (b : ℕ) :
    ∑ i ∈ Finset.range b, x ^ i ≤ 2 := by
  have key : ∀ m : ℕ, ∑ i ∈ Finset.range m, x ^ i ≤ 2 * (1 - x ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ j ih =>
      have hxj : (0 : ℝ) ≤ x ^ j := pow_nonneg hx0 j
      have hstep : 2 * x * x ^ j ≤ x ^ j := by nlinarith
      rw [Finset.sum_range_succ]
      have : x ^ (j + 1) = x * x ^ j := by ring
      rw [this]
      nlinarith [ih]
  have hb : (0 : ℝ) ≤ x ^ b := pow_nonneg hx0 b
  linarith [key b]

/-- **C2.**  For a prime `p` and `1 ≤ n`, `ν_p(n!) ≤ n/p + 2n/p²`.

Legendre's formula `ν_p(n!) = ∑_{i ≥ 1} ⌊n/p^i⌋`, then `⌊n/p^i⌋ ≤ n/p^i` termwise
and a geometric tail `∑_{i ≥ 2} n/p^i ≤ 2n/p²`. -/
theorem factorization_factorial_le (n p : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / p + 2 * (n : ℝ) / (p : ℝ) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hb : Nat.log p n < n + 1 := by
    have := Nat.log_lt_self p (show n ≠ 0 by omega)
    omega
  rw [Nat.factorization_def _ hp, padicValNat_factorial hb]
  -- termwise: `⌊n/p^i⌋ ≤ n/p^i`
  have hcast : (((∑ i ∈ Finset.Ico 1 (n + 1), n / p ^ i : ℕ)) : ℝ)
      ≤ ∑ i ∈ Finset.Ico 1 (n + 1), (n : ℝ) / (p : ℝ) ^ i := by
    rw [Nat.cast_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := p ^ i)
    simpa using this
  -- split off the `i = 1` term
  have hsplit : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ico 2 (n + 1)) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Ico 2 (n + 1) := by simp
  have hhead : ∑ i ∈ Finset.Ico 1 (n + 1), (n : ℝ) / (p : ℝ) ^ i
      = (n : ℝ) / (p : ℝ) + ∑ i ∈ Finset.Ico 2 (n + 1), (n : ℝ) / (p : ℝ) ^ i := by
    rw [hsplit, Finset.sum_insert hnotmem]
    simp
  -- the geometric tail
  have htail : ∑ i ∈ Finset.Ico 2 (n + 1), (n : ℝ) / (p : ℝ) ^ i
      ≤ 2 * (n : ℝ) / (p : ℝ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hrw : ∀ j ∈ Finset.range (n + 1 - 2),
        (n : ℝ) / (p : ℝ) ^ (2 + j) = ((n : ℝ) / (p : ℝ) ^ 2) * (1 / (p : ℝ)) ^ j := by
      intro j _
      rw [pow_add, div_pow, one_pow]
      field_simp
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    have hx : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hp2
    have hx0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hg := geom_range_le_two (1 / (p : ℝ)) hx0 hx (n + 1 - 2)
    have hnn : (0 : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ 2 := by positivity
    calc ((n : ℝ) / (p : ℝ) ^ 2) * (∑ j ∈ Finset.range (n + 1 - 2), (1 / (p : ℝ)) ^ j)
        ≤ ((n : ℝ) / (p : ℝ) ^ 2) * 2 := by exact mul_le_mul_of_nonneg_left hg hnn
      _ = 2 * (n : ℝ) / (p : ℝ) ^ 2 := by ring
  calc (((∑ i ∈ Finset.Ico 1 (n + 1), n / p ^ i : ℕ)) : ℝ)
      ≤ ∑ i ∈ Finset.Ico 1 (n + 1), (n : ℝ) / (p : ℝ) ^ i := hcast
    _ = (n : ℝ) / (p : ℝ) + ∑ i ∈ Finset.Ico 2 (n + 1), (n : ℝ) / (p : ℝ) ^ i := hhead
    _ ≤ (n : ℝ) / (p : ℝ) + 2 * (n : ℝ) / (p : ℝ) ^ 2 := by linarith

/-! ## C3.  The convergent constant `∑_{2 ≤ k ≤ n} (log k)/k² ≤ 6` -/

/-- The telescoping step: for `0 < a ≤ b` with `b² = a² + 1` one has
`1/b³ ≤ 2(1/a - 1/b)`. -/
private theorem inv_cube_le_telescope {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hsq : b ^ 2 = a ^ 2 + 1) : 1 / b ^ 3 ≤ 2 * (1 / a - 1 / b) := by
  have hfac : (b - a) * (b + a) = 1 := by linear_combination hsq
  have hsum : (0 : ℝ) < b + a := by linarith
  have h1 : a * (b + a) ≤ 2 * b ^ 2 := by nlinarith
  have h2 : a * (b + a) ≤ (2 * (b - a) * b ^ 2) * (b + a) := by
    have heq : 2 * b ^ 2 = (2 * (b - a) * b ^ 2) * (b + a) := by
      linear_combination (-(2 * b ^ 2)) * hfac
    linarith [h1, heq.le, heq.symm.le]
  have hkey : a ≤ 2 * (b - a) * b ^ 2 := le_of_mul_le_mul_right h2 hsum
  have hb3 : (0 : ℝ) < b ^ 3 := by positivity
  rw [div_le_iff₀ hb3]
  have hrw : 2 * (1 / a - 1 / b) * b ^ 3 = 2 * (b - a) * b ^ 2 / a := by
    field_simp
  rw [hrw, le_div_iff₀ ha]
  linarith

/-- The per-term comparison: for `2 ≤ k`,
`(log k)/k² ≤ 4 (1/√(k-1) - 1/√k)`. -/
private theorem log_div_sq_le_telescope (k : ℕ) (hk : 2 ≤ k) :
    Real.log k / (k : ℝ) ^ 2
      ≤ 4 * (1 / Real.sqrt ((k : ℝ) - 1) - 1 / Real.sqrt (k : ℝ)) := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
  have hkm : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  set a := Real.sqrt ((k : ℝ) - 1) with ha_def
  set b := Real.sqrt (k : ℝ) with hb_def
  have hasq : a ^ 2 = (k : ℝ) - 1 := Real.sq_sqrt hkm
  have hbsq : b ^ 2 = (k : ℝ) := Real.sq_sqrt hk0
  have hapos : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hsq : b ^ 2 = a ^ 2 + 1 := by rw [hasq, hbsq]; ring
  -- step 1: `log k ≤ 2 b`
  have hlogb : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hbpos
  have hlogk : Real.log (k : ℝ) = 2 * Real.log b := by
    rw [← hbsq, Real.log_pow]
    push_cast
    ring
  have hstep1 : Real.log (k : ℝ) ≤ 2 * b := by rw [hlogk]; linarith
  -- step 2: `(log k)/k² ≤ 2/b³`
  have hk4 : (k : ℝ) ^ 2 = b ^ 4 := by rw [← hbsq]; ring
  have hb3 : (0 : ℝ) < b ^ 3 := by positivity
  have hb4 : (0 : ℝ) < b ^ 4 := by positivity
  have hstep2 : Real.log (k : ℝ) / (k : ℝ) ^ 2 ≤ 2 * (1 / b ^ 3) := by
    rw [hk4]
    rw [div_le_iff₀ hb4]
    have : 2 * (1 / b ^ 3) * b ^ 4 = 2 * b := by field_simp
    rw [this]
    exact hstep1
  -- step 3: telescope
  have hstep3 := inv_cube_le_telescope hapos hbpos hab hsq
  linarith

/-- **C3.**  `∑_{2 ≤ k ≤ n} (log k)/k² ≤ 6`.  (In fact `≤ 4`; the slack is
deliberate.) -/
theorem sum_log_div_sq_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 n, Real.log k / (k : ℝ) ^ 2 ≤ 6 := by
  have hIcc : Finset.Icc 2 n = Finset.Ico 2 (n + 1) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  set m := n + 1 - 2 with hm_def
  -- the telescoping antiderivative
  set G : ℕ → ℝ := fun j => 4 / Real.sqrt ((j : ℝ) + 1) with hG_def
  have hterm : ∀ j ∈ Finset.range m,
      Real.log ((2 + j : ℕ) : ℝ) / (((2 + j : ℕ)) : ℝ) ^ 2 ≤ G j - G (j + 1) := by
    intro j _
    have h := log_div_sq_le_telescope (2 + j) (by omega)
    have hc1 : ((2 + j : ℕ) : ℝ) - 1 = (j : ℝ) + 1 := by push_cast; ring
    have hc2 : ((2 + j : ℕ) : ℝ) = ((j : ℝ) + 1) + 1 := by push_cast; ring
    rw [hc1] at h
    have hG0 : G j = 4 / Real.sqrt ((j : ℝ) + 1) := rfl
    have hG1 : G (j + 1) = 4 / Real.sqrt (((j : ℝ) + 1) + 1) := by
      rw [hG_def]; push_cast; ring_nf
    rw [hG0, hG1, ← hc2]
    have hrw : 4 * (1 / Real.sqrt ((j : ℝ) + 1) - 1 / Real.sqrt ((2 + j : ℕ) : ℝ))
        = 4 / Real.sqrt ((j : ℝ) + 1) - 4 / Real.sqrt ((2 + j : ℕ) : ℝ) := by
      ring
    rw [hrw] at h
    exact h
  have hsum : ∑ j ∈ Finset.range m, Real.log ((2 + j : ℕ) : ℝ) / (((2 + j : ℕ)) : ℝ) ^ 2
      ≤ ∑ j ∈ Finset.range m, (G j - G (j + 1)) := Finset.sum_le_sum hterm
  have htel : ∑ j ∈ Finset.range m, (G j - G (j + 1)) = G 0 - G m :=
    Finset.sum_range_sub' G m
  have hG0 : G 0 = 4 := by
    rw [hG_def]
    norm_num
  have hGm : 0 ≤ G m := by
    rw [hG_def]
    positivity
  calc ∑ j ∈ Finset.range m, Real.log ((2 + j : ℕ) : ℝ) / (((2 + j : ℕ)) : ℝ) ^ 2
      ≤ ∑ j ∈ Finset.range m, (G j - G (j + 1)) := hsum
    _ = G 0 - G m := htel
    _ ≤ 4 := by rw [hG0]; linarith
    _ ≤ 6 := by norm_num

/-! ## C4.  Mertens' first theorem, lower bound -/

/-- **C4 — Mertens I, lower bound.**  For `2 ≤ n`,

```
log n - 13  ≤  ∑_{p ≤ n, p prime} (log p)/p.
```

The constant `13 = 1 + 2·6` comes from `C0` (the `-n` in `n log n - n`) and from
`C3` (the convergent constant `∑ (log k)/k² ≤ 6` doubled by `C2`).  It is
absolute and explicit; no attempt is made to optimise it.

Group 7 / **C4 tail estimate**, `findings_ls_verification.md` §2.10. -/
theorem mertens_lower (n : ℕ) (hn : 2 ≤ n) :
    Real.log n - 13 ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  set S := (Finset.range (n + 1)).filter Nat.Prime with hS_def
  have hprime : ∀ p ∈ S, p.Prime ∧ p ≤ n := by
    intro p hp
    rw [hS_def, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.2, by omega⟩
  -- (a) the factorial lower bound
  have h1 : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) :=
    log_factorial_lower n (by omega)
  -- (b) Legendre in logarithmic form
  have h2 := log_factorial_eq_sum n
  -- (c) the exponent bound
  have h3 : ∑ p ∈ S, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ S, ((n : ℝ) / p + 2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log p := by
    refine Finset.sum_le_sum ?_
    intro p hp
    obtain ⟨hpp, _⟩ := hprime p hp
    have hlognn : (0 : ℝ) ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    exact mul_le_mul_of_nonneg_right (factorization_factorial_le n p hpp (by omega)) hlognn
  -- (d) split the sum
  have h4 : ∑ p ∈ S, ((n : ℝ) / p + 2 * (n : ℝ) / (p : ℝ) ^ 2) * Real.log p
      = (n : ℝ) * (∑ p ∈ S, Real.log p / p)
        + 2 * (n : ℝ) * (∑ p ∈ S, Real.log p / (p : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  -- (e) the convergent piece
  have hsub : S ⊆ Finset.Icc 2 n := by
    intro p hp
    obtain ⟨hpp, hple⟩ := hprime p hp
    rw [Finset.mem_Icc]
    exact ⟨hpp.two_le, hple⟩
  have hnn : ∀ k ∈ Finset.Icc 2 n, k ∉ S → (0 : ℝ) ≤ Real.log k / (k : ℝ) ^ 2 := by
    intro k hk _
    rw [Finset.mem_Icc] at hk
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hl : (0 : ℝ) ≤ Real.log k := Real.log_nonneg this
    positivity
  have h5 : ∑ p ∈ S, Real.log p / (p : ℝ) ^ 2 ≤ ∑ k ∈ Finset.Icc 2 n, Real.log k / (k : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have h6 : ∑ p ∈ S, Real.log p / (p : ℝ) ^ 2 ≤ 6 := le_trans h5 (sum_log_div_sq_le n)
  -- (f) assemble
  have hbig : (n : ℝ) * Real.log n - n
      ≤ (n : ℝ) * (∑ p ∈ S, Real.log p / p) + 2 * (n : ℝ) * 6 := by
    have hmul : 2 * (n : ℝ) * (∑ p ∈ S, Real.log p / (p : ℝ) ^ 2) ≤ 2 * (n : ℝ) * 6 :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    rw [h2] at h1
    linarith [h1, h3, h4.le, h4.symm.le, hmul]
  have hfinal : (n : ℝ) * (Real.log n - 13) ≤ (n : ℝ) * (∑ p ∈ S, Real.log p / p) := by
    nlinarith [hbig]
  exact le_of_mul_le_mul_left hfinal hn0


/-! ## C5.  A windowed `log log` lower bound

Discrete summation by parts of `∑_{z < r ≤ Y} 1/r = ∑ (log r / r) · (1/log r)`
against the partial Mertens sum `M(t) = ∑_{p ≤ t} (log p)/p`, using the two-sided
control `log t - 13 ≤ M(t) ≤ 2 log 4 (2 + log t)` (`mertens_lower` above, and
`LargeStepRoughness.mertens_upper`).
-/

open LargeStepRoughness

/-- The Abel weight `1/log t`. -/
private noncomputable def wt (t : ℕ) : ℝ := 1 / Real.log t

/-- `log log t`. -/
private noncomputable def LL (t : ℕ) : ℝ := Real.log (Real.log t)

/-- The Mertens increment `gLog t / t`, i.e. `(log t)/t` on primes and `0` elsewhere. -/
private noncomputable def aterm (t : ℕ) : ℝ := gLog t / (t : ℝ)

private theorem M_succ (t : ℕ) : mertensPartial (t + 1) = mertensPartial t + aterm (t + 1) := by
  rw [mertensPartial_succ, aterm]
  push_cast
  ring

/-- Telescoping over `Finset.Ico`, decreasing form. -/
private theorem sum_Ico_telescope (f : ℕ → ℝ) (A B : ℕ) (h : A ≤ B) :
    ∑ t ∈ Finset.Ico A B, (f t - f (t + 1)) = f A - f B := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hg : ∀ j ∈ Finset.range (B - A),
      f (A + j) - f (A + j + 1) = (fun i => f (A + i)) j - (fun i => f (A + i)) (j + 1) := by
    intro j _
    simp only [← Nat.add_assoc]
  rw [Finset.sum_congr rfl hg, Finset.sum_range_sub' (fun i => f (A + i)) (B - A)]
  simp only [Nat.add_zero]
  rw [Nat.add_sub_cancel' h]

/-- Telescoping over `Finset.Ico`, increasing form. -/
private theorem sum_Ico_telescope' (f : ℕ → ℝ) (A B : ℕ) (h : A ≤ B) :
    ∑ t ∈ Finset.Ico A B, (f (t + 1) - f t) = f B - f A := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hg : ∀ j ∈ Finset.range (B - A),
      f (A + j + 1) - f (A + j) = (fun i => f (A + i)) (j + 1) - (fun i => f (A + i)) j := by
    intro j _
    simp only [← Nat.add_assoc]
  rw [Finset.sum_congr rfl hg, Finset.sum_range_sub (fun i => f (A + i)) (B - A)]
  simp only [Nat.add_zero]
  rw [Nat.add_sub_cancel' h]

/-- `2 < log t` for `t ≥ 16` (via `log 2 > 0.6931471803`). -/
private theorem log_gt_two {t : ℕ} (ht : 16 ≤ t) : (2 : ℝ) < Real.log t := by
  have h16 : (16 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hl : Real.log 16 ≤ Real.log t := Real.log_le_log (by norm_num) h16
  have h4 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have h2 := Real.log_two_gt_d9
  linarith

/-- `log (t+1) - log t ≤ 1/t`. -/
private theorem log_succ_sub_le {t : ℕ} (ht : 1 ≤ t) :
    Real.log ((t : ℝ) + 1) - Real.log t ≤ 1 / (t : ℝ) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hlog : Real.log (((t : ℝ) + 1) / (t : ℝ)) ≤ ((t : ℝ) + 1) / (t : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  have hval : ((t : ℝ) + 1) / (t : ℝ) - 1 = 1 / (t : ℝ) := by
    field_simp
    ring
  rw [hval] at hlog
  exact hlog

/-- `log u - log v ≤ (u - v)/v` for `0 < v ≤ u`. -/
private theorem log_ratio_bound {u v : ℝ} (hv : 0 < v) (hu : 0 < u) :
    Real.log u - Real.log v ≤ (u - v) / v := by
  have h : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hu.ne' hv.ne'] at h
  have hval : u / v - 1 = (u - v) / v := by field_simp
  rw [hval] at h
  exact h

private theorem wt_anti {t : ℕ} (ht : 16 ≤ t) : wt (t + 1) ≤ wt t := by
  have hv : (2 : ℝ) < Real.log t := log_gt_two ht
  have ht0 : (0 : ℝ) < (t : ℝ) := by
    have : (16 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hle : Real.log (t : ℝ) ≤ Real.log (((t + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log ht0
    push_cast
    linarith
  unfold wt
  exact one_div_le_one_div_of_le (by linarith) hle

private theorem wt_nonneg {t : ℕ} (ht : 16 ≤ t) : 0 ≤ wt t := by
  have hv : (2 : ℝ) < Real.log t := log_gt_two ht
  unfold wt
  positivity

/-- The key per-term estimate: `log log (t+1) - log log t - 1/(4t²) ≤ log t · (w t - w (t+1))`. -/
private theorem loglog_step_le {t : ℕ} (ht : 16 ≤ t) :
    LL (t + 1) - LL t - 1 / (4 * (t : ℝ) ^ 2) ≤ Real.log t * (wt t - wt (t + 1)) := by
  have htR : (16 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
  have hv2 : (2 : ℝ) < Real.log (t : ℝ) := log_gt_two ht
  have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
  have hvu : Real.log (t : ℝ) ≤ Real.log ((t : ℝ) + 1) :=
    Real.log_le_log ht0 (by linarith)
  set v := Real.log (t : ℝ) with hv_def
  set u := Real.log ((t : ℝ) + 1) with hu_def
  have hu2 : (2 : ℝ) < u := by linarith
  have hd0 : (0 : ℝ) ≤ u - v := by linarith
  have hd : u - v ≤ 1 / (t : ℝ) := log_succ_sub_le (by omega)
  -- the exact identity for the weighted increment
  have hid : v * (wt t - wt (t + 1)) = (u - v) / u := by
    unfold wt
    rw [hcast, ← hv_def, ← hu_def]
    field_simp
  -- the comparison of the log-difference with the increment
  have hlog : Real.log u - Real.log v ≤ (u - v) / v :=
    log_ratio_bound (by linarith) (by linarith)
  have hsplit : (u - v) / v = (u - v) / u + (u - v) ^ 2 / (u * v) := by
    field_simp
    ring
  -- the error term
  have huv : (0 : ℝ) < u * v := by nlinarith
  have h1 : (u - v) ^ 2 ≤ 1 / (t : ℝ) ^ 2 := by
    have hmm : (u - v) * (u - v) ≤ (1 / (t : ℝ)) * (1 / (t : ℝ)) :=
      mul_self_le_mul_self hd0 hd
    calc (u - v) ^ 2 = (u - v) * (u - v) := by ring
      _ ≤ (1 / (t : ℝ)) * (1 / (t : ℝ)) := hmm
      _ = 1 / (t : ℝ) ^ 2 := by ring
  have h2 : (4 : ℝ) ≤ u * v := by nlinarith
  have herr : (u - v) ^ 2 / (u * v) ≤ 1 / (4 * (t : ℝ) ^ 2) := by
    rw [div_le_iff₀ huv]
    have ht2 : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
    have hq : 1 / (4 * (t : ℝ) ^ 2) * (u * v) = (u * v) / (4 * (t : ℝ) ^ 2) := by ring
    rw [hq, le_div_iff₀ (by positivity)]
    have hstep1 : (u - v) ^ 2 * (4 * (t : ℝ) ^ 2) ≤ (1 / (t : ℝ) ^ 2) * (4 * (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have hstep2 : (1 / (t : ℝ) ^ 2) * (4 * (t : ℝ) ^ 2) = 4 := by field_simp
    linarith
  have hLL1 : LL (t + 1) = Real.log u := by
    unfold LL
    rw [hcast, ← hu_def]
  have hLL0 : LL t = Real.log v := by unfold LL; rw [← hv_def]
  rw [hLL1, hLL0, hid]
  linarith

/-- `∑_{A ≤ t < B} 1/(4t²) ≤ 1/4` for `2 ≤ A ≤ B`. -/
private theorem sum_inv_sq_le {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ∑ t ∈ Finset.Ico A B, 1 / (4 * (t : ℝ) ^ 2) ≤ 1 / 4 := by
  set f : ℕ → ℝ := fun s => 1 / (4 * ((s : ℝ) - 1)) with hf_def
  have hterm : ∀ t ∈ Finset.Ico A B, 1 / (4 * (t : ℝ) ^ 2) ≤ f t - f (t + 1) := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 2 ≤ t)
    have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
    have hval : f t - f (t + 1) = 1 / (4 * ((t : ℝ) - 1) * (t : ℝ)) := by
      rw [hf_def]
      simp only
      rw [hcast, show ((t : ℝ) + 1 - 1) = (t : ℝ) by ring]
      have h1 : (0 : ℝ) < (t : ℝ) - 1 := by linarith
      have h0 : (0 : ℝ) < (t : ℝ) := by linarith
      field_simp
      ring
    rw [hval]
    have hpos1 : (0 : ℝ) < 4 * ((t : ℝ) - 1) * (t : ℝ) := by nlinarith
    have hpos2 : (0 : ℝ) < 4 * (t : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hpos2 hpos1]
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [sum_Ico_telescope f A B hAB] at hsum
  have hfA : f A ≤ 1 / 4 := by
    rw [hf_def]
    simp only
    have hA1 : (1 : ℝ) ≤ (A : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      linarith
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hfB : 0 ≤ f B := by
    rw [hf_def]
    simp only
    have hB1 : (1 : ℝ) ≤ (B : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 2 ≤ B)
      linarith
    positivity
  linarith

/-- The Abel identity for the window `(z, Y]`. -/
private theorem abel_window (z : ℕ) : ∀ Y, z + 1 ≤ Y →
    ∑ t ∈ Finset.Ioc z Y, aterm t * wt t
      = mertensPartial Y * wt Y - mertensPartial z * wt (z + 1)
        + ∑ t ∈ Finset.Ico (z + 1) Y, mertensPartial t * (wt t - wt (t + 1)) := by
  intro Y hY
  induction Y, hY using Nat.le_induction with
  | base =>
      rw [Finset.sum_Ioc_succ_top (le_refl z), Finset.Ioc_self, Finset.Ico_self,
        Finset.sum_empty, Finset.sum_empty, M_succ z]
      ring
  | succ Y hY ih =>
      rw [Finset.sum_Ioc_succ_top (by omega : z ≤ Y), ih,
        Finset.sum_Ico_succ_top (by omega : z + 1 ≤ Y), M_succ Y]
      ring

/-- **C5 — the windowed `log log` lower bound.**  For `16 ≤ z ≤ Y`,

```
log log Y - log log z - 16  ≤  ∑_{z < r ≤ Y, r prime} 1/r.
```

Group 7 / **C4 tail estimate**, `findings_ls_verification.md` §2.10; Session 310. -/
theorem window_recip_lower (z Y : ℕ) (hz : 16 ≤ z) (hzY : z ≤ Y) :
    Real.log (Real.log Y) - Real.log (Real.log z) - 16
      ≤ ∑ r ∈ (Finset.Ioc z Y).filter Nat.Prime, (1 : ℝ) / r := by
  rcases eq_or_lt_of_le hzY with rfl | hlt
  · rw [Finset.Ioc_self]
    simp
  · have hY1 : z + 1 ≤ Y := hlt
    have hzR : (16 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hz2 : (2 : ℝ) < Real.log z := log_gt_two hz
    have hY16 : 16 ≤ Y := by omega
    have hY2 : (2 : ℝ) < Real.log Y := log_gt_two hY16
    -- rewrite the left-hand sum in Abel form
    have hsum : ∑ r ∈ (Finset.Ioc z Y).filter Nat.Prime, (1 : ℝ) / r
        = ∑ t ∈ Finset.Ioc z Y, aterm t * wt t := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro t htm
      rw [Finset.mem_Ioc] at htm
      have ht16 : 16 ≤ t := by omega
      have ht0 : (0 : ℝ) < (t : ℝ) := by
        have : (16 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht16
        linarith
      have hl : (2 : ℝ) < Real.log t := log_gt_two ht16
      unfold aterm wt gLog
      split_ifs with hp
      · field_simp
      · simp
    rw [hsum, abel_window z Y hY1]
    -- (i) the head term is nonnegative
    have hMYnn : 0 ≤ mertensPartial Y := by
      rw [mertensPartial]
      refine Finset.sum_nonneg ?_
      intro p hp
      rw [Finset.mem_filter] at hp
      have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
      positivity
    have hhead : 0 ≤ mertensPartial Y * wt Y :=
      mul_nonneg hMYnn (wt_nonneg hY16)
    -- (ii) the boundary term is bounded
    have hwz1 : wt (z + 1) ≤ 1 / 2 := by
      have h1 : wt (z + 1) ≤ wt z := wt_anti hz
      have h2 : wt z ≤ 1 / 2 := by
        unfold wt
        exact one_div_le_one_div_of_le (by norm_num) hz2.le
      linarith
    have hwz1nn : 0 ≤ wt (z + 1) := wt_nonneg (by omega)
    have hMzu : mertensPartial z ≤ 2 * Real.log 4 * (2 + Real.log z) := mertens_upper z
    have hMz4 : mertensPartial z ≤ 4 * (2 + Real.log z) := by
      have h4 := log_four_le_two
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4), hz2]
    have hboundary : mertensPartial z * wt (z + 1) ≤ 8 := by
      have hstep : mertensPartial z * wt (z + 1) ≤ (4 * (2 + Real.log z)) * wt (z + 1) :=
        mul_le_mul_of_nonneg_right hMz4 hwz1nn
      have hwz : wt (z + 1) ≤ 1 / Real.log z := by
        unfold wt
        exact one_div_le_one_div_of_le (by linarith)
          (Real.log_le_log (by linarith) (by push_cast; linarith))
      have hfinal : (4 * (2 + Real.log z)) * wt (z + 1) ≤ 8 := by
        have hmul : (4 * (2 + Real.log z)) * wt (z + 1)
            ≤ (4 * (2 + Real.log z)) * (1 / Real.log z) :=
          mul_le_mul_of_nonneg_left hwz (by linarith)
        have hval : (4 * (2 + Real.log z)) * (1 / Real.log z) = 8 / Real.log z + 4 := by
          field_simp
          ring
        have h8 : 8 / Real.log z ≤ 4 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        linarith
      linarith
    -- (iii) the main sum
    have hstep : ∀ t ∈ Finset.Ico (z + 1) Y,
        (LL (t + 1) - LL t) - 1 / (4 * (t : ℝ) ^ 2) - 13 * (wt t - wt (t + 1))
          ≤ mertensPartial t * (wt t - wt (t + 1)) := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      have ht16 : 16 ≤ t := by omega
      have hw : 0 ≤ wt t - wt (t + 1) := by linarith [wt_anti ht16]
      have hMt : Real.log t - 13 ≤ mertensPartial t := mertens_lower t (by omega)
      have hkey := loglog_step_le ht16
      have h1 : (Real.log t - 13) * (wt t - wt (t + 1))
          ≤ mertensPartial t * (wt t - wt (t + 1)) :=
        mul_le_mul_of_nonneg_right hMt hw
      nlinarith [hkey, h1]
    have hsle := Finset.sum_le_sum hstep
    have hdecomp : ∑ t ∈ Finset.Ico (z + 1) Y,
          ((LL (t + 1) - LL t) - 1 / (4 * (t : ℝ) ^ 2) - 13 * (wt t - wt (t + 1)))
        = (∑ t ∈ Finset.Ico (z + 1) Y, (LL (t + 1) - LL t))
          - (∑ t ∈ Finset.Ico (z + 1) Y, 1 / (4 * (t : ℝ) ^ 2))
          - 13 * (∑ t ∈ Finset.Ico (z + 1) Y, (wt t - wt (t + 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    have htel1 : ∑ t ∈ Finset.Ico (z + 1) Y, (LL (t + 1) - LL t) = LL Y - LL (z + 1) :=
      sum_Ico_telescope' LL (z + 1) Y hY1
    have htel2 : ∑ t ∈ Finset.Ico (z + 1) Y, (wt t - wt (t + 1)) = wt (z + 1) - wt Y :=
      sum_Ico_telescope wt (z + 1) Y hY1
    have hinvsq : ∑ t ∈ Finset.Ico (z + 1) Y, 1 / (4 * (t : ℝ) ^ 2) ≤ 1 / 4 :=
      sum_inv_sq_le (by omega) hY1
    have hwY : 0 ≤ wt Y := wt_nonneg hY16
    have hbigsum : LL Y - LL (z + 1) - 1 / 4 - 13 * (1 / 2)
        ≤ ∑ t ∈ Finset.Ico (z + 1) Y, mertensPartial t * (wt t - wt (t + 1)) := by
      rw [hdecomp, htel1, htel2] at hsle
      have h13 : 13 * (wt (z + 1) - wt Y) ≤ 13 * (1 / 2) := by linarith
      linarith
    -- (iv) `log log (z+1) ≤ log log z + 1`
    have hLLz : LL (z + 1) ≤ LL z + 1 := by
      have hcast : ((z + 1 : ℕ) : ℝ) = (z : ℝ) + 1 := by push_cast; ring
      have hvu : Real.log (z : ℝ) ≤ Real.log ((z : ℝ) + 1) :=
        Real.log_le_log (by linarith) (by linarith)
      have hd : Real.log ((z : ℝ) + 1) - Real.log (z : ℝ) ≤ 1 / (z : ℝ) :=
        log_succ_sub_le (by omega)
      have hlog := log_ratio_bound (u := Real.log ((z : ℝ) + 1)) (v := Real.log (z : ℝ))
        (by linarith) (by linarith)
      have hzinv : 1 / (z : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      have hquot : (Real.log ((z : ℝ) + 1) - Real.log (z : ℝ)) / Real.log (z : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      unfold LL
      rw [hcast]
      linarith
    have hLLY : LL Y = Real.log (Real.log Y) := rfl
    have hLLzz : LL z = Real.log (Real.log z) := rfl
    rw [← hLLY, ← hLLzz]
    linarith

/-- **C5, existential form** — the shape requested by the Group 7 tail estimate:
there is an absolute constant `C` (here `C = 16`) with

```
log log Y - log log z - C  ≤  ∑_{z < r ≤ Y, r prime} 1/r      (16 ≤ z ≤ Y).
```
-/
theorem window_recip_lower_exists :
    ∃ C : ℝ, ∀ z Y : ℕ, 16 ≤ z → z ≤ Y →
      Real.log (Real.log Y) - Real.log (Real.log z) - C
        ≤ ∑ r ∈ (Finset.Ioc z Y).filter Nat.Prime, (1 : ℝ) / r :=
  ⟨16, window_recip_lower⟩

end MertensLower
