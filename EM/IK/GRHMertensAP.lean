import EM.IK.GRHStatements
import EM.IK.Ch2
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Analysis.PSeries

/-!
# Mertens' first theorem in arithmetic progressions, uniformly in the modulus, under GRH

Assume the GRH bound for the twisted Chebyshev function,
`|ψ(x, χ)| ≤ C √x log²(q x)` for every non-principal character `χ` modulo `q` and every
`x ≥ 2` (`IK.GRHPsiBound C`). Then there is an absolute constant `C'` such that for every
modulus `q > 1`, every `a` coprime to `q` and every `x ≥ 2`,

  `| ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)/n  −  (log x)/φ(q) |  ≤  C' · log²(2q)`.

This is `weightedPNTinAP_uniform_of_grh`. Its corollary `weightedPNTinAP_of_grh` is the
statement `IK.WeightedPNTinAP` (a constant for each modulus), which this repository otherwise
carries as an open hypothesis.

## Proof

* **Orthogonality** (`ap_sum_eq_char_sum`). For `a` coprime to `q`,
  `φ(q) · ∑_{n ≤ N, n ≡ a} f(n) = ∑_χ χ(a⁻¹) ∑_{n ≤ N} f(n) χ(n)`.
* **Principal character.** Its contribution is `∑_{n ≤ N, (n,q)=1} Λ(n)/n`. The full sum is
  `log N + O(1)` (`mertens_first_nat`: Mertens' first theorem, from
  `∑_{n ≤ N} Λ(n) ⌊N/n⌋ = log N!`, Stirling's lower bound and Chebyshev's `ψ(N) ≤ (log 4 + 4) N`).
  The terms with `(n, q) > 1` are prime powers `p^k` with `p ∣ q`, and
  `∑_{p ∣ q} ∑_{k ≥ 1} (log p)/p^k ≤ ∑_{p ∣ q} log p ≤ log q`
  (`sum_vonMangoldt_div_not_coprime_le`). This is the only place where a term of size `log q`
  is forced; it is genuinely present (take `q` a primorial).
* **Non-principal characters** (`norm_twisted_sum_le`). Summation by parts gives
  `∑_{n ≤ N} Λ(n)χ(n)/n = ψ(N,χ)/N + ∑_{n < N} ψ(n,χ) (1/n − 1/(n+1))`. With
  `log²(q n) ≤ 2 log² q + 128 n^{1/4}` the hypothesis gives `|ψ(n,χ)| ≤ C (2 log² q + 128) n^{3/4}`,
  and `∑ n^{3/4}/n² = ζ(5/4) < ∞`. So the twisted sum is `O(log² q)` uniformly in `N` and `χ`.

The shape `C' log²(2q)` of the error is what the argument gives: `log² q` from the
non-principal characters, `log q` from the principal one, and `2q` instead of `q` only to keep
the bound positive for small `q`. No positivity of `C` is needed beyond `0 ≤ C`.
-/

noncomputable section

namespace IK

open Finset ArithmeticFunction

/-! ## Mertens' first theorem -/

private theorem Icc_one_eq_Ioc (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext n; simp only [mem_Icc, mem_Ioc]; omega

/-- **Mertens' first theorem**, at integers, with explicit constants:
`log N − 1 ≤ ∑_{n ≤ N} Λ(n)/n ≤ log N + log 4 + 4` for `N ≥ 1`. -/
theorem mertens_first_nat (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Icc 1 N, Λ n / n ∧
      ∑ n ∈ Icc 1 N, Λ n / n ≤ Real.log N + (Real.log 4 + 4) := by
  rw [Icc_one_eq_Ioc]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) = ∑ n ∈ Ioc 0 N, Real.log n := by
    rw [← sum_Ioc_mul_zeta_eq_sum, vonMangoldt_mul_zeta]
    exact sum_congr rfl fun n _ => by simp [log_apply]
  have hmul : (N : ℝ) * ∑ n ∈ Ioc 0 N, Λ n / n = ∑ n ∈ Ioc 0 N, Λ n * ((N : ℝ) / n) := by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
  have hlow : (N : ℝ) * Real.log N - N ≤ ∑ n ∈ Ioc 0 N, Real.log n := Real.le_sum_log_nat N
  have hupp : ∑ n ∈ Ioc 0 N, Real.log n ≤ (N : ℝ) * Real.log N := by
    have := Real.sum_log_le' (x := (N : ℝ)) (by exact_mod_cast hN)
    simpa [Nat.floor_natCast] using this
  have hpsi : ∑ n ∈ Ioc 0 N, Λ n ≤ (Real.log 4 + 4) * N := by
    have := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hN0.le
    simpa [Chebyshev.psi, Nat.floor_natCast] using this
  -- floors against real quotients
  have hfl1 : ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) ≤ ∑ n ∈ Ioc 0 N, Λ n * ((N : ℝ) / n) :=
    sum_le_sum fun n _ => mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
  have hfl2 : ∑ n ∈ Ioc 0 N, Λ n * ((N : ℝ) / n) ≤
      ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) + ∑ n ∈ Ioc 0 N, Λ n := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (mem_Ioc.mp hn).1
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 : (N : ℝ) < (n : ℝ) * (((N / n : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ N hn0
    have h2 : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn0']; linarith
    calc Λ n * ((N : ℝ) / n) ≤ Λ n * (((N / n : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h2 vonMangoldt_nonneg
      _ = Λ n * ((N / n : ℕ) : ℝ) + Λ n := by ring
  constructor
  · have : (N : ℝ) * (Real.log N - 1) ≤ (N : ℝ) * ∑ n ∈ Ioc 0 N, Λ n / n := by
      rw [hmul]; linarith
    exact le_of_mul_le_mul_left this hN0
  · have : (N : ℝ) * ∑ n ∈ Ioc 0 N, Λ n / n ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by
      rw [hmul]; linarith
    exact le_of_mul_le_mul_left this hN0

/-! ## The terms not coprime to the modulus -/

private theorem geom_sum_Icc_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Icc 1 N, r ^ k ≤ 1 - r ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    have := pow_nonneg hr0 N
    have h2 : r ^ (N + 1) = r ^ N * r := pow_succ r N
    nlinarith

/-- The part of `∑_{n ≤ N} Λ(n)/n` over `n` not coprime to `q` is at most `log q`:
such `n` are powers of primes dividing `q`. -/
theorem sum_vonMangoldt_div_not_coprime_le (q : ℕ) (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n / n ≤ Real.log q := by
  set f : ℕ → ℝ := fun n => Λ n / n with hf
  have hfnn : ∀ n, 0 ≤ f n := fun n => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  set g : ℕ × ℕ → ℕ := fun pk => pk.1 ^ pk.2 with hg
  have hsub : ((Icc 1 N).filter (fun n => ¬ Nat.Coprime n q)).filter (fun n => f n ≠ 0) ⊆
      (q.primeFactors ×ˢ Icc 1 N).image g := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨_, hnN⟩, hncop⟩, hfn⟩ := hn
    have hΛ : Λ n ≠ 0 := fun h0 => hfn (by simp [hf, h0])
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hpq : p ∣ q := by
      by_contra hnd
      exact hncop (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    have hkN : k ≤ N := (Nat.lt_pow_self hp.one_lt).le.trans hnN
    exact mem_image.mpr ⟨(p, k),
      mem_product.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩, mem_Icc.mpr ⟨hk, hkN⟩⟩, rfl⟩
  have hinner : ∀ p ∈ q.primeFactors, ∑ k ∈ Icc 1 N, f (p ^ k) ≤ Λ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    have hr : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; simpa using hp2
    have hterm : ∀ k ∈ Icc 1 N, f (p ^ k) = Λ p * ((p : ℝ)⁻¹) ^ k := by
      intro k hk
      have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
      simp only [hf, vonMangoldt_apply_pow hk0, Nat.cast_pow, inv_pow]
      rw [div_eq_mul_inv]
    rw [sum_congr rfl hterm, ← mul_sum]
    have hgeo := geom_sum_Icc_le _ hr0 hr N
    have hpow : 0 ≤ ((p : ℝ)⁻¹) ^ N := pow_nonneg hr0 N
    calc Λ p * ∑ k ∈ Icc 1 N, ((p : ℝ)⁻¹) ^ k ≤ Λ p * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) vonMangoldt_nonneg
      _ = Λ p := mul_one _
  calc ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), f n
      = ∑ n ∈ ((Icc 1 N).filter (fun n => ¬ Nat.Coprime n q)).filter (fun n => f n ≠ 0), f n :=
        (sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (q.primeFactors ×ˢ Icc 1 N).image g, f n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hfnn n
    _ ≤ ∑ pk ∈ q.primeFactors ×ˢ Icc 1 N, f (g pk) :=
        sum_image_le_of_nonneg fun n _ => hfnn n
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ Icc 1 N, f (p ^ k) := sum_product _ _ _
    _ ≤ ∑ p ∈ q.primeFactors, Λ p := sum_le_sum hinner
    _ ≤ ∑ d ∈ q.divisors, Λ d :=
        sum_le_sum_of_subset_of_nonneg
          (fun p hp => Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, hq⟩)
          fun _ _ _ => vonMangoldt_nonneg
    _ = Real.log q := vonMangoldt_sum

/-! ## Orthogonality of characters -/

/-- **Orthogonality.** For `a` coprime to `q`, a sum over the progression `n ≡ a (mod q)` is the
average over the characters `χ` modulo `q` of `χ(a⁻¹)` times the `χ`-twisted sum. -/
theorem ap_sum_eq_char_sum (q : ℕ) [NeZero q] (a : ℕ) (ha : Nat.Coprime a q) (N : ℕ)
    (f : ℕ → ℝ) :
    (q.totient : ℂ) * ((∑ n ∈ (Icc 1 N).filter (fun n => n % q = a % q), f n : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) *
        ∑ n ∈ Icc 1 N, (f n : ℂ) * χ (n : ZMod q) := by
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hrhs : ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) *
        ∑ n ∈ Icc 1 N, (f n : ℂ) * χ (n : ZMod q) =
      ∑ n ∈ Icc 1 N, (f n : ℂ) *
        ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ (n : ZMod q) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun n _ => sum_congr rfl fun χ _ => by ring
  rw [hrhs, Complex.ofReal_sum, sum_filter, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hau]
  have hiff : ((a : ZMod q) = (n : ZMod q)) ↔ n % q = a % q := by
    rw [ZMod.natCast_eq_natCast_iff']; exact eq_comm
  by_cases h : n % q = a % q
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr h))]; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (hiff.mp h'))]; simp

/-! ## Non-principal characters: summation by parts -/

/-- Summation by parts for `∑ c(n)/n`. -/
private theorem abel_div (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 (N + 1), c n / n =
      (∑ k ∈ Icc 1 (N + 1), c k) / ((N : ℂ) + 1) +
        ∑ n ∈ Icc 1 N, (∑ k ∈ Icc 1 n, c k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e1 : ∑ n ∈ Icc 1 (N + 1 + 1), c n / n =
        ∑ n ∈ Icc 1 (N + 1), c n / n + c (N + 1 + 1) / ((N + 1 + 1 : ℕ) : ℂ) :=
      sum_Icc_succ_top (by omega) _
    have e2 : ∑ k ∈ Icc 1 (N + 1 + 1), c k = ∑ k ∈ Icc 1 (N + 1), c k + c (N + 1 + 1) :=
      sum_Icc_succ_top (by omega) _
    have e3 : ∑ n ∈ Icc 1 (N + 1), (∑ k ∈ Icc 1 n, c k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) =
        ∑ n ∈ Icc 1 N, (∑ k ∈ Icc 1 n, c k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) +
          (∑ k ∈ Icc 1 (N + 1), c k) * (1 / ((N + 1 : ℕ) : ℂ) - 1 / (((N + 1 : ℕ) : ℂ) + 1)) :=
      sum_Icc_succ_top (by omega) _
    rw [e1, e2, e3, ih]
    generalize ∑ k ∈ Icc 1 (N + 1), c k = A
    generalize ∑ n ∈ Icc 1 N, (∑ k ∈ Icc 1 n, c k) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) = T
    have h1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have h2 : (N : ℂ) + 1 + 1 ≠ 0 := by
      have := Nat.cast_add_one_ne_zero (R := ℂ) (N + 1)
      simpa using this
    push_cast
    field_simp
    ring

/-- Facts about `r = t^{1/8}` for real `t ≥ 1`. -/
private theorem eighth_root_facts {t : ℝ} (ht : 1 ≤ t) :
    1 ≤ t ^ (1 / 8 : ℝ) ∧ (t ^ (1 / 8 : ℝ)) ^ 8 = t ∧
      t ^ (5 / 4 : ℝ) = (t ^ (1 / 8 : ℝ)) ^ 10 ∧ Real.sqrt t = (t ^ (1 / 8 : ℝ)) ^ 4 ∧
      Real.log t ≤ 8 * t ^ (1 / 8 : ℝ) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have h1 : 1 ≤ t ^ (1 / 8 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have h8 : (t ^ (1 / 8 : ℝ)) ^ 8 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]; norm_num
  have h10 : t ^ (5 / 4 : ℝ) = (t ^ (1 / 8 : ℝ)) ^ 10 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]; norm_num
  have hsq : Real.sqrt t = (t ^ (1 / 8 : ℝ)) ^ 4 := by
    have : t = ((t ^ (1 / 8 : ℝ)) ^ 4) ^ 2 := by rw [← pow_mul]; exact h8.symm
    conv_lhs => rw [this]
    exact Real.sqrt_sq (by positivity)
  have hlog : Real.log t ≤ 8 * t ^ (1 / 8 : ℝ) := by
    have := Real.log_le_rpow_div ht0 (show (0 : ℝ) < 1 / 8 by norm_num)
    linarith
  exact ⟨h1, h8, h10, hsq, hlog⟩

/-- `√t · (L + log t)² ≤ (2L² + 128) · t^{3/4}` for `t ≥ 1`, written with `r = t^{1/8}`. -/
private theorem sqrt_mul_log_sq_le (L : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    Real.sqrt t * (L + Real.log t) ^ 2 ≤ (2 * L ^ 2 + 128) * (t ^ (1 / 8 : ℝ)) ^ 6 := by
  obtain ⟨h1, -, -, hsq, hlog⟩ := eighth_root_facts ht
  set r := t ^ (1 / 8 : ℝ)
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hA : (L + Real.log t) ^ 2 ≤ 2 * L ^ 2 + 2 * Real.log t ^ 2 := by
    nlinarith [sq_nonneg (L - Real.log t)]
  have hB : Real.log t ^ 2 ≤ 64 * r ^ 2 := by nlinarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hD : 2 * L ^ 2 + 2 * Real.log t ^ 2 ≤ (2 * L ^ 2 + 128) * r ^ 2 := by
    nlinarith [sq_nonneg L]
  have hr4 : 0 ≤ r ^ 4 := by positivity
  rw [hsq]
  calc r ^ 4 * (L + Real.log t) ^ 2 ≤ r ^ 4 * ((2 * L ^ 2 + 128) * r ^ 2) :=
        mul_le_mul_of_nonneg_left (hA.trans hD) hr4
    _ = (2 * L ^ 2 + 128) * r ^ 6 := by ring

/-- The constant `ζ(5/4) = ∑ n^{-5/4}`. -/
private def zeta54 : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹

private theorem zeta54_nonneg : 0 ≤ zeta54 :=
  tsum_nonneg fun n => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem sum_le_zeta54 (s : Finset ℕ) :
    ∑ n ∈ s, ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ ≤ zeta54 :=
  Summable.sum_le_tsum s
    (fun n _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (Real.summable_nat_rpow_inv.mpr (by norm_num))

/-- Under the GRH bound, `|ψ(n, χ)| ≤ C (2 log² q + 128) n^{3/4}` for every integer `n ≥ 1`. -/
private theorem norm_psiChi_nat_le {C : ℝ} (hC : 0 ≤ C) (h : GRHPsiBound C)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) (hn : 1 ≤ n) :
    ‖psiChi χ (n : ℝ)‖ ≤
      C * (2 * Real.log q ^ 2 + 128) * (((n : ℝ) ^ (1 / 8 : ℝ)) ^ 6) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : 0 ≤ C * (2 * Real.log q ^ 2 + 128) := by positivity
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have : n = 1 := by omega
    subst this
    have : psiChi χ ((1 : ℕ) : ℝ) = 0 := by simp [psiChi]
    rw [this, norm_zero]
    positivity
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hge
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hgrh := h q χ hχ (n : ℝ) hn2
    rw [Real.log_mul hq0 (by linarith)] at hgrh
    calc ‖psiChi χ (n : ℝ)‖
        ≤ C * Real.sqrt n * (Real.log q + Real.log n) ^ 2 := hgrh
      _ = C * (Real.sqrt n * (Real.log q + Real.log n) ^ 2) := by ring
      _ ≤ C * ((2 * Real.log q ^ 2 + 128) * (((n : ℝ) ^ (1 / 8 : ℝ)) ^ 6)) :=
          mul_le_mul_of_nonneg_left (sqrt_mul_log_sq_le _ hn1) hC
      _ = _ := by ring

/-- **Non-principal characters.** Under the GRH bound the twisted sums
`∑_{n ≤ N} Λ(n) χ(n)/n` are bounded by `C (2 log² q + 128)(1 + ζ(5/4))`, uniformly in `N`, in the
non-principal character `χ` and in the modulus `q`. -/
private theorem norm_twisted_sum_le {C : ℝ} (hC : 0 ≤ C) (h : GRHPsiBound C)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((Λ n / n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      C * (2 * Real.log q ^ 2 + 128) * (1 + zeta54) := by
  set K : ℝ := C * (2 * Real.log q ^ 2 + 128) with hKdef
  have hK : 0 ≤ K := by positivity
  have hZ := zeta54_nonneg
  rcases N with _ | N
  · simp only [zero_lt_one, Icc_eq_empty_of_lt, sum_empty, norm_zero]
    positivity
  set c : ℕ → ℂ := fun n => (Λ n : ℂ) * χ (n : ZMod q) with hc
  have hA : ∀ k : ℕ, ∑ j ∈ Icc 1 k, c j = psiChi χ (k : ℝ) := by
    intro k; simp [psiChi, hc, Nat.floor_natCast]
  have hrew : ∑ n ∈ Icc 1 (N + 1), ((Λ n / n : ℝ) : ℂ) * χ (n : ZMod q) =
      ∑ n ∈ Icc 1 (N + 1), c n / n :=
    sum_congr rfl fun n _ => by simp only [hc]; push_cast; ring
  rw [hrew, abel_div]
  simp_rw [hA]
  -- the boundary term
  have hbd : ‖psiChi χ ((N + 1 : ℕ) : ℝ) / ((N : ℂ) + 1)‖ ≤ K := by
    have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    obtain ⟨h1, h8, -, -, -⟩ := eighth_root_facts hN1
    have hb := norm_psiChi_nat_le hC h q χ hχ (N + 1) (by omega)
    set r := ((N + 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)
    have hden : ‖(N : ℂ) + 1‖ = r ^ 8 := by
      rw [h8]
      have : (N : ℂ) + 1 = (((N + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_div, hden, div_le_iff₀ (by positivity)]
    have h68 : r ^ 6 ≤ r ^ 8 := pow_le_pow_right₀ h1 (by norm_num)
    calc ‖psiChi χ ((N + 1 : ℕ) : ℝ)‖ ≤ K * r ^ 6 := hb
      _ ≤ K * r ^ 8 := mul_le_mul_of_nonneg_left h68 hK
  -- the interior terms
  have hterm : ∀ n ∈ Icc 1 N,
      ‖psiChi χ (n : ℝ) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))‖ ≤
        K * ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    obtain ⟨h1, h8, h10, -, -⟩ := eighth_root_facts hn1'
    have hb := norm_psiChi_nat_le hC h q χ hχ n hn1
    set r := (n : ℝ) ^ (1 / 8 : ℝ)
    have hr0 : 0 < r := by linarith
    have hw : (1 / (n : ℂ) - 1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      have hc1 : (n : ℂ) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      have hc2 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      push_cast
      field_simp
      ring
    have hn8 : (n : ℝ) * ((n : ℝ) + 1) = r ^ 8 * (r ^ 8 + 1) := by rw [h8]
    rw [norm_mul, hw, Complex.norm_real, Real.norm_of_nonneg (by positivity), h10, hn8]
    have hle : r ^ 6 * (1 / (r ^ 8 * (r ^ 8 + 1))) ≤ (r ^ 10)⁻¹ := by
      rw [mul_one_div, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hr0 8, pow_pos hr0 16]
    calc ‖psiChi χ (n : ℝ)‖ * (1 / (r ^ 8 * (r ^ 8 + 1)))
        ≤ K * r ^ 6 * (1 / (r ^ 8 * (r ^ 8 + 1))) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = K * (r ^ 6 * (1 / (r ^ 8 * (r ^ 8 + 1)))) := by ring
      _ ≤ K * (r ^ 10)⁻¹ := mul_le_mul_of_nonneg_left hle hK
  have hcast : ((N : ℂ) + 1) = (((N + 1 : ℕ) : ℕ) : ℂ) := by push_cast; ring
  calc ‖psiChi χ ((N + 1 : ℕ) : ℝ) / ((N : ℂ) + 1) +
        ∑ n ∈ Icc 1 N, psiChi χ (n : ℝ) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))‖
      ≤ ‖psiChi χ ((N + 1 : ℕ) : ℝ) / ((N : ℂ) + 1)‖ +
        ∑ n ∈ Icc 1 N, ‖psiChi χ (n : ℝ) * (1 / (n : ℂ) - 1 / ((n : ℂ) + 1))‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ K + ∑ n ∈ Icc 1 N, K * ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ := add_le_add hbd (sum_le_sum hterm)
    _ = K + K * ∑ n ∈ Icc 1 N, ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ := by rw [mul_sum]
    _ ≤ K + K * zeta54 := by
        have := mul_le_mul_of_nonneg_left (sum_le_zeta54 (Icc 1 N)) hK
        linarith
    _ = K * (1 + zeta54) := by ring

/-! ## The principal character -/

/-- The principal character's twisted sum is the sum over `n` coprime to `q`, and that is the
full sum minus the part not coprime to `q`. -/
private theorem principal_twisted_sum (q : ℕ) [NeZero q] (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (f n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      ((∑ n ∈ Icc 1 N, f n -
        ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), f n : ℝ) : ℂ) := by
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) (fun n => Nat.Coprime n q) f
  have hcop : ∑ n ∈ Icc 1 N, f n -
      ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), f n =
      ∑ n ∈ (Icc 1 N).filter (fun n => Nat.Coprime n q), f n := by linarith
  rw [hcop, Complex.ofReal_sum, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : Nat.Coprime n q
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hn), MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn), mul_one]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hn), MulChar.map_nonunit _ (fun hu => hn ((ZMod.isUnit_iff_coprime n q).mp hu))]
    simp

/-! ## The theorem -/

/-- **Mertens' first theorem in arithmetic progressions, uniformly in the modulus, under GRH.**
If `|ψ(x, χ)| ≤ C √x log²(q x)` for all non-principal characters, then there is an absolute
constant `C'` with

  `| ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)/n − (log x)/φ(q) | ≤ C' log²(2q)`

for all moduli `q > 1`, all `a` coprime to `q` and all `x ≥ 2`. One may take
`C' = 8 + 130 · C · (1 + ζ(5/4))`. -/
theorem weightedPNTinAP_uniform_of_grh {C : ℝ} (hC : 0 ≤ C) (h : GRHPsiBound C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (q a : ℕ), 1 < q → Nat.Coprime a q → ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), Λ n / n
        - Real.log x / q.totient| ≤ C' * Real.log (2 * q) ^ 2 := by
  classical
  have hZ := zeta54_nonneg
  refine ⟨8 + 130 * C * (1 + zeta54), by positivity, ?_⟩
  intro q a hq ha x hx
  have : NeZero q := ⟨by omega⟩
  set N := ⌊x⌋₊ with hNdef
  set f : ℕ → ℝ := fun n => Λ n / n with hf
  set S : ℝ := ∑ n ∈ (Icc 1 N).filter (fun n => n % q = a % q), f n with hS
  set S0 : ℝ := ∑ n ∈ Icc 1 N, f n with hS0
  set R : ℝ := ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), f n with hR
  set B : ℝ := C * (2 * Real.log q ^ 2 + 128) * (1 + zeta54) with hB
  have hB0 : 0 ≤ B := by positivity
  have hφpos : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast hφpos
  -- size of N and of log N against log x
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog1 : Real.log N ≤ Real.log x := Real.log_le_log hN0 hNx
  have hlog2 : Real.log x ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hN0.ne']
    refine Real.log_le_log (by linarith) ?_
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  -- the principal part
  obtain ⟨hM1, hM2⟩ := mertens_first_nat N (by omega)
  have hR0 : 0 ≤ R :=
    sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
  have hRq : R ≤ Real.log q := sum_vonMangoldt_div_not_coprime_le q (by omega) N
  have hprin : |S0 - R - Real.log x| ≤ 7 + Real.log q := by
    rw [abs_le]; constructor <;> linarith
  -- orthogonality and splitting off the principal character
  have horth := ap_sum_eq_char_sum q a ha N f
  rw [← add_sum_erase univ _ (mem_univ (1 : DirichletCharacter ℂ q))] at horth
  have hau : IsUnit ((a : ZMod q)⁻¹) :=
    IsUnit.of_mul_eq_one _
      ((ZMod.inv_mul_eq_one_of_isUnit ((ZMod.isUnit_iff_coprime a q).mpr ha) _).mpr rfl)
  rw [MulChar.one_apply hau, one_mul, principal_twisted_sum] at horth
  -- the non-principal part
  have hnp : ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ ((a : ZMod q)⁻¹) * ∑ n ∈ Icc 1 N, (f n : ℂ) * χ (n : ZMod q)‖ ≤ q.totient * B := by
    have hcard : ((univ : Finset (DirichletCharacter ℂ q)).erase 1).card ≤ q.totient := by
      have h1 := card_erase_le (s := (univ : Finset (DirichletCharacter ℂ q))) (a := 1)
      have h2 : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
        rw [card_univ, ← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      omega
    calc _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
            ‖χ ((a : ZMod q)⁻¹) * ∑ n ∈ Icc 1 N, (f n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, B := by
          refine sum_le_sum fun χ hχ => ?_
          rw [norm_mul]
          have h1 := DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)
          have h2 := norm_twisted_sum_le hC h q χ (ne_of_mem_erase hχ) N
          calc _ ≤ 1 * B := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
            _ = B := one_mul B
      _ = (((univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) * B := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ q.totient * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB0
  -- assemble
  have hmain : |(q.totient : ℝ) * S - Real.log x| ≤ 7 + Real.log q + q.totient * B := by
    have heq : (((q.totient : ℝ) * S - Real.log x : ℝ) : ℂ) =
        ((S0 - R - Real.log x : ℝ) : ℂ) +
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
            χ ((a : ZMod q)⁻¹) * ∑ n ∈ Icc 1 N, (f n : ℂ) * χ (n : ZMod q) := by
      have horth2 : (q.totient : ℂ) * (S : ℂ) = ((S0 - R : ℝ) : ℂ) +
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
            χ ((a : ZMod q)⁻¹) * ∑ n ∈ Icc 1 N, (f n : ℂ) * χ (n : ZMod q) := horth
      push_cast
      rw [horth2]
      push_cast
      ring
    rw [← Real.norm_eq_abs, ← Complex.norm_real, heq]
    refine (norm_add_le _ _).trans (add_le_add ?_ hnp)
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hprin
  have hdiv : S - Real.log x / q.totient = ((q.totient : ℝ) * S - Real.log x) / q.totient := by
    field_simp
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
  have hfinal : |S - Real.log x / q.totient| ≤ 7 + Real.log q + B := by
    rw [hdiv, abs_div, abs_of_pos (by linarith : (0 : ℝ) < q.totient), div_le_iff₀ (by linarith)]
    refine hmain.trans ?_
    nlinarith
  -- compare with log²(2q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hLL : Real.log q ≤ Real.log (2 * q) := Real.log_le_log (by linarith) (by linarith)
  have hL1 : 1 ≤ Real.log (2 * q) := by
    have h4 : Real.log 4 ≤ Real.log (2 * q) := Real.log_le_log (by norm_num) (by linarith)
    have h44 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  set L := Real.log q
  set LL := Real.log (2 * (q : ℝ))
  have hLL2 : LL ≤ LL ^ 2 := by nlinarith
  have hsq : L ^ 2 ≤ LL ^ 2 := by nlinarith
  have hCZ : 0 ≤ C * (1 + zeta54) := by positivity
  calc |S - Real.log x / q.totient| ≤ 7 + L + B := hfinal
    _ = 7 + L + C * (1 + zeta54) * (2 * L ^ 2 + 128) := by rw [hB]; ring
    _ ≤ 8 * LL ^ 2 + C * (1 + zeta54) * (130 * LL ^ 2) := by
        have h1 : 7 + L ≤ 8 * LL ^ 2 := by nlinarith
        have h2 : 2 * L ^ 2 + 128 ≤ 130 * LL ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left h2 hCZ
        linarith
    _ = (8 + 130 * C * (1 + zeta54)) * LL ^ 2 := by ring

/-- **GRH implies the weighted prime number theorem in arithmetic progressions**
(`IK.WeightedPNTinAP`, Iwaniec–Kowalski Theorem 2.2): for each modulus `q > 1` and each `a`
coprime to `q`, `∑_{n ≤ x, n ≡ a (mod q)} Λ(n)/n = (log x)/φ(q) + O_q(1)`. Here the constant is
`C' log²(2q)` with `C'` absolute. -/
theorem weightedPNTinAP_of_grh {C : ℝ} (hC : 0 ≤ C) (h : GRHPsiBound C) : WeightedPNTinAP := by
  obtain ⟨C', hC', hbound⟩ := weightedPNTinAP_uniform_of_grh hC h
  intro q a hq ha
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by linarith)
  exact ⟨C' * Real.log (2 * q) ^ 2, by positivity, fun x hx => hbound q a hq ha x hx⟩

end IK
