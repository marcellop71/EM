import EM.FunctionField.QuadCharBridge
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Stable primes have analytic density zero (unconditional)

`StableDensity.stable_density_zero` proves that the stable primes have natural density zero
from the prime number theorem for quadratic characters, taken as a hypothesis. This file runs
the same sieve with the logarithmically weighted Dirichlet density, where the analytic input is
in Mathlib: `L(s, χ)` does not vanish on `Re s ≥ 1`, so `−L'/L(s, χ)` is continuous there for
`χ` non-principal. The result has no hypothesis.

## The argument

Write `w_s(p) = log p · p^{−s}` for `p` prime and `0` otherwise (`pw`), with `s > 1` real.

1. `∑_n Λ(n) n^{−s} = 1/(s−1) + O(1)` on `(1, 2]` (`vm_bound`), from the continuity of
   `−ζ'/ζ(s) − 1/(s−1)` on `Re s ≥ 1`
   (`ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` with modulus `1`).
2. For `D` not a square, `∑_n χ_D(n) Λ(n) n^{−s} = O_D(1)` on `(1, 2]` (`twisted_bound`), from
   `DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv` for the character
   `QuadCharBridge.chiC D` mod `4|D|`.
3. Prime powers: for `|c_n| ≤ 1`, `∑_n c_n Λ(n) n^{−s}` and `∑_p c_p w_s(p)` differ by at most
   `∑_{n not prime} Λ(n)/n < ∞` (`abs_tsum_sub_tsum_mul_pw_le`).
4. `χ_D(p)` and `(D / p)` differ only at the primes dividing `4|D|`, which contribute at most
   `∑_{p ∣ 4|D|} log p`. Hence `|∑_p (D / p) w_s(p)| ≤ C_D` on `(1, 2]` (`jacobi_bound`).
5. Sieve (`sieve`): the detector `∏_{k<K} (1 − (Δ_k / p))` is `≥ 0`, equals `2^K` at a stable
   prime, and expands over `A ⊆ {0..K−1}`; so
   `2^K ∑_{p stable} w_s(p) ≤ ∑_p w_s(p) + ∑_{A ≠ ∅} C_{Δ_A}`.
6. Multiply by `s − 1` and let `s → 1⁺`, then `K → ∞`.

The prime `2` needs no separate treatment: it is not stable, and the detector is non-negative
at every natural number.

## Main results

* `stable_analytic_density_zero` — `(s − 1) ∑_{p stable} log p · p^{−s} → 0` as `s → 1⁺`.
* `primes_analytic_density_one` — `(s − 1) ∑_{p prime} log p · p^{−s} → 1` as `s → 1⁺`, the
  normalisation that makes the first statement a density.
-/

namespace FunctionFieldAnalog

namespace StableAnalyticDensity

open Finset Filter Topology StablePrimes StableCount QuadCharBridge TowerClassification
open ArithmeticFunction

/-- The set of stable primes. -/
def stableSet : Set ℕ := {p | ∃ h : p.Prime, @Stable p ⟨h⟩}

theorem mem_stableSet {p : ℕ} : p ∈ stableSet ↔ ∃ h : p.Prime, @Stable p ⟨h⟩ := Iff.rfl

/-- The weight `Λ(p) / p^x` on the primes, `0` elsewhere. -/
noncomputable def pw (x : ℝ) (n : ℕ) : ℝ := (if n.Prime then vonMangoldt n else 0) / (n : ℝ) ^ x

/-- The weight `Λ(n) / n` on the non-primes, `0` on the primes. -/
noncomputable def npw (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n) / n

/-! ## 1. Real series and `L`-series -/

theorem summable_vm {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => vonMangoldt n / (n : ℝ) ^ x := by
  have h := (LSeriesSummable_vonMangoldt (s := (x : ℂ)) (by simpa using hx)).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · simp [h0]
  · simp [abs_of_nonneg vonMangoldt_nonneg]

/-- The `L`-series of a real sequence at a real point. -/
theorem LSeries_ofReal (g : ℕ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    LSeries (fun n => (g n : ℂ)) x = ((∑' n, g n / (n : ℝ) ^ x : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hx]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_natCast]

/-- A function continuous on `Re s ≥ 1` is bounded on the real segment `[1, 2]`. -/
theorem bdd_real_segment {F : ℂ → ℂ} (hF : ContinuousOn F {s | 1 ≤ s.re}) :
    ∃ C, ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 → ‖F x‖ ≤ C := by
  have hc : ContinuousOn (fun x : ℝ => F x) (Set.Icc 1 2) :=
    hF.comp Complex.continuous_ofReal.continuousOn fun x hx => by
      simpa using hx.1
  exact isCompact_Icc.exists_bound_of_continuousOn hc

/-- `∑ Λ(n) n^{−x} = 1/(x−1) + O(1)` for `1 < x ≤ 2`. -/
theorem vm_bound : ∃ C, ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
    |∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ x - 1 / (x - 1)| ≤ C := by
  obtain ⟨C, hC⟩ := bdd_real_segment
    (vonMangoldt.continuousOn_LFunctionResidueClassAux (0 : ZMod 1))
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x ⟨hx.1.le, hx.2⟩
  have hs : (x : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hx.1
  have he := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) (a := 0)
    (isUnit_of_subsingleton 0) hs
  have hL : LSeries (fun n : ℕ => ((vonMangoldt.residueClass (0 : ZMod 1) n : ℝ) : ℂ)) x =
      ((∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    rw [← LSeries_ofReal _ (by linarith [hx.1])]
    refine LSeries_congr (fun {n} _ => ?_) _
    simp [vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) 0]
  have hval : vonMangoldt.LFunctionResidueClassAux (0 : ZMod 1) (x : ℂ) =
      ((∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ x - 1 / (x - 1) : ℝ) : ℂ) := by
    rw [he]
    simp only [hL]
    push_cast
    simp
  rw [hval, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The real-valued form of the character `χ_D`. -/
noncomputable def chiR (D : ℤ) (n : ℕ) : ℝ := ((chiZ D (n : ZMod (4 * D.natAbs)) : ℤ) : ℝ)

theorem abs_chiR_le_one (D : ℤ) (n : ℕ) : |chiR D n| ≤ 1 := by
  rw [chiR, ← Int.cast_abs]
  exact_mod_cast abs_chiZ_le_one D n

theorem ne_zero_of_not_isSquare {D : ℤ} (hD : ¬ IsSquare D) : D ≠ 0 := by
  rintro rfl
  exact hD ⟨0, by simp⟩

/-- `∑ χ_D(n) Λ(n) n^{−x} = O_D(1)` for `1 < x ≤ 2`, when `D` is not a square. -/
theorem twisted_bound {D : ℤ} (hD : ¬ IsSquare D) : ∃ C, ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
    |∑' n : ℕ, chiR D n * vonMangoldt n / (n : ℝ) ^ x| ≤ C := by
  have hDabs : 1 ≤ D.natAbs := Int.natAbs_pos.mpr (ne_zero_of_not_isSquare hD)
  have hNe : NeZero (4 * D.natAbs) := ⟨by omega⟩
  obtain ⟨C, hC⟩ := bdd_real_segment
    ((DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv (chiC_ne_one hD)).mono
      fun s (hs : 1 ≤ s.re) =>
        DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (.inl (chiC_ne_one hD)) hs)
  refine ⟨C, fun x hx => ?_⟩
  have h : ‖-deriv (DirichletCharacter.LFunction (chiC D)) (x : ℂ) /
      DirichletCharacter.LFunction (chiC D) (x : ℂ)‖ ≤ C := hC x ⟨hx.1.le, hx.2⟩
  have hs : 1 < (x : ℂ).re := by simpa using hx.1
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs,
    DirichletCharacter.LFunction_eq_LSeries _ hs,
    ← DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hs] at h
  have hL : LSeries ((fun n : ℕ => chiC D n) * fun n : ℕ => (vonMangoldt n : ℂ)) x =
      ((∑' n : ℕ, chiR D n * vonMangoldt n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    rw [← LSeries_ofReal _ (by linarith [hx.1])]
    refine LSeries_congr (fun {n} _ => ?_) _
    simp [chiC_apply, chiR]
  rw [hL, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-! ## 2. Primes and prime powers -/

theorem summable_npw : Summable npw := by
  refine (vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)).congr fun n => ?_
  simp [npw, vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) 0]

theorem div_rpow_le_div {a : ℝ} (ha : 0 ≤ a) (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    a / (n : ℝ) ^ x ≤ a / n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Real.zero_rpow (by linarith : x ≠ 0)]
  · refine div_le_div_of_nonneg_left ha (by exact_mod_cast hn) ?_
    conv_lhs => rw [← Real.rpow_one n]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx

theorem pw_nonneg (x : ℝ) (n : ℕ) : 0 ≤ pw x n := by
  unfold pw
  have : (0 : ℝ) ≤ if n.Prime then vonMangoldt n else 0 := by
    split_ifs
    · exact vonMangoldt_nonneg
    · exact le_rfl
  positivity

theorem pw_le (x : ℝ) (n : ℕ) : pw x n ≤ vonMangoldt n / (n : ℝ) ^ x := by
  unfold pw
  gcongr
  split_ifs
  · exact le_rfl
  · exact vonMangoldt_nonneg

theorem summable_pw {x : ℝ} (hx : 1 < x) : Summable (pw x) :=
  Summable.of_nonneg_of_le (pw_nonneg x) (pw_le x) (summable_vm hx)

theorem summable_mul_pw {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) {x : ℝ} (hx : 1 < x) :
    Summable fun n => c n * pw x n := by
  refine Summable.of_norm_bounded (summable_pw hx) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pw_nonneg x n)]
  exact mul_le_of_le_one_left (pw_nonneg x n) (hc n)

theorem summable_mul_vm {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => c n * vonMangoldt n / (n : ℝ) ^ x := by
  refine Summable.of_norm_bounded (summable_vm hx) fun n => ?_
  have h0 : (0 : ℝ) ≤ vonMangoldt n / (n : ℝ) ^ x := by positivity [vonMangoldt_nonneg (n := n)]
  rw [mul_div_assoc, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  exact mul_le_of_le_one_left h0 (hc n)

/-- For a weight bounded by `1`, the series over all `n` with `Λ` and the series over the primes
    differ by at most `∑_{n not prime} Λ(n) / n`. -/
theorem abs_tsum_sub_tsum_mul_pw_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) {x : ℝ} (hx : 1 < x) :
    |∑' n : ℕ, c n * vonMangoldt n / (n : ℝ) ^ x - ∑' n, c n * pw x n| ≤ ∑' n, npw n := by
  rw [← Summable.tsum_sub (summable_mul_vm hc hx) (summable_mul_pw hc hx), ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded summable_npw.hasSum fun n => ?_
  have hnp : (0 : ℝ) ≤ if n.Prime then 0 else vonMangoldt n := by
    split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  have h0 : (0 : ℝ) ≤ (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ x := by positivity
  have he : c n * vonMangoldt n / (n : ℝ) ^ x - c n * pw x n =
      c n * ((if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ x) := by
    unfold pw
    split_ifs <;> ring
  rw [he, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  exact (mul_le_of_le_one_left h0 (hc n)).trans (div_rpow_le_div hnp n hx.le)

/-- `∑_p log p · p^{−x} = 1/(x−1) + O(1)` for `1 < x ≤ 2`. -/
theorem pw_bound : ∃ C, ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
    |∑' n, pw x n - 1 / (x - 1)| ≤ C := by
  obtain ⟨C, hC⟩ := vm_bound
  refine ⟨C + ∑' n, npw n, fun x hx => ?_⟩
  have h1 := hC x hx
  have h2 := abs_tsum_sub_tsum_mul_pw_le (c := fun _ => 1) (fun _ => by simp) hx.1
  simp only [one_mul] at h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## 3. The quadratic symbol over the primes -/

theorem abs_jacobiSym_le_one (D : ℤ) (n : ℕ) : |(jacobiSym D n : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy D n with h | h | h <;> rw [h] <;> norm_num

/-- `∑_p (D / p) log p · p^{−x} = O_D(1)` for `1 < x ≤ 2`, when `D` is not a square. -/
theorem jacobi_bound {D : ℤ} (hD : ¬ IsSquare D) : ∃ C, ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
    |∑' n : ℕ, (jacobiSym D n : ℝ) * pw x n| ≤ C := by
  classical
  have hDabs : 1 ≤ D.natAbs := Int.natAbs_pos.mpr (ne_zero_of_not_isSquare hD)
  have hM : 4 * D.natAbs ≠ 0 := by omega
  obtain ⟨C, hC⟩ := twisted_bound hD
  set E : ℕ → ℝ := fun n => if n ∈ (4 * D.natAbs).primeFactors then Real.log n else 0 with hE
  have hE0 : ∀ n, 0 ≤ E n := fun n => by
    simp only [hE]
    split_ifs
    · exact Real.log_natCast_nonneg n
    · exact le_rfl
  have hEs : Summable E :=
    summable_of_ne_finset_zero (s := (4 * D.natAbs).primeFactors) fun n hn => ite_eq_right hn
  refine ⟨C + ∑' n, npw n + ∑' n, E n, fun x hx => ?_⟩
  have h1 := hC x hx
  have h2 := abs_tsum_sub_tsum_mul_pw_le (abs_chiR_le_one D) hx.1
  have h3 : |∑' n : ℕ, (jacobiSym D n : ℝ) * pw x n - ∑' n, chiR D n * pw x n| ≤ ∑' n, E n := by
    rw [← Summable.tsum_sub (summable_mul_pw (abs_jacobiSym_le_one D) hx.1)
      (summable_mul_pw (abs_chiR_le_one D) hx.1), ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hEs.hasSum fun n => ?_
    rw [Real.norm_eq_abs]
    by_cases hp : n.Prime
    · by_cases hco : n.Coprime (4 * D.natAbs)
      · have : chiR D n = (jacobiSym D n : ℝ) := by
          rw [chiR, chiZ_natCast, ite_eq_left hco]
        rw [this, sub_self, abs_zero]
        exact hE0 n
      · have hdvd : n ∣ 4 * D.natAbs := by
          by_contra hnd
          exact hco ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
        have h0 : chiR D n = 0 := by
          rw [chiR, chiZ_natCast, ite_eq_right hco, Int.cast_zero]
        have hEn : E n = Real.log n := by
          simp only [hE]
          rw [ite_eq_left (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hM⟩)]
        have hpw : pw x n ≤ Real.log n := by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_lt.le
          calc pw x n = vonMangoldt n / (n : ℝ) ^ x := by rw [pw, ite_eq_left hp]
            _ ≤ vonMangoldt n / n := div_rpow_le_div vonMangoldt_nonneg n hx.1.le
            _ ≤ vonMangoldt n := div_le_self vonMangoldt_nonneg hn1
            _ = Real.log n := vonMangoldt_apply_prime hp
        rw [h0, zero_mul, sub_zero, abs_mul, abs_of_nonneg (pw_nonneg x n), hEn]
        exact (mul_le_of_le_one_left (pw_nonneg x n) (abs_jacobiSym_le_one D n)).trans hpw
    · have : pw x n = 0 := by rw [pw, ite_eq_right hp, zero_div]
      rw [this, mul_zero, mul_zero, sub_self, abs_zero]
      exact hE0 n
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-! ## 4. The sieve -/

/-- **The sieve inequality with the weight `log p · p^{−x}`.** -/
theorem sieve (K : ℕ) {x : ℝ} (hx : 1 < x) :
    (2 : ℝ) ^ K * ∑' n, stableSet.indicator (pw x) n ≤
      ∑ A ∈ (range K).powerset,
        (-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n := by
  have hdet : ∀ n : ℕ, ((∏ k ∈ range K, (1 - jacobiSym (discZ k) n) : ℤ) : ℝ) * pw x n =
      ∑ A ∈ (range K).powerset,
        (-1 : ℝ) ^ A.card * ((jacobiSym (discProd A) n : ℝ) * pw x n) := by
    intro n
    rw [prod_one_sub_eq]
    push_cast
    rw [Finset.sum_mul]
    exact sum_congr rfl fun A _ => by ring
  have hsumA : ∀ A : Finset ℕ, Summable fun n : ℕ =>
      (-1 : ℝ) ^ A.card * ((jacobiSym (discProd A) n : ℝ) * pw x n) := fun A =>
    (summable_mul_pw (abs_jacobiSym_le_one _) hx).mul_left _
  have hsumD : Summable fun n : ℕ =>
      ((∏ k ∈ range K, (1 - jacobiSym (discZ k) n) : ℤ) : ℝ) * pw x n :=
    (summable_sum fun A (_ : A ∈ (range K).powerset) => hsumA A).congr fun n => (hdet n).symm
  have hR : ∑ A ∈ (range K).powerset,
        (-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n =
      ∑' n : ℕ, ((∏ k ∈ range K, (1 - jacobiSym (discZ k) n) : ℤ) : ℝ) * pw x n := by
    rw [tsum_congr hdet, Summable.tsum_finsetSum fun A _ => hsumA A]
    exact sum_congr rfl fun A _ => by rw [tsum_mul_left]
  rw [hR, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (((summable_pw hx).indicator _).mul_left _) hsumD
  by_cases hn : n ∈ stableSet
  · obtain ⟨hp, hs⟩ := hn
    rw [Set.indicator_of_mem (show n ∈ stableSet from ⟨hp, hs⟩), detector_of_stable K hp hs]
    push_cast
    exact le_rfl
  · rw [Set.indicator_of_notMem hn, mul_zero]
    exact mul_nonneg (by exact_mod_cast detector_nonneg K n) (pw_nonneg x n)

/-- For each `K` there is `R` with
    `2^K (x−1) ∑_{p stable} log p · p^{−x} ≤ 1 + (x−1) R` on `(1, 2]`. -/
theorem main_bound (K : ℕ) : ∃ R : ℝ, ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
    (2 : ℝ) ^ K * ((x - 1) * ∑' n, stableSet.indicator (pw x) n) ≤ 1 + (x - 1) * R := by
  classical
  have hex : ∀ D : ℤ, ∃ C : ℝ, ¬ IsSquare D → ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 →
      |∑' n : ℕ, (jacobiSym D n : ℝ) * pw x n| ≤ C := fun D => by
    by_cases h : IsSquare D
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨C, hC⟩ := jacobi_bound h
      exact ⟨C, fun _ => hC⟩
  choose Cq hCq using hex
  obtain ⟨C0, hC0⟩ := pw_bound
  set U : Finset ℕ → ℝ := fun A => if A = ∅ then 0 else Cq (discProd A) with hU
  refine ⟨C0 + ∑ A ∈ (range K).powerset, U A, fun x hx => ?_⟩
  have hx0 : 0 < x - 1 := sub_pos.mpr hx.1
  have hT : ∑' n, pw x n ≤ 1 / (x - 1) + C0 := by
    have := (abs_le.mp (hC0 x hx)).2
    linarith
  have hterm : ∀ A ∈ (range K).powerset,
      (-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n ≤
        (if A = ∅ then ∑' n, pw x n else 0) + U A := by
    intro A _
    by_cases hA : A = ∅
    · subst hA
      simp [hU, discProd, jacobiSym.one_left]
    · have hb := hCq (discProd A) (not_isSquare_prod_discZ (nonempty_iff_ne_empty.mpr hA)) x hx
      simp only [hU, ite_eq_right hA, zero_add]
      calc (-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n
          ≤ |(-1 : ℝ) ^ A.card * ∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n| :=
            le_abs_self _
        _ = |∑' n : ℕ, (jacobiSym (discProd A) n : ℝ) * pw x n| := by
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        _ ≤ Cq (discProd A) := hb
  have hsum := (sieve K hx.1).trans (sum_le_sum hterm)
  rw [sum_add_distrib, sum_ite_eq' _ _ _, ite_eq_left (empty_mem_powerset _)] at hsum
  have h1 : (2 : ℝ) ^ K * ∑' n, stableSet.indicator (pw x) n ≤
      1 / (x - 1) + (C0 + ∑ A ∈ (range K).powerset, U A) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hx0.le
  have h3 : (x - 1) * (1 / (x - 1) + (C0 + ∑ A ∈ (range K).powerset, U A)) =
      1 + (x - 1) * (C0 + ∑ A ∈ (range K).powerset, U A) := by
    field_simp
  rw [h3] at h2
  linarith

/-! ## 5. The density statements -/

theorem tendsto_stable_pw :
    Tendsto (fun x : ℝ => (x - 1) * ∑' n, stableSet.indicator (pw x) n) (𝓝[>] 1) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨R, hR⟩ := main_bound K
  have ht : Tendsto (fun x : ℝ => (1 / 2 : ℝ) ^ K * (1 + (x - 1) * R)) (𝓝[>] 1)
      (𝓝 ((1 / 2 : ℝ) ^ K * (1 + ((1 : ℝ) - 1) * R))) :=
    (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
  have hlt : (1 / 2 : ℝ) ^ K * (1 + ((1 : ℝ) - 1) * R) < ε := by simpa using hK
  filter_upwards [ht.eventually_lt_const hlt, Ioc_mem_nhdsGT one_lt_two] with x h1 hx
  have hx0 : 0 < x - 1 := sub_pos.mpr hx.1
  have hF0 : 0 ≤ (x - 1) * ∑' n, stableSet.indicator (pw x) n :=
    mul_nonneg hx0.le (tsum_nonneg fun n => Set.indicator_nonneg (fun n _ => pw_nonneg x n) n)
  have h2 : (1 / 2 : ℝ) ^ K * 2 ^ K = 1 := by rw [← mul_pow]; norm_num
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hF0]
  calc (x - 1) * ∑' n, stableSet.indicator (pw x) n
      = (1 / 2 : ℝ) ^ K * (2 ^ K * ((x - 1) * ∑' n, stableSet.indicator (pw x) n)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ (1 / 2 : ℝ) ^ K * (1 + (x - 1) * R) :=
        mul_le_mul_of_nonneg_left (hR x hx) (by positivity)
    _ < ε := h1

theorem pw_of_prime (x : ℝ) {p : ℕ} (hp : p.Prime) :
    pw x p = Real.log p * (p : ℝ) ^ (-x) := by
  rw [pw, ite_eq_left hp, vonMangoldt_apply_prime hp, Real.rpow_neg (Nat.cast_nonneg p),
    div_eq_mul_inv]

/-- **The stable primes have analytic density zero.**
    `(s − 1) ∑_{p stable} log p · p^{−s} → 0` as `s → 1⁺`, with no hypothesis. -/
theorem stable_analytic_density_zero :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' p : ℕ, stableSet.indicator (fun p : ℕ => Real.log p * (p : ℝ) ^ (-s)) p)
      (𝓝[>] 1) (𝓝 0) := by
  refine tendsto_stable_pw.congr fun x => ?_
  congr 2
  funext n
  exact congrFun (Set.indicator_congr fun p hp => pw_of_prime x hp.1) n

/-- **Normalisation.** `(s − 1) ∑_{p prime} log p · p^{−s} → 1` as `s → 1⁺`. -/
theorem primes_analytic_density_one :
    Tendsto (fun s : ℝ => (s - 1) *
        ∑' p : ℕ, (if p.Prime then Real.log p * (p : ℝ) ^ (-s) else 0))
      (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C, hC⟩ := pw_bound
  have hpw : ∀ x : ℝ, (fun p : ℕ => if p.Prime then Real.log p * (p : ℝ) ^ (-x) else 0) =
      pw x := fun x => by
    funext p
    split_ifs with hp
    · exact (pw_of_prime x hp).symm
    · rw [pw, ite_eq_right hp, zero_div]
  have hlo : Tendsto (fun x : ℝ => 1 - (x - 1) * C) (𝓝[>] 1) (𝓝 (1 - ((1 : ℝ) - 1) * C)) :=
    (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun x : ℝ => 1 + (x - 1) * C) (𝓝[>] 1) (𝓝 (1 + ((1 : ℝ) - 1) * C)) :=
    (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
  rw [show (1 : ℝ) - ((1 : ℝ) - 1) * C = 1 by ring] at hlo
  rw [show (1 : ℝ) + ((1 : ℝ) - 1) * C = 1 by ring] at hhi
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 1, 1 - (x - 1) * C ≤ (x - 1) * ∑' p : ℕ, pw x p ∧
      (x - 1) * ∑' p : ℕ, pw x p ≤ 1 + (x - 1) * C := by
    filter_upwards [Ioc_mem_nhdsGT one_lt_two] with x hx
    have hx0 : 0 < x - 1 := sub_pos.mpr hx.1
    have h := abs_le.mp (hC x hx)
    have h1 := mul_le_mul_of_nonneg_left h.1 hx0.le
    have h2 := mul_le_mul_of_nonneg_left h.2 hx0.le
    have h3 : (x - 1) * (∑' n, pw x n - 1 / (x - 1)) = (x - 1) * ∑' n, pw x n - 1 := by
      field_simp
    rw [h3] at h1 h2
    constructor <;> linarith
  simp only [hpw]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (hev.mono fun _ h => h.1)
    (hev.mono fun _ h => h.2)

end StableAnalyticDensity

end FunctionFieldAnalog
