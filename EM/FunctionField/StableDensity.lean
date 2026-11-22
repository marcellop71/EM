import EM.FunctionField.StableCount

/-!
# Stable primes have density zero

`StableCount.two_pow_mul_card_stable_le` bounds the number of stable primes up to `x` by
`π(x) / 2^K` plus the sums over primes of the quadratic symbols `(Δ_A / p)`, `Δ_A` a
non-square. If each such sum is `o(π(x))` — the prime number theorem for one non-trivial
quadratic character — then the stable primes have natural density zero among the primes.

## The analytic input

`QuadPrimeSumLittleO` says: for every non-square integer `D`,
`∑_{p ≤ x} (D / p) = o(π(x))`. It is classical (Dirichlet's theorem with natural density for
the quadratic character `(D / ·)`, or Chebotarev for `ℚ(√D)`), and it is formalized outside
this repository: in the Tau Ceti library, natural-density Chebotarev
(`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`) together with the description
of Frobenius in a multiquadratic field by Legendre symbols
(`galoisGroupEquiv_frobenius`). Tau Ceti is on a later toolchain and is not a dependency
here; the statement is a hypothesis, never an axiom.

## Main result

* `stable_density_zero` — under `QuadPrimeSumLittleO`,
  `#{stable p ≤ x} / π(x) → 0`.
-/

namespace FunctionFieldAnalog

namespace StableDensity

open Finset Filter Topology StablePrimes StableCount

/-- For every non-square `D`, `∑_{p ≤ x} (D / p) = o(π(x))`. -/
def QuadPrimeSumLittleO : Prop :=
  ∀ D : ℤ, ¬ IsSquare D →
    Tendsto (fun x : ℕ => (charSum D x : ℝ) / ((primesLE x).card : ℝ)) atTop (𝓝 0)

theorem card_primesLE_pos {x : ℕ} (hx : 2 ≤ x) : 0 < (primesLE x).card :=
  card_pos.mpr ⟨2, mem_filter.mpr ⟨mem_Icc.mpr ⟨by norm_num, hx⟩, Nat.prime_two⟩⟩

/-- **Stable primes have density zero**, given the prime number theorem for quadratic
    characters. -/
theorem stable_density_zero (h : QuadPrimeSumLittleO) :
    Tendsto (fun x : ℕ => ((stableLE x).card : ℝ) / ((primesLE x).card : ℝ)) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose `K` with `2^{-K} < ε / 2`
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  -- eventually every character sum with `∅ ≠ A ⊆ {0..K−1}` is at most `(ε/2) π(x)`
  have hall : ∀ᶠ x : ℕ in atTop, ∀ A ∈ (range K).powerset, A.Nonempty →
      |(charSum (discProd A) x : ℝ)| ≤ ε / 2 * (primesLE x).card := by
    rw [eventually_all_finset]
    intro A _
    by_cases hA : A.Nonempty
    · have h1 := (Metric.tendsto_nhds.mp (h (discProd A) (not_isSquare_prod_discZ hA)))
        (ε / 2) (half_pos hε)
      filter_upwards [h1, eventually_ge_atTop 2] with x hx hx2 _
      have hpos : (0 : ℝ) < (primesLE x).card := by exact_mod_cast card_primesLE_pos hx2
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos] at hx
      exact hx.le
    · exact Eventually.of_forall fun x hne => absurd hne hA
  filter_upwards [hall, eventually_ge_atTop 2] with x hx hx2
  have hpos : (0 : ℝ) < (primesLE x).card := by exact_mod_cast card_primesLE_pos hx2
  have hmain := two_pow_mul_card_stable_le K x (ε / 2 * (primesLE x).card)
    fun A hA hne => hx A (mem_powerset.mpr hA) hne
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  have hK' : (1 : ℝ) < ε / 2 * 2 ^ K := by
    have : (1 / 2 : ℝ) ^ K * 2 ^ K = 1 := by rw [← mul_pow]; norm_num
    nlinarith
  have hS : (0 : ℝ) ≤ (stableLE x).card := Nat.cast_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hS hpos.le), div_lt_iff₀ hpos]
  -- `2^K S ≤ π + (2^K − 1)(ε/2)π < 2^K ε π`
  have hE : (0 : ℝ) ≤ ε / 2 * (primesLE x).card := by positivity
  nlinarith [mul_pos h2 hpos]

end StableDensity

end FunctionFieldAnalog
