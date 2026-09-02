import EM.FunctionField.FrobeniusOrbit
import EM.FunctionField.CompositeFloors
import Mathlib.Tactic.ComputeDegree

/-!
# The Euclid–Mullin sequence over `𝔽_2[X]`: the first terms, and sharpness of the constant 3

`CompositeFloors.lean` shows that over `𝔽_2` no four consecutive Euclid polynomials are
irreducible.  Here we show the bound is attained: for **every** `FFEMData 2` (the seed is `X`,
the choice function arbitrary) the first three Euclid polynomials

    X + 1,   X² + X + 1,   X⁴ + X + 1

are irreducible, so the first four terms of the sequence are forced,

    ffSeq = X, X + 1, X² + X + 1, X⁴ + X + 1, …,   ffProd 3 = X⁸ + X⁴ + X² + X,

and the fourth Euclid polynomial splits as `(X⁴ + X³ + 1)(X⁴ + X³ + X² + X + 1)` — a tie between
two quartics (`ff_two_first_terms`, `ff_two_attains_three`).

Irreducibility of `X² + X + 1` and `X⁴ + X + 1` over `𝔽_2` is proved by the Frobenius-orbit
criterion of `FrobeniusOrbit.lean`: a root `y` of `y⁴ + y + 1` satisfies `y⁴ = y + 1`, hence
`y¹⁶ = y⁴ + 1 = y` and `y⁴ ≠ y`, `y² ≠ y`, so its Frobenius orbit has exactly four points
(`quartic_root_minimalPeriod`); a root of `y² + y + 1` has period two.  These period facts are
reused in `AutonomousDegrees.lean`.
-/

namespace FunctionFieldAnalog

namespace CharTwo

open Polynomial FrobeniusOrbit CompositeFloors

theorem two_eq_zero_L : (2 : Lp 2) = 0 := by
  have := CharP.cast_eq_zero (Lp 2) 2
  exact_mod_cast this

/-! ## 1. Periods of roots -/

theorem quadratic_root_minimalPeriod {y : Lp 2} (hy : y ^ 2 + y + 1 = 0) :
    Function.minimalPeriod (⇑(φ 2)) y = 2 :=
  phi3_root_minimalPeriod 2 (by norm_num) hy

theorem quartic_root_pow_four {y : Lp 2} (hy : y ^ 4 + y + 1 = 0) : y ^ 4 = y + 1 := by
  linear_combination hy + (-(y + 1)) * two_eq_zero_L

theorem quartic_root_minimalPeriod {y : Lp 2} (hy : y ^ 4 + y + 1 = 0) :
    Function.minimalPeriod (⇑(φ 2)) y = 4 := by
  have h2 := two_eq_zero_L
  have hy4 := quartic_root_pow_four hy
  have hper : Function.IsPeriodicPt (⇑(φ 2)) 4 y := by
    show (⇑(φ 2))^[4] y = y
    rw [φ_iterate, show (2 : ℕ) ^ 4 = 4 * 4 by norm_num, pow_mul, hy4]
    linear_combination (2 * y ^ 3 + 3 * y ^ 2 + 2 * y + 1) * h2 + hy4
  have hnot2 : ¬ Function.IsPeriodicPt (⇑(φ 2)) 2 y := by
    intro h
    have h' : (⇑(φ 2))^[2] y = y := h
    rw [φ_iterate, show (2 : ℕ) ^ 2 = 4 by norm_num, hy4] at h'
    exact one_ne_zero (by linear_combination h' : (1 : Lp 2) = 0)
  have hnot1 : ¬ Function.IsPeriodicPt (⇑(φ 2)) 1 y := by
    intro h
    have h' : (⇑(φ 2))^[1] y = y := h
    rw [φ_iterate, pow_one] at h'
    have h4 : y ^ 4 = y := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h', h']
    rw [hy4] at h4
    exact one_ne_zero (by linear_combination h4 : (1 : Lp 2) = 0)
  have hdvd : Function.minimalPeriod (⇑(φ 2)) y ∣ 2 ^ 2 := by
    simpa using hper.minimalPeriod_dvd
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · exfalso; apply hnot1
    rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, hkeq]; norm_num
  · exfalso; apply hnot2
    rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, hkeq]; norm_num
  · rw [hkeq]; norm_num

/-! ## 2. Two irreducible polynomials over `𝔽_2` -/

theorem X_sq_add_X_add_one_irreducible : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  obtain ⟨y, hy⟩ := exists_root_of_natDegree_pos 2 (f := X ^ 2 + X + 1) (by rw [hdeg]; norm_num)
  have hy' : y ^ 2 + y + 1 = 0 := by simpa using hy
  exact irreducible_of_natDegree_eq_minimalPeriod 2 (by monicity!) hy
    (by rw [hdeg, quadratic_root_minimalPeriod hy'])

theorem X_four_add_X_add_one_irreducible : Irreducible (X ^ 4 + X + 1 : (ZMod 2)[X]) := by
  have hdeg : (X ^ 4 + X + 1 : (ZMod 2)[X]).natDegree = 4 := by compute_degree!
  obtain ⟨y, hy⟩ := exists_root_of_natDegree_pos 2 (f := X ^ 4 + X + 1) (by rw [hdeg]; norm_num)
  have hy' : y ^ 4 + y + 1 = 0 := by simpa using hy
  exact irreducible_of_natDegree_eq_minimalPeriod 2 (by monicity!) hy
    (by rw [hdeg, quartic_root_minimalPeriod hy'])

theorem X_add_one_irreducible : Irreducible (X + 1 : (ZMod 2)[X]) := by
  have : (X + 1 : (ZMod 2)[X]) = X - C 1 := by
    rw [C_1]; linear_combination two_eq_zero_poly
  rw [this]; exact irreducible_X_sub_C _

/-! ## 3. The first terms of every `𝔽_2` sequence -/

theorem euclid_zero (d : FFEMData 2) : d.ffProd 0 + 1 = X + 1 := by rw [d.ffProd_zero]

theorem euclid_zero_irreducible (d : FFEMData 2) : Irreducible (d.ffProd 0 + 1) := by
  rw [euclid_zero]; exact X_add_one_irreducible

theorem ffProd_one (d : FFEMData 2) : d.ffProd 1 = X ^ 2 + X := by
  rw [ffProd_succ_of_irreducible d 0 (euclid_zero_irreducible d), d.ffProd_zero]; ring

theorem euclid_one (d : FFEMData 2) : d.ffProd 1 + 1 = X ^ 2 + X + 1 := by rw [ffProd_one]

theorem euclid_one_irreducible (d : FFEMData 2) : Irreducible (d.ffProd 1 + 1) := by
  rw [euclid_one]; exact X_sq_add_X_add_one_irreducible

theorem ffProd_two (d : FFEMData 2) : d.ffProd 2 = X ^ 4 + X := by
  rw [ffProd_add_two_of_two_irreducible d 0 (euclid_zero_irreducible d) (euclid_one_irreducible d),
    d.ffProd_zero]

theorem euclid_two (d : FFEMData 2) : d.ffProd 2 + 1 = X ^ 4 + X + 1 := by rw [ffProd_two]

theorem euclid_two_irreducible (d : FFEMData 2) : Irreducible (d.ffProd 2 + 1) := by
  rw [euclid_two]; exact X_four_add_X_add_one_irreducible

theorem ffProd_three (d : FFEMData 2) : d.ffProd 3 = X ^ 8 + X ^ 4 + X ^ 2 + X := by
  rw [ffProd_succ_of_irreducible d 2 (euclid_two_irreducible d), ffProd_two]
  linear_combination (X ^ 5 : (ZMod 2)[X]) * two_eq_zero_poly

/-- The fourth Euclid polynomial over `𝔽_2` splits into two quartics: the first tie. -/
theorem euclid_three_factor (d : FFEMData 2) :
    d.ffProd 3 + 1 = (X ^ 4 + X ^ 3 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by
  rw [ffProd_three]
  linear_combination (-(X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 : (ZMod 2)[X])) * two_eq_zero_poly

theorem euclid_three_reducible (d : FFEMData 2) : ¬ Irreducible (d.ffProd 3 + 1) :=
  euclid_three_reducible_of_two d 0 (euclid_zero_irreducible d) (euclid_one_irreducible d)
    (euclid_two_irreducible d)

/-- **The first four terms of every Euclid–Mullin sequence over `𝔽_2[X]` are forced:**
`X, X + 1, X² + X + 1, X⁴ + X + 1`. -/
theorem ff_two_first_terms (d : FFEMData 2) :
    d.ffSeq 0 = X ∧ d.ffSeq 1 = X + 1 ∧ d.ffSeq 2 = X ^ 2 + X + 1 ∧ d.ffSeq 3 = X ^ 4 + X + 1 :=
  ⟨d.ffSeq_zero,
   by rw [ffSeq_succ_eq_of_irreducible d 0 (euclid_zero_irreducible d), euclid_zero],
   by rw [ffSeq_succ_eq_of_irreducible d 1 (euclid_one_irreducible d), euclid_one],
   by rw [ffSeq_succ_eq_of_irreducible d 2 (euclid_two_irreducible d), euclid_two]⟩

/-- **Sharpness of the constant 3.**  The seed `X` produces three consecutive irreducible Euclid
polynomials and then a reducible one. -/
theorem ff_two_attains_three (d : FFEMData 2) :
    Irreducible (d.ffProd 0 + 1) ∧ Irreducible (d.ffProd 1 + 1) ∧ Irreducible (d.ffProd 2 + 1) ∧
      ¬ Irreducible (d.ffProd 3 + 1) :=
  ⟨euclid_zero_irreducible d, euclid_one_irreducible d, euclid_two_irreducible d,
   euclid_three_reducible d⟩

end CharTwo

end FunctionFieldAnalog
