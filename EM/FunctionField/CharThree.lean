import EM.FunctionField.CompositeFloors
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree

/-!
# The Euclid–Mullin sequence over `𝔽_3[X]`

Over `𝔽_3` the third cyclotomic polynomial has a double root: `Φ₃(y) = y² + y + 1 = (y − 1)²`.
Consequently, if a Euclid polynomial `E_n = P_n + 1` is irreducible, the next one is a
**perfect square**,

    E_{n+1} = Φ₃(P_n) = (P_n − 1)²                       (`euclid_succ_eq_sq`),

hence reducible (`euclid_succ_reducible`): the composite floor holds with constant 1, the growth
constant vanishes for every sequence (`ffGrowthConstant_eq_zero`), and after an irreducible
stage the selected factor divides `P_n − 1` (`ffSeq_dvd_sub_one`).

The first five terms of every `𝔽_3` sequence are forced (`ff_three_first_terms`):

    X,  X + 1,  X + 2,  X³ + 2X + 1,  X³ + 2X + 2,

with `ffProd 2 = X³ + 2X = X³ − X`, the product of *all* linear polynomials: over `𝔽_3` the
sequence captures every linear irreducible in its first three steps.

Landscape for the composite floor: `𝔽_2` constant 3 (sharp), `𝔽_3` constant 1 (square), `𝔽_p`
with `p ≡ 1 (mod 3)` constant 1 (split), `𝔽_5` false for the seed `X` (stable tower).
-/

namespace FunctionFieldAnalog

namespace CharThree

open Polynomial FFDegreeTelescope CompositeFloors

instance instFactPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem three_eq_zero_poly : (3 : (ZMod 3)[X]) = 0 := by
  have := CharP.cast_eq_zero (ZMod 3)[X] 3
  exact_mod_cast this

/-! ## 1. The square identity and the floor -/

/-- After an irreducible stage the Euclid polynomial is a perfect square: `Φ₃(P) = (P − 1)²`. -/
theorem euclid_succ_eq_sq (d : FFEMData 3) (n : ℕ) (h : Irreducible (d.ffProd n + 1)) :
    d.ffProd (n + 1) + 1 = (d.ffProd n - 1) ^ 2 := by
  rw [ffProd_succ_of_irreducible d n h]
  linear_combination (d.ffProd n : (ZMod 3)[X]) * three_eq_zero_poly

theorem natDegree_sub_one_pos (d : FFEMData 3) (n : ℕ) : 0 < (d.ffProd n - 1).natDegree := by
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · exact ffProd_natDegree_pos d n
  · rw [natDegree_one]; exact ffProd_natDegree_pos d n

/-- **Constant 1 over `𝔽_3`.** -/
theorem euclid_succ_reducible (d : FFEMData 3) (n : ℕ) (h : Irreducible (d.ffProd n + 1)) :
    ¬ Irreducible (d.ffProd (n + 1) + 1) := by
  rw [euclid_succ_eq_sq d n h, sq]
  exact not_irreducible_mul_of_natDegree_pos (natDegree_sub_one_pos d n) (natDegree_sub_one_pos d n)

theorem infinitelyManyReducible (d : FFEMData 3) : FFInfinitelyManyReducible d := by
  intro N
  by_cases h : Irreducible (d.ffProd N + 1)
  · exact ⟨N + 1, by omega, euclid_succ_reducible d N h⟩
  · exact ⟨N, le_rfl, h⟩

/-- **The composite floor over `𝔽_3[X]`: the growth constant vanishes for every sequence.** -/
theorem ffGrowthConstant_eq_zero (d : FFEMData 3) : ffGrowthConstant d = 0 :=
  (ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero d).mp (infinitelyManyReducible d)

theorem not_perpetual (d : FFEMData 3) (N : ℕ) : ¬ FFPerpetualIrreducibility d N :=
  (ffInfinitelyManyReducible_iff d).mp (infinitelyManyReducible d) N

/-- After an irreducible stage, the selected factor divides `P_n − 1`. -/
theorem ffSeq_dvd_sub_one (d : FFEMData 3) (n : ℕ) (h : Irreducible (d.ffProd n + 1)) :
    d.ffSeq (n + 2) ∣ d.ffProd n - 1 := by
  obtain ⟨_, hirr, hdvd⟩ := d.ffSeq_succ (n + 1)
  rw [euclid_succ_eq_sq d n h] at hdvd
  exact hirr.prime.dvd_of_dvd_pow hdvd

/-! ## 2. The first five terms -/

theorem X_add_one_irreducible : Irreducible (X + 1 : (ZMod 3)[X]) := by
  have : (X + 1 : (ZMod 3)[X]) = X - C (-1) := by simp [sub_eq_add_neg]
  rw [this]; exact irreducible_X_sub_C _

theorem X_add_two_irreducible : Irreducible (X + 2 : (ZMod 3)[X]) := by
  have : (X + 2 : (ZMod 3)[X]) = X - C (-2) := by rw [map_neg, sub_neg_eq_add, map_ofNat]
  rw [this]; exact irreducible_X_sub_C _

/-- A cubic over `𝔽_3` with no root in `𝔽_3` is irreducible. -/
theorem cubic_irreducible_of_no_root {f : (ZMod 3)[X]} (hdeg : f.natDegree = 3)
    (hroot : ∀ a : ZMod 3, f.eval a ≠ 0) : Irreducible f := by
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  exact hroot a ((mem_roots hf0).mp ha)

theorem eval_cubic_one (a : ZMod 3) : eval a (X ^ 3 + 2 * X + 1 : (ZMod 3)[X]) = a ^ 3 + 2 * a + 1 := by
  simp

theorem eval_cubic_two (a : ZMod 3) : eval a (X ^ 3 + 2 * X + 2 : (ZMod 3)[X]) = a ^ 3 + 2 * a + 2 := by
  simp

theorem cubic_one_irreducible : Irreducible (X ^ 3 + 2 * X + 1 : (ZMod 3)[X]) := by
  refine cubic_irreducible_of_no_root (by compute_degree!) ?_
  intro a; rw [eval_cubic_one]; fin_cases a <;> decide

theorem cubic_two_irreducible : Irreducible (X ^ 3 + 2 * X + 2 : (ZMod 3)[X]) := by
  refine cubic_irreducible_of_no_root (by compute_degree!) ?_
  intro a; rw [eval_cubic_two]; fin_cases a <;> decide

theorem euclid_zero_irreducible (d : FFEMData 3) : Irreducible (d.ffProd 0 + 1) := by
  rw [d.ffProd_zero]; exact X_add_one_irreducible

theorem ffProd_one (d : FFEMData 3) : d.ffProd 1 = X ^ 2 + X := by
  rw [ffProd_succ_of_irreducible d 0 (euclid_zero_irreducible d), d.ffProd_zero]; ring

/-- The second Euclid polynomial over `𝔽_3` is the square `(X + 2)²`. -/
theorem euclid_one (d : FFEMData 3) : d.ffProd 1 + 1 = (X + 2) ^ 2 := by
  rw [ffProd_one]; linear_combination (-(X + 1) : (ZMod 3)[X]) * three_eq_zero_poly

theorem ffSeq_two (d : FFEMData 3) : d.ffSeq 2 = X + 2 := by
  obtain ⟨hm, hirr, hdvd⟩ := d.ffSeq_succ 1
  rw [euclid_one] at hdvd
  exact eq_of_monic_irreducible_dvd hm hirr (monic_X_add_C 2) X_add_two_irreducible
    (hirr.prime.dvd_of_dvd_pow hdvd)

/-- `ffProd 2 = X³ − X`: all three linear polynomials are captured by stage 2. -/
theorem ffProd_two (d : FFEMData 3) : d.ffProd 2 = X ^ 3 + 2 * X := by
  rw [d.ffProd_succ, ffSeq_two, ffProd_one]
  linear_combination (X ^ 2 : (ZMod 3)[X]) * three_eq_zero_poly

theorem euclid_two (d : FFEMData 3) : d.ffProd 2 + 1 = X ^ 3 + 2 * X + 1 := by rw [ffProd_two]

theorem euclid_two_irreducible (d : FFEMData 3) : Irreducible (d.ffProd 2 + 1) := by
  rw [euclid_two]; exact cubic_one_irreducible

theorem ffSeq_three (d : FFEMData 3) : d.ffSeq 3 = X ^ 3 + 2 * X + 1 := by
  rw [ffSeq_succ_eq_of_irreducible d 2 (euclid_two_irreducible d), euclid_two]

/-- The fourth Euclid polynomial is again a square, `(X³ + 2X + 2)²`. -/
theorem euclid_three (d : FFEMData 3) : d.ffProd 3 + 1 = (X ^ 3 + 2 * X + 2) ^ 2 := by
  rw [euclid_succ_eq_sq d 2 (euclid_two_irreducible d), ffProd_two]
  linear_combination (-(2 * X ^ 3 + 4 * X + 1) : (ZMod 3)[X]) * three_eq_zero_poly

theorem ffSeq_four (d : FFEMData 3) : d.ffSeq 4 = X ^ 3 + 2 * X + 2 := by
  obtain ⟨hm, hirr, hdvd⟩ := d.ffSeq_succ 3
  rw [euclid_three] at hdvd
  exact eq_of_monic_irreducible_dvd hm hirr (by monicity!) cubic_two_irreducible
    (hirr.prime.dvd_of_dvd_pow hdvd)

/-- **The first five terms of every Euclid–Mullin sequence over `𝔽_3[X]` are forced:**
`X, X + 1, X + 2, X³ + 2X + 1, X³ + 2X + 2`. -/
theorem ff_three_first_terms (d : FFEMData 3) :
    d.ffSeq 0 = X ∧ d.ffSeq 1 = X + 1 ∧ d.ffSeq 2 = X + 2 ∧
      d.ffSeq 3 = X ^ 3 + 2 * X + 1 ∧ d.ffSeq 4 = X ^ 3 + 2 * X + 2 :=
  ⟨d.ffSeq_zero,
   by rw [ffSeq_succ_eq_of_irreducible d 0 (euclid_zero_irreducible d), d.ffProd_zero],
   ffSeq_two d, ffSeq_three d, ffSeq_four d⟩

end CharThree

end FunctionFieldAnalog
