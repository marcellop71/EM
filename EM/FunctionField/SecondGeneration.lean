import EM.FunctionField.CompositeFloors
import Mathlib.RingTheory.Polynomial.Selmer
import Mathlib.FieldTheory.KummerPolynomial

/-!
# The second generation: the first stage off the tower, for `p ≡ 1 (mod 3)`

2026-11-22.

Every sequence over `𝔽_p[X]` starts `X, X + 1`, and its Euclid polynomial at stage `1` is
`X² + X + 1`. For `p ≡ 1 (mod 3)` this splits as `(X − ω)(X − ω²)`, the tower is left, and
the term chosen is `X − ω` for a primitive cube root of unity `ω`. The accumulator is then
`X (X + 1) (X − ω)`.

The three roots `0, −1, ω` are the vertices of an equilateral triangle: the affine map
`y ↦ ω² y − 1` permutes them cyclically. So the accumulator is invariant under a rotation of
order `3` and is a *pure cubic* about the centre `(ω − 1)/3`:

  `27 · (X (X + 1) (X − ω) + 1) = (3X + 1 − ω)³ + 6 (5 + ω)`.

Hence the Euclid polynomial at stage `2` is a Kummer polynomial, and its factorization is
decided by one cubic residue condition:

* it is irreducible iff `−6 (5 + ω)` is not a cube in `𝔽_p`;
* otherwise it is a product of three linear factors.

It is never "linear times irreducible quadratic". In the first case the sequence takes a
prime stage (the whole cubic); in the second it captures a linear polynomial at stage `3`.

This is the counterpart, one generation later and with exponent `3` in place of `2`, of the
stability criterion of `StabilityCriterion.lean`: there the accumulator `X (X + 1)` is a pure
square about `−1/2` and the quadratic character of the values at that centre decides the
tower. The identity holds with any polynomial `B` in place of `X` (`cubic_identity`), so it
applies to every stage `n` of every sequence at which `E_n` is irreducible and `P_n − ω` is
the next term.

## Main results

* `cubic_identity` — the pure-cubic identity, for any base `B`.
* `cubic_irreducible_iff` — over a field with `3 ≠ 0`: `X (X+1) (X−ω) + 1` is irreducible iff
  `−6 (5 + ω)` is not a cube.
* `cubic_eq_prod` — if `b³ = −6 (5 + ω)`, the three linear factors.
* `ffProd_one`, `exists_ffSeq_two`, `euclid_two` — the first two stages of every sequence.
* `euclid_two_irreducible_iff` — stage `2` is prime iff `−6 (5 + ω)` is not a cube.
* `ffSeq_three_natDegree` — the term at stage `3` has degree `3` or `1`, never `2`.
-/

namespace FunctionFieldAnalog

namespace SecondGeneration

open Polynomial CompositeFloors

/-! ## 1. The pure cubic, over any field -/

section Field

variable {K : Type*} [Field K]

theorem C_root {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (C ω : K[X]) ^ 2 + C ω + 1 = 0 := by
  have := congrArg (C : K → K[X]) hω
  simpa [map_add, map_pow, map_one] using this

/-- **The pure-cubic identity.** For `ω² + ω + 1 = 0` and any `B`,
    `27 (B (B + 1) (B − ω) + 1) = (3B + 1 − ω)³ + 6 (5 + ω)`. -/
theorem cubic_identity {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (B : K[X]) :
    27 * (B * (B + 1) * (B - C ω) + 1) = (3 * B + 1 - C ω) ^ 3 + 6 * (5 + C ω) := by
  linear_combination (-(9 * B + 4 - C ω)) * C_root hω

/-- The rotation `y ↦ ω² y − 1` of order `3` preserves `y (y + 1) (y − ω)`. -/
theorem rotation_invariant {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (y : K) :
    (ω ^ 2 * y - 1) * (ω ^ 2 * y - 1 + 1) * (ω ^ 2 * y - 1 - ω) = y * (y + 1) * (y - ω) := by
  linear_combination
    (y ^ 3 * (ω - 1) * (ω ^ 3 + 1) - y ^ 2 * ((2 + ω) * ω * (ω - 1) + 1) + y * ω) * hω

/-- The cubic `X (X + 1) (X − ω) + 1`. -/
noncomputable def cubic (ω : K) : K[X] := X * (X + 1) * (X - C ω) + 1

/-- If `b³ = −6 (5 + ω)`, the cubic is a product of three linear factors. -/
theorem cubic_eq_prod {ω b : K} (hω : ω ^ 2 + ω + 1 = 0) (hb : b ^ 3 = -(6 * (5 + ω))) :
    27 * cubic ω = (3 * X + 1 - C ω - C b) * (3 * X + 1 - C ω - C ω * C b) *
      (3 * X + 1 - C ω - C ω ^ 2 * C b) := by
  have hbC : (C b : K[X]) ^ 3 = -(6 * (5 + C ω)) := by
    have := congrArg (C : K → K[X]) hb
    simpa only [map_add, map_pow, map_mul, map_neg, map_ofNat] using this
  rw [cubic, cubic_identity hω X]
  linear_combination
    (C b * (3 * X + 1 - C ω) ^ 2 - C ω * C b ^ 2 * (3 * X + 1 - C ω) + (C ω - 1) * C b ^ 3) *
      C_root hω + hbC

/-- If `b³ = −6 (5 + ω)` and `3 ≠ 0`, then `(b − 1 + ω)/3` is a root of the cubic. -/
theorem cubic_root {ω b : K} (h3 : (3 : K) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0)
    (hb : b ^ 3 = -(6 * (5 + ω))) : (cubic ω).IsRoot ((b - 1 + ω) / 3) := by
  have h := congrArg (eval ((b - 1 + ω) / 3)) (cubic_eq_prod hω hb)
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h3
  have hz : 3 * ((b - 1 + ω) / 3) + 1 - ω - b = 0 := by field_simp; ring
  simp only [eval_mul, eval_sub, eval_add, eval_ofNat, eval_X, eval_C, eval_one, eval_pow,
    hz, zero_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h h27
  · exact h

/-- **The Kummer criterion for the cubic.** Over a field with `3 ≠ 0`, the cubic
    `X (X + 1) (X − ω) + 1` is irreducible iff `−6 (5 + ω)` is not a cube. -/
theorem cubic_irreducible_iff {ω : K} (h3 : (3 : K) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0) :
    Irreducible (cubic ω) ↔ ∀ b : K, b ^ 3 ≠ -(6 * (5 + ω)) := by
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h3
  let _ : Invertible (3 : K) := invertibleOfNonzero h3
  -- the Kummer polynomial and its image under `X ↦ 3X + (1 − ω)`
  have hK : algEquivCMulXAddC (3 : K) (1 - ω) (X ^ 3 - C (-(6 * (5 + ω)))) = 27 * cubic ω := by
    rw [cubic, cubic_identity hω X]
    simp only [algEquivCMulXAddC_apply, map_sub, map_pow, aeval_X, aeval_C, map_neg, map_mul,
      map_add, map_one, algebraMap_eq, map_ofNat]
    ring
  have hunit : IsUnit (27 : K[X]) := by
    have : (27 : K[X]) = C 27 := (map_ofNat C 27).symm
    rw [this]; exact isUnit_C.mpr (IsUnit.mk0 _ h27)
  rw [← irreducible_isUnit_mul hunit, ← hK,
    ← X_pow_sub_C_irreducible_iff_of_prime Nat.prime_three]
  exact MulEquiv.irreducible_iff (algEquivCMulXAddC (3 : K) (1 - ω)).toMulEquiv

end Field

/-! ## 2. The first stages of every sequence over `𝔽_p`, `p ≡ 1 (mod 3)` -/

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem three_ne_zero_of_one_mod_three (hp3 : p % 3 = 1) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_three).mp h'
  omega

/-- Every sequence has `P_1 = X (X + 1)`. -/
theorem ffProd_one (d : FFEMData p) : d.ffProd 1 = X * (X + 1) := by
  have hirr : Irreducible (d.ffProd 0 + 1) := by
    rw [d.ffProd_zero]
    have : (X + 1 : (ZMod p)[X]) = X + C 1 := by simp
    rw [this]
    exact irreducible_of_degree_eq_one (degree_X_add_C 1)
  rw [ffProd_succ_of_irreducible d 0 hirr, d.ffProd_zero]

/-- For `p ≡ 1 (mod 3)`, the term at stage `2` is `X − ω` for a primitive cube root of unity. -/
theorem exists_ffSeq_two (hp3 : p % 3 = 1) (d : FFEMData p) :
    ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 ∧ d.ffSeq 2 = X - C ω := by
  obtain ⟨ω, hω⟩ := exists_root_phi3 hp3
  have hω2 : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
    linear_combination (ω ^ 2 - ω + 1) * hω
  obtain ⟨hm, hirr, hdvd⟩ := d.ffSeq_succ 1
  have hfac : d.ffProd 1 + 1 = (X - C ω) * (X - C (ω ^ 2)) := by
    rw [ffProd_one, C_pow]
    linear_combination (X - (C ω - 1)) * C_root hω
  rw [hfac] at hdvd
  rcases hirr.prime.dvd_or_dvd hdvd with h | h
  · exact ⟨ω, hω, eq_of_monic_irreducible_dvd hm hirr (monic_X_sub_C ω)
      (irreducible_X_sub_C ω) h⟩
  · exact ⟨ω ^ 2, hω2, eq_of_monic_irreducible_dvd hm hirr (monic_X_sub_C _)
      (irreducible_X_sub_C _) h⟩

/-- **Stage `2` of every sequence, `p ≡ 1 (mod 3)`.** The Euclid polynomial is the cubic
    `X (X + 1) (X − ω) + 1`, with `X − ω` the term chosen at stage `2`. -/
theorem euclid_two (hp3 : p % 3 = 1) (d : FFEMData p) :
    ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 ∧ d.ffSeq 2 = X - C ω ∧ d.ffProd 2 + 1 = cubic ω := by
  obtain ⟨ω, hω, h2⟩ := exists_ffSeq_two hp3 d
  refine ⟨ω, hω, h2, ?_⟩
  rw [d.ffProd_succ 1, ffProd_one, h2, cubic]

/-- **Stage `2` is prime iff `−6 (5 + ω)` is not a cube.** -/
theorem euclid_two_irreducible_iff (hp3 : p % 3 = 1) (d : FFEMData p) :
    ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 ∧ d.ffSeq 2 = X - C ω ∧
      (Irreducible (d.ffProd 2 + 1) ↔ ∀ b : ZMod p, b ^ 3 ≠ -(6 * (5 + ω))) := by
  obtain ⟨ω, hω, h2, hE⟩ := euclid_two hp3 d
  exact ⟨ω, hω, h2, by
    rw [hE]; exact cubic_irreducible_iff (three_ne_zero_of_one_mod_three hp3) hω⟩

/-- **The term at stage `3` has degree `3` or `1`.** For `p ≡ 1 (mod 3)`, every sequence
    either takes the whole cubic at stage `3` or captures a linear polynomial there. -/
theorem ffSeq_three_natDegree (hp3 : p % 3 = 1) (d : FFEMData p) :
    (d.ffSeq 3 = d.ffProd 2 + 1 ∧ (d.ffSeq 3).natDegree = 3) ∨ (d.ffSeq 3).natDegree = 1 := by
  obtain ⟨ω, hω, -, hE⟩ := euclid_two hp3 d
  have h3 := three_ne_zero_of_one_mod_three hp3
  by_cases hcube : ∃ b : ZMod p, b ^ 3 = -(6 * (5 + ω))
  · right
    obtain ⟨b, hb⟩ := hcube
    have hroot := cubic_root h3 hω hb
    have hdvd : X - C ((b - 1 + ω) / 3) ∣ d.ffProd 2 + 1 := by
      rw [hE]; exact dvd_iff_isRoot.mpr hroot
    have hle : (d.ffSeq 3).natDegree ≤ _ := d.ffSeq_minimal 2 _ (monic_X_sub_C _) (irreducible_X_sub_C _) hdvd
    rw [natDegree_X_sub_C] at hle
    have hpos : 0 < (d.ffSeq 3).natDegree :=
      (d.ffSeq_succ 2).2.1.natDegree_pos
    omega
  · left
    have hirr : Irreducible (d.ffProd 2 + 1) := by
      rw [hE]
      exact (cubic_irreducible_iff h3 hω).mpr fun b hb => hcube ⟨b, hb⟩
    have hseq := ffSeq_succ_eq_of_irreducible d 2 hirr
    refine ⟨hseq, ?_⟩
    rw [hseq, hE, cubic]
    compute_degree!

end SecondGeneration

end FunctionFieldAnalog
