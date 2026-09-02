import EM.FunctionField.DegreeTelescope

/-!
# The composite floor is a theorem over `𝔽_2[X]` and over `𝔽_p[X]`, `p ≡ 1 (mod 3)`

Over `ℤ` the composite floor `(C∞)` — infinitely many composite Euclid numbers — is open and
Fermat-shaped (`EM/Population/DefectTelescope.lean`).  Over `𝔽_5[X]` it is *false* for the seed
`X` (`EM/FunctionField/StableTower.lean`).  This file proves it in two families of function
fields, with explicit constants, for **every** `FFEMData p` (the seed is `X`, the choice
function arbitrary):

* **`p ≡ 1 (mod 3)`, constant 1.**  `Φ₃ = y² + y + 1` splits as `(y − ω)(y − ω²)` for a
  primitive cube root of unity `ω ∈ 𝔽_p`.  If `E_n = P_n + 1` is irreducible then the next
  accumulator is `P_n(P_n + 1)` and `E_{n+1} = Φ₃(P_n) = (P_n − ω)(P_n − ω²)` is reducible.
  So no two consecutive Euclid polynomials are irreducible
  (`euclid_succ_reducible_of_one_mod_three`).
* **`p = 2`, constant 3 (sharp).**  The take-all map `P ↦ P(P+1) = P² + P` is additive in
  characteristic 2, so after three autonomous steps `P_{n+3} = P⁸ + P⁴ + P² + P` and

      P⁸ + P⁴ + P² + P + 1 = (P⁴ + P³ + 1)(P⁴ + P³ + P² + P + 1).

  So no four consecutive Euclid polynomials are irreducible
  (`euclid_three_reducible_of_two`, `not_four_consecutive_irreducible`); the seed `X` attains
  three (`X+1`, `X²+X+1`, `X⁴+X+1`), so the constant is sharp.

In both cases `FFInfinitelyManyReducible d` holds and the growth constant vanishes
(`ffGrowthConstant_eq_zero_of_one_mod_three`, `ffGrowthConstant_eq_zero_of_two`), and every
`FFPerpetualIrreducibility d N` is false.

## Conceptual reason (Artin–Schreier for `p = 2`)

The roots of `(F+1)^k P + 1` satisfy `P(β) = y` with `(F+1)^{k+1} y = 0`, so `y ∈ 𝔽_{2^{2^j}}`
for `2^j ≥ k + 1` and `deg β ≤ 2^j deg P`, while an irreducible `E_{n+k}` would need
`deg β = 2^k deg P`.  For `k = 3`: `4 < 8`.  The proof below is the explicit factorisation.

## Landscape

| ring | composite floor |
|---|---|
| `ℤ` | open (Sylvester/Fermat shape) |
| `𝔽_2[X]` | **theorem**, constant 3 |
| `𝔽_p[X]`, `p ≡ 1 (3)` | **theorem**, constant 1 |
| `𝔽_p[X]`, `p ≡ 2 (3)` | decided by the level constants `13, 217, 57073, …` mod `p` |
| `𝔽_5[X]` | **false** for the seed `X` (stable tower) |

See `docs/analysis/logic_routes_2026-09-01.md` §9, §11.
-/

namespace FunctionFieldAnalog

namespace CompositeFloors

open Polynomial FFDegreeTelescope

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## 1. Generalities -/

theorem ffProd_natDegree_pos (d : FFEMData p) (n : ℕ) : 0 < (d.ffProd n).natDegree :=
  ffDeg_pos d n

/-- The Euclid polynomial `P_n + 1` is monic. -/
theorem euclid_monic (d : FFEMData p) (n : ℕ) : (d.ffProd n + 1).Monic := by
  refine (ffProd_monic p d n).add_of_left ?_
  rw [degree_one, degree_eq_natDegree (ffProd_monic p d n).ne_zero]
  exact_mod_cast ffProd_natDegree_pos d n

/-- **The autonomous step.**  If the Euclid polynomial is irreducible, it is the selected factor
(whatever the choice function), so the next accumulator is `P_n (P_n + 1)`. -/
theorem ffSeq_succ_eq_of_irreducible (d : FFEMData p) (n : ℕ) (h : Irreducible (d.ffProd n + 1)) :
    d.ffSeq (n + 1) = d.ffProd n + 1 := by
  obtain ⟨hm, hirr, hdvd⟩ := d.ffSeq_succ n
  exact eq_of_monic_of_associated hm (euclid_monic d n) (hirr.associated_of_dvd h hdvd)

theorem ffProd_succ_of_irreducible (d : FFEMData p) (n : ℕ) (h : Irreducible (d.ffProd n + 1)) :
    d.ffProd (n + 1) = d.ffProd n * (d.ffProd n + 1) := by
  rw [d.ffProd_succ, ffSeq_succ_eq_of_irreducible d n h]

/-- A monic irreducible factor of a monic irreducible polynomial is that polynomial. -/
theorem eq_of_monic_irreducible_dvd {f g : (ZMod p)[X]} (hf : f.Monic) (hfi : Irreducible f)
    (hg : g.Monic) (hgi : Irreducible g) (hdvd : f ∣ g) : f = g :=
  eq_of_monic_of_associated hf hg (hfi.associated_of_dvd hgi hdvd)

/-- A product of two polynomials of positive degree is reducible. -/
theorem not_irreducible_mul_of_natDegree_pos {A B : (ZMod p)[X]} (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree) : ¬ Irreducible (A * B) := fun h =>
  (h.isUnit_or_isUnit rfl).elim
    (not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hA))
    (not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hB))

/-! ## 2. `p ≡ 1 (mod 3)`: constant 1 -/

/-- A primitive cube root of unity exists in `𝔽_p` when `p ≡ 1 (mod 3)`. -/
theorem exists_root_phi3 (hp3 : p % 3 = 1) : ∃ ω : ZMod p, ω ^ 2 + ω + 1 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 := (Fact.out : Nat.Prime p).two_le
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  refine ⟨(x : ZMod p), ?_⟩
  have h3 : (x : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
  have h1 : (x : ZMod p) ≠ 1 := by
    intro h
    rw [Units.val_eq_one.mp h, orderOf_one] at hx
    norm_num at hx
  have hprod : ((x : ZMod p) - 1) * ((x : ZMod p) ^ 2 + x + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact h

/-- **Constant 1.**  For `p ≡ 1 (mod 3)`, an irreducible Euclid polynomial is followed by a
reducible one: `E_{n+1} = Φ₃(P_n) = (P_n − ω)(P_n − ω²)`. -/
theorem euclid_succ_reducible_of_one_mod_three (hp3 : p % 3 = 1) (d : FFEMData p) (n : ℕ)
    (h : Irreducible (d.ffProd n + 1)) : ¬ Irreducible (d.ffProd (n + 1) + 1) := by
  obtain ⟨ω, hω⟩ := exists_root_phi3 hp3
  rw [ffProd_succ_of_irreducible d n h]
  have hC : (C ω) ^ 2 + C ω + 1 = (0 : (ZMod p)[X]) := by
    have := congrArg (C : ZMod p → (ZMod p)[X]) hω
    simpa [map_add, map_pow, map_one] using this
  have hfac : d.ffProd n * (d.ffProd n + 1) + 1 =
      (d.ffProd n - C ω) * (d.ffProd n - C (ω ^ 2)) := by
    rw [C_pow]
    linear_combination (d.ffProd n - (C ω - 1)) * hC
  rw [hfac]
  have hd := ffProd_natDegree_pos d n
  exact not_irreducible_mul_of_natDegree_pos (by rw [natDegree_sub_C]; exact hd)
    (by rw [natDegree_sub_C]; exact hd)

theorem infinitelyManyReducible_of_one_mod_three (hp3 : p % 3 = 1) (d : FFEMData p) :
    FFInfinitelyManyReducible d := by
  intro N
  by_cases h : Irreducible (d.ffProd N + 1)
  · exact ⟨N + 1, by omega, euclid_succ_reducible_of_one_mod_three hp3 d N h⟩
  · exact ⟨N, le_rfl, h⟩

/-- **The composite floor over `𝔽_p[X]`, `p ≡ 1 (mod 3)`: the growth constant vanishes.** -/
theorem ffGrowthConstant_eq_zero_of_one_mod_three (hp3 : p % 3 = 1) (d : FFEMData p) :
    ffGrowthConstant d = 0 :=
  (ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero d).mp
    (infinitelyManyReducible_of_one_mod_three hp3 d)

theorem not_perpetual_of_one_mod_three (hp3 : p % 3 = 1) (d : FFEMData p) (N : ℕ) :
    ¬ FFPerpetualIrreducibility d N :=
  (ffInfinitelyManyReducible_iff d).mp (infinitelyManyReducible_of_one_mod_three hp3 d) N

/-! ## 3. `p = 2`: constant 3 -/

theorem two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  have := CharP.cast_eq_zero (ZMod 2)[X] 2
  exact_mod_cast this

/-- Two autonomous steps over `𝔽_2`: `P ↦ P(P+1) ↦ P⁴ + P` (additivity of `P ↦ P² + P`). -/
theorem ffProd_add_two_of_two_irreducible (d : FFEMData 2) (n : ℕ)
    (h0 : Irreducible (d.ffProd n + 1)) (h1 : Irreducible (d.ffProd (n + 1) + 1)) :
    d.ffProd (n + 2) = d.ffProd n ^ 4 + d.ffProd n := by
  have htwo := two_eq_zero_poly
  rw [ffProd_succ_of_irreducible d (n + 1) h1, ffProd_succ_of_irreducible d n h0]
  linear_combination (d.ffProd n ^ 3 + d.ffProd n ^ 2) * htwo

/-- **Constant 3.**  Over `𝔽_2`, three consecutive irreducible Euclid polynomials force the
fourth to factor: `P⁸ + P⁴ + P² + P + 1 = (P⁴ + P³ + 1)(P⁴ + P³ + P² + P + 1)`. -/
theorem euclid_three_reducible_of_two (d : FFEMData 2) (n : ℕ)
    (h0 : Irreducible (d.ffProd n + 1)) (h1 : Irreducible (d.ffProd (n + 1) + 1))
    (h2 : Irreducible (d.ffProd (n + 2) + 1)) : ¬ Irreducible (d.ffProd (n + 3) + 1) := by
  have htwo := two_eq_zero_poly
  set P := d.ffProd n with hP
  have e1 : d.ffProd (n + 1) = P * (P + 1) := ffProd_succ_of_irreducible d n h0
  have e2 : d.ffProd (n + 2) = P ^ 4 + P := ffProd_add_two_of_two_irreducible d n h0 h1
  have e3 : d.ffProd (n + 3) + 1 = (P ^ 4 + P ^ 3 + 1) * (P ^ 4 + P ^ 3 + P ^ 2 + P + 1) := by
    rw [ffProd_succ_of_irreducible d (n + 2) h2, e2]
    linear_combination (-(P ^ 7 + P ^ 6 + P ^ 4 + P ^ 3)) * htwo
  rw [e3]
  have hd : 0 < P.natDegree := ffProd_natDegree_pos d n
  have hm : P.Monic := ffProd_monic 2 d n
  have h4 : (P ^ 4).natDegree = 4 * P.natDegree := hm.natDegree_pow 4
  have h3 : (P ^ 3).natDegree = 3 * P.natDegree := hm.natDegree_pow 3
  have h2' : (P ^ 2).natDegree = 2 * P.natDegree := hm.natDegree_pow 2
  have h43 : (P ^ 4 + P ^ 3).natDegree = 4 * P.natDegree := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [h3, h4]; omega), h4]
  have hA : 0 < (P ^ 4 + P ^ 3 + 1).natDegree := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_one, h43]; omega), h43]; omega
  have hB : 0 < (P ^ 4 + P ^ 3 + P ^ 2 + P + 1).natDegree := by
    have h432 : (P ^ 4 + P ^ 3 + P ^ 2).natDegree = 4 * P.natDegree := by
      rw [natDegree_add_eq_left_of_natDegree_lt (by rw [h2', h43]; omega), h43]
    have h4321 : (P ^ 4 + P ^ 3 + P ^ 2 + P).natDegree = 4 * P.natDegree := by
      rw [natDegree_add_eq_left_of_natDegree_lt (by rw [h432]; omega), h432]
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_one, h4321]; omega), h4321]
    omega
  exact not_irreducible_mul_of_natDegree_pos hA hB

/-- No four consecutive Euclid polynomials over `𝔽_2` are irreducible. -/
theorem not_four_consecutive_irreducible (d : FFEMData 2) (n : ℕ) :
    ¬ ∀ k < 4, Irreducible (d.ffProd (n + k) + 1) := fun h =>
  euclid_three_reducible_of_two d n (h 0 (by norm_num)) (h 1 (by norm_num)) (h 2 (by norm_num))
    (h 3 (by norm_num))

theorem infinitelyManyReducible_of_two (d : FFEMData 2) : FFInfinitelyManyReducible d := by
  intro N
  by_cases h0 : Irreducible (d.ffProd N + 1)
  swap; · exact ⟨N, le_rfl, h0⟩
  by_cases h1 : Irreducible (d.ffProd (N + 1) + 1)
  swap; · exact ⟨N + 1, by omega, h1⟩
  by_cases h2 : Irreducible (d.ffProd (N + 2) + 1)
  swap; · exact ⟨N + 2, by omega, h2⟩
  exact ⟨N + 3, by omega, euclid_three_reducible_of_two d N h0 h1 h2⟩

/-- **The composite floor over `𝔽_2[X]`: the growth constant vanishes for every sequence.** -/
theorem ffGrowthConstant_eq_zero_of_two (d : FFEMData 2) : ffGrowthConstant d = 0 :=
  (ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero d).mp (infinitelyManyReducible_of_two d)

theorem not_perpetual_of_two (d : FFEMData 2) (N : ℕ) : ¬ FFPerpetualIrreducibility d N :=
  (ffInfinitelyManyReducible_iff d).mp (infinitelyManyReducible_of_two d) N

end CompositeFloors

end FunctionFieldAnalog
