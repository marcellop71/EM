import EM.MullinGroupCore
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Quadratic Reciprocity and SubgroupEscape

Uses quadratic reciprocity to analyze SE for the QR (index-2) subgroup:
* Legendre symbol conditions for each EM multiplier prime {3,5,7,13,43,53}
* `se_qr_obstruction`: constrains "bad" primes to ≤1.6% density
* `se_of_prime_index_escape`: multi-witness SE (different mults escape different subgroups)
* Concrete SE at q = 131 (multi-witness)
-/

namespace MullinGroup

open Mullin Euclid Classical

/-! ## Quadratic Reciprocity and SubgroupEscape

We use quadratic reciprocity to show that specific EM multiplier primes
are quadratic non-residues modulo q, for explicit congruence classes of q.
This gives concrete instances of SubgroupEscape for the index-2 (QR) subgroup.

For each multiplier prime p ∈ {3, 5, 7, 13, 43, 53}:
- (p/q) = 1 iff p is a quadratic residue mod q
- By QR, (p/q) depends on q modulo a small modulus
- The "bad" primes (all 6 are QRs) lie in thin residue classes mod M

This section formalizes the individual QR conditions. -/

-- Fact instances for multiplier primes
instance fact_prime_3 : Fact (Nat.Prime 3) := ⟨by decide⟩
instance fact_prime_5 : Fact (Nat.Prime 5) := ⟨by decide⟩
instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by decide⟩
instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by decide⟩
instance fact_prime_43 : Fact (Nat.Prime 43) := ⟨by decide⟩
instance fact_prime_53 : Fact (Nat.Prime 53) := ⟨by decide⟩

/-! ### Helper lemmas for quadratic reciprocity -/

/-- When q ≡ 1 mod 4, (-1)^(q/2) = 1. -/
theorem neg_one_pow_half_eq_one {q : ℕ} (hq : q % 4 = 1) :
    (-1 : ℤ) ^ (q / 2) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
  have : (4 * k + 1) / 2 = 2 * k := by omega
  rw [this, pow_mul]; norm_num

/-- When q ≡ 3 mod 4, (-1)^(q/2) = -1. -/
theorem neg_one_pow_half_eq_neg_one' {q : ℕ} (hq : q % 4 = 3) :
    (-1 : ℤ) ^ (q / 2) = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
  have : (4 * k + 3) / 2 = 2 * k + 1 := by omega
  rw [this, pow_add, pow_mul, pow_one]; norm_num

/-- For odd multiplier m, (-1)^(m*n) = (-1)^n. -/
theorem neg_one_pow_odd_mul {m n : ℕ} (hm : m % 2 = 1) :
    (-1 : ℤ) ^ (m * n) = (-1 : ℤ) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  rw [show (2 * k + 1) * n = 2 * (k * n) + n from by ring]
  rw [pow_add, pow_mul]; norm_num

/-- Reduce legendreSym p (↑q) to legendreSym p r when q ≡ r mod p. -/
theorem legendreSym_nat_eq_mod (p : ℕ) [Fact (Nat.Prime p)] (q : ℕ) (r : ℤ)
    (h : (q : ℤ) % (p : ℤ) = r) :
    legendreSym p (q : ℤ) = legendreSym p r := by
  rw [legendreSym.mod p (q : ℤ), h]

/-! ### QR condition for p = 3

3 ≡ 3 mod 4, so by QR: (3/q) = (-1)^(q/2) · (q/3).
QRs mod 3: {1}. NQRs mod 3: {2}.
(3/q) = -1 iff q ≡ 5 or 7 mod 12.
(3/q) = 1 iff q ≡ ±1 mod 12. -/

/-- (3/q) = -1 when q ≡ 5 mod 12. -/
theorem legendreSym_three_eq_neg_one_of_five {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 12 = 5) : legendreSym q 3 = -1 := by
  have hqr := @legendreSym.quadratic_reciprocity' 3 q _ _
    (by decide) (by intro h; subst h; omega)
  simp only [show (3 : ℕ) / 2 = 1 from by decide, one_mul] at hqr
  show legendreSym q (↑(3 : ℕ)) = -1; rw [hqr]
  rw [neg_one_pow_half_eq_one (by omega), one_mul]
  rw [legendreSym_nat_eq_mod 3 q 2 (by omega)]; native_decide

/-- (3/q) = -1 when q ≡ 7 mod 12. -/
theorem legendreSym_three_eq_neg_one_of_seven {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 12 = 7) : legendreSym q 3 = -1 := by
  have hqr := @legendreSym.quadratic_reciprocity' 3 q _ _
    (by decide) (by intro h; subst h; omega)
  simp only [show (3 : ℕ) / 2 = 1 from by decide, one_mul] at hqr
  show legendreSym q (↑(3 : ℕ)) = -1; rw [hqr]
  rw [neg_one_pow_half_eq_neg_one' (by omega)]
  rw [legendreSym_nat_eq_mod 3 q 1 (by omega)]; native_decide

/-- 3 is a QNR mod q for primes q > 3 with q ≢ ±1 mod 12. -/
theorem legendreSym_three_eq_neg_one {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 3) (hmod1 : q % 12 ≠ 1) (hmod11 : q % 12 ≠ 11) :
    legendreSym q 3 = -1 := by
  have hq_prime := (Fact.out : Nat.Prime q)
  have hq_mod2 : q % 2 = 1 := Nat.odd_iff.mp (hq_prime.odd_of_ne_two (by omega))
  have hq_not3 : q % 3 ≠ 0 := by
    intro h; have := hq_prime.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h); omega
  have : q % 12 = 5 ∨ q % 12 = 7 := by omega
  rcases this with h | h
  · exact legendreSym_three_eq_neg_one_of_five h
  · exact legendreSym_three_eq_neg_one_of_seven h

/-! ### QR condition for p = 5

5 ≡ 1 mod 4, so by QR: (5/q) = (q/5).
QRs mod 5: {1, 4}. NQRs mod 5: {2, 3}.
(5/q) = -1 iff q ≡ 2 or 3 mod 5 (i.e., q ≢ ±1 mod 5). -/

/-- (5/q) = -1 when q ≡ 2 mod 5. -/
theorem legendreSym_five_eq_neg_one_of_two {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 2) (hmod : q % 5 = 2) : legendreSym q 5 = -1 := by
  have hqr := @legendreSym.quadratic_reciprocity_one_mod_four 5 q _ _
    (by decide) (by omega)
  show legendreSym q (↑(5 : ℕ)) = -1; rw [hqr]
  rw [legendreSym_nat_eq_mod 5 q 2 (by omega)]; native_decide

/-- (5/q) = -1 when q ≡ 3 mod 5. -/
theorem legendreSym_five_eq_neg_one_of_three {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 5 = 3) : legendreSym q 5 = -1 := by
  have hqr := @legendreSym.quadratic_reciprocity_one_mod_four 5 q _ _
    (by decide) (by intro h; subst h; omega)
  show legendreSym q (↑(5 : ℕ)) = -1; rw [hqr]
  rw [legendreSym_nat_eq_mod 5 q 3 (by omega)]; native_decide

/-- 5 is a QNR mod q for primes q > 5 with q ≢ ±1 mod 5. -/
theorem legendreSym_five_eq_neg_one {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 5) (hmod1 : q % 5 ≠ 1) (hmod4 : q % 5 ≠ 4) :
    legendreSym q 5 = -1 := by
  have hq_prime := (Fact.out : Nat.Prime q)
  have hq_not5 : q % 5 ≠ 0 := by
    intro h; have := hq_prime.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h); omega
  have : q % 5 = 2 ∨ q % 5 = 3 := by omega
  rcases this with h | h
  · exact legendreSym_five_eq_neg_one_of_two (by omega) h
  · exact legendreSym_five_eq_neg_one_of_three h

/-! ### QR condition for p = 7

7 ≡ 3 mod 4, 7/2 = 3 (odd), so (7/q) = (-1)^(q/2) · (q/7).
QRs mod 7: {1, 2, 4}. NQRs mod 7: {3, 5, 6}.
(7/q) = -1 iff q % 28 ∈ {5, 11, 13, 15, 17, 23}. -/

/-- Helper: reduce (7/q) via QR to (-1)^(q/2) * (q mod 7 / 7).
    Steps 1-4 of the common pattern for all six residue classes mod 28. -/
private theorem legendreSym_seven_reduce {q : ℕ} [Fact (Nat.Prime q)]
    (hq2 : q ≠ 2) : legendreSym q 7 = (-1) ^ (q / 2) * legendreSym 7 (q : ℤ) := by
  have hqr := @legendreSym.quadratic_reciprocity' 7 q _ _
    (by decide) hq2
  simp only [show (7 : ℕ) / 2 = 3 from by decide] at hqr
  show legendreSym q (↑(7 : ℕ)) = _; rw [hqr]
  rw [neg_one_pow_odd_mul (by decide : (3 : ℕ) % 2 = 1)]

/-- Helper: (7/q) = -1 when q % 4 = 1 and q mod 7 is a quadratic non-residue mod 7. -/
private theorem legendreSym_seven_neg_one_mod4_1 {q : ℕ} [Fact (Nat.Prime q)]
    (hq2 : q ≠ 2) (hmod4 : q % 4 = 1) (r : ℤ) (hr : (q : ℤ) % ↑(7 : ℕ) = r)
    (hnqr : legendreSym 7 r = -1) : legendreSym q 7 = -1 := by
  rw [legendreSym_seven_reduce hq2, neg_one_pow_half_eq_one hmod4, one_mul,
    legendreSym.mod 7 (q : ℤ), hr, hnqr]

/-- Helper: (7/q) = -1 when q % 4 = 3 and q mod 7 is a quadratic residue mod 7. -/
private theorem legendreSym_seven_neg_one_mod4_3 {q : ℕ} [Fact (Nat.Prime q)]
    (hq2 : q ≠ 2) (hmod4 : q % 4 = 3) (r : ℤ) (hr : (q : ℤ) % ↑(7 : ℕ) = r)
    (hqr : legendreSym 7 r = 1) : legendreSym q 7 = -1 := by
  rw [legendreSym_seven_reduce hq2, neg_one_pow_half_eq_neg_one' hmod4,
    legendreSym.mod 7 (q : ℤ), hr, hqr, mul_one]

theorem legendreSym_seven_eq_neg_one_5 {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 28 = 5) : legendreSym q 7 = -1 :=
  legendreSym_seven_neg_one_mod4_1 (by omega) (by omega) 5 (by omega) (by native_decide)

theorem legendreSym_seven_eq_neg_one_11 {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 28 = 11) : legendreSym q 7 = -1 :=
  legendreSym_seven_neg_one_mod4_3 (by omega) (by omega) 4 (by omega) (by native_decide)

theorem legendreSym_seven_eq_neg_one_13 {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 28 = 13) : legendreSym q 7 = -1 :=
  legendreSym_seven_neg_one_mod4_1 (by omega) (by omega) 6 (by omega) (by native_decide)

theorem legendreSym_seven_eq_neg_one_15 {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 28 = 15) : legendreSym q 7 = -1 :=
  legendreSym_seven_neg_one_mod4_3 (by omega) (by omega) 1 (by omega) (by native_decide)

theorem legendreSym_seven_eq_neg_one_17 {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 28 = 17) : legendreSym q 7 = -1 :=
  legendreSym_seven_neg_one_mod4_1 (by omega) (by omega) 3 (by omega) (by native_decide)

theorem legendreSym_seven_eq_neg_one_23 {q : ℕ} [Fact (Nat.Prime q)]
    (hmod : q % 28 = 23) : legendreSym q 7 = -1 :=
  legendreSym_seven_neg_one_mod4_3 (by omega) (by omega) 2 (by omega) (by native_decide)

/-- 7 is a QNR mod q for primes q > 7 outside the 6 QR classes mod 28. -/
theorem legendreSym_seven_eq_neg_one {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 7)
    (h1 : q % 28 ≠ 1) (h3 : q % 28 ≠ 3) (h9 : q % 28 ≠ 9)
    (h19 : q % 28 ≠ 19) (h25 : q % 28 ≠ 25) (h27 : q % 28 ≠ 27) :
    legendreSym q 7 = -1 := by
  have hq_prime := (Fact.out : Nat.Prime q)
  have hq_mod2 : q % 2 = 1 := Nat.odd_iff.mp (hq_prime.odd_of_ne_two (by omega))
  have hq_mod7 : q % 7 ≠ 0 := by
    intro h; have := hq_prime.eq_one_or_self_of_dvd 7 (Nat.dvd_of_mod_eq_zero h); omega
  have : q % 28 = 5 ∨ q % 28 = 11 ∨ q % 28 = 13 ∨
         q % 28 = 15 ∨ q % 28 = 17 ∨ q % 28 = 23 := by omega
  rcases this with h | h | h | h | h | h
  · exact legendreSym_seven_eq_neg_one_5 h
  · exact legendreSym_seven_eq_neg_one_11 h
  · exact legendreSym_seven_eq_neg_one_13 h
  · exact legendreSym_seven_eq_neg_one_15 h
  · exact legendreSym_seven_eq_neg_one_17 h
  · exact legendreSym_seven_eq_neg_one_23 h

/-! ### QR condition for p = 13

13 ≡ 1 mod 4, so (13/q) = (q/13).
QRs mod 13: {1, 3, 4, 9, 10, 12}. NQRs: {2, 5, 6, 7, 8, 11}.
(13/q) = -1 iff q % 13 ∈ {2, 5, 6, 7, 8, 11}. -/

/-- 13 is a QNR mod q for primes q > 13 outside the 6 QR classes mod 13. -/
theorem legendreSym_thirteen_eq_neg_one {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 13)
    (h1 : q % 13 ≠ 1) (h3 : q % 13 ≠ 3) (h4 : q % 13 ≠ 4)
    (h9 : q % 13 ≠ 9) (h10 : q % 13 ≠ 10) (h12 : q % 13 ≠ 12) :
    legendreSym q 13 = -1 := by
  have hq_prime := (Fact.out : Nat.Prime q)
  have hq_not13 : q % 13 ≠ 0 := by
    intro h; have := hq_prime.eq_one_or_self_of_dvd 13 (Nat.dvd_of_mod_eq_zero h); omega
  have hqr := @legendreSym.quadratic_reciprocity_one_mod_four 13 q _ _
    (by decide) (by omega : q ≠ 2)
  show legendreSym q (↑(13 : ℕ)) = -1; rw [hqr]
  have : q % 13 = 2 ∨ q % 13 = 5 ∨ q % 13 = 6 ∨
         q % 13 = 7 ∨ q % 13 = 8 ∨ q % 13 = 11 := by omega
  rcases this with h | h | h | h | h | h
  · rw [legendreSym_nat_eq_mod 13 q 2 (by omega)]; native_decide
  · rw [legendreSym_nat_eq_mod 13 q 5 (by omega)]; native_decide
  · rw [legendreSym_nat_eq_mod 13 q 6 (by omega)]; native_decide
  · rw [legendreSym_nat_eq_mod 13 q 7 (by omega)]; native_decide
  · rw [legendreSym_nat_eq_mod 13 q 8 (by omega)]; native_decide
  · rw [legendreSym_nat_eq_mod 13 q 11 (by omega)]; native_decide

/-! ### QR condition for p = 53

53 ≡ 1 mod 4, so (53/q) = (q/53).
QRs mod 53: {1,4,6,7,9,10,11,13,15,16,17,24,25,28,29,36,37,38,40,42,43,44,46,47,49,52}.
NQRs mod 53: {2,3,5,8,12,14,18,19,20,21,22,23,26,27,30,31,32,33,34,35,39,41,45,48,50,51}.
(53/q) = -1 iff q % 53 is a NQR. -/

/-- 53 is a QNR mod q for primes q > 53 outside the 26 QR classes mod 53. -/
theorem legendreSym_fiftythree_eq_neg_one {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 53)
    (h1 : q % 53 ≠ 1) (h4 : q % 53 ≠ 4) (h6 : q % 53 ≠ 6) (h7 : q % 53 ≠ 7)
    (h9 : q % 53 ≠ 9) (h10 : q % 53 ≠ 10) (h11 : q % 53 ≠ 11) (h13 : q % 53 ≠ 13)
    (h15 : q % 53 ≠ 15) (h16 : q % 53 ≠ 16) (h17 : q % 53 ≠ 17) (h24 : q % 53 ≠ 24)
    (h25 : q % 53 ≠ 25) (h28 : q % 53 ≠ 28) (h29 : q % 53 ≠ 29) (h36 : q % 53 ≠ 36)
    (h37 : q % 53 ≠ 37) (h38 : q % 53 ≠ 38) (h40 : q % 53 ≠ 40) (h42 : q % 53 ≠ 42)
    (h43 : q % 53 ≠ 43) (h44 : q % 53 ≠ 44) (h46 : q % 53 ≠ 46) (h47 : q % 53 ≠ 47)
    (h49 : q % 53 ≠ 49) (h52 : q % 53 ≠ 52) :
    legendreSym q 53 = -1 := by
  have hq_prime := (Fact.out : Nat.Prime q)
  have hq_not53 : q % 53 ≠ 0 := by
    intro h; have := hq_prime.eq_one_or_self_of_dvd 53 (Nat.dvd_of_mod_eq_zero h); omega
  have hqr := @legendreSym.quadratic_reciprocity_one_mod_four 53 q _ _
    (by decide) (by omega : q ≠ 2)
  show legendreSym q (↑(53 : ℕ)) = -1; rw [hqr]
  rw [legendreSym.mod 53 (↑q : ℤ)]
  -- q%53 is an NQR: {2,3,5,8,12,14,18,19,20,21,22,23,26,27,30,31,32,33,34,35,39,41,45,48,50,51}
  have hcase : q % 53 = 2 ∨ q % 53 = 3 ∨ q % 53 = 5 ∨ q % 53 = 8 ∨
         q % 53 = 12 ∨ q % 53 = 14 ∨ q % 53 = 18 ∨ q % 53 = 19 ∨
         q % 53 = 20 ∨ q % 53 = 21 ∨ q % 53 = 22 ∨ q % 53 = 23 ∨
         q % 53 = 26 ∨ q % 53 = 27 ∨ q % 53 = 30 ∨ q % 53 = 31 ∨
         q % 53 = 32 ∨ q % 53 = 33 ∨ q % 53 = 34 ∨ q % 53 = 35 ∨
         q % 53 = 39 ∨ q % 53 = 41 ∨ q % 53 = 45 ∨ q % 53 = 48 ∨
         q % 53 = 50 ∨ q % 53 = 51 := by omega
  rcases hcase with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> {
    have : (↑q : ℤ) % (↑(53 : ℕ) : ℤ) = ↑(q % 53 : ℕ) := by omega
    rw [this, h]; native_decide }

/-! ### QR condition for p = 43

43 ≡ 3 mod 4, 43/2 = 21 (odd), so (43/q) = (-1)^(q/2) · (q/43).
QRs mod 43: {1,4,6,9,10,11,13,14,15,16,17,21,23,24,25,31,35,36,38,40,41}.
NQRs mod 43: {2,3,5,7,8,12,18,19,20,22,26,27,28,29,30,32,33,34,37,39,42}.
When q ≡ 1 mod 4: (43/q) = (q/43), so (43/q) = -1 iff q%43 ∈ NQR set.
When q ≡ 3 mod 4: (43/q) = -(q/43), so (43/q) = -1 iff q%43 ∈ QR set. -/

set_option maxHeartbeats 800000 in
/-- (43/q) = -1 when q ≡ 1 mod 4 and q%43 is not a QR mod 43. -/
theorem legendreSym_fortythree_eq_neg_one_mod4_1 {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 43) (hmod4 : q % 4 = 1)
    (h1 : q % 43 ≠ 1) (h4 : q % 43 ≠ 4) (h6 : q % 43 ≠ 6) (h9 : q % 43 ≠ 9)
    (h10 : q % 43 ≠ 10) (h11 : q % 43 ≠ 11) (h13 : q % 43 ≠ 13) (h14 : q % 43 ≠ 14)
    (h15 : q % 43 ≠ 15) (h16 : q % 43 ≠ 16) (h17 : q % 43 ≠ 17) (h21 : q % 43 ≠ 21)
    (h23 : q % 43 ≠ 23) (h24 : q % 43 ≠ 24) (h25 : q % 43 ≠ 25) (h31 : q % 43 ≠ 31)
    (h35 : q % 43 ≠ 35) (h36 : q % 43 ≠ 36) (h38 : q % 43 ≠ 38) (h40 : q % 43 ≠ 40)
    (h41 : q % 43 ≠ 41) :
    legendreSym q 43 = -1 := by
  have hq_prime := (Fact.out : Nat.Prime q)
  have hq_not43 : q % 43 ≠ 0 := by
    intro h; have := hq_prime.eq_one_or_self_of_dvd 43 (Nat.dvd_of_mod_eq_zero h); omega
  have hqr := @legendreSym.quadratic_reciprocity' 43 q _ _
    (by decide) (by intro h; subst h; omega)
  simp only [show (43 : ℕ) / 2 = 21 from by decide] at hqr
  show legendreSym q (↑(43 : ℕ)) = -1; rw [hqr]
  rw [neg_one_pow_odd_mul (by decide : (21 : ℕ) % 2 = 1)]
  rw [neg_one_pow_half_eq_one hmod4, one_mul]
  rw [legendreSym.mod 43 (↑q : ℤ)]
  have hcase : q % 43 = 2 ∨ q % 43 = 3 ∨ q % 43 = 5 ∨ q % 43 = 7 ∨
    q % 43 = 8 ∨ q % 43 = 12 ∨ q % 43 = 18 ∨ q % 43 = 19 ∨
    q % 43 = 20 ∨ q % 43 = 22 ∨ q % 43 = 26 ∨ q % 43 = 27 ∨
    q % 43 = 28 ∨ q % 43 = 29 ∨ q % 43 = 30 ∨ q % 43 = 32 ∨
    q % 43 = 33 ∨ q % 43 = 34 ∨ q % 43 = 37 ∨ q % 43 = 39 ∨
    q % 43 = 42 := by omega
  rcases hcase with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> {
    have : (↑q : ℤ) % (↑(43 : ℕ) : ℤ) = ↑(q % 43 : ℕ) := by omega
    rw [this, h]; native_decide }

set_option maxHeartbeats 800000 in
/-- (43/q) = -1 when q ≡ 3 mod 4 and q%43 is not an NQR mod 43. -/
theorem legendreSym_fortythree_eq_neg_one_mod4_3 {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 43) (hmod4 : q % 4 = 3)
    (h2 : q % 43 ≠ 2) (h3 : q % 43 ≠ 3) (h5 : q % 43 ≠ 5) (h7 : q % 43 ≠ 7)
    (h8 : q % 43 ≠ 8) (h12 : q % 43 ≠ 12) (h18 : q % 43 ≠ 18) (h19 : q % 43 ≠ 19)
    (h20 : q % 43 ≠ 20) (h22 : q % 43 ≠ 22) (h26 : q % 43 ≠ 26) (h27 : q % 43 ≠ 27)
    (h28 : q % 43 ≠ 28) (h29 : q % 43 ≠ 29) (h30 : q % 43 ≠ 30) (h32 : q % 43 ≠ 32)
    (h33 : q % 43 ≠ 33) (h34 : q % 43 ≠ 34) (h37 : q % 43 ≠ 37) (h39 : q % 43 ≠ 39)
    (h42 : q % 43 ≠ 42) :
    legendreSym q 43 = -1 := by
  have hq_prime := (Fact.out : Nat.Prime q)
  have hq_not43 : q % 43 ≠ 0 := by
    intro h; have := hq_prime.eq_one_or_self_of_dvd 43 (Nat.dvd_of_mod_eq_zero h); omega
  have hqr := @legendreSym.quadratic_reciprocity' 43 q _ _
    (by decide) (by intro h; subst h; omega)
  simp only [show (43 : ℕ) / 2 = 21 from by decide] at hqr
  show legendreSym q (↑(43 : ℕ)) = -1; rw [hqr]
  rw [neg_one_pow_odd_mul (by decide : (21 : ℕ) % 2 = 1)]
  rw [neg_one_pow_half_eq_neg_one' hmod4]
  rw [legendreSym.mod 43 (↑q : ℤ)]
  -- Goal: -1 * legendreSym 43 ((↑q : ℤ) % ↑43) = -1
  -- q%43 must be in QR set, so legendreSym 43 r = 1, giving -1 * 1 = -1
  have hcase : q % 43 = 1 ∨ q % 43 = 4 ∨ q % 43 = 6 ∨ q % 43 = 9 ∨
    q % 43 = 10 ∨ q % 43 = 11 ∨ q % 43 = 13 ∨ q % 43 = 14 ∨
    q % 43 = 15 ∨ q % 43 = 16 ∨ q % 43 = 17 ∨ q % 43 = 21 ∨
    q % 43 = 23 ∨ q % 43 = 24 ∨ q % 43 = 25 ∨ q % 43 = 31 ∨
    q % 43 = 35 ∨ q % 43 = 36 ∨ q % 43 = 38 ∨ q % 43 = 40 ∨
    q % 43 = 41 := by omega
  rcases hcase with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> {
    have : (↑q : ℤ) % (↑(43 : ℕ) : ℤ) = ↑(q % 43 : ℕ) := by omega
    rw [this, h]; native_decide }

/-! ### Bridge: Legendre symbol to IsSquare (SubgroupEscape connection)

The Legendre symbol (p/q) = -1 means p is NOT a quadratic residue mod q,
i.e., the multiplier (p : ZMod q) is not in the QR subgroup. This gives
concrete SubgroupEscape instances for the index-2 subgroup. -/

/-- 3 is not a square mod q when q ≢ ±1 mod 12. -/
theorem mult_three_escapes_qr {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 3) (h1 : q % 12 ≠ 1) (h11 : q % 12 ≠ 11) :
    ¬ IsSquare ((3 : ℤ) : ZMod q) := by
  rw [← legendreSym.eq_neg_one_iff]
  exact legendreSym_three_eq_neg_one hq h1 h11

/-- 5 is not a square mod q when q ≢ ±1 mod 5. -/
theorem mult_five_escapes_qr {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 5) (h1 : q % 5 ≠ 1) (h4 : q % 5 ≠ 4) :
    ¬ IsSquare ((5 : ℤ) : ZMod q) := by
  rw [← legendreSym.eq_neg_one_iff]
  exact legendreSym_five_eq_neg_one hq h1 h4

/-- 7 is not a square mod q when q is outside the 6 QR classes mod 28. -/
theorem mult_seven_escapes_qr {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 7)
    (h1 : q % 28 ≠ 1) (h3 : q % 28 ≠ 3) (h9 : q % 28 ≠ 9)
    (h19 : q % 28 ≠ 19) (h25 : q % 28 ≠ 25) (h27 : q % 28 ≠ 27) :
    ¬ IsSquare ((7 : ℤ) : ZMod q) := by
  rw [← legendreSym.eq_neg_one_iff]
  exact legendreSym_seven_eq_neg_one hq h1 h3 h9 h19 h25 h27

/-- 13 is not a square mod q when q is outside the 6 QR classes mod 13. -/
theorem mult_thirteen_escapes_qr {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 13)
    (h1 : q % 13 ≠ 1) (h3 : q % 13 ≠ 3) (h4 : q % 13 ≠ 4)
    (h9 : q % 13 ≠ 9) (h10 : q % 13 ≠ 10) (h12 : q % 13 ≠ 12) :
    ¬ IsSquare ((13 : ℤ) : ZMod q) := by
  rw [← legendreSym.eq_neg_one_iff]
  exact legendreSym_thirteen_eq_neg_one hq h1 h3 h4 h9 h10 h12

/-- 43 is not a square mod q when q ≡ 1 mod 4 and q%43 is outside the QR set. -/
theorem mult_fortythree_escapes_qr_case1 {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 43) (hmod4 : q % 4 = 1)
    (h1 : q % 43 ≠ 1) (h4 : q % 43 ≠ 4) (h6 : q % 43 ≠ 6) (h9 : q % 43 ≠ 9)
    (h10 : q % 43 ≠ 10) (h11 : q % 43 ≠ 11) (h13 : q % 43 ≠ 13) (h14 : q % 43 ≠ 14)
    (h15 : q % 43 ≠ 15) (h16 : q % 43 ≠ 16) (h17 : q % 43 ≠ 17) (h21 : q % 43 ≠ 21)
    (h23 : q % 43 ≠ 23) (h24 : q % 43 ≠ 24) (h25 : q % 43 ≠ 25) (h31 : q % 43 ≠ 31)
    (h35 : q % 43 ≠ 35) (h36 : q % 43 ≠ 36) (h38 : q % 43 ≠ 38) (h40 : q % 43 ≠ 40)
    (h41 : q % 43 ≠ 41) :
    ¬ IsSquare ((43 : ℤ) : ZMod q) := by
  rw [← legendreSym.eq_neg_one_iff]
  exact legendreSym_fortythree_eq_neg_one_mod4_1 hq hmod4
    h1 h4 h6 h9 h10 h11 h13 h14 h15 h16 h17 h21 h23 h24 h25 h31 h35 h36 h38 h40 h41

/-- 43 is not a square mod q when q ≡ 3 mod 4 and q%43 is outside the NQR set. -/
theorem mult_fortythree_escapes_qr_case3 {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 43) (hmod4 : q % 4 = 3)
    (h2 : q % 43 ≠ 2) (h3 : q % 43 ≠ 3) (h5 : q % 43 ≠ 5) (h7 : q % 43 ≠ 7)
    (h8 : q % 43 ≠ 8) (h12 : q % 43 ≠ 12) (h18 : q % 43 ≠ 18) (h19 : q % 43 ≠ 19)
    (h20 : q % 43 ≠ 20) (h22 : q % 43 ≠ 22) (h26 : q % 43 ≠ 26) (h27 : q % 43 ≠ 27)
    (h28 : q % 43 ≠ 28) (h29 : q % 43 ≠ 29) (h30 : q % 43 ≠ 30) (h32 : q % 43 ≠ 32)
    (h33 : q % 43 ≠ 33) (h34 : q % 43 ≠ 34) (h37 : q % 43 ≠ 37) (h39 : q % 43 ≠ 39)
    (h42 : q % 43 ≠ 42) :
    ¬ IsSquare ((43 : ℤ) : ZMod q) := by
  rw [← legendreSym.eq_neg_one_iff]
  exact legendreSym_fortythree_eq_neg_one_mod4_3 hq hmod4
    h2 h3 h5 h7 h8 h12 h18 h19 h20 h22 h26 h27 h28 h29 h30 h32 h33 h34 h37 h39 h42

/-- 53 is not a square mod q when q is outside the 26 QR classes mod 53. -/
theorem mult_fiftythree_escapes_qr {q : ℕ} [Fact (Nat.Prime q)]
    (hq : q > 53)
    (h1 : q % 53 ≠ 1) (h4 : q % 53 ≠ 4) (h6 : q % 53 ≠ 6) (h7 : q % 53 ≠ 7)
    (h9 : q % 53 ≠ 9) (h10 : q % 53 ≠ 10) (h11 : q % 53 ≠ 11) (h13 : q % 53 ≠ 13)
    (h15 : q % 53 ≠ 15) (h16 : q % 53 ≠ 16) (h17 : q % 53 ≠ 17) (h24 : q % 53 ≠ 24)
    (h25 : q % 53 ≠ 25) (h28 : q % 53 ≠ 28) (h29 : q % 53 ≠ 29) (h36 : q % 53 ≠ 36)
    (h37 : q % 53 ≠ 37) (h38 : q % 53 ≠ 38) (h40 : q % 53 ≠ 40) (h42 : q % 53 ≠ 42)
    (h43 : q % 53 ≠ 43) (h44 : q % 53 ≠ 44) (h46 : q % 53 ≠ 46) (h47 : q % 53 ≠ 47)
    (h49 : q % 53 ≠ 49) (h52 : q % 53 ≠ 52) :
    ¬ IsSquare ((53 : ℤ) : ZMod q) := by
  rw [← legendreSym.eq_neg_one_iff]
  exact legendreSym_fiftythree_eq_neg_one hq h1 h4 h6 h7 h9 h10 h11 h13 h15 h16 h17 h24
    h25 h28 h29 h36 h37 h38 h40 h42 h43 h44 h46 h47 h49 h52

/-- **QR Obstruction Theorem (Extended)**: if 3, 5, 7, 13, 43, and 53 are all
    quadratic residues mod a prime q > 53, then q is confined to specific
    residue classes modulo 12, 5, 28, 13, 43, and 53 simultaneously.
    By CRT on lcm(12,5,28,13,43,53) = 12443340, at most 39312 of the
    φ(12443340) = 2515968 coprime residue classes survive (density ≤ 1.6%).
    For all other primes, at least one of {3,5,7,13,43,53} escapes the QR
    subgroup, giving SubgroupEscape for the index-2 subgroup. -/
theorem se_qr_obstruction {q : ℕ} [Fact (Nat.Prime q)] (hq : q > 53)
    (h3 : IsSquare ((3 : ℤ) : ZMod q))
    (h5 : IsSquare ((5 : ℤ) : ZMod q))
    (h7 : IsSquare ((7 : ℤ) : ZMod q))
    (h13 : IsSquare ((13 : ℤ) : ZMod q))
    (h43 : IsSquare ((43 : ℤ) : ZMod q))
    (h53 : IsSquare ((53 : ℤ) : ZMod q)) :
    (q % 12 = 1 ∨ q % 12 = 11) ∧
    (q % 5 = 1 ∨ q % 5 = 4) ∧
    (q % 28 = 1 ∨ q % 28 = 3 ∨ q % 28 = 9 ∨
     q % 28 = 19 ∨ q % 28 = 25 ∨ q % 28 = 27) ∧
    (q % 13 = 1 ∨ q % 13 = 3 ∨ q % 13 = 4 ∨
     q % 13 = 9 ∨ q % 13 = 10 ∨ q % 13 = 12) ∧
    -- p=43: QR condition depends on q%4
    ((q % 4 = 1 →
        (q % 43 = 1 ∨ q % 43 = 4 ∨ q % 43 = 6 ∨ q % 43 = 9 ∨
         q % 43 = 10 ∨ q % 43 = 11 ∨ q % 43 = 13 ∨ q % 43 = 14 ∨
         q % 43 = 15 ∨ q % 43 = 16 ∨ q % 43 = 17 ∨ q % 43 = 21 ∨
         q % 43 = 23 ∨ q % 43 = 24 ∨ q % 43 = 25 ∨ q % 43 = 31 ∨
         q % 43 = 35 ∨ q % 43 = 36 ∨ q % 43 = 38 ∨ q % 43 = 40 ∨
         q % 43 = 41)) ∧
     (q % 4 = 3 →
        (q % 43 = 2 ∨ q % 43 = 3 ∨ q % 43 = 5 ∨ q % 43 = 7 ∨
         q % 43 = 8 ∨ q % 43 = 12 ∨ q % 43 = 18 ∨ q % 43 = 19 ∨
         q % 43 = 20 ∨ q % 43 = 22 ∨ q % 43 = 26 ∨ q % 43 = 27 ∨
         q % 43 = 28 ∨ q % 43 = 29 ∨ q % 43 = 30 ∨ q % 43 = 32 ∨
         q % 43 = 33 ∨ q % 43 = 34 ∨ q % 43 = 37 ∨ q % 43 = 39 ∨
         q % 43 = 42))) ∧
    (q % 53 = 1 ∨ q % 53 = 4 ∨ q % 53 = 6 ∨ q % 53 = 7 ∨
     q % 53 = 9 ∨ q % 53 = 10 ∨ q % 53 = 11 ∨ q % 53 = 13 ∨
     q % 53 = 15 ∨ q % 53 = 16 ∨ q % 53 = 17 ∨ q % 53 = 24 ∨
     q % 53 = 25 ∨ q % 53 = 28 ∨ q % 53 = 29 ∨ q % 53 = 36 ∨
     q % 53 = 37 ∨ q % 53 = 38 ∨ q % 53 = 40 ∨ q % 53 = 42 ∨
     q % 53 = 43 ∨ q % 53 = 44 ∨ q % 53 = 46 ∨ q % 53 = 47 ∨
     q % 53 = 49 ∨ q % 53 = 52) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hc; push_neg at hc
    exact absurd h3 (mult_three_escapes_qr (by omega) hc.1 hc.2)
  · by_contra hc; push_neg at hc
    exact absurd h5 (mult_five_escapes_qr (by omega) hc.1 hc.2)
  · by_contra hc; push_neg at hc
    exact absurd h7 (mult_seven_escapes_qr (by omega)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · by_contra hc; push_neg at hc
    exact absurd h13 (mult_thirteen_escapes_qr (by omega)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2)
  · -- p=43: split by q%4
    constructor
    · intro hmod4; by_contra hc; push_neg at hc
      obtain ⟨ne1, ne4, ne6, ne9, ne10, ne11, ne13, ne14, ne15, ne16, ne17,
              ne21, ne23, ne24, ne25, ne31, ne35, ne36, ne38, ne40, ne41⟩ := hc
      exact absurd h43 (mult_fortythree_escapes_qr_case1 (by omega) hmod4
        ne1 ne4 ne6 ne9 ne10 ne11 ne13 ne14 ne15 ne16 ne17
        ne21 ne23 ne24 ne25 ne31 ne35 ne36 ne38 ne40 ne41)
    · intro hmod4; by_contra hc; push_neg at hc
      obtain ⟨ne2, ne3, ne5, ne7, ne8, ne12, ne18, ne19, ne20, ne22, ne26, ne27,
              ne28, ne29, ne30, ne32, ne33, ne34, ne37, ne39, ne42⟩ := hc
      exact absurd h43 (mult_fortythree_escapes_qr_case3 (by omega) hmod4
        ne2 ne3 ne5 ne7 ne8 ne12 ne18 ne19 ne20 ne22 ne26 ne27
        ne28 ne29 ne30 ne32 ne33 ne34 ne37 ne39 ne42)
  · by_contra hc; push_neg at hc
    obtain ⟨ne1, ne4, ne6, ne7, ne9, ne10, ne11, ne13, ne15, ne16, ne17, ne24,
            ne25, ne28, ne29, ne36, ne37, ne38, ne40, ne42, ne43, ne44, ne46, ne47,
            ne49, ne52⟩ := hc
    exact absurd h53 (mult_fiftythree_escapes_qr (by omega)
      ne1 ne4 ne6 ne7 ne9 ne10 ne11 ne13 ne15 ne16 ne17 ne24
      ne25 ne28 ne29 ne36 ne37 ne38 ne40 ne42 ne43 ne44 ne46 ne47
      ne49 ne52)

/-! ## SE via prime-index escape (multi-witness)

In a cyclic group of order n, the maximal proper subgroups (coatoms) are
exactly the subgroups of index ℓ for each prime ℓ | n. An element g lies
in the index-ℓ subgroup iff g^(n/ℓ) = 1 (Lagrange).

This gives a WEAKER criterion than primitive root: instead of finding ONE
multiplier that generates the whole group, we find DIFFERENT multipliers
escaping DIFFERENT prime-index subgroups. Formally:

  SE at q ← ∀ prime ℓ | (q-1), ∃ mult m, m^((q-1)/ℓ) ≠ 1

This is strictly more general than `se_at_of_pow_checks` (which requires
a single multiplier escaping ALL prime-index subgroups simultaneously). -/

/-- In a finite group, if `g ∈ H` for subgroup `H`, then `g ^ |H| = 1`.
    This is the "Lagrange" fact: the order of `g` divides `|H|`. -/
theorem pow_card_subgroup_eq_one {G : Type*} [Group G] [Fintype G]
    {g : G} {H : Subgroup G} (hg : g ∈ H) :
    g ^ Fintype.card H = 1 := by
  have h1 : orderOf (⟨g, hg⟩ : H) ∣ Fintype.card H := orderOf_dvd_card
  have h2 : orderOf (⟨g, hg⟩ : H) = orderOf g :=
    (orderOf_injective H.subtype H.subtype_injective ⟨g, hg⟩).symm
  rw [h2] at h1
  obtain ⟨c, hc⟩ := h1
  rw [hc, pow_mul, pow_orderOf_eq_one, one_pow]

/-- If `|H|` divides `d`, then every element of `H` satisfies `g^d = 1`. -/
theorem pow_eq_one_of_mem_subgroup {G : Type*} [Group G] [Fintype G]
    {g : G} {H : Subgroup G} (hg : g ∈ H) {d : ℕ} (hd : Fintype.card H ∣ d) :
    g ^ d = 1 := by
  obtain ⟨k, hk⟩ := hd
  rw [hk, pow_mul, pow_card_subgroup_eq_one hg, one_pow]

/-- **SE via prime-index escape**: SubgroupEscape holds at q if, for every
    prime ℓ dividing q-1, some multiplier residue m satisfies m^((q-1)/ℓ) ≠ 1
    (i.e., m is NOT an ℓ-th power residue mod q).

    Different multipliers may witness different prime indices. This is
    strictly weaker than finding a single primitive root.

    **Proof**: Suppose for contradiction that all mults lie in some proper H.
    Then |H| divides q-1, and since |H| < q-1, the quotient (q-1)/|H| > 1
    has a prime factor ℓ. Since |H| divides (q-1)/ℓ, every element of H
    satisfies g^((q-1)/ℓ) = 1. But the hypothesis gives a mult with
    m^((q-1)/ℓ) ≠ 1, contradiction. -/
theorem se_of_prime_index_escape {q : Nat} [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hesc : ∀ ℓ ∈ (q - 1).primeFactors,
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ^ ((q - 1) / ℓ) ≠ 1) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  intro H hH
  -- Step 1: H is a proper subgroup, so |H| < q-1 = |(ZMod q)×|
  have hcard_G : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime inst.out]
  have hcard_H_dvd : Fintype.card H ∣ q - 1 := by
    rw [← hcard_G, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H
  have hcard_H_le : Fintype.card H ≤ Fintype.card (ZMod q)ˣ :=
    Fintype.card_le_of_injective H.subtype H.subtype_injective
  have hcard_H_ne : Fintype.card H ≠ Fintype.card (ZMod q)ˣ := by
    intro heq
    exact hH (Subgroup.eq_top_of_card_eq H
      (show Nat.card H = Nat.card (ZMod q)ˣ by
        simp only [Nat.card_eq_fintype_card]; exact heq))
  have hcard_H_lt : Fintype.card H < q - 1 :=
    hcard_G ▸ (lt_of_le_of_ne hcard_H_le hcard_H_ne)
  -- Step 2: k = (q-1)/|H| > 1, so it has a prime factor ℓ
  set d := Fintype.card H
  set k := (q - 1) / d
  have hd_pos : 0 < d := Fintype.card_pos
  have hqm1_pos : 0 < q - 1 := by have := inst.out.one_lt; omega
  have hk_gt_one : k > 1 := by
    rcases hcard_H_dvd with ⟨c, hc⟩
    show (q - 1) / d > 1
    rw [hc, Nat.mul_div_cancel_left _ hd_pos]
    -- c = (q-1)/d and d < q-1, so d*c = q-1 > d*1, hence c > 1
    by_contra h; push_neg at h
    interval_cases c <;> omega
  have hk_ne_one : k ≠ 1 := by omega
  -- Get a prime factor ℓ of k
  set ℓ := k.minFac
  have hℓ_prime : Nat.Prime ℓ := Nat.minFac_prime hk_ne_one
  have hℓ_dvd_k : ℓ ∣ k := Nat.minFac_dvd k
  -- ℓ divides q-1 (since ℓ | k and k | q-1)
  have hk_dvd : k ∣ (q - 1) := Nat.div_dvd_of_dvd hcard_H_dvd
  have hℓ_dvd_qm1 : ℓ ∣ (q - 1) := dvd_trans hℓ_dvd_k hk_dvd
  have hqm1_ne : q - 1 ≠ 0 := by omega
  have hℓ_mem : ℓ ∈ (q - 1).primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero hqm1_ne).mpr ⟨hℓ_prime, hℓ_dvd_qm1⟩
  -- Step 3: By hypothesis, some mult has m^((q-1)/ℓ) ≠ 1
  obtain ⟨n, hn⟩ := hesc ℓ hℓ_mem
  -- Step 4: Show this mult ∉ H (if it were in H, its power would be 1)
  refine ⟨n, fun hmem => hn ?_⟩
  -- d | (q-1)/ℓ: since q-1 = d*k and ℓ | k, we have (q-1)/ℓ = d*(k/ℓ)
  have hd_dvd_quot : d ∣ (q - 1) / ℓ := by
    have hqdk : q - 1 = d * k := by
      have := (Nat.div_mul_cancel hcard_H_dvd).symm  -- q - 1 = k * d
      rwa [mul_comm] at this
    rw [hqdk, Nat.mul_div_assoc d hℓ_dvd_k]
    exact dvd_mul_right d _
  exact pow_eq_one_of_mem_subgroup hmem hd_dvd_quot

/-- **Concrete SE helper (multi-witness)**: verify SubgroupEscape at prime q
    by providing, for each prime factor ℓ of q-1, a multiplier index n and
    value v such that v^((q-1)/ℓ) ≠ 1. Different primes ℓ may use different
    multiplier indices. The value checks are `native_decide`-friendly. -/
theorem se_of_prime_index_concrete {q : Nat} [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hesc : ∀ ℓ ∈ (q - 1).primeFactors,
      ∃ n, ∃ v : ZMod q, v ≠ 0 ∧ multZ q n = v ∧ v ^ ((q - 1) / ℓ) ≠ 1) :
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
  apply se_of_prime_index_escape hq hne
  intro ℓ hℓ
  obtain ⟨n, v, hv, hmult, hpow⟩ := hesc ℓ hℓ
  refine ⟨n, ?_⟩
  -- Need: (Units.mk0 (multZ q n) _)^((q-1)/ℓ) ≠ 1
  -- Since multZ q n = v, this is (Units.mk0 v _)^((q-1)/ℓ) ≠ 1
  -- which holds iff v^((q-1)/ℓ) ≠ 1 (by Units.val injectivity)
  subst hmult
  intro h
  exact hpow (by simpa [Units.ext_iff] using h)

/-! ## Concrete SE at q = 131 (multi-witness)

At q = 131, all 6 standard multiplier residues {3,7,43,13,53,5} are
quadratic residues mod 131. No single multiplier among the first 6 is
a primitive root mod 131 — so `se_at_of_pow_checks` cannot verify SE here.

But 131-1 = 130 = 2 × 5 × 13, giving three maximal subgroups.
We escape each with a different multiplier:
- Index 13: mult 0 = 3 satisfies 3^10 ≠ 1 mod 131 (3 is not a 13th power)
- Index 5: mult 0 = 3 satisfies 3^26 ≠ 1 mod 131 (3 is not a 5th power)
- Index 2: mult 6 = seq(7) mod 131 = 88 satisfies 88^65 ≠ 1 mod 131
  (88 is a quadratic non-residue — the 7th multiplier breaks the QR barrier)

Uses the new `se_of_prime_index_escape` framework with manual witnesses. -/

instance fact_prime_131 : Fact (Nat.Prime 131) := ⟨by decide⟩

theorem se_at_131 (hq : IsPrime 131) (hne : ∀ k, seq k ≠ 131) :
    ∀ H : Subgroup (ZMod 131)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 131 m) (multZ_ne_zero hq hne m)) ∉ H := by
  apply se_of_prime_index_concrete hq hne
  intro ℓ hℓ
  -- 130 = 2 × 5 × 13, so primeFactors = {2, 5, 13}
  have hpf : (131 - 1 : ℕ).primeFactors = {2, 5, 13} := by native_decide
  rw [hpf, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hℓ
  rcases hℓ with rfl | rfl | rfl
  · -- ℓ = 2: mult 6 (= seq 7 mod 131 = 88), 88^65 ≠ 1 mod 131
    exact ⟨6, 88, by native_decide, by native_decide, by native_decide⟩
  · -- ℓ = 5: mult 0 (= 3), 3^26 ≠ 1 mod 131
    exact ⟨0, 3, by native_decide, by native_decide, by native_decide⟩
  · -- ℓ = 13: mult 0 (= 3), 3^10 ≠ 1 mod 131
    exact ⟨0, 3, by native_decide, by native_decide, by native_decide⟩

end MullinGroup
