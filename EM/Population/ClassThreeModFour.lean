import EM.Population.Confinement
import EM.Population.ClassInfinitude
import Mathlib.NumberTheory.SumTwoSquares

/-!
# `CI(3 mod 4)`: the 2-adic walk, and the emptiness of the Gaussian locus

2026-09-24.  Companion to `docs/analysis/euclid_systems_theory_2026-09-23.md` §14.

`CI(3 mod 4)` — infinitely many Euclid–Mullin primes `≡ 3 (mod 4)` — is the weakest open
class statement: it holds on the Sylvester tower (`EuclidClasses.perpetual_seq_mod_four`), so its
content is `(C∞) ⟹ CI(3 mod 4)`.  Two structural facts:

* **The 2-adic reformulation.**  `P_n ≡ 2 (mod 4)` and a multiplier `≡ 3 (mod 4)` is exactly a
  change of `P_n mod 8` (`prod_succ_mod_eight_eq_iff`), so `CI(3 mod 4)` says the accumulator
  (equivalently the Euclid number) is **not eventually constant modulo 8**
  (`classInfinitude_three_mod_four_iff_prod_mod_eight`): the torsion component of the
  2-deleted walk keeps flipping.
* **The Gaussian locus is empty.**  The analogue of confinement for `ℚ(i)` would be
  `D_n = −s²`, i.e. `4c_n − 1` a perfect square.  It never happens
  (`four_cofactor_sub_one_not_square`): it would make `4c_n E_{n+1} = (2E_n − 1)² + s²` a sum of
  two squares, hence every prime `≡ 3 (mod 4)` would divide `E_{n+1}` to even order, while
  `E_{n+1} ≡ 3 (mod 4)`.  So, unlike `(C∞)` whose failure has an algebraic locus (the tower in
  `ℚ(√−3)`), a failure of `CI(3 mod 4)` has no quadratic-field locus at all: it would be purely
  "transcendental".
-/

noncomputable section
open Classical Mullin QuadraticStep Confinement EuclidClasses

namespace ClassThreeModFour

/-! ## 1. The Gaussian locus is empty -/

theorem sq_add_sq_mod_four_ne_three (x y : ℕ) : (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
  intro h
  have h4 : ((x ^ 2 + y ^ 2 : ℕ) : ZMod 4) = 3 := by
    have := (ZMod.natCast_eq_natCast_iff' (x ^ 2 + y ^ 2) 3 4).mpr (by rw [h])
    simpa using this
  push_cast at h4
  have key : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
  exact key _ _ h4

/-- **`4 c_n − 1` is never a perfect square**: no stage is confined to `ℚ(i)`. -/
theorem four_cofactor_sub_one_not_square (n : ℕ) : ¬ ∃ s : ℤ, disc n = -1 * s ^ 2 := by
  rintro ⟨s, hs⟩
  set E' := prod (n + 1) + 1 with hE'
  have hid := four_cofactor_mul_euclid_succ n
  rw [hs] at hid
  -- `4 c E' = x² + y²` in `ℕ`
  have hx : 1 ≤ 2 * (prod n + 1) := by omega
  have hsum : 4 * cofactor n * E' = (2 * (prod n + 1) - 1) ^ 2 + s.natAbs ^ 2 := by
    have h1 : ((2 * (prod n + 1) - 1 : ℕ) : ℤ) = 2 * ((prod n + 1 : ℕ) : ℤ) - 1 := by
      push_cast [Nat.cast_sub hx]; ring
    have h2 : ((s.natAbs : ℕ) : ℤ) ^ 2 = s ^ 2 := by
      rw [Int.natCast_natAbs, sq_abs]
    have : ((4 * cofactor n * E' : ℕ) : ℤ)
        = ((2 * (prod n + 1) - 1 : ℕ) : ℤ) ^ 2 + ((s.natAbs : ℕ) : ℤ) ^ 2 := by
      rw [h1, h2, hE']
      push_cast at hid ⊢
      linear_combination hid
    exact_mod_cast this
  have hE'3 : E' % 4 = 3 := euclid_mod_four (n + 1)
  have hE'0 : E' ≠ 0 := by omega
  have hc0 : cofactor n ≠ 0 := (cofactor_pos n).ne'
  -- every prime `q ≡ 3 (4)` divides `E'` to even order
  have hcrit : ∀ q ∈ E'.primeFactors, q % 4 = 3 → Even (padicValNat q E') := by
    intro q hq hq3
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqp⟩
    have hqE : q ∣ E' := Nat.dvd_of_mem_primeFactors hq
    have hall := Nat.eq_sq_add_sq_iff.mp ⟨_, _, hsum⟩
    have hq' : q ∈ (4 * cofactor n * E').primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hqp, hqE.mul_left _, by positivity⟩
    have hev := hall q hq' hq3
    rw [padicValNat.mul (by positivity) hE'0, padicValNat.mul (by norm_num) hc0] at hev
    have h4 : padicValNat q 4 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      interval_cases q <;> simp_all
    have hc : padicValNat q (cofactor n) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      exact not_dvd_euclid_of_dvd_euclid_succ hqp hqE
        (h.trans ⟨Mullin.seq (n + 1), by rw [mul_comm]; exact (seq_mul_cofactor n).symm⟩)
    rw [h4, hc, zero_add, zero_add] at hev
    exact hev
  obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_iff.mpr hcrit
  exact sq_add_sq_mod_four_ne_three x y (hxy ▸ hE'3)

/-! ## 2. The 2-adic reformulation -/

/-- A step keeps `P_n mod 8` iff the multiplier is `≡ 1 (mod 4)`. -/
theorem prod_succ_mod_eight_eq_iff (n : ℕ) :
    prod (n + 1) % 8 = prod n % 8 ↔ Mullin.seq (n + 1) % 4 = 1 := by
  have hP := prod_mod_four n
  obtain ⟨k, hk⟩ := seq_odd (k := n + 1) (by omega)
  have h8 : prod n % 8 = 2 ∨ prod n % 8 = 6 := by omega
  have hs8 : Mullin.seq (n + 1) % 8 = 1 ∨ Mullin.seq (n + 1) % 8 = 3 ∨
      Mullin.seq (n + 1) % 8 = 5 ∨ Mullin.seq (n + 1) % 8 = 7 := by omega
  rw [prod_succ, Nat.mul_mod]
  rcases h8 with h | h <;> rcases hs8 with h' | h' | h' | h' <;> rw [h, h'] <;> omega

/-- **`CI(3 mod 4)` ⟺ the accumulator is not eventually constant modulo `8`.** -/
theorem classInfinitude_three_mod_four_iff_prod_mod_eight :
    ClassInfinitude 4 3 ↔ ∀ N, ∃ n, N ≤ n ∧ prod (n + 1) % 8 ≠ prod n % 8 := by
  constructor
  · intro h N
    obtain ⟨k, hk, hk3⟩ := h (N + 1)
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    refine ⟨n, by omega, ?_⟩
    rw [Ne, prod_succ_mod_eight_eq_iff]
    omega
  · intro h N
    obtain ⟨n, hn, hne⟩ := h N
    refine ⟨n + 1, by omega, ?_⟩
    rw [Ne, prod_succ_mod_eight_eq_iff] at hne
    obtain ⟨k, hk⟩ := seq_odd (k := n + 1) (by omega)
    omega

/-- Equivalently, the Euclid numbers are not eventually constant modulo `8`. -/
theorem classInfinitude_three_mod_four_iff_euclid_mod_eight :
    ClassInfinitude 4 3 ↔ ∀ N, ∃ n, N ≤ n ∧ (prod (n + 1) + 1) % 8 ≠ (prod n + 1) % 8 := by
  rw [classInfinitude_three_mod_four_iff_prod_mod_eight]
  constructor <;> intro h N <;> obtain ⟨n, hn, hne⟩ := h N <;> exact ⟨n, hn, by omega⟩

end ClassThreeModFour

end
