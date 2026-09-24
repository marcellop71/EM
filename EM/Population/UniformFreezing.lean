import EM.Population.Confinement
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Squarefree

/-!
# Theorem A: a uniformly frozen class forces confinement

2026-09-24.  Companion to `docs/analysis/euclid_systems_theory_2026-09-23.md` §11.2.

If at one stage `n` the discriminant `D_n = 1 − 4c_n` is a non-square modulo *every*
sufficiently large prime `q ≡ 2 (mod 3)`, then `D_n = −3 s²`: the stage is confined to the
tower's field `ℚ(√−3)` (`confined_of_uniformly_frozen`).  The general statement
(`eq_neg_three_mul_sq_of_nonsquare_two_mod_three`) is for any negative `D ≡ 1 (mod 4)`.

Proof.  For `D < 0`, `D ≡ 1 (mod 4)` and an odd prime `q`, reciprocity gives
`J(D | q) = J(q | |D|)` (`jacobiSym_neg_one_mod_four`).  Write `|D| = 3^e M` with `3 ∤ M`.  If
`M` is not a square, the Jacobi character `J(· | M)` takes the value `−1`
(`exists_jacobiSym_eq_neg_one`), so by Dirichlet there are large primes `q ≡ 2 (mod 3)` in a
class mod `M` where `J(q | 3)^e J(q | M) = +1`, contradicting the hypothesis; so `M` is a
square.  Then `J(q | |D|) = (−1)^e`, forcing `e` odd, and `|D| = 3 · (3^{(e−1)/2} √M)²`.
-/

noncomputable section
open Classical

namespace UniformFreezing

/-! ## 1. Dirichlet in a coprime class -/

/-- Infinitely many primes in every class coprime to `M`. -/
theorem exists_prime_gt_mod {M a : ℕ} (hM : 0 < M) (h : Nat.Coprime a M) (B : ℕ) :
    ∃ q, B < q ∧ q.Prime ∧ q % M = a % M := by
  have : NeZero M := ⟨hM.ne'⟩
  have hu : IsUnit ((a : ℕ) : ZMod M) := by
    have := (ZMod.unitOfCoprime a h).isUnit
    rwa [ZMod.coe_unitOfCoprime] at this
  obtain ⟨q, hq, hqp, hqa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu B
  exact ⟨q, hq, hqp, (ZMod.natCast_eq_natCast_iff' q a M).mp hqa⟩

/-! ## 2. Reciprocity for a negative discriminant `≡ 1 (mod 4)` -/

theorem jacobiSym_neg_one_mod_four {D : ℤ} (hD : D < 0) (h1 : D % 4 = 1) {q : ℕ}
    (hodd : q % 2 = 1) :
    jacobiSym D q = jacobiSym (q : ℤ) D.natAbs := by
  set A := D.natAbs with hAdef
  have hA : (A : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD.le
  have hA4 : A % 4 = 3 := by
    have : (A : ℤ) % 4 = 3 := by rw [hA]; omega
    exact_mod_cast this
  have hAodd : Odd A := Nat.odd_iff.mpr (by omega)
  have hqodd : Odd q := Nat.odd_iff.mpr hodd
  have hsplit : D = -1 * (A : ℤ) := by rw [hA]; ring
  rw [hsplit, jacobiSym.mul_left, jacobiSym.at_neg_one hqodd]
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with h4 | h4
  · rw [ZMod.χ₄_nat_one_mod_four h4, jacobiSym.quadratic_reciprocity_one_mod_four' hAodd h4]
    ring
  · rw [ZMod.χ₄_nat_three_mod_four h4, jacobiSym.quadratic_reciprocity_three_mod_four hA4 h4]
    ring

/-! ## 3. The Jacobi character of a non-square is nontrivial -/

theorem coprime_of_modEq_one {x m : ℕ} (h : x % m = 1 % m) : Nat.Coprime x m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at h; subst h; exact Nat.coprime_one_left 0
  · rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · have : m = 1 := by omega
      subst this; exact Nat.coprime_one_right x
    · rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.mod_eq_of_lt hm2]
      exact Nat.gcd_one_left m

theorem jacobiSym_eq_one_of_isSquare {M x : ℕ} (hM : M ≠ 0) (hs : IsSquare M)
    (hcop : Nat.Coprime x M) : jacobiSym x M = 1 := by
  obtain ⟨s, rfl⟩ := hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hM
  have : NeZero s := ⟨hs0⟩
  rw [jacobiSym.mul_right, ← sq]
  apply jacobiSym.sq_one
  have := Nat.Coprime.coprime_dvd_right (dvd_mul_right s s) hcop
  exact_mod_cast this

/-- For odd `M` that is not a square there is a class `x` coprime to `M` with `J(x | M) = −1`. -/
theorem exists_jacobiSym_eq_neg_one {M : ℕ} (hM : Odd M) (hns : ¬ IsSquare M) :
    ∃ x : ℕ, Nat.Coprime x M ∧ jacobiSym x M = -1 := by
  have hM0 : M ≠ 0 := by rintro rfl; simp at hM
  obtain ⟨b, a, hb, ha, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hM0)
  -- `M = a² b` with `b` squarefree, `b ≠ 1`
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hns ⟨a, by rw [← hab]; ring⟩
  obtain ⟨ℓ, hℓ, hℓb⟩ := Nat.exists_prime_and_dvd hb1
  have hℓM : ℓ ∣ M := by rw [← hab]; exact hℓb.mul_left _
  have hℓodd : ℓ ≠ 2 := by
    rintro rfl
    exact absurd (hM.of_dvd_nat hℓM) (by decide)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  -- the exponent of `ℓ` in `M` is odd
  have hval : Odd (M.factorization ℓ) := by
    rw [← hab, Nat.factorization_mul (by positivity) hb.ne', Nat.factorization_pow]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : b.factorization ℓ = 1 := by
      apply le_antisymm (hsq.natFactorization_le_one ℓ)
      exact (Nat.Prime.dvd_iff_one_le_factorization hℓ hb.ne').mp hℓb
    rw [h1]
    exact ⟨a.factorization ℓ, by ring⟩
  -- `M = ℓ^v * m` with `ℓ ∤ m`
  set v := M.factorization ℓ
  set m := M / ℓ ^ v with hm
  have hMvm : ℓ ^ v * m = M := Nat.ordProj_mul_ordCompl_eq_self M ℓ
  have hℓm : ¬ ℓ ∣ m := Nat.not_dvd_ordCompl hℓ hM0
  have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hMvm; exact hM0 hMvm.symm
  -- a non-residue mod `ℓ`
  obtain ⟨r, hr⟩ := FiniteField.exists_nonsquare (F := ZMod ℓ) (by rw [ZMod.ringChar_zmod_n]; exact hℓodd)
  have hr0 : r ≠ 0 := by rintro rfl; exact hr ⟨0, by simp⟩
  -- CRT: `x ≡ r.val (mod ℓ)`, `x ≡ 1 (mod m)`
  have hcop : Nat.Coprime ℓ m := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓm
  obtain ⟨x, hxℓ, hxm⟩ := Nat.chineseRemainder hcop r.val 1
  refine ⟨x, ?_, ?_⟩
  · -- coprime to `M`
    rw [← hMvm]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ]
      intro hdvd
      have : (x : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      have hx : (x : ZMod ℓ) = r := by
        rw [← ZMod.natCast_zmod_val r]
        exact (ZMod.natCast_eq_natCast_iff' x r.val ℓ).mpr hxℓ
      rw [hx] at this
      exact hr0 this
    · exact coprime_of_modEq_one hxm
  · -- the value
    rw [← hMvm, jacobiSym.mul_right' _ (pow_ne_zero _ hℓ.ne_zero) hm0, jacobiSym.pow_right]
    have hxr : jacobiSym x ℓ = -1 := by
      rw [jacobiSym.mod_left' (b := ℓ) (a₂ := (r.val : ℤ)) (by exact_mod_cast hxℓ)]
      exact ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr
        (by rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hr)
    have hxm' : jacobiSym x m = 1 := by
      rw [jacobiSym.mod_left' (b := m) (a₂ := 1) (by exact_mod_cast hxm)]
      exact jacobiSym.one_left m
    rw [hxr, hxm', hval.neg_one_pow]
    ring

/-! ## 4. Theorem A -/

theorem two_not_square_zmod_three : ¬ IsSquare (2 : ZMod 3) := by decide

/-- `2` is not a square mod `3`: `J(q | 3) = −1` for `q ≡ 2 (mod 3)`. -/
theorem jacobiSym_two_mod_three {q : ℕ} (hq : q % 3 = 2) : jacobiSym (q : ℤ) 3 = -1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : ((q : ℤ) : ZMod 3) = 2 := by
    rw [Int.cast_natCast]
    have := (ZMod.natCast_eq_natCast_iff' q 2 3).mpr (by omega)
    simpa using this
  exact ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (by rw [h2]; exact two_not_square_zmod_three)

/-- **Theorem A.**  A negative `D ≡ 1 (mod 4)` that is a non-square modulo every sufficiently
large prime `q ≡ 2 (mod 3)` is `−3` times a square. -/
theorem eq_neg_three_mul_sq_of_nonsquare_two_mod_three {D : ℤ} (hD : D < 0) (h1 : D % 4 = 1)
    (h : ∃ B : ℕ, ∀ q : ℕ, B < q → q.Prime → q % 3 = 2 → ¬ IsSquare ((D : ZMod q))) :
    ∃ s : ℕ, D.natAbs = 3 * s ^ 2 := by
  obtain ⟨B, hB⟩ := h
  set A := D.natAbs with hAdef
  have hA0 : A ≠ 0 := by
    rw [hAdef]; exact Int.natAbs_ne_zero.mpr hD.ne
  have hAodd : Odd A := by
    have : (A : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD.le
    have h3 : (A : ℤ) % 4 = 3 := by rw [this]; omega
    exact Nat.odd_iff.mpr (by omega)
  -- the key consequence of the hypothesis: `J(q | A) = −1` for large `q ≡ 2 (mod 3)`
  have key : ∀ q : ℕ, B < q → 2 < q → q.Prime → q % 3 = 2 → jacobiSym (q : ℤ) A = -1 := by
    intro q hq h2 hqp hq3
    have : Fact q.Prime := ⟨hqp⟩
    have hodd : q % 2 = 1 := by
      rcases hqp.eq_two_or_odd with h | h
      · omega
      · exact h
    rw [← jacobiSym_neg_one_mod_four hD h1 hodd]
    exact ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (hB q hq hqp hq3)
  -- `A = 3^e * M`, `3 ∤ M`
  obtain ⟨e, M, hM3, hAeM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hA0 3 (by norm_num)
  have hM0 : M ≠ 0 := by rintro rfl; simp at hAeM; exact hA0 hAeM
  have hModd : Odd M := by
    have := hAodd; rw [hAeM] at this
    exact (Nat.odd_mul.mp this).2
  have hcop3M : Nat.Coprime 3 M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3
  -- for `q` coprime to `3M`: `J(q | A) = (−1)^e * J(q | M)`
  have hsplit : ∀ q : ℕ, q % 3 = 2 → jacobiSym (q : ℤ) A = (-1) ^ e * jacobiSym (q : ℤ) M := by
    intro q hq3
    rw [hAeM, jacobiSym.mul_right' _ (pow_ne_zero _ (by norm_num)) hM0, jacobiSym.pow_right,
      jacobiSym_two_mod_three hq3]
  -- Step 1: `M` is a square
  have hMsq : IsSquare M := by
    by_contra hns
    obtain ⟨x, hxcop, hx⟩ := exists_jacobiSym_eq_neg_one hModd hns
    -- choose the class `x₀ mod M` with `J(x₀ | M) = (−1)^e`
    obtain ⟨x₀, hx₀cop, hx₀⟩ : ∃ x₀ : ℕ, Nat.Coprime x₀ M ∧ jacobiSym x₀ M = (-1) ^ e := by
      rcases Nat.even_or_odd e with he | he
      · exact ⟨1, Nat.coprime_one_left M, by rw [he.neg_one_pow]; simp⟩
      · exact ⟨x, hxcop, by rw [he.neg_one_pow]; exact hx⟩
    -- CRT: `c ≡ 2 (mod 3)`, `c ≡ x₀ (mod M)`
    obtain ⟨c, hc3, hcM⟩ := Nat.chineseRemainder hcop3M 2 x₀
    have hc3' : c % 3 = 2 := hc3
    have hcM' : c % M = x₀ % M := hcM
    have hccop : Nat.Coprime c (3 * M) := by
      apply Nat.Coprime.mul_right
      · rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc3']; decide
      · rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hcM', ← Nat.gcd_rec, Nat.gcd_comm]
        exact hx₀cop
    obtain ⟨q, hq, hqp, hqc⟩ := exists_prime_gt_mod (by positivity) hccop (max B (3 * M + 2))
    have hq3 : q % 3 = 2 := by
      have h1' : q % 3 = c % 3 := by
        rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 3 M), hqc, Nat.mod_mod_of_dvd c (dvd_mul_right 3 M)]
      rw [h1']; exact hc3'
    have hqM : q % M = x₀ % M := by
      have h1' : q % M = c % M := by
        rw [← Nat.mod_mod_of_dvd q (dvd_mul_left M 3), hqc, Nat.mod_mod_of_dvd c (dvd_mul_left M 3)]
      rw [h1']; exact hcM'
    have hJ := key q (lt_of_le_of_lt (le_max_left _ _) hq)
      (by have := le_max_right B (3 * M + 2); omega) hqp hq3
    rw [hsplit q hq3, jacobiSym.mod_left' (b := M) (a₂ := (x₀ : ℤ)) (by exact_mod_cast hqM),
      hx₀] at hJ
    have h2 : ((-1 : ℤ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [← sq] at hJ
    rw [h2] at hJ
    norm_num at hJ
  -- Step 2: `e` is odd
  have he : Odd e := by
    have h2M : Nat.Coprime 2 M :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hModd.not_two_dvd_nat
    obtain ⟨q, hq, hqp, hqc⟩ := exists_prime_gt_mod (M := 3 * M) (by positivity)
      (Nat.Coprime.mul_right (by decide : Nat.Coprime 2 3) h2M) (max B (3 * M + 2))
    have hq3 : q % 3 = 2 := by
      rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 3 M), hqc, Nat.mod_mod_of_dvd 2 (dvd_mul_right 3 M)]
    have hqM : Nat.Coprime q M := by
      have h1' : q % M = 2 % M := by
        rw [← Nat.mod_mod_of_dvd q (dvd_mul_left M 3), hqc, Nat.mod_mod_of_dvd 2 (dvd_mul_left M 3)]
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1', ← Nat.gcd_rec, Nat.gcd_comm]
      exact h2M
    have hJ := key q (lt_of_le_of_lt (le_max_left _ _) hq)
      (by have := le_max_right B (3 * M + 2); omega) hqp hq3
    rw [hsplit q hq3, jacobiSym_eq_one_of_isSquare hM0 hMsq hqM, mul_one] at hJ
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    rw [hev.neg_one_pow] at hJ
    norm_num at hJ
  -- assemble: `A = 3^e M = 3 (3^k √M)²` with `e = 2k + 1`
  obtain ⟨k, hk⟩ := he
  obtain ⟨t, ht⟩ := hMsq
  refine ⟨3 ^ k * t, ?_⟩
  rw [hAeM, hk, ht]
  ring

/-- **Uniformly frozen class at a stage ⟹ confined.**  If `D_n` is a non-square modulo every
sufficiently large prime `q ≡ 2 (mod 3)`, then `D_n = −3 s²`. -/
theorem confined_of_uniformly_frozen {n : ℕ}
    (h : ∃ B : ℕ, ∀ q : ℕ, B < q → q.Prime → q % 3 = 2 → ¬ IsSquare ((QuadraticStep.disc n : ZMod q))) :
    Confinement.Confined n := by
  have hc := QuadraticStep.cofactor_pos n
  have hD : QuadraticStep.disc n < 0 := by
    unfold QuadraticStep.disc; have : (1 : ℤ) ≤ QuadraticStep.cofactor n := by exact_mod_cast hc
    linarith
  have h1 : QuadraticStep.disc n % 4 = 1 := by
    unfold QuadraticStep.disc; omega
  obtain ⟨s, hs⟩ := eq_neg_three_mul_sq_of_nonsquare_two_mod_three hD h1 h
  refine ⟨s, ?_⟩
  have hA : ((QuadraticStep.disc n).natAbs : ℤ) = -QuadraticStep.disc n :=
    Int.ofNat_natAbs_of_nonpos hD.le
  have : ((QuadraticStep.disc n).natAbs : ℤ) = 3 * (s : ℤ) ^ 2 := by exact_mod_cast hs
  linarith

end UniformFreezing

end
