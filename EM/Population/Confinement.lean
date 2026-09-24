import EM.Population.QuadraticStep

/-!
# Confined stages: the discriminant in `ℚ(√−3)`

2026-09-24.  Companion to `docs/analysis/euclid_systems_theory_2026-09-23.md` §11.

A stage `n` is **confined** if its discriminant lies in the field of the Sylvester tower,
`D_n = −3 s²` (`Confined`); a prime stage is confined with `s = 1`
(`confined_of_prime`), and on a confined stage `c_n = 3t² + 3t + 1` is a cuban number.  The
locus "confined from some stage on" sits strictly between the tower and the frozen class
`q ≡ 2 (mod 3)`: it is the analogue of a constant-field extension, which is the mechanism of
the `𝔽_5[t]` refutation.

The one thing confinement forces at the next stage is a **positive divisibility fact**: from
`4 c_n E_{n+1} = (2E_n − 1)² + 3s²` and the inertness of `q ≡ 2 (mod 3)` in `ℚ(√−3)`, every
prime `ℓ ≡ 2 (mod 3)` dividing `E_{n+1}` divides it at least twice
(`sq_dvd_of_confined`).  Hence if `E_{n+1}` is squarefree, none of its prime factors is
`≡ 2 (mod 3)`, and in particular the next multiplier is not (`multiplier_not_two_mod_three`).
Confinement is therefore a strong form of "no prime `≡ 2 (mod 3)` is captured", the class
statement whose infinitude `CI(2 mod 3)` implies `(C∞)` (`ClassInfinitude.lean`).
-/

noncomputable section
open Classical Mullin QuadraticStep

namespace Confinement

/-- A stage is confined if its discriminant is `−3` times a square. -/
def Confined (n : ℕ) : Prop := ∃ s : ℤ, disc n = -3 * s ^ 2

/-- A prime stage is confined (`s = 1`). -/
theorem confined_of_prime {n : ℕ} (h : Nat.Prime (prod n + 1)) : Confined n :=
  ⟨1, by rw [disc_eq_neg_three_of_prime h]; ring⟩

/-- **Inertness of `ℓ ≡ 2 (mod 3)` in `ℚ(√−3)`**: if `ℓ ∣ a² + 3b²` then `ℓ ∣ a` and `ℓ ∣ b`. -/
theorem dvd_of_dvd_sq_add_three_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (h3 : ℓ % 3 = 2) (h5 : 5 ≤ ℓ)
    {a b : ℤ} (h : (ℓ : ℤ) ∣ a ^ 2 + 3 * b ^ 2) : (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b := by
  have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  have h0 : ((a ^ 2 + 3 * b ^ 2 : ℤ) : ZMod ℓ) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  push_cast at h0
  have hb : (b : ZMod ℓ) = 0 := by
    by_contra hb
    apply not_isSquare_neg_three h3 h5
    refine ⟨(a : ZMod ℓ) / b, ?_⟩
    push_cast
    field_simp
    linear_combination -h0
  have ha : (a : ZMod ℓ) = 0 := by
    rw [hb] at h0
    have : (a : ZMod ℓ) ^ 2 = 0 := by linear_combination h0
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb⟩

/-- Consecutive Euclid numbers have no common prime factor: a common prime `ℓ` would divide
`p_{n+1} − 1` while being at least `p_{n+1}`. -/
theorem not_dvd_euclid_of_dvd_euclid_succ {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (h1 : ℓ ∣ prod (n + 1) + 1) : ¬ ℓ ∣ prod n + 1 := by
  intro h0
  set p := Mullin.seq (n + 1) with hp
  have hp1 : 1 ≤ p := seq_succ_pos n
  -- `ℓ ∣ p − 1`
  have hdvd : ℓ ∣ p - 1 := by
    have h2 : ℓ ∣ (prod n + 1) * p := h0.mul_right p
    have h3 : (prod n + 1) * p = (prod (n + 1) + 1) + (p - 1) := by
      have e : (prod n + 1) * p = prod n * p + p := by ring
      rw [e, prod_succ, ← hp]; omega
    rw [h3] at h2
    exact (Nat.dvd_add_right h1).mp h2
  -- but `ℓ ≥ p` since `p = minFac (prod n + 1)` and `ℓ ∣ prod n + 1`
  have hge : p ≤ ℓ := by
    rw [hp, seq_succ]
    exact Euclid.minFac_min' _ _ (by have := prod_ge_two n; omega) hℓ.two_le h0
  have hp2 : 2 ≤ p := by
    rw [hp]; exact ((MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))).two_le
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **Confinement forces double divisibility.**  If stage `n` is confined and a prime
`ℓ ≡ 2 (mod 3)`, `ℓ ≥ 5`, divides `E_{n+1}`, then `ℓ² ∣ E_{n+1}`. -/
theorem sq_dvd_of_confined {n ℓ : ℕ} (hc : Confined n) (hℓ : ℓ.Prime) (h3 : ℓ % 3 = 2)
    (h5 : 5 ≤ ℓ) (hdvd : ℓ ∣ prod (n + 1) + 1) : ℓ ^ 2 ∣ prod (n + 1) + 1 := by
  obtain ⟨s, hs⟩ := hc
  have hid := four_cofactor_mul_euclid_succ n
  rw [hs] at hid
  -- `ℓ ∣ (2E − 1)² + 3 s²`
  have h1 : (ℓ : ℤ) ∣ (2 * ((prod n + 1 : ℕ) : ℤ) - 1) ^ 2 + 3 * s ^ 2 := by
    have : (ℓ : ℤ) ∣ 4 * (cofactor n : ℤ) * ((prod (n + 1) + 1 : ℕ) : ℤ) :=
      (Int.natCast_dvd_natCast.mpr hdvd).mul_left _
    rw [hid] at this
    have e : (2 * ((prod n + 1 : ℕ) : ℤ) - 1) ^ 2 - -3 * s ^ 2
        = (2 * ((prod n + 1 : ℕ) : ℤ) - 1) ^ 2 + 3 * s ^ 2 := by ring
    rwa [e] at this
  obtain ⟨ha, hb⟩ := dvd_of_dvd_sq_add_three_sq hℓ h3 h5 h1
  -- hence `ℓ² ∣ 4 c E_{n+1}`
  have h2 : ((ℓ ^ 2 : ℕ) : ℤ) ∣ 4 * (cofactor n : ℤ) * ((prod (n + 1) + 1 : ℕ) : ℤ) := by
    rw [hid]
    have e : (2 * ((prod n + 1 : ℕ) : ℤ) - 1) ^ 2 - -3 * s ^ 2
        = (2 * ((prod n + 1 : ℕ) : ℤ) - 1) ^ 2 + 3 * s ^ 2 := by ring
    rw [e]
    push_cast
    exact (pow_dvd_pow_of_dvd ha 2).add ((pow_dvd_pow_of_dvd hb 2).mul_left 3)
  have h2' : ℓ ^ 2 ∣ 4 * cofactor n * (prod (n + 1) + 1) := by
    have := Int.natCast_dvd_natCast.mp (by push_cast at h2 ⊢; exact h2)
    exact this
  -- `ℓ` is coprime to `4 c_n`: odd, and `ℓ ∤ c_n` since `c_n ∣ E_n`
  have hodd : ¬ ℓ ∣ 4 := fun h => absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have hnc : ¬ ℓ ∣ cofactor n := fun h =>
    not_dvd_euclid_of_dvd_euclid_succ hℓ hdvd (h.trans ⟨Mullin.seq (n + 1), by
      rw [mul_comm]; exact (seq_mul_cofactor n).symm⟩)
  have hcop : Nat.Coprime (ℓ ^ 2) (4 * cofactor n) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hℓ]
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · exact hodd h
    · exact hnc h
  exact hcop.dvd_of_dvd_mul_left h2'

/-- On a confined stage with squarefree `E_{n+1}`, no prime `≡ 2 (mod 3)` (`≥ 5`) divides
`E_{n+1}`. -/
theorem not_dvd_of_confined_squarefree {n ℓ : ℕ} (hc : Confined n)
    (hsq : Squarefree (prod (n + 1) + 1)) (hℓ : ℓ.Prime) (h3 : ℓ % 3 = 2) (h5 : 5 ≤ ℓ) :
    ¬ ℓ ∣ prod (n + 1) + 1 := by
  intro hdvd
  have := hsq ℓ (by rw [← pow_two]; exact sq_dvd_of_confined hc hℓ h3 h5 hdvd)
  exact absurd (Nat.isUnit_iff.mp this) hℓ.one_lt.ne'

/-- **The multiplier after a confined stage is not `≡ 2 (mod 3)`** when `E_{n+1}` is
squarefree (the multiplier `2` is excluded by `E_{n+1}` odd, and `5 ≤ ℓ` holds for every
prime `≡ 2 (mod 3)` other than `2`). -/
theorem multiplier_not_two_mod_three {n : ℕ} (hc : Confined n)
    (hsq : Squarefree (prod (n + 1) + 1)) : Mullin.seq (n + 2) % 3 ≠ 2 := by
  intro h3
  have hp := (MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime (n + 2))
  have hdvd : Mullin.seq (n + 2) ∣ prod (n + 1) + 1 := seq_succ_dvd_euclid (n + 1)
  have h5 : 5 ≤ Mullin.seq (n + 2) := by
    have h2 : Mullin.seq (n + 2) ≠ 2 := by
      intro h2
      rw [h2] at hdvd
      -- `E_{n+1}` is odd: `2 ∣ prod (n+1)`
      have : 2 ∣ prod (n + 1) := by
        have := seq_dvd_prod 0 (n + 1) (Nat.zero_le _); rwa [seq_zero] at this
      omega
    have := hp.two_le
    omega
  exact not_dvd_of_confined_squarefree hc hsq hp h3 h5 hdvd

end Confinement

end
