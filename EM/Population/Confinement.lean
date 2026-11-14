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

/-! ## Confined runs -/

/-- **On two consecutive confined stages the multiplier is `≡ 1 (mod 3)`**, with no
squarefreeness assumption: a multiplier `p ≡ 2 (mod 3)` would divide `E_{n+1}` twice
(`sq_dvd_of_confined` at stage `n`), hence divide the cofactor `c_{n+1} = (3s'² + 1)/4`
(stage `n+1` confined), which has no prime factor `≡ 2 (mod 3)` since `−3` would be a square. -/
theorem multiplier_one_mod_three_of_confined_pair {n : ℕ} (hc : Confined n)
    (hc' : Confined (n + 1)) : Mullin.seq (n + 2) % 3 = 1 := by
  have hprime : (Mullin.seq (n + 2)).Prime :=
    (MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime (n + 2))
  have hdvd : Mullin.seq (n + 2) ∣ prod (n + 1) + 1 := seq_succ_dvd_euclid (n + 1)
  have h2 : 2 ∣ prod (n + 1) := by
    have := seq_dvd_prod 0 (n + 1) (Nat.zero_le _); rwa [seq_zero] at this
  have h3 : 3 ∣ prod (n + 1) := by
    have := seq_dvd_prod 1 (n + 1) (by omega); rwa [seq_one] at this
  have hp2 : Mullin.seq (n + 2) ≠ 2 := by
    intro h
    have h' : 2 ∣ prod (n + 1) + 1 := by rw [← h]; exact hdvd
    have := (Nat.dvd_add_right h2).mp h'
    omega
  have hp3 : Mullin.seq (n + 2) ≠ 3 := by
    intro h
    have h' : 3 ∣ prod (n + 1) + 1 := by rw [← h]; exact hdvd
    have := (Nat.dvd_add_right h3).mp h'
    omega
  have h5 : 5 ≤ Mullin.seq (n + 2) := by
    have := hprime.two_le; have := hprime.eq_two_or_odd; omega
  by_contra hne
  have hmod : Mullin.seq (n + 2) % 3 = 2 := by
    rcases Nat.lt_or_ge (Mullin.seq (n + 2) % 3) 1 with h0 | h0
    · exfalso
      have hd3 : 3 ∣ Mullin.seq (n + 2) := Nat.dvd_of_mod_eq_zero (by omega)
      rcases hprime.eq_one_or_self_of_dvd 3 hd3 with h | h
      · omega
      · exact hp3 h.symm
    · omega
  have hsq : Mullin.seq (n + 2) ^ 2 ∣ prod (n + 1) + 1 :=
    sq_dvd_of_confined hc hprime hmod h5 hdvd
  have hc2 : Mullin.seq (n + 2) ∣ cofactor (n + 1) := by
    have hE : prod (n + 1) + 1 = Mullin.seq (n + 2) * cofactor (n + 1) :=
      (seq_mul_cofactor (n + 1)).symm
    rw [hE, pow_two] at hsq
    exact Nat.dvd_of_mul_dvd_mul_left hprime.pos hsq
  obtain ⟨s, hs⟩ := hc'
  have hcof : 4 * (cofactor (n + 1) : ℤ) = 3 * s ^ 2 + 1 := by
    unfold disc at hs; linarith
  have : Fact (Nat.Prime (Mullin.seq (n + 2))) := ⟨hprime⟩
  apply not_isSquare_neg_three hmod h5
  have hz : ((3 * s ^ 2 + 1 : ℤ) : ZMod (Mullin.seq (n + 2))) = 0 := by
    rw [← hcof]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ((Int.natCast_dvd_natCast.mpr hc2).mul_left 4)
  push_cast at hz
  refine ⟨3 * (s : ZMod (Mullin.seq (n + 2))), ?_⟩
  push_cast
  linear_combination (-3 : ZMod (Mullin.seq (n + 2))) * hz

/-- The orbit is confined from some stage on. -/
def ConfinedRun : Prop := ∃ N, ∀ n, N ≤ n → Confined n

/-- **A confined run refutes MC**: no prime `≡ 2 (mod 3)` is ever a multiplier past the start
of the run, so a Dirichlet prime `q ≡ 2 (mod 3)` beyond the bag is missing. -/
theorem not_mc_of_confinedRun (h : ConfinedRun) : ¬ MullinConjecture := by
  obtain ⟨N, hN⟩ := h
  intro hmc
  obtain ⟨q, hqB, hq, hq3⟩ := QuadraticStep.exists_prime_two_mod_three_gt (prod (N + 2))
  obtain ⟨k, hk⟩ := hmc q ((MullinGroup.isPrime_iff_natPrime q).mpr hq)
  have hk3 : N + 3 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hdvd : Mullin.seq k ∣ prod (N + 2) := seq_dvd_prod k (N + 2) (by omega)
    rw [hk] at hdvd
    exact absurd (Nat.le_of_dvd (by have := prod_ge_two (N + 2); omega) hdvd) (by omega)
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have := multiplier_one_mod_three_of_confined_pair (hN n (by omega)) (hN (n + 1) (by omega))
  rw [hk] at this
  omega

/-- **Under the dichotomy conjecture a confined run is eventually a Sylvester tower**: question
(3) of the memo is a consequence of the conjecture.

Note (2026-11-10): confinement enters this proof only through `not_mc_of_confinedRun`, i.e.
through `¬ MullinConjecture`.  The theorem is the instance at `ConfinedRun` of the general
fact "`DichotomyConjecture` and `¬ MC` give perpetual primality" (the dichotomy says the growth
constant is positive or MC holds), and says nothing specific about the structure of a confined
run: no step of the argument relates the confined stages to the tower. -/
theorem perpetual_of_confinedRun_of_dichotomy (hd : Dichotomy.DichotomyConjecture)
    (h : ConfinedRun) : ∃ N, AutonomousBranch.PerpetualPrimality N := by
  rw [← DefectTelescope.growthConstant_pos_iff_perpetualPrimality]
  by_contra hle
  push Not at hle
  have h0 : DefectTelescope.growthConstant = 0 :=
    le_antisymm hle DefectTelescope.growthConstant_nonneg
  exact not_mc_of_confinedRun h (Dichotomy.mc_of_dichotomy hd h0)

/-! ## The shifted-tower family: an algebraic source of confined pairs

The search of memo §12.3 found composite confined stages whose successor is again confined
along the line `s = (4p+5)/3`.  It is an identity: with `p = 3k + 1`,

    (p c − 1) p + 1 = p' c',   c = 12k² + 18k + 7,  p' = p² + 3p + 3 = 9k² + 15k + 7,  c' = 12k² + 6k + 1,

and `4c − 1 = 3(4k+3)²`, `4c' − 1 = 3(4k+1)²` are both cuban.  So whenever `E_n = p·c` with
`p = lpf E_n` and `p² + 3p + 3 = lpf E_{n+1}` (three quadratics in `k` simultaneously prime, a
Schinzel-type condition), stages `n` and `n + 1` are both confined and composite.  The
"coincidence" of a confined successor therefore has an algebraic sub-locus — the special
subvariety inside the unlikely locus, exactly as Zilber–Pink predicts. -/

/-- The shifted-tower identity. -/
theorem shifted_tower_identity (k : ℕ) :
    (3 * k + 1) ^ 2 * (12 * k ^ 2 + 18 * k + 7) = (9 * k ^ 2 + 15 * k + 7) * (12 * k ^ 2 + 6 * k + 1) + 3 * k := by
  ring

/-- **The shifted-tower family gives confined pairs.**  If `E_n = (3k+1)(12k²+18k+7)` with
multiplier `3k + 1` and next multiplier `9k² + 15k + 7`, then stages `n` and `n+1` are confined. -/
theorem confined_pair_of_shifted_tower {n k : ℕ}
    (hE : prod n + 1 = (3 * k + 1) * (12 * k ^ 2 + 18 * k + 7))
    (hp : Mullin.seq (n + 1) = 3 * k + 1) (hp' : Mullin.seq (n + 2) = 9 * k ^ 2 + 15 * k + 7) :
    Confined n ∧ Confined (n + 1) := by
  have hc : cofactor n = 12 * k ^ 2 + 18 * k + 7 := by
    unfold cofactor; rw [hE, hp, Nat.mul_div_cancel_left _ (by omega)]
  have hE' : prod (n + 1) + 1 = (9 * k ^ 2 + 15 * k + 7) * (12 * k ^ 2 + 6 * k + 1) := by
    have h1 : prod (n + 1) = prod n * Mullin.seq (n + 1) := prod_succ n
    have h2 : prod n = (3 * k + 1) * (12 * k ^ 2 + 18 * k + 7) - 1 := by omega
    rw [h1, h2, hp]
    have := shifted_tower_identity k
    have hpos : 1 ≤ (3 * k + 1) * (12 * k ^ 2 + 18 * k + 7) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    zify [hpos] at *
    nlinarith [this]
  have hc' : cofactor (n + 1) = 12 * k ^ 2 + 6 * k + 1 := by
    unfold cofactor; rw [hE', hp', Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨⟨4 * k + 3, ?_⟩, ⟨4 * k + 1, ?_⟩⟩
  · unfold disc; rw [hc]; push_cast; ring
  · unfold disc; rw [hc']; push_cast; ring

end Confinement

end
