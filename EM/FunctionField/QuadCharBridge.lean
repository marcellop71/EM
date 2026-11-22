import EM.IK.GRHStatements
import EM.FunctionField.StableCount
import Mathlib.NumberTheory.Chebyshev

/-!
# From the GRH bound for `ψ(x, χ)` to sums of a quadratic symbol over primes

`StableCount.QuadPrimeSumBound C'` asks for `|∑_{p ≤ x} (D / p)| ≤ C' √x log²(|D| x)` for every
non-square integer `D`. `IK.GRHPsiBound C` is the bound `|ψ(x, χ)| ≤ C √x log²(N x)` for every
non-principal Dirichlet character `χ` mod `N`. This file proves that the second implies the
first, with `C' = 9 (C + 2) / log 2 + 3 / log² 2`.

## The steps

1. **A negative symbol.** If `D` is not a square, there is an odd `n` with `(D / n) = −1`
   (`exists_odd_jacobiSym_eq_neg_one`). Write `|D| = b² a` with `a` squarefree. If an odd prime
   `p` divides `a`, then `D = p^k u` with `k` odd and `p ∤ u`; take `n ≡ 1 mod 8|u|` and `n` a
   non-residue mod `p`, and use quadratic reciprocity. Otherwise `D ∈ {−1, 2, −2} · b²`, and `n`
   coprime to `b` with `n ≡ 3` or `5 mod 8` works. No prime `n` is needed.
2. **The character.** For odd `n` the symbol `(D / n)` depends only on `n mod 4|D|`
   (`jacobiSym.mod_right`), so `a ↦ (D / a)` on the units of `ℤ/4|D|` and `0` elsewhere is a
   Dirichlet character `χ_D` mod `4|D|` (`chiZ`, `chiC`), non-principal by step 1.
3. **From `ψ` to primes.** `ψ(n, χ_D)` and `θ(n, χ_D) = ∑_{p ≤ n} χ_D(p) log p` differ by at most
   `ψ(n) − θ(n) ≤ 2 √n log n` (Mathlib's Chebyshev file). A discrete Abel summation
   (`abs_sum_le_of_abs_sum_mul_log_le`) removes the weight `log p` at the cost of a factor
   `1 / log 2`. Finally `χ_D(p)` and `(D / p)` differ only at the primes dividing `4|D|`, of
   which there are at most `log(4|D|) / log 2`.

## Main result

* `quadPrimeSumBound_of_grhPsiBound` — `IK.GRHPsiBound C → ∃ C', StableCount.QuadPrimeSumBound C'`
  for `C ≥ 0`.
-/

namespace FunctionFieldAnalog

namespace QuadCharBridge

open Finset

/-! ## 1. A non-square has a negative symbol -/

/-- For `b ≠ 0` there is `n ≡ c mod 8` which, when `c` is odd, is coprime to `b`. -/
theorem exists_mod_eight_coprime {b : ℕ} (hb : b ≠ 0) (c : ℕ) :
    ∃ n : ℕ, n % 8 = c % 8 ∧ (Odd c → n.Coprime b) := by
  obtain ⟨e, b', hb', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb 2 (by norm_num)
  have hco2 : Nat.Coprime 2 b' := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hb'
  have hco : Nat.Coprime 8 b' := Nat.Coprime.pow_left 3 hco2
  obtain ⟨n, h8, hb1⟩ := Nat.chineseRemainder hco c 1
  refine ⟨n, h8, fun hc => ?_⟩
  have hodd : Odd n := by
    have h8' : n % 8 = c % 8 := h8
    rw [Nat.odd_iff] at hc ⊢
    omega
  have h1 : n.Coprime b' := by
    have := hb1.gcd_eq
    rw [Nat.gcd_one_left] at this
    exact this
  exact Nat.Coprime.mul_right (Nat.Coprime.pow_right e hodd.coprime_two_right) h1

/-- If `(u / n) = −1` for every `n ≡ c mod 8` (`c` odd), then `u b²` has a negative symbol at
    some odd `n`. -/
theorem exists_neg_of_mul_sq (u : ℤ) (c : ℕ) (hc : Odd c)
    (hu : ∀ n : ℕ, n % 8 = c % 8 → jacobiSym u n = -1) {b : ℕ} (hb : b ≠ 0) :
    ∃ n : ℕ, Odd n ∧ jacobiSym (u * (b : ℤ) ^ 2) n = -1 := by
  obtain ⟨n, hn, hco⟩ := exists_mod_eight_coprime hb c
  refine ⟨n, ?_, ?_⟩
  · rw [Nat.odd_iff] at hc ⊢
    omega
  · have hg : Int.gcd (b : ℤ) (n : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact (hco hc).symm
    rw [jacobiSym.mul_left, hu n hn, jacobiSym.sq_one' hg, mul_one]

/-- If `D = p^k u` with `p` an odd prime, `k` odd and `p ∤ u ≠ 0`, then `(D / n) = −1` for some
    odd `n`: take `n ≡ 1 mod 8|u|` and `n` a non-residue mod `p`. -/
theorem exists_neg_of_odd_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : Odd k)
    {u : ℤ} (hu0 : u ≠ 0) (hpu : ¬ p ∣ u.natAbs) :
    ∃ n : ℕ, Odd n ∧ jacobiSym ((p : ℤ) ^ k * u) n = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have hco : Nat.Coprime p (8 * u.natAbs) := by
    refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu)
    exact Nat.Coprime.pow_right 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨n, hnp, hnu⟩ := Nat.chineseRemainder hco a.val 1
  have hupos : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  have h8 : n % 8 = 1 := Nat.ModEq.of_mul_right _ hnu
  have h4u : n % (4 * u.natAbs) = 1 := by
    have h : n ≡ 1 [MOD 4 * u.natAbs] := Nat.ModEq.of_dvd ⟨2, by ring⟩ hnu
    rw [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < 4 * u.natAbs by omega)] at h
    exact h
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h4 : n % 4 = 1 := by omega
  refine ⟨n, hodd, ?_⟩
  have hu1 : jacobiSym u n = 1 := by
    rw [jacobiSym.mod_right u hodd, h4u, jacobiSym.one_right]
  have hpn : jacobiSym p n = -1 := by
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four h4 (hp.odd_of_ne_two hp2),
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have hcast : ((n : ℤ) : ZMod p) = a := by
      rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff n a.val p).mpr hnp,
        ZMod.natCast_zmod_val]
    rwa [hcast]
  rw [jacobiSym.mul_left, jacobiSym.pow_left, hpn, hu1, hk.neg_one_pow, mul_one]

/-- **A non-square integer has a negative Jacobi symbol** at some odd modulus. -/
theorem exists_odd_jacobiSym_eq_neg_one {D : ℤ} (hD : ¬ IsSquare D) :
    ∃ n : ℕ, Odd n ∧ jacobiSym D n = -1 := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact hD ⟨0, by simp⟩
  have hDabs : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  obtain ⟨b, a, hab, hsf⟩ := exists_sq_mul_squarefree D.natAbs
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hDabs (by rw [← hab]; simp)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hDabs (by rw [← hab]; simp)
  have hDsign : D = D.sign * ((b ^ 2 * a : ℕ) : ℤ) := by
    rw [hab]
    exact (Int.sign_mul_natAbs D).symm
  by_cases hodd : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ a
  · obtain ⟨p, hp, hp2, a', rfl⟩ := hodd
    have hpa' : ¬ p ∣ a' := by
      rintro ⟨c, rfl⟩
      have := hsf p ⟨c, by ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
    obtain ⟨j, b', hb', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb0 p hp.ne_one
    have hDeq : D = (p : ℤ) ^ (2 * j + 1) * (D.sign * ((b' ^ 2 * a' : ℕ) : ℤ)) := by
      conv_lhs => rw [hDsign]
      push_cast
      ring
    have hu0 : D.sign * ((b' ^ 2 * a' : ℕ) : ℤ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hDeq
      exact hD0 hDeq
    have hpu : ¬ p ∣ (D.sign * ((b' ^ 2 * a' : ℕ) : ℤ)).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hD0, one_mul, Int.natAbs_natCast]
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact hb' (hp.dvd_of_dvd_pow h)
      · exact hpa' h
    obtain ⟨n, hn, hJ⟩ := exists_neg_of_odd_prime_pow hp hp2 (k := 2 * j + 1) ⟨j, rfl⟩ hu0 hpu
    exact ⟨n, hn, by rw [hDeq]; exact hJ⟩
  · push Not at hodd
    have hapow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) ha0
      (fun {d} hd hdvd => by
        by_contra h
        exact hodd d hd h hdvd)
    have ha12 : a = 1 ∨ a = 2 := by
      generalize a.primeFactorsList.length = k at hapow
      rcases k with _ | _ | k
      · left; simpa using hapow
      · right; simpa using hapow
      · exfalso
        have := hsf 2 ⟨2 ^ k, by rw [hapow]; ring⟩
        exact absurd (Nat.isUnit_iff.mp this) (by norm_num)
    have h3 : ∀ n : ℕ, n % 8 = 3 % 8 → jacobiSym (-1) n = -1 := fun n hn => by
      rw [jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
        ZMod.χ₄_nat_three_mod_four (by omega)]
    have h5 : ∀ n : ℕ, n % 8 = 5 % 8 → jacobiSym 2 n = -1 := fun n hn => by
      rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
      split_ifs <;> first | rfl | omega
    have h5' : ∀ n : ℕ, n % 8 = 5 % 8 → jacobiSym (-2) n = -1 := fun n hn => by
      rw [jacobiSym.at_neg_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈'_nat_eq_if_mod_eight]
      split_ifs <;> first | rfl | omega
    rcases lt_or_gt_of_ne hD0 with hneg | hpos
    · have hs : D.sign = -1 := Int.sign_eq_neg_one_of_neg hneg
      rcases ha12 with rfl | rfl
      · have hDeq : D = -1 * (b : ℤ) ^ 2 := by
          conv_lhs => rw [hDsign, hs]
          push_cast
          ring
        rw [hDeq]
        exact exists_neg_of_mul_sq (-1) 3 (by decide) h3 hb0
      · have hDeq : D = -2 * (b : ℤ) ^ 2 := by
          conv_lhs => rw [hDsign, hs]
          push_cast
          ring
        rw [hDeq]
        exact exists_neg_of_mul_sq (-2) 5 (by decide) h5' hb0
    · have hs : D.sign = 1 := Int.sign_eq_one_of_pos hpos
      rcases ha12 with rfl | rfl
      · exfalso
        refine hD ⟨(b : ℤ), ?_⟩
        conv_lhs => rw [hDsign, hs]
        push_cast
        ring
      · have hDeq : D = 2 * (b : ℤ) ^ 2 := by
          conv_lhs => rw [hDsign, hs]
          push_cast
          ring
        rw [hDeq]
        exact exists_neg_of_mul_sq 2 5 (by decide) h5 hb0

/-! ## 2. The symbol as a Dirichlet character mod `4|D|` -/

/-- A unit of `ℤ/4|D|` has an odd representative. -/
theorem odd_val_of_isUnit {D : ℤ} {a : ZMod (4 * D.natAbs)} (ha : IsUnit a) : Odd a.val := by
  obtain ⟨u, rfl⟩ := ha
  exact (Nat.Coprime.coprime_dvd_right ⟨2 * D.natAbs, by ring⟩
    (ZMod.val_coe_unit_coprime u)).odd_of_right

open Classical in
/-- The character `χ_D` mod `4|D|` with integer values: `(D / a)` at the units, `0` elsewhere. -/
noncomputable def chiZ (D : ℤ) : MulChar (ZMod (4 * D.natAbs)) ℤ where
  toFun a := if IsUnit a then jacobiSym D a.val else 0
  map_one' := by
    rw [ite_eq_left isUnit_one, ZMod.val_one_eq_one_mod,
      Nat.one_mod_eq_one.mpr (by omega), jacobiSym.one_right]
  map_mul' a b := by
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · have hoa := odd_val_of_isUnit ha
        have hob := odd_val_of_isUnit hb
        rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (ha.mul hb), ZMod.val_mul,
          ← jacobiSym.mod_right D (hoa.mul hob),
          jacobiSym.mul_right' D hoa.pos.ne' hob.pos.ne']
      · rw [ite_eq_right hb, ite_eq_right (fun h => hb (IsUnit.mul_iff.mp h).2), mul_zero]
    · rw [ite_eq_right ha, ite_eq_right (fun h => ha (IsUnit.mul_iff.mp h).1), zero_mul]
  map_nonunit' a ha := ite_eq_right ha

/-- `χ_D(n) = (D / n)` when `n` is coprime to `4|D|`, and `0` otherwise. -/
theorem chiZ_natCast (D : ℤ) (n : ℕ) :
    chiZ D (n : ZMod (4 * D.natAbs)) =
      if n.Coprime (4 * D.natAbs) then jacobiSym D n else 0 := by
  classical
  change (if IsUnit (n : ZMod (4 * D.natAbs)) then
    jacobiSym D (n : ZMod (4 * D.natAbs)).val else 0) = _
  by_cases h : n.Coprime (4 * D.natAbs)
  · have hodd : Odd n := (Nat.Coprime.coprime_dvd_right ⟨2 * D.natAbs, by ring⟩ h).odd_of_right
    rw [ite_eq_left h, ite_eq_left ((ZMod.isUnit_iff_coprime _ _).mpr h), ZMod.val_natCast,
      ← jacobiSym.mod_right D hodd]
  · rw [ite_eq_right h, ite_eq_right (fun hu => h ((ZMod.isUnit_iff_coprime _ _).mp hu))]

theorem abs_chiZ_le_one (D : ℤ) (n : ℕ) : |chiZ D (n : ZMod (4 * D.natAbs))| ≤ 1 := by
  rw [chiZ_natCast]
  split_ifs
  · rcases jacobiSym.trichotomy D n with h | h | h <;> rw [h] <;> norm_num
  · norm_num

/-- The character `χ_D` with complex values. -/
noncomputable def chiC (D : ℤ) : DirichletCharacter ℂ (4 * D.natAbs) :=
  (chiZ D).ringHomComp (Int.castRingHom ℂ)

theorem chiC_apply (D : ℤ) (a : ZMod (4 * D.natAbs)) : chiC D a = ((chiZ D a : ℤ) : ℂ) := rfl

/-- **`χ_D` is non-principal when `D` is not a square.** -/
theorem chiC_ne_one {D : ℤ} (hD : ¬ IsSquare D) : chiC D ≠ 1 := by
  obtain ⟨n, hodd, hn⟩ := exists_odd_jacobiSym_eq_neg_one hD
  have : NeZero n := ⟨hodd.pos.ne'⟩
  have hg : Int.gcd D n = 1 := by
    by_contra h
    rw [jacobiSym.eq_zero_iff_not_coprime.mpr h] at hn
    norm_num at hn
  have hco : n.Coprime (4 * D.natAbs) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 hodd.coprime_two_right) ?_
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast] at hg
    exact (Nat.coprime_comm.mp hg)
  intro h
  have h1 : chiC D (n : ZMod (4 * D.natAbs)) = 1 := by
    rw [h, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr hco)]
  rw [chiC_apply, chiZ_natCast, ite_eq_left hco, hn] at h1
  norm_num at h1

/-! ## 3. Discrete Abel summation: removing the weight `log` -/

/-- **Abel summation.** If `a 1 = 0` and the partial sums of `a k log k` up to every `n ≤ N`
    are at most `T` in absolute value, then `|∑_{k ≤ N} a k| ≤ T / log 2`. -/
theorem abs_sum_le_of_abs_sum_mul_log_le (a : ℕ → ℝ) (ha1 : a 1 = 0) (N : ℕ) {T : ℝ}
    (h : ∀ n, n ≤ N → |∑ k ∈ Icc 1 n, a k * Real.log k| ≤ T) :
    |∑ k ∈ Icc 1 N, a k| ≤ T / Real.log 2 := by
  have hT : 0 ≤ T := (abs_nonneg _).trans (h 0 (Nat.zero_le _))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set θ : ℕ → ℝ := fun n => ∑ k ∈ Icc 1 n, a k * Real.log k with hθ
  set g : ℕ → ℝ := fun n => (Real.log n)⁻¹ with hg
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have : ∑ k ∈ Icc 1 N, a k = 0 := by
      interval_cases N
      · simp
      · simp [ha1]
    rw [this, abs_zero]
    positivity
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  -- the summation-by-parts identity
  have key : ∀ m : ℕ, ∑ k ∈ Icc 1 (2 + m), a k =
      θ (2 + m) * g (2 + m) + ∑ i ∈ range m, θ (2 + i) * (g (2 + i) - g (2 + i + 1)) := by
    intro m
    induction m with
    | zero =>
      have hI : Icc 1 2 = {1, 2} := by decide
      simp only [hθ, hg, add_zero, range_zero, sum_empty, hI]
      rw [sum_pair (by norm_num), sum_pair (by norm_num), ha1]
      have : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
        rw [Nat.cast_ofNat]; exact hl2.ne'
      field_simp
      ring
    | succ m ih =>
      have hL : Real.log ((2 + m + 1 : ℕ) : ℝ) ≠ 0 := by
        refine (Real.log_pos ?_).ne'
        have : (1 : ℝ) < ((2 + m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 + m + 1)
        exact this
      have hθs : θ (2 + (m + 1)) = θ (2 + m) + a (2 + m + 1) * Real.log ((2 + m + 1 : ℕ) : ℝ) := by
        simp only [hθ]
        rw [← add_assoc, sum_Icc_succ_top (by omega)]
      rw [sum_range_succ, hθs]
      rw [show 2 + (m + 1) = 2 + m + 1 from rfl, sum_Icc_succ_top (by omega)]
      simp only [hg] at ih ⊢
      have : a (2 + m + 1) * Real.log ((2 + m + 1 : ℕ) : ℝ) *
          (Real.log ((2 + m + 1 : ℕ) : ℝ))⁻¹ = a (2 + m + 1) := by
        field_simp
      linear_combination ih - this
  have hgpos : ∀ i : ℕ, 0 ≤ g (2 + i) - g (2 + i + 1) := by
    intro i
    simp only [hg]
    have h1 : (0 : ℝ) < Real.log ((2 + i : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 2 + i))
    have h2 : Real.log ((2 + i : ℕ) : ℝ) ≤ Real.log ((2 + i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 + i))
        (by exact_mod_cast (by omega : 2 + i ≤ 2 + i + 1))
    exact sub_nonneg.mpr (inv_anti₀ h1 h2)
  have hgN : 0 ≤ g (2 + m) := by
    simp only [hg]
    exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 + m)))
  have htel : ∑ i ∈ range m, (g (2 + i) - g (2 + i + 1)) = g 2 - g (2 + m) := by
    have := sum_range_sub' (fun i => g (2 + i)) m
    simpa [add_assoc] using this
  rw [key m]
  calc |θ (2 + m) * g (2 + m) + ∑ i ∈ range m, θ (2 + i) * (g (2 + i) - g (2 + i + 1))|
      ≤ |θ (2 + m) * g (2 + m)| + ∑ i ∈ range m, |θ (2 + i) * (g (2 + i) - g (2 + i + 1))| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)
    _ ≤ T * g (2 + m) + ∑ i ∈ range m, T * (g (2 + i) - g (2 + i + 1)) := by
        refine add_le_add ?_ (sum_le_sum fun i hi => ?_)
        · rw [abs_mul, abs_of_nonneg hgN]
          exact mul_le_mul_of_nonneg_right (h _ le_rfl) hgN
        · rw [abs_mul, abs_of_nonneg (hgpos i)]
          exact mul_le_mul_of_nonneg_right (h _ (by have := mem_range.mp hi; omega)) (hgpos i)
    _ = T / Real.log 2 := by
        rw [← mul_sum, htel]
        simp only [hg, Nat.cast_ofNat]
        ring

/-! ## 4. From `ψ(x, χ_D)` to the sum over primes -/

open ArithmeticFunction in
/-- `|ψ(n, χ) − θ(n, χ)| ≤ 2 √n log n` for any weight `f` bounded by `1`: the difference is
    carried by the proper prime powers. -/
theorem abs_psi_sub_theta_twisted_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    |∑ k ∈ Icc 1 n, vonMangoldt k * f k -
        ∑ k ∈ Icc 1 n, (if k.Prime then f k else 0) * Real.log k| ≤
      2 * Real.sqrt n * Real.log n := by
  have hcheb := Chebyshev.psi_sub_theta_le (x := (n : ℝ)) (by exact_mod_cast hn)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast] at hcheb
  have hIoc : Ioc 0 n = Icc 1 n := by
    ext k
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hIoc, sum_filter] at hcheb
  refine le_trans ?_ hcheb
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  by_cases hk : k.Prime
  · rw [ite_eq_left hk, ite_eq_right (not_not.mpr hk), vonMangoldt_apply_prime hk]
    rw [show Real.log k * f k - f k * Real.log k = 0 by ring, abs_zero]
  · rw [ite_eq_right hk, ite_eq_left hk, zero_mul, sub_zero, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (hf k)

/-- The number of primes dividing `M ≠ 0` is at most `log M / log 2`. -/
theorem card_primeFactors_le_log {M : ℕ} (hM : M ≠ 0) :
    (M.primeFactors.card : ℝ) ≤ Real.log M / Real.log 2 := by
  have h1 : 2 ^ M.primeFactors.card ≤ M := by
    refine le_trans (pow_card_le_prod _ (fun p => p) 2 fun p hp => ?_)
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.prod_primeFactors_dvd M))
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2, ← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast h1)

/-- The sum of `χ_D` over the primes `p ≤ N` differs from the sum of `(D / p)` by at most the
    number of primes dividing `4|D|`. -/
theorem abs_charSum_sub_le {D : ℤ} (hD0 : D ≠ 0) (N : ℕ) :
    |(StableCount.charSum D N : ℝ) - ∑ k ∈ Icc 1 N,
        (if k.Prime then ((chiZ D (k : ZMod (4 * D.natAbs)) : ℤ) : ℝ) else 0)| ≤
      Real.log ((4 * D.natAbs : ℕ) : ℝ) / Real.log 2 := by
  have hM : 4 * D.natAbs ≠ 0 := by
    have := Int.natAbs_pos.mpr hD0
    omega
  refine le_trans ?_ (card_primeFactors_le_log hM)
  rw [← sum_filter, StableCount.charSum, StableCount.primesLE, Int.cast_sum, ← sum_sub_distrib]
  calc |∑ p ∈ (Icc 1 N).filter Nat.Prime,
          ((jacobiSym D p : ℝ) - ((chiZ D (p : ZMod (4 * D.natAbs)) : ℤ) : ℝ))|
      ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          |(jacobiSym D p : ℝ) - ((chiZ D (p : ZMod (4 * D.natAbs)) : ℤ) : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          (if p ∈ (4 * D.natAbs).primeFactors then (1 : ℝ) else 0) := by
        refine sum_le_sum fun p hp => ?_
        have hpp : p.Prime := (mem_filter.mp hp).2
        rw [chiZ_natCast]
        by_cases hco : p.Coprime (4 * D.natAbs)
        · rw [ite_eq_left hco, sub_self, abs_zero]
          split_ifs <;> norm_num
        · have hdvd : p ∣ 4 * D.natAbs := by
            by_contra hnd
            exact hco ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hnd)
          rw [ite_eq_right hco, ite_eq_left (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hM⟩),
            Int.cast_zero, sub_zero]
          rcases jacobiSym.trichotomy D p with h | h | h <;> rw [h] <;> norm_num
    _ = (((Icc 1 N).filter Nat.Prime).filter (· ∈ (4 * D.natAbs).primeFactors)).card := by
        rw [sum_boole]
    _ ≤ (4 * D.natAbs).primeFactors.card := by
        exact_mod_cast card_le_card fun p hp => (mem_filter.mp hp).2

/-- **The GRH bound for `ψ(x, χ)` gives the prime-sum bound for quadratic symbols.**
    If `|ψ(x, χ)| ≤ C √x log²(N x)` for every non-principal Dirichlet character `χ` mod `N` and
    every `x ≥ 2`, then for every non-square integer `D` and every natural `x ≥ 2`,
    `|∑_{p ≤ x} (D / p)| ≤ C' √x log²(|D| x)` with `C' = 9 (C + 2) / log 2 + 3 / log² 2`. -/
theorem quadPrimeSumBound_of_grhPsiBound {C : ℝ} (hC : 0 ≤ C) (h : IK.GRHPsiBound C) :
    ∃ C', StableCount.QuadPrimeSumBound C' := by
  refine ⟨9 * (C + 2) / Real.log 2 + 3 / Real.log 2 ^ 2, fun D hD N hN => ?_⟩
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact hD ⟨0, by simp⟩
  have hDabs : 1 ≤ D.natAbs := Int.natAbs_pos.mpr hD0
  have hNe : NeZero (4 * D.natAbs) := ⟨by omega⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDreal : (1 : ℝ) ≤ |(D : ℝ)| := by
    have : ((D.natAbs : ℕ) : ℝ) = |(D : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← this]
    exact_mod_cast hDabs
  have hMcast : ((4 * D.natAbs : ℕ) : ℝ) = 4 * |(D : ℝ)| := by
    rw [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
    norm_num
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM4 : (4 : ℝ) ≤ ((4 * D.natAbs : ℕ) : ℝ) := by
    rw [hMcast]
    linarith
  set f : ℕ → ℝ := fun k => ((chiZ D (k : ZMod (4 * D.natAbs)) : ℤ) : ℝ) with hf
  have hfle : ∀ k, |f k| ≤ 1 := fun k => by
    simp only [hf]
    rw [← Int.cast_abs]
    exact_mod_cast abs_chiZ_le_one D k
  set lm : ℝ := Real.log (((4 * D.natAbs : ℕ) : ℝ) * N) with hlm
  set s : ℝ := Real.sqrt N with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- the bound for the log-weighted prime sums
  have hθ : ∀ n, n ≤ N →
      |∑ k ∈ Icc 1 n, (if k.Prime then f k else 0) * Real.log k| ≤ (C + 2) * s * lm ^ 2 := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have h0 : ∑ k ∈ Icc 1 n, (if k.Prime then f k else 0) * Real.log k = 0 := by
        interval_cases n <;> simp
      rw [h0, abs_zero]
      positivity
    · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
      have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
      have hpsi := h (4 * D.natAbs) (chiC D) (chiC_ne_one hD) (n : ℝ) hn2
      have hcast : IK.psiChi (chiC D) (n : ℝ) =
          ((∑ k ∈ Icc 1 n, ArithmeticFunction.vonMangoldt k * f k : ℝ) : ℂ) := by
        simp only [IK.psiChi, Nat.floor_natCast, chiC_apply, hf]
        push_cast
        rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hpsi
      have hdiff := abs_psi_sub_theta_twisted_le f hfle (n := n) (by omega)
      have hMn : (8 : ℝ) ≤ ((4 * D.natAbs : ℕ) : ℝ) * n := by nlinarith
      have hln1 : 1 ≤ Real.log (((4 * D.natAbs : ℕ) : ℝ) * n) := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        have := Real.exp_one_lt_d9
        linarith
      have hln_le : Real.log (((4 * D.natAbs : ℕ) : ℝ) * n) ≤ lm :=
        Real.log_le_log (by linarith) (by nlinarith)
      have hlogn : Real.log n ≤ Real.log (((4 * D.natAbs : ℕ) : ℝ) * n) :=
        Real.log_le_log (by linarith) (by nlinarith)
      have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
      have hsn : Real.sqrt n ≤ s := Real.sqrt_le_sqrt hnN
      have hsn0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
      have hsq : Real.log (((4 * D.natAbs : ℕ) : ℝ) * n) ^ 2 ≤ lm ^ 2 :=
        pow_le_pow_left₀ (by linarith) hln_le 2
      have hA : C * Real.sqrt n * Real.log (((4 * D.natAbs : ℕ) : ℝ) * n) ^ 2 ≤
          C * s * lm ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsn hC) hsq (by positivity) (by positivity)
      have hB : 2 * Real.sqrt n * Real.log n ≤ 2 * s * lm ^ 2 := by
        have h1 : Real.log (n : ℝ) ≤ lm ^ 2 := by nlinarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsn (by norm_num)) h1 hlogn0
          (by positivity)
      rw [abs_le] at hpsi hdiff ⊢
      constructor <;> nlinarith [hpsi.1, hpsi.2, hdiff.1, hdiff.2]
  have hS := abs_sum_le_of_abs_sum_mul_log_le (fun k => if k.Prime then f k else 0)
    (by simp [Nat.not_prime_one]) N hθ
  have hdiff := abs_charSum_sub_le hD0 N
  -- sizes of the logarithms
  set L : ℝ := Real.log (|(D : ℝ)| * N) with hL
  have hX : (2 : ℝ) ≤ |(D : ℝ)| * N := by nlinarith
  have hl2L : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hX
  have hL0 : 0 ≤ L := hl2.le.trans hl2L
  have hlm_eq : lm = 2 * Real.log 2 + L := by
    rw [hlm, hMcast, mul_assoc, Real.log_mul (by norm_num) (by linarith),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat]
  have hlm_le : lm ≤ 3 * L := by linarith
  have hlm0 : 0 ≤ lm := by linarith
  have hlM : Real.log ((4 * D.natAbs : ℕ) : ℝ) ≤ 3 * L :=
    (Real.log_le_log (by linarith) (by nlinarith)).trans hlm_le
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
  have hcs : |(StableCount.charSum D N : ℝ)| ≤
      (C + 2) * s * lm ^ 2 / Real.log 2 + Real.log ((4 * D.natAbs : ℕ) : ℝ) / Real.log 2 := by
    rw [abs_le] at hS hdiff ⊢
    constructor <;> linarith [hS.1, hS.2, hdiff.1, hdiff.2]
  have hT : (C + 2) * s * lm ^ 2 / Real.log 2 ≤ (C + 2) * s * (3 * L) ^ 2 / Real.log 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlm0 hlm_le 2) (by positivity)) hl2.le
  have hE : Real.log ((4 * D.natAbs : ℕ) : ℝ) / Real.log 2 ≤
      3 * s * L ^ 2 / Real.log 2 ^ 2 := by
    have e1 : Real.log ((4 * D.natAbs : ℕ) : ℝ) * Real.log 2 ≤ 3 * L * L :=
      mul_le_mul hlM hl2L hl2.le (by positivity)
    have e2 : 3 * L * L ≤ 3 * s * L ^ 2 := by nlinarith [sq_nonneg L]
    have e3 := mul_le_mul_of_nonneg_right (e1.trans e2) hl2.le
    rw [div_le_div_iff₀ hl2 (pow_pos hl2 2)]
    linarith
  have hring : (9 * (C + 2) / Real.log 2 + 3 / Real.log 2 ^ 2) * s * L ^ 2 =
      (C + 2) * s * (3 * L) ^ 2 / Real.log 2 + 3 * s * L ^ 2 / Real.log 2 ^ 2 := by
    ring
  rw [hring]
  linarith

end QuadCharBridge

end FunctionFieldAnalog
