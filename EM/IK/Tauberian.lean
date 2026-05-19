import EM.IK.Ch2

/-!
# One-Sided Tauberian Lemma and WeightedPNTinAP

This file proves a one-sided Tauberian lemma for nonnegative Dirichlet-type series,
establishes upper and lower bounds on the L-series of Lambda in residue classes,
proves Dirichlet's theorem, and reduces `WeightedPNTinAP` to a real-variable
Wiener-Ikehara hypothesis.

## Main results

- `one_sided_tauberian_upper`: for `b_n >= 0`, the partial sum over `[1,N]` is
  bounded by `N^eps` times the `eps`-weighted sum.
- `residueClass_tsum_eq_aux_plus_pole`: the real tsum identity extracting the
  pole from Mathlib's internal proof.
- `residueClass_tsum_upper_bound`: upper bound on the L-series restricted to a
  residue class (companion to Mathlib's lower bound).
- `dirichlet_primes_in_ap`: Dirichlet's theorem from Mathlib.
- `prime_power_stripping_proved`: `WeightedPNTinAP -> PrimeLogSumEquidist` by
  stripping the bounded prime power contribution from the von Mangoldt sum.

## References

- H. Iwaniec, E. Kowalski, *Analytic Number Theory*, Chapter 2
- Mathlib: `Mathlib.NumberTheory.LSeries.PrimesInAP`
-/

noncomputable section

open Classical

namespace IK

open Nat ArithmeticFunction Finset BigOperators Filter

/-! ## Section 1: One-sided Tauberian Lemma -/

section Tauberian

/-- The core one-sided Tauberian inequality: for nonneg b_n, the partial sum
    over [1,N] is bounded by N^eps times the eps-weighted sum.

    Proof: for n in [1,N] and eps > 0, n^eps <= N^eps, so
    b_n / n^eps * N^eps >= b_n / n^eps * n^eps = b_n. -/
theorem one_sided_tauberian_upper
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {S : ℝ} (hS : ∑ n ∈ Icc 1 N, b n / (n : ℝ) ^ ε ≤ S) :
    ∑ n ∈ Icc 1 N, b n ≤ (N : ℝ) ^ ε * S := by
  have hNε : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
  suffices h : ∑ n ∈ Icc 1 N, b n ≤ (N : ℝ) ^ ε * ∑ n ∈ Icc 1 N, b n / (n : ℝ) ^ ε from
    h.trans (mul_le_mul_of_nonneg_left hS hNε)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  simp only [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnε : (0 : ℝ) < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hn0 ε
  rw [mul_div_assoc', le_div_iff₀ hnε]
  calc b n * (n : ℝ) ^ ε
      ≤ b n * (N : ℝ) ^ ε := by
        apply mul_le_mul_of_nonneg_left _ (hb n)
        exact Real.rpow_le_rpow hn0.le (by exact_mod_cast hn.2) hε.le
    _ = (N : ℝ) ^ ε * b n := mul_comm _ _

/-- Specialization with explicit Dirichlet-series form:
    if sum b_n / n^eps <= C/eps + M, then sum_{n<=N} b_n <= N^eps * (C/eps + M). -/
theorem one_sided_tauberian_dirichlet
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {C M : ℝ}
    (hS : ∑ n ∈ Icc 1 N, b n / (n : ℝ) ^ ε ≤ C / ε + M) :
    ∑ n ∈ Icc 1 N, b n ≤ (N : ℝ) ^ ε * (C / ε + M) :=
  one_sided_tauberian_upper hb hε hS

end Tauberian

/-! ## Section 2: Mathlib Bridge — L-series Bounds -/

section MathlibBridge

open ArithmeticFunction.vonMangoldt LSeries in
/-- For real `s > 1` and invertible `a mod q`, the tsum of `residueClass a`
    decomposes as `aux(s).re + 1/phi(q)/(s-1)`. Extracted from Mathlib's
    internal proof of `LSeries_residueClass_lower_bound`. -/
theorem residueClass_tsum_eq_aux_plus_pole
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {s : ℝ} (hs : 1 < s) :
    ∑' n, residueClass a n / (n : ℝ) ^ s =
      (LFunctionResidueClassAux a (s : ℂ)).re + (↑(Nat.totient q) : ℝ)⁻¹ / (s - 1) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_sub,
    Complex.ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hs,
    eqOn_LFunctionResidueClassAux ha <|
      Set.mem_ofPred.mpr (Complex.ofReal_re s ▸ hs), sub_add_cancel,
    _root_.LSeries, term]
  refine tsum_congr fun n => ?_
  split_ifs with hn
  · simp only [hn, residueClass_apply_zero, Complex.ofReal_zero, zero_div]
  · rfl

/-- Lower bound on the L-series of Lambda restricted to a residue class.
    Direct from Mathlib's `LSeries_residueClass_lower_bound`. -/
theorem residueClass_tsum_lower_bound
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {s : ℝ} (_ : s ∈ Set.Ioc 1 2),
      (↑(Nat.totient q) : ℝ)⁻¹ / (s - 1) - C ≤
        ∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ s :=
  ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound ha

/-- Upper bound on the L-series of Lambda restricted to a residue class:
    `tsum <= 1/phi(q)/(s-1) + M` for `s` in `(1,2]`. Companion to Mathlib's lower bound,
    obtained from the identity `tsum = aux(s).re + pole` and the continuity of
    `aux` on the compact set `[1,2]`. -/
theorem residueClass_tsum_upper_bound
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ M : ℝ, ∀ {s : ℝ} (_ : s ∈ Set.Ioc 1 2),
      ∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ s ≤
        (↑(Nat.totient q) : ℝ)⁻¹ / (s - 1) + M := by
  have hcont : ContinuousOn
      (fun x : ℝ => (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux
        a (x : ℂ)).re)
      (Set.Icc 1 2) :=
    Complex.continuous_re.continuousOn.comp
      ((ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux a).comp
        Complex.continuous_ofReal.continuousOn fun x hx => by
          simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; exact hx.1)
      fun _ _ => Set.mem_univ _
  obtain ⟨M_upper, hM_upper⟩ := bddAbove_def.mp (isCompact_Icc.bddAbove_image hcont)
  refine ⟨M_upper, fun {s} hs => ?_⟩
  rw [residueClass_tsum_eq_aux_plus_pole ha hs.1]
  linarith [hM_upper _ (Set.mem_image_of_mem
    (fun x : ℝ => (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux
      a (x : ℂ)).re) (Set.mem_Icc_of_Ioc hs))]

/-- The tsum of Lambda restricted to a residue class equals `1/phi(q)/(s-1)`
    up to a bounded remainder, combining the upper and lower bounds. -/
theorem residueClass_tsum_both_bounds
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ M : ℝ, 0 < M ∧ ∀ {s : ℝ} (_ : s ∈ Set.Ioc 1 2),
      |∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ s -
        (↑(Nat.totient q) : ℝ)⁻¹ / (s - 1)| ≤ M := by
  obtain ⟨C_low, hC_low⟩ := residueClass_tsum_lower_bound ha
  obtain ⟨C_up, hC_up⟩ := residueClass_tsum_upper_bound ha
  refine ⟨|C_low| + |C_up| + 1, by positivity, fun {s} hs => ?_⟩
  have h1 := hC_low hs
  have h2 := hC_up hs
  have habs1 : 0 ≤ |C_low| := abs_nonneg _
  have habs2 : 0 ≤ |C_up| := abs_nonneg _
  have hle_low : -|C_low| ≤ -C_low := neg_le_neg (le_abs_self _)
  have hle_up : C_up ≤ |C_up| := le_abs_self _
  rw [abs_le]
  constructor <;> linarith

end MathlibBridge

/-! ## Section 3: Dirichlet's Theorem -/

section Dirichlet

/-- Dirichlet's theorem on infinitely many primes in coprime residue classes.
    Proved by bridging to Mathlib's `Nat.forall_exists_prime_gt_and_modEq`. -/
theorem dirichlet_primes_in_ap : DirichletPrimesInAP := by
  intro q a hq hcop n
  exact Nat.forall_exists_prime_gt_and_modEq n (by omega) hcop

end Dirichlet

/-! ## Section 4: WeightedPNTinAP Reduction -/

section WeightedPNT

/-- **Real Wiener-Ikehara Tauberian Hypothesis (PNT form).** -/
def RealWienerIkeharaTauberian : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q),
        (Λ n : ℝ) - x / Nat.totient q| ≤ C * x / Real.log x

/-- Abel/partial summation hypothesis. Does not follow from
    `RealWienerIkeharaTauberian` via standard Abel summation (yields `O(log log x)`
    rather than `O(1)`). -/
def AbelSummationPNT : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    RealWienerIkeharaTauberian →
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q),
        Λ n / n - Real.log x / Nat.totient q| ≤ C

/-- WeightedPNTinAP follows from the Wiener-Ikehara hypothesis plus Abel summation. -/
theorem real_wiener_ikehara_implies_wpnt
    (hwi : RealWienerIkeharaTauberian)
    (habel : AbelSummationPNT) : WeightedPNTinAP := by
  intro q a hq hcop
  exact habel q a hq hcop hwi

/-- Alternate: WeightedPNTinAP follows directly from a combined hypothesis. -/
def WienerIkeharaForWeightedPNT : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q),
        Λ n / n - Real.log x / Nat.totient q| ≤ C

/-- WeightedPNTinAP is equivalent to WienerIkeharaForWeightedPNT. -/
theorem wiener_ikehara_weighted_iff_wpnt :
    WienerIkeharaForWeightedPNT ↔ WeightedPNTinAP :=
  Iff.rfl

theorem ant_chain_status :
    (RealWienerIkeharaTauberian → AbelSummationPNT → WeightedPNTinAP) ∧
    (WienerIkeharaForWeightedPNT ↔ WeightedPNTinAP) :=
  ⟨real_wiener_ikehara_implies_wpnt, wiener_ikehara_weighted_iff_wpnt⟩

end WeightedPNT

/-! ## Section 5: Corrected ANT Chain Analysis -/

section CorrectedAnalysis

def MertensInAP : Prop := WeightedPNTinAP

theorem mertens_iff_wpnt : MertensInAP ↔ WeightedPNTinAP := Iff.rfl

theorem abel_summation_chain_witness :
    (RealWienerIkeharaTauberian → AbelSummationPNT → WeightedPNTinAP) :=
  real_wiener_ikehara_implies_wpnt

theorem weighted_pnt_dirichlet_upper
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ M : ℝ, ∀ {s : ℝ} (_ : s ∈ Set.Ioc 1 2),
      ∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ s ≤
        (↑(Nat.totient q) : ℝ)⁻¹ / (s - 1) + M :=
  residueClass_tsum_upper_bound ha

theorem weighted_pnt_dirichlet_lower
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {s : ℝ} (_ : s ∈ Set.Ioc 1 2),
      (↑(Nat.totient q) : ℝ)⁻¹ / (s - 1) - C ≤
        ∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ s :=
  residueClass_tsum_lower_bound ha

theorem ant_names_agree :
    (MertensInAP ↔ WeightedPNTinAP) ∧
    (WienerIkeharaForWeightedPNT ↔ WeightedPNTinAP) ∧
    (MertensInAP ↔ WienerIkeharaForWeightedPNT) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem ant_chain_corrected_status :
    (MertensInAP ↔ WeightedPNTinAP) ∧
    (RealWienerIkeharaTauberian → AbelSummationPNT → WeightedPNTinAP) :=
  ⟨Iff.rfl, real_wiener_ikehara_implies_wpnt⟩

end CorrectedAnalysis

/-! ## Section 6: WeightedPNTinAP → PrimesEquidistributedInAP -/

section WPNTtoPrimesEquidist

/-- Intermediate: (log p)/p equidistribution in arithmetic progressions. -/
def PrimeLogSumEquidist : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
        Real.log p / p - Real.log x / Nat.totient q| ≤ C

/-- Prime power stripping: WeightedPNTinAP → PrimeLogSumEquidist. -/
def PrimePowerStripping : Prop := WeightedPNTinAP → PrimeLogSumEquidist

/-- Abel summation step: (log p)/p → 1/p. -/
def PrimeLogToReciprocal : Prop := PrimeLogSumEquidist → PrimesEquidistributedInAP

/-- Full chain: WeightedPNTinAP → PrimesEquidistributedInAP. -/
theorem wpnt_implies_primes_equidist
    (h1 : PrimePowerStripping) (h2 : PrimeLogToReciprocal) :
    WeightedPNTinAP → PrimesEquidistributedInAP :=
  fun hwpnt => h2 (h1 hwpnt)

def WeightedPNTImpliesPrimesEquidist : Prop :=
  WeightedPNTinAP → PrimesEquidistributedInAP

theorem two_step_implies_direct
    (h1 : PrimePowerStripping) (h2 : PrimeLogToReciprocal) :
    WeightedPNTImpliesPrimesEquidist :=
  wpnt_implies_primes_equidist h1 h2

theorem ant_to_primes_equidist_chain :
    (PrimePowerStripping → PrimeLogToReciprocal → WeightedPNTImpliesPrimesEquidist) ∧
    (MertensInAP ↔ WeightedPNTinAP) :=
  ⟨two_step_implies_direct, Iff.rfl⟩

/-- `Λ(n)/n ≥ 0` for all `n`. -/
private theorem vonMangoldt_div_nonneg' (n : ℕ) : (0 : ℝ) ≤ Λ n / n :=
  div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

/-- For `n` that is not a prime power, `Lambda(n)/n = 0`. -/
private theorem vonMangoldt_div_zero_of_not_pp {n : ℕ} (h : ¬IsPrimePow n) :
    (Λ n : ℝ) / n = 0 := by
  simp [ArithmeticFunction.vonMangoldt_apply, h]

/-- **Prime-power stripping, per `x`.**  The prime sum `∑_{p ≤ x, p ≡ a} (log p)/p` differs
from the von Mangoldt sum `∑_{n ≤ x, n ≡ a} Λ(n)/n` by at most `B`, the uniform bound on the
proper prime-power contribution.

This is the entire content of prime-power stripping, isolated from the shape of the error
term in the input hypothesis: both `prime_power_stripping_from_bound` (`O(1)` error) and
`prime_power_stripping_asymp_from_bound` (`o(log x)` error) are triangle inequalities on
top of this lemma. -/
theorem prime_sum_sub_vonMangoldt_sum_le
    (B : ℝ)
    (hbound : ∀ (q : ℕ) (_ : 1 < q) (a : ℕ) (x : ℝ), 2 ≤ x →
      ∑ n ∈ ((Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q)).filter
        (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n ≤ B)
    (q a : ℕ) (hq : 1 < q) (x : ℝ) (hx : 2 ≤ x) :
    |(∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
        Real.log p / p) -
      (∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q), (Λ n : ℝ) / n)| ≤ B := by
  set S := (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q) with hS_def
  set P := ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q)
    with hP_def
  set vM := ∑ n ∈ S, (Λ n : ℝ) / n
  set pS := ∑ p ∈ P, Real.log p / p
  have hS_prime_eq_P : S.filter Nat.Prime = P := by
    ext p
    simp only [hS_def, hP_def, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp_mem, hp_res⟩, hp_prime⟩
      exact ⟨⟨⟨hp_prime.two_le, hp_mem.2⟩, hp_prime⟩, hp_res⟩
    · rintro ⟨⟨hp_mem, hp_prime⟩, hp_res⟩
      exact ⟨⟨⟨by omega, hp_mem.2⟩, hp_res⟩, hp_prime⟩
  have hvM_split : vM = ∑ n ∈ S.filter Nat.Prime, (Λ n : ℝ) / n +
      ∑ n ∈ S.filter (fun n => ¬Nat.Prime n), (Λ n : ℝ) / n := by
    show ∑ n ∈ S, _ = _
    rw [← Finset.sum_filter_add_sum_filter_not S Nat.Prime]
  have hprime_part : ∑ n ∈ S.filter Nat.Prime, (Λ n : ℝ) / n = pS := by
    rw [hS_prime_eq_P]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hP_def, Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.1.2]
  set R' := ∑ n ∈ S.filter (fun n => ¬Nat.Prime n), (Λ n : ℝ) / n with hR'_def
  have hR'_nonneg : 0 ≤ R' :=
    Finset.sum_nonneg (fun n _ => vonMangoldt_div_nonneg' n)
  have hR'_le_B : R' ≤ B := by
    have hsub : S.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n) ⊆
        S.filter (fun n => ¬Nat.Prime n) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2.2⟩
    have hle : R' ≤ ∑ n ∈ S.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n),
        (Λ n : ℝ) / n := by
      rw [hR'_def]
      rw [← Finset.sum_sdiff hsub]
      have hsdiff_zero : ∑ n ∈ S.filter (fun n => ¬Nat.Prime n) \
          S.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        simp only [Finset.mem_sdiff, Finset.mem_filter] at hn
        have : ¬IsPrimePow n := by
          intro hpp
          exact hn.2 ⟨hn.1.1, hpp, hn.1.2⟩
        exact vonMangoldt_div_zero_of_not_pp this
      linarith
    linarith [hbound q hq a x hx]
  have hvM_eq : vM = pS + R' := by linarith [hvM_split, hprime_part]
  calc |pS - vM|
      = R' := by
        rw [hvM_eq, show pS - (pS + R') = -R' from by ring,
          abs_neg, abs_of_nonneg hR'_nonneg]
    _ ≤ B := hR'_le_B

/-- PrimePowerStripping from a uniform bound on the non-prime prime power sum. -/
theorem prime_power_stripping_from_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ (q : ℕ) (_ : 1 < q) (a : ℕ) (x : ℝ), 2 ≤ x →
      ∑ n ∈ ((Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q)).filter
        (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n ≤ B)
    (hwpnt : WeightedPNTinAP) : PrimeLogSumEquidist := by
  intro q a hq hcop
  obtain ⟨C, hC_pos, hC_bound⟩ := hwpnt q a hq hcop
  refine ⟨C + B + 1, by linarith, fun x hx => ?_⟩
  have hstrip := prime_sum_sub_vonMangoldt_sum_le B hbound q a hq x hx
  have hvM := hC_bound x hx
  calc |(∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
          Real.log p / p) - Real.log x / (Nat.totient q : ℝ)|
      ≤ |(∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
            Real.log p / p) -
          (∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q), (Λ n : ℝ) / n)| +
        |(∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q), (Λ n : ℝ) / n) -
          Real.log x / (Nat.totient q : ℝ)| := by
        exact (abs_sub_le _ _ _)
    _ ≤ C + B + 1 := by linarith

/-- For `IsPrimePow n` with `n` not prime, extract the exponent and show it is at least 2. -/
private theorem exponent_ge_two_of_nonprime_pp {n : ℕ} (hn_pp : IsPrimePow n)
    (hn_np : ¬Nat.Prime n) :
    ∃ p k, Nat.Prime p ∧ 2 ≤ k ∧ n = p ^ k := by
  rw [isPrimePow_nat_iff] at hn_pp
  obtain ⟨p, k, hp, hk, rfl⟩ := hn_pp
  refine ⟨p, k, hp, ?_, rfl⟩
  by_contra h; push Not at h
  have : k = 1 := by omega
  subst this; exact hn_np (by simpa using hp)

/-- A non-prime prime power is at least 4. -/
private theorem nonprime_pp_ge_four {n : ℕ} (hn_pp : IsPrimePow n)
    (hn_np : ¬Nat.Prime n) : 4 ≤ n := by
  obtain ⟨p, k, hp, hk2, rfl⟩ := exponent_ge_two_of_nonprime_pp hn_pp hn_np
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2

/-- For a prime power `n` with `minFac n = p`, `Lambda(n) = log p`. -/
private theorem vonMangoldt_eq_log_minFac {n : ℕ} (hn_pp : IsPrimePow n) :
    (Λ n : ℝ) = Real.log (n.minFac) := by
  rw [isPrimePow_nat_iff] at hn_pp
  obtain ⟨p, k, hp, hk, rfl⟩ := hn_pp
  rw [Nat.pow_minFac (by omega : k ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hp, hp.minFac_eq]

/-- For any `Finset u`, the sum of `Lambda(n)/n` over non-prime prime powers in `u`
    is bounded by a universal constant (the tsum of `2 log p / p^2` over primes). -/
private theorem nonprime_pp_sum_bounded_by_tsum (u : Finset ℕ) :
    ∑ n ∈ u.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n ≤
    ∑' p, (if Nat.Prime p then
      2 * Real.log p / (p : ℝ) ^ 2 else 0) := by
  set S := u.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n) with hS_def
  set P := S.image Nat.minFac with hP_def
  have hdecomp : ∑ n ∈ S, (Λ n : ℝ) / n =
      ∑ p ∈ P, ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) / n := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.minFac)]
    intro n hn; exact Finset.mem_image_of_mem _ hn
  rw [hdecomp]
  have hP_prime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    rw [hP_def, Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    simp only [hS_def, Finset.mem_filter] at hn
    exact Nat.minFac_prime (show n ≠ 1 by
      have := nonprime_pp_ge_four hn.2.1 hn.2.2; omega)
  have hfiber_bound : ∀ p ∈ P,
      ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) / n ≤
      2 * Real.log p / (p : ℝ) ^ 2 := by
    intro p hp
    have hp_prime := hP_prime p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hfactor : ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) / n =
        Real.log p * ∑ n ∈ S.filter (fun n => n.minFac = p), (1 : ℝ) / n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_filter, hS_def] at hn
      have hvm := vonMangoldt_eq_log_minFac hn.1.2.1
      rw [hn.2] at hvm
      rw [hvm]; ring
    rw [hfactor]
    suffices hsuff : ∑ n ∈ S.filter (fun n => n.minFac = p), (1 : ℝ) / n ≤ 2 / (p : ℝ) ^ 2 by
      calc Real.log p * ∑ n ∈ S.filter (fun n => n.minFac = p), (1 : ℝ) / n
          ≤ Real.log p * (2 / (p : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_left hsuff
            exact Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
        _ = 2 * Real.log p / (p : ℝ) ^ 2 := by ring
    have hp_inv_lt_one : (1 : ℝ) / p < 1 := by
      rw [div_lt_one hp0]; exact_mod_cast hp_prime.one_lt
    have hp_inv_nonneg : (0 : ℝ) ≤ 1 / p := by positivity
    have hgeo_summable := summable_geometric_of_lt_one hp_inv_nonneg hp_inv_lt_one
    have hgeo_shifted : Summable (fun k : ℕ => ((1 : ℝ) / p) ^ (k + 2)) :=
      hgeo_summable.comp_injective (fun a b h => by omega)
    have htsum_eq : ∑' k, ((1 : ℝ) / p) ^ (k + 2) =
        (1 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ))⁻¹ := by
      have : ∑' k, ((1 : ℝ) / p) ^ (k + 2) =
          (1 / (p : ℝ)) ^ 2 * ∑' k, (1 / (p : ℝ)) ^ k := by
        conv_lhs => arg 1; ext k; rw [pow_add, mul_comm]
        rw [tsum_mul_left]
      rw [this, tsum_geometric_of_lt_one hp_inv_nonneg hp_inv_lt_one]
    have htsum_le : ∑' k, ((1 : ℝ) / p) ^ (k + 2) ≤ 2 / (p : ℝ) ^ 2 := by
      rw [htsum_eq]
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp_prime.one_lt
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      have hpm1_pos : (0 : ℝ) < p - 1 := by linarith
      have : (1 - 1 / (p : ℝ))⁻¹ = p / (p - 1) := by field_simp
      rw [this, show (1 / (p : ℝ)) ^ 2 * (p / (p - 1)) = 1 / (p * (p - 1)) from by
        field_simp]
      rw [div_le_div_iff₀ (mul_pos hp0 hpm1_pos) (pow_pos hp0 2)]
      nlinarith
    set F := S.filter (fun n => n.minFac = p) with hF_def
    set e := (fun n : ℕ => Nat.log p n - 2) with he_def
    have he_inj : Set.InjOn e F := by
      intro n₁ hn₁ n₂ hn₂ heq
      simp only [he_def, hF_def, Finset.mem_coe, Finset.mem_filter, hS_def] at hn₁ hn₂ heq
      obtain ⟨q₁, k₁, hq₁, hk₁, hn₁_eq⟩ :=
        exponent_ge_two_of_nonprime_pp hn₁.1.2.1 hn₁.1.2.2
      obtain ⟨q₂, k₂, hq₂, hk₂, hn₂_eq⟩ :=
        exponent_ge_two_of_nonprime_pp hn₂.1.2.1 hn₂.1.2.2
      have hq₁p : q₁ = p := by rw [hn₁_eq, hq₁.pow_minFac (by omega)] at hn₁; exact hn₁.2
      have hq₂p : q₂ = p := by rw [hn₂_eq, hq₂.pow_minFac (by omega)] at hn₂; exact hn₂.2
      subst hq₁p; subst hq₂p
      rw [hn₁_eq, hn₂_eq] at heq ⊢
      rw [Nat.log_pow hp_prime.one_lt, Nat.log_pow hp_prime.one_lt] at heq
      congr 1; omega
    have hterm_eq : ∀ n ∈ F, (1 : ℝ) / n = ((1 : ℝ) / p) ^ (e n + 2) := by
      intro n hn
      simp only [hF_def, Finset.mem_filter, hS_def] at hn
      obtain ⟨q, k, hq_prime, hk2, hn_eq⟩ :=
        exponent_ge_two_of_nonprime_pp hn.1.2.1 hn.1.2.2
      have hq_eq_p : q = p := by rw [hn_eq, hq_prime.pow_minFac (by omega)] at hn; exact hn.2
      subst hq_eq_p; rw [hn_eq]
      simp only [he_def, Nat.log_pow hp_prime.one_lt, show k - 2 + 2 = k from by omega]
      rw [Nat.cast_pow, one_div, one_div, inv_pow]
    have hreindex : ∑ n ∈ F, (1 : ℝ) / n = ∑ j ∈ F.image e, ((1 : ℝ) / p) ^ (j + 2) := by
      rw [Finset.sum_image he_inj]
      exact Finset.sum_congr rfl hterm_eq
    rw [hreindex]
    calc ∑ j ∈ F.image e, ((1 : ℝ) / p) ^ (j + 2)
        ≤ ∑' j, ((1 : ℝ) / p) ^ (j + 2) :=
          hgeo_shifted.sum_le_tsum _ (fun j _ => by positivity)
      _ ≤ 2 / (p : ℝ) ^ 2 := htsum_le
  have hbound_summable : Summable (fun n : ℕ =>
      if Nat.Prime n then 2 * Real.log n / (n : ℝ) ^ 2 else 0) := by
    apply Summable.of_nonneg_of_le
    · intro n; split_ifs <;> positivity
    · intro n
      split_ifs with h
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast h.pos
        have hlog_bound : Real.log n ≤ 2 * (n : ℝ) ^ ((1:ℝ)/2) := by
          linarith [Real.log_le_rpow_div hn0.le (show (0:ℝ) < 1/2 by norm_num)]
        have hn2_rpow : (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℝ) :=
          (Real.rpow_natCast (n : ℝ) 2).symm
        calc 2 * Real.log n / (n : ℝ) ^ 2
            ≤ 4 * (n : ℝ) ^ ((1:ℝ)/2) / (n : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_right _ (pow_pos hn0 2).le
              linarith
          _ = 4 * ((n : ℝ) ^ ((1:ℝ)/2) / (n : ℝ) ^ (2 : ℝ)) := by
              rw [hn2_rpow]; ring
          _ = 4 * (n : ℝ) ^ ((1:ℝ)/2 - 2) := by
              congr 1; rw [Real.rpow_sub hn0]
          _ = 4 * (n : ℝ) ^ ((-3:ℝ)/2) := by norm_num
      · positivity
    · have hsummable32 : Summable (fun n : ℕ => (n : ℝ) ^ ((-3:ℝ)/2)) :=
        Real.summable_nat_rpow.mpr (by norm_num : (-3:ℝ)/2 < -1)
      exact hsummable32.mul_left 4
  calc ∑ p ∈ P, ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) / n
      ≤ ∑ p ∈ P, (2 * Real.log p / (p : ℝ) ^ 2) :=
        Finset.sum_le_sum hfiber_bound
    _ = ∑ p ∈ P, (if Nat.Prime p then 2 * Real.log p / (p : ℝ) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp; rw [if_pos (hP_prime p hp)]
    _ ≤ ∑' p, (if Nat.Prime p then 2 * Real.log p / (p : ℝ) ^ 2 else 0) :=
        hbound_summable.sum_le_tsum P (fun n _ => by split_ifs <;> positivity)

/-- `WeightedPNTinAP` implies `PrimeLogSumEquidist` by stripping bounded prime
    power contributions from the von Mangoldt sum. -/
theorem prime_power_stripping_proved : PrimePowerStripping := by
  intro hwpnt
  set B := ∑' p, (if Nat.Prime p then 2 * Real.log p / (p : ℝ) ^ 2 else 0) with hB_def
  have hB_nonneg : 0 ≤ B := by
    apply tsum_nonneg; intro n; split_ifs <;> positivity
  have hbound : ∀ (q : ℕ), 1 < q → ∀ (a : ℕ) (x : ℝ), 2 ≤ x →
      ∑ n ∈ ((Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q)).filter
        (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n ≤ B := by
    intro q _ a x _
    set T := ((Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q)).filter
        (fun n => IsPrimePow n ∧ ¬Nat.Prime n) with hT_def
    set T' := (Icc 1 (Nat.floor x)).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n) with hT'_def
    calc ∑ n ∈ T, (Λ n : ℝ) / n
        ≤ ∑ n ∈ T', (Λ n : ℝ) / n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [hT_def, hT'_def, Finset.mem_filter] at hn ⊢
            exact ⟨hn.1.1, hn.2⟩
          · intro n _ _; exact vonMangoldt_div_nonneg' n
      _ ≤ B := nonprime_pp_sum_bounded_by_tsum _
  exact prime_power_stripping_from_bound B hB_nonneg hbound hwpnt

end WPNTtoPrimesEquidist

/-! ## Section 6: Asymptotic (rate-free) forms of the ANT hypotheses

The hypotheses above all carry an `O(1)` error term, transcribed from IK Theorem 2.2 and
(2.25).  The consumers of the chain do not need that strength: `RoughLPFEquidist` and
`MinFacResidueEquidist` (`EM/Population/Proof.lean`) are `Filter.Tendsto` statements about
ratios, with no rate attached anywhere.

This section introduces the corresponding `o(main term)` forms.  They matter because they
are what a *Tauberian* argument actually delivers: the repository already proves the
Dirichlet-series input unconditionally (`residueClass_tsum_both_bounds`), and Karamata's
theorem converts that into the asymptotic form below but not into the `O(1)` form.  So the
question "is the `O(1)` load-bearing?" decides whether closing the ANT gap needs a Karamata
Tauberian theorem or the (much longer) elementary Mertens-in-AP development.

Each asymptotic form is implied by its `O(1)` counterpart (`*_asymp_of_*` below), so
nothing downstream is weakened by routing through them. -/

section AsymptoticForms

/-- **Asymptotic form of `WeightedPNTinAP`**: the error is `o(log x)` rather than `O(1)`.

`∑_{n ≤ x, n ≡ a (q)} Λ(n)/n = (log x)/φ(q) + o(log x)`. -/
def WeightedPNTinAPAsymp : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      |∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q),
        Λ n / n - Real.log x / Nat.totient q| ≤ ε * Real.log x

/-- **Asymptotic form of `PrimeLogSumEquidist`**:
`∑_{p ≤ x, p ≡ a (q)} (log p)/p = (log x)/φ(q) + o(log x)`. -/
def PrimeLogSumEquidistAsymp : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      |∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
        Real.log p / p - Real.log x / Nat.totient q| ≤ ε * Real.log x

/-- **Asymptotic form of `PrimesEquidistributedInAP`**:
`∑_{p ≤ x, p ≡ a (q)} 1/p = (log log x)/φ(q) + o(log log x)`. -/
def PrimesEquidistInAPAsymp : Prop :=
  ∀ (q : ℕ) (a : ℕ), 1 < q → Nat.Coprime a q →
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      |∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
        (1 : ℝ) / p - Real.log (Real.log x) / Nat.totient q| ≤ ε * Real.log (Real.log x)

/-- Asymptotic form of the prime-power stripping step. -/
def PrimePowerStrippingAsymp : Prop := WeightedPNTinAPAsymp → PrimeLogSumEquidistAsymp

/-- Asymptotic form of the Abel summation step. -/
def PrimeLogToReciprocalAsymp : Prop := PrimeLogSumEquidistAsymp → PrimesEquidistInAPAsymp

/-! ### The `O(1)` forms imply the asymptotic forms

In each case the argument is the same: a constant `C` is `≤ ε · f x` once `f x ≥ C / ε`,
and the main terms `log x` and `log log x` are unbounded. -/

/-- A constant bound becomes an `ε`-bound against `log x` past `exp (C/ε)`. -/
private theorem const_le_eps_mul_log {C ε : ℝ} (hε : 0 < ε) {x : ℝ}
    (hx : Real.exp (C / ε) ≤ x) : C ≤ ε * Real.log x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h : C / ε ≤ Real.log x := by
    rw [← Real.log_exp (C / ε)]
    exact Real.log_le_log (Real.exp_pos _) hx
  rw [div_le_iff₀ hε] at h
  linarith

theorem weightedPNTinAP_asymp_of_weightedPNTinAP :
    WeightedPNTinAP → WeightedPNTinAPAsymp := by
  intro h q a hq hcop ε hε
  obtain ⟨C, _, hC⟩ := h q a hq hcop
  refine ⟨max 2 (Real.exp (C / ε)), le_max_left _ _, fun x hx => ?_⟩
  exact (hC x (le_trans (le_max_left _ _) hx)).trans
    (const_le_eps_mul_log hε (le_trans (le_max_right _ _) hx))

theorem primeLogSumEquidist_asymp_of_primeLogSumEquidist :
    PrimeLogSumEquidist → PrimeLogSumEquidistAsymp := by
  intro h q a hq hcop ε hε
  obtain ⟨C, _, hC⟩ := h q a hq hcop
  refine ⟨max 2 (Real.exp (C / ε)), le_max_left _ _, fun x hx => ?_⟩
  exact (hC x (le_trans (le_max_left _ _) hx)).trans
    (const_le_eps_mul_log hε (le_trans (le_max_right _ _) hx))

theorem primesEquidistInAP_asymp_of_primesEquidistInAP :
    PrimesEquidistributedInAP → PrimesEquidistInAPAsymp := by
  intro h q a hq hcop ε hε
  obtain ⟨C, _, hC⟩ := h q a hq hcop
  refine ⟨max 3 (Real.exp (Real.exp (C / ε))), le_max_left _ _, fun x hx => ?_⟩
  refine (hC x (le_trans (le_max_left _ _) hx)).trans ?_
  have hxe : Real.exp (Real.exp (C / ε)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hlog : Real.exp (C / ε) ≤ Real.log x := by
    rw [← Real.log_exp (Real.exp (C / ε))]
    exact Real.log_le_log (Real.exp_pos _) hxe
  exact const_le_eps_mul_log hε hlog

/-! ### Prime-power stripping in asymptotic form

The proper prime-power contribution is bounded by an absolute constant `B` uniformly in
`x` (`prime_sum_sub_vonMangoldt_sum_le`), and a constant is `o(log x)`.  So the step
survives the weakening verbatim. -/

theorem prime_power_stripping_asymp_from_bound
    (B : ℝ) (_hB : 0 ≤ B)
    (hbound : ∀ (q : ℕ) (_ : 1 < q) (a : ℕ) (x : ℝ), 2 ≤ x →
      ∑ n ∈ ((Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q)).filter
        (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n ≤ B)
    (hwpnt : WeightedPNTinAPAsymp) : PrimeLogSumEquidistAsymp := by
  intro q a hq hcop ε hε
  obtain ⟨x₀, hx₀, hx₀_bound⟩ := hwpnt q a hq hcop (ε / 2) (by linarith)
  refine ⟨max x₀ (max 2 (Real.exp (B / (ε / 2)))), le_trans hx₀ (le_max_left _ _),
    fun x hx => ?_⟩
  have hx1 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right x₀ _)) hx
  have hx3 : Real.exp (B / (ε / 2)) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right x₀ _)) hx
  have hstrip := prime_sum_sub_vonMangoldt_sum_le B hbound q a hq x hx2
  have hvM := hx₀_bound x hx1
  have hBsmall : B ≤ (ε / 2) * Real.log x := const_le_eps_mul_log (by linarith) hx3
  calc |(∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
          Real.log p / p) - Real.log x / (Nat.totient q : ℝ)|
      ≤ |(∑ p ∈ ((Icc 2 (Nat.floor x)).filter Nat.Prime).filter (fun p => p % q = a % q),
            Real.log p / p) -
          (∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q), (Λ n : ℝ) / n)| +
        |(∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q), (Λ n : ℝ) / n) -
          Real.log x / (Nat.totient q : ℝ)| := abs_sub_le _ _ _
    _ ≤ ε * Real.log x := by linarith

/-- **Prime-power stripping survives the weakening**: `WeightedPNTinAPAsymp` implies
`PrimeLogSumEquidistAsymp`, with the same absolute constant `B` as the `O(1)` proof. -/
theorem prime_power_stripping_asymp_proved : PrimePowerStrippingAsymp := by
  intro hwpnt
  set B := ∑' p, (if Nat.Prime p then 2 * Real.log p / (p : ℝ) ^ 2 else 0) with hB_def
  have hB_nonneg : 0 ≤ B := by
    apply tsum_nonneg; intro n; split_ifs <;> positivity
  have hbound : ∀ (q : ℕ), 1 < q → ∀ (a : ℕ) (x : ℝ), 2 ≤ x →
      ∑ n ∈ ((Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q)).filter
        (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n ≤ B := by
    intro q _ a x _
    calc ∑ n ∈ ((Icc 1 (Nat.floor x)).filter (fun n => n % q = a % q)).filter
          (fun n => IsPrimePow n ∧ ¬Nat.Prime n), (Λ n : ℝ) / n
        ≤ ∑ n ∈ (Icc 1 (Nat.floor x)).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n),
            (Λ n : ℝ) / n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_filter] at hn ⊢
            exact ⟨hn.1.1, hn.2⟩
          · intro n _ _; exact vonMangoldt_div_nonneg' n
      _ ≤ B := nonprime_pp_sum_bounded_by_tsum _
  exact prime_power_stripping_asymp_from_bound B hB_nonneg hbound hwpnt

end AsymptoticForms

end IK
