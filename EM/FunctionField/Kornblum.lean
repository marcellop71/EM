import EM.FunctionField.KornblumCharacter
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kornblum's theorem: Dirichlet's theorem for `F_p[t]`

**Statement** (`ffDirichletDensity`). Let `Q` be a monic irreducible polynomial
over `F_p` and `a` a polynomial with `Q ∤ a`. Then

  `∑_{P ≡ a (mod Q), 1 ≤ deg P ≤ Y} p^{-deg P} → ∞`  as `Y → ∞`,

the sum running over monic irreducible `P`. This is exactly the hypothesis
`FFDirichletDensity p` of `EM/FunctionField/DensityMC.lean`, so the headline
`ff_almost_all_genmixed_density` becomes unconditional
(`ff_almost_all_genmixed_density_unconditional`).

**Proof.** Write `q = p`, `d = deg Q`, `F = F_p[t]/(Q)`, and let `χ` range over
the multiplicative characters of the finite field `F`.

1. *von Mangoldt identity* (`KornblumVonMangoldt.lean`). With
   `A_n(χ) = ∑_{f monic, deg f = n} χ(f)` and
   `Ψ_n(χ) = ∑_{j deg P = n} deg P · χ(P)^j`, one has
   `n A_n(χ) = ∑_{k ≤ n} Ψ_k(χ) A_{n-k}(χ)`, and `Ψ_n(1) = q^n` for the constant
   function `1`, so `|Ψ_n(χ)| ≤ q^n`.
2. *Exact cancellation* (`KornblumCharacter.lean`). For `χ ≠ 1`, `A_n(χ) = 0`
   when `n ≥ d`; so `Ψ_n(χ)` satisfies a linear recurrence with coefficients
   `A_0(χ), …, A_{d-1}(χ)`.
3. *Non-vanishing* (`lPoly_eval_ne_zero`): `L(1/q, χ) = ∑_{k<d} A_k(χ) q^{-k} ≠ 0`
   for `χ ≠ 1`.
4. *Bounded logarithms* (`bounded_psi_sums`, from `bounded_partial_sums` in
   `KornblumSeries.lean`): by 1–3 the partial sums `∑_{n ≤ N} Ψ_n(χ)/(n q^n)`
   are bounded for `χ ≠ 1`.
5. *This file.* For the trivial character, `Ψ_n(χ_0) ≥ q^n - n`
   (`psi_one_char_lower`: only the powers of `Q` are missing), so
   `∑_{n ≤ N} Ψ_n(χ_0)/(n q^n) ≥ H_N - 1` with `H_N` the harmonic sum
   (`partialLog_one_lower`). By orthogonality of characters
   (`sum_char_mul_partialLog`)

     `∑_χ χ(a)^{-1} ∑_{n ≤ N} Ψ_n(χ)/(n q^n)
        = #{χ} · ∑_{(P, j) : P^j ≡ a, j deg P ≤ N} 1/(j q^{j deg P})`,

   so the prime-power sum on the right is `≥ (H_N - C)/#{χ}` (`main_lower`).
   The prime powers with `j ≥ 2` contribute at most `16`
   (`primePowerSum_le`), and the terms with `j = 1` are the sum in the
   statement. Since `H_N → ∞`, the theorem follows.

No Euler product, no infinite product and no complex analysis is used: all
sums are finite, and the only limit taken is `H_N → ∞`.
-/

namespace FunctionFieldAnalog.Kornblum

open Polynomial Finset

open scoped Classical

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

section Assembly

variable (Q : Polynomial (ZMod p)) [hQ : Fact (Irreducible Q)]

/-! ## The logarithm sums and the prime-power sum -/

/-- The partial sum `∑_{n ≤ N} Ψ_n(χ) / (n p^n)` of the logarithm of `L(u, χ)` at
    `u = 1/p`. -/
noncomputable def partialLog (χ : MulChar (AdjoinRoot Q) ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N + 1), psi p (charHom p Q χ) n / ((n : ℂ) * (p : ℂ) ^ n)

/-- The sum of `1/(j p^{j deg P})` over the pairs (monic irreducible `P`, `j ≥ 1`)
    with `j deg P ≤ N` and `P^j ≡ x (mod Q)`. -/
noncomputable def primePowerSum (x : AdjoinRoot Q) (N : ℕ) : ℝ :=
  ∑ P ∈ irrUpTo p N, ∑ j ∈ Icc 1 N,
    if j * P.natDegree ≤ N ∧ AdjoinRoot.mk Q P ^ j = x then
      1 / ((j : ℝ) * (p : ℝ) ^ (j * P.natDegree)) else 0

/-- **Orthogonality**: `∑_χ χ(x)^{-1} · ∑_{n ≤ N} Ψ_n(χ)/(n p^n)` is the number of
    characters times the prime-power sum of the class `x`. -/
theorem sum_char_mul_partialLog {x : AdjoinRoot Q} (hx : x ≠ 0) (N : ℕ) :
    ∑ χ : MulChar (AdjoinRoot Q) ℂ, χ x⁻¹ * partialLog p Q χ N =
      (((Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℝ) * primePowerSum p Q x N : ℝ) : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h1 : ∀ χ : MulChar (AdjoinRoot Q) ℂ, χ x⁻¹ * partialLog p Q χ N =
      ∑ P ∈ irrUpTo p N, ∑ j ∈ Icc 1 N, if j * P.natDegree ≤ N then
        (P.natDegree : ℂ) * charHom p Q χ P ^ j *
          (χ x⁻¹ / (((j * P.natDegree : ℕ) : ℂ) * (p : ℂ) ^ (j * P.natDegree))) else 0 := by
    intro χ
    rw [← sum_psi_mul p (charHom p Q χ) (fun n => χ x⁻¹ / ((n : ℂ) * (p : ℂ) ^ n)) N,
      partialLog, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring
  rw [sum_congr rfl fun χ _ => h1 χ, sum_comm, primePowerSum, Complex.ofReal_mul,
    Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun P hP => ?_
  have hd : 0 < P.natDegree := ((mem_irrUpTo p).mp hP).2.1.natDegree_pos
  have hd0 : (P.natDegree : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [sum_comm, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj0 : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hj).1; omega)
  by_cases hle : j * P.natDegree ≤ N
  · simp only [hle, ↓reduceIte, true_and]
    have h2 : ∀ χ : MulChar (AdjoinRoot Q) ℂ,
        (P.natDegree : ℂ) * charHom p Q χ P ^ j *
          (χ x⁻¹ / (((j * P.natDegree : ℕ) : ℂ) * (p : ℂ) ^ (j * P.natDegree))) =
        χ (x⁻¹ * AdjoinRoot.mk Q P ^ j) *
          ((P.natDegree : ℂ) / (((j * P.natDegree : ℕ) : ℂ) * (p : ℂ) ^ (j * P.natDegree))) := by
      intro χ
      rw [map_mul, map_pow, charHom_apply]
      ring
    rw [sum_congr rfl fun χ _ => h2 χ, ← sum_mul, sum_char_eq]
    by_cases heq : AdjoinRoot.mk Q P ^ j = x
    · have h3 : x⁻¹ * AdjoinRoot.mk Q P ^ j = 1 := by rw [heq, inv_mul_cancel₀ hx]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h3), ite_eq_left_of_eq_true _ _ (eq_true heq)]
      push_cast
      field_simp
    · have h3 : x⁻¹ * AdjoinRoot.mk Q P ^ j ≠ 1 := fun h =>
        heq (by rw [← mul_one x, ← h, mul_inv_cancel_left₀ hx])
      simp [h3, heq]
  · simp [hle]

/-! ## The trivial character -/

/-- For the trivial character mod `Q`, `Ψ_n(χ_0)` is a natural number which is at
    least `Ψ_n(1) - n`: only the powers of `Q` are missing. -/
theorem psi_one_char_lower (hQm : Q.Monic) (n : ℕ) :
    ∃ k : ℕ, psi p (charHom p Q 1) n = (k : ℂ) ∧ psiNat p n ≤ k + n := by
  set g : Polynomial (ZMod p) → ℕ := fun P =>
    ∑ j ∈ Icc 1 n, if j * P.natDegree = n then P.natDegree else 0 with hg
  refine ⟨∑ P ∈ irrUpTo p n, if Q ∣ P then 0 else g P, ?_, ?_⟩
  · unfold psi
    push_cast
    refine sum_congr rfl fun P _ => ?_
    by_cases hQP : Q ∣ P
    · simp only [hQP, ↓reduceIte, charHom_one_apply]
      refine sum_eq_zero fun j hj => ?_
      have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
      simp [hj0]
    · have h1 : charHom p Q 1 P = 1 := by
        rw [charHom_one_apply, ite_eq_right_of_eq_false _ _ (eq_false hQP)]
      simp only [hQP, ↓reduceIte, h1, one_pow, mul_one, hg]
      push_cast
      rfl
  · have hsplit : ∀ P ∈ irrUpTo p n,
        g P = (if Q ∣ P then 0 else g P) + if P = Q then g Q else 0 := by
      intro P hP
      rw [mem_irrUpTo] at hP
      by_cases hQP : Q ∣ P
      · have hPQ : P = Q :=
          (eq_of_monic_of_associated hQm hP.1 (hQ.out.associated_of_dvd hP.2.1 hQP)).symm
        simp [hPQ]
      · have hPQ : P ≠ Q := fun h => hQP (h ▸ dvd_rfl)
        simp [hQP, hPQ]
    have hgQ : g Q ≤ n := by
      have hd : 0 < Q.natDegree := hQ.out.natDegree_pos
      calc g Q ≤ ∑ j ∈ Icc 1 n, if j = n / Q.natDegree then n else 0 := by
            refine sum_le_sum fun j hj => ?_
            by_cases h : j * Q.natDegree = n
            · have h1 : j = n / Q.natDegree := (Nat.div_eq_of_eq_mul_left hd h.symm).symm
              have h2 : Q.natDegree ≤ n := h ▸ Nat.le_mul_of_pos_left _ (mem_Icc.mp hj).1
              rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h1)]
              exact h2
            · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
              exact Nat.zero_le _
        _ ≤ n := by
            rw [sum_ite_eq']
            split_ifs
            · exact le_rfl
            · exact Nat.zero_le _
    calc psiNat p n = ∑ P ∈ irrUpTo p n, g P := rfl
      _ = ∑ P ∈ irrUpTo p n, (if Q ∣ P then 0 else g P) +
            ∑ P ∈ irrUpTo p n, if P = Q then g Q else 0 := by
          rw [← sum_add_distrib]
          exact sum_congr rfl hsplit
      _ ≤ ∑ P ∈ irrUpTo p n, (if Q ∣ P then 0 else g P) + n := by
          refine Nat.add_le_add_left ?_ _
          rw [sum_ite_eq']
          split_ifs
          · exact hgQ
          · exact Nat.zero_le _

/-- For the trivial character the logarithm sum is real and at least `H_N - 1`,
    where `H_N = 1 + 1/2 + … + 1/N`. -/
theorem partialLog_one_lower (hQm : Q.Monic) (N : ℕ) :
    ∃ s : ℝ, partialLog p Q 1 N = (s : ℂ) ∧ ∑ n ∈ range N, 1 / ((n : ℝ) + 1) - 1 ≤ s := by
  choose k hk1 hk2 using psi_one_char_lower p Q hQm
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  refine ⟨∑ n ∈ range (N + 1), (k n : ℝ) / ((n : ℝ) * (p : ℝ) ^ n), ?_, ?_⟩
  · unfold partialLog
    push_cast
    exact sum_congr rfl fun n _ => by rw [hk1]
  · rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, div_zero, add_zero]
    have hterm : ∀ n ∈ range N, 1 / ((n : ℝ) + 1) - (1 / 2 : ℝ) ^ (n + 1) ≤
        (k (n + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (n + 1)) := by
      intro n _
      have h := hk2 (n + 1)
      rw [psiNat_eq p (Nat.succ_pos n)] at h
      have h' : (p : ℝ) ^ (n + 1) ≤ k (n + 1) + ((n : ℝ) + 1) := by exact_mod_cast h
      have hpn : (0 : ℝ) < (p : ℝ) ^ (n + 1) := by positivity
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : (1 : ℝ) / (p : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) hp2 _)
      have h3 : 1 / ((n : ℝ) + 1) - 1 / (p : ℝ) ^ (n + 1) ≤
          (k (n + 1) : ℝ) / (((n : ℝ) + 1) * (p : ℝ) ^ (n + 1)) := by
        rw [div_sub_div _ _ hn.ne' hpn.ne']
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      push_cast
      linarith
    have hgeom : ∑ n ∈ range N, (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := by
      have h := sum_geometric_two_le N
      simp_rw [pow_succ]
      rw [← sum_mul]
      linarith
    calc ∑ n ∈ range N, 1 / ((n : ℝ) + 1) - 1
        ≤ ∑ n ∈ range N, (1 / ((n : ℝ) + 1) - (1 / 2 : ℝ) ^ (n + 1)) := by
          rw [sum_sub_distrib]
          linarith
      _ ≤ ∑ n ∈ range N, (k (n + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (n + 1)) :=
          sum_le_sum hterm

/-! ## The lower bound for the prime-power sum -/

/-- **Main lower bound**: for a non-zero residue `x` mod `Q`, the prime-power sum
    of the class `x`, times the number of characters, is at least `H_N - C`. -/
theorem main_lower (hQm : Q.Monic) {x : AdjoinRoot Q} (hx : x ≠ 0) :
    ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ range N, 1 / ((n : ℝ) + 1) - C ≤
      (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℝ) * primePowerSum p Q x N := by
  have hex : ∀ χ : MulChar (AdjoinRoot Q) ℂ, ∃ C : ℝ, χ ≠ 1 →
      ∀ N : ℕ, ‖partialLog p Q χ N‖ ≤ C := by
    intro χ
    by_cases h : χ = 1
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨C, hC⟩ := bounded_psi_sums p Q hQm h
      exact ⟨C, fun _ N => hC (N + 1)⟩
  choose Cb hCb using hex
  refine ⟨1 + ∑ χ ∈ univ.erase 1, Cb χ, fun N => ?_⟩
  have hA := sum_char_mul_partialLog p Q hx N
  rw [← add_sum_erase univ _ (mem_univ (1 : MulChar (AdjoinRoot Q) ℂ))] at hA
  have h1x : (1 : MulChar (AdjoinRoot Q) ℂ) x⁻¹ = 1 :=
    MulChar.one_apply (isUnit_iff_ne_zero.mpr (inv_ne_zero hx))
  rw [h1x, one_mul] at hA
  obtain ⟨s1, hs1, hs1lower⟩ := partialLog_one_lower p Q hQm N
  have hrest : ‖∑ χ ∈ univ.erase (1 : MulChar (AdjoinRoot Q) ℂ), χ x⁻¹ * partialLog p Q χ N‖ ≤
      ∑ χ ∈ univ.erase 1, Cb χ :=
    (norm_sum_le _ _).trans (sum_le_sum fun χ hχ => by
      rw [norm_mul]
      calc ‖χ x⁻¹‖ * ‖partialLog p Q χ N‖ ≤ 1 * Cb χ :=
            mul_le_mul (norm_char_le_one p Q χ _) (hCb χ (ne_of_mem_erase hχ) N)
              (norm_nonneg _) zero_le_one
        _ = Cb χ := one_mul _)
  have hre := congrArg Complex.re hA
  rw [Complex.add_re, hs1, Complex.ofReal_re, Complex.ofReal_re] at hre
  have habs := (Complex.abs_re_le_norm _).trans hrest
  have hlow := (abs_le.mp habs).1
  linarith

/-! ## Prime powers contribute a bounded amount -/

omit hQ in
/-- The residue class condition of `ffClassIrredUpTo`, in the residue field. -/
theorem modByMonic_eq_iff (hQm : Q.Monic) (P a : Polynomial (ZMod p)) :
    P %ₘ Q = a %ₘ Q ↔ AdjoinRoot.mk Q P = AdjoinRoot.mk Q a := by
  rw [AdjoinRoot.mk_eq_mk, ← modByMonic_eq_zero_iff_dvd hQm, sub_modByMonic, sub_eq_zero]

omit hQ in
theorem ffClassIrredUpTo_eq (hQm : Q.Monic) (a : Polynomial (ZMod p)) (N : ℕ) :
    ffClassIrredUpTo p Q a N =
      (irrUpTo p N).filter (fun P => AdjoinRoot.mk Q P = AdjoinRoot.mk Q a) := by
  ext P
  simp only [ffClassIrredUpTo, irrUpTo, mem_biUnion, mem_filter, modByMonic_eq_iff p Q hQm]
  constructor
  · rintro ⟨e, he, hP, h⟩
    exact ⟨⟨e, he, hP⟩, h⟩
  · rintro ⟨⟨e, he, hP⟩, h⟩
    exact ⟨e, he, hP, h⟩

/-- The sum of `8 / p^{2 deg P}` over the monic irreducibles of degree `≤ N` is at
    most `16`. -/
theorem sum_irrUpTo_inv_sq_le (N : ℕ) :
    ∑ P ∈ irrUpTo p N, 8 / ((p : ℝ) ^ P.natDegree) ^ 2 ≤ 16 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hdisj : ((Icc 1 N : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun e => ffIrredDeg p e) := by
    intro e _ e' _ hne
    refine Finset.disjoint_left.mpr fun P h1 h2 => hne ?_
    rw [mem_ffIrredDeg] at h1 h2
    rw [← h1.2.2, ← h2.2.2]
  rw [irrUpTo, sum_biUnion hdisj]
  have hper : ∀ e ∈ Icc 1 N,
      ∑ P ∈ ffIrredDeg p e, 8 / ((p : ℝ) ^ P.natDegree) ^ 2 ≤ 8 * (1 / 2 : ℝ) ^ e := by
    intro e _
    have hpe : (0 : ℝ) < (p : ℝ) ^ e := by positivity
    have hcongr : ∀ P ∈ ffIrredDeg p e,
        8 / ((p : ℝ) ^ P.natDegree) ^ 2 = 8 / ((p : ℝ) ^ e) ^ 2 := fun P hP => by
      rw [((mem_ffIrredDeg p).mp hP).2.2]
    rw [sum_congr rfl hcongr, sum_const, nsmul_eq_mul]
    have hcard : ((ffIrredDeg p e).card : ℝ) ≤ (p : ℝ) ^ e := by
      exact_mod_cast ffIrredDeg_card_le_pow p e
    have h2 : (1 : ℝ) / (p : ℝ) ^ e ≤ (1 / 2 : ℝ) ^ e := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) hp2 _)
    calc ((ffIrredDeg p e).card : ℝ) * (8 / ((p : ℝ) ^ e) ^ 2)
        ≤ (p : ℝ) ^ e * (8 / ((p : ℝ) ^ e) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 8 * (1 / (p : ℝ) ^ e) := by field_simp
      _ ≤ 8 * (1 / 2 : ℝ) ^ e := by linarith
  calc ∑ e ∈ Icc 1 N, ∑ P ∈ ffIrredDeg p e, 8 / ((p : ℝ) ^ P.natDegree) ^ 2
      ≤ ∑ e ∈ Icc 1 N, 8 * (1 / 2 : ℝ) ^ e := sum_le_sum hper
    _ ≤ ∑ e ∈ range (N + 1), 8 * (1 / 2 : ℝ) ^ e :=
        sum_le_sum_of_subset_of_nonneg
          (fun e he => mem_range.mpr (by have := (mem_Icc.mp he).2; omega))
          (fun _ _ _ => by positivity)
    _ ≤ 16 := by
        rw [← mul_sum]
        linarith [sum_geometric_two_le (N + 1)]

/-- **Prime powers are negligible**: the prime-power sum of the class of `a`
    exceeds the sum over the primes `P ≡ a (mod Q)` by at most `16`. -/
theorem primePowerSum_le (hQm : Q.Monic) (a : Polynomial (ZMod p)) (N : ℕ) :
    primePowerSum p Q (AdjoinRoot.mk Q a) N ≤
      ∑ P ∈ ffClassIrredUpTo p Q a N, 1 / (p : ℝ) ^ P.natDegree + 16 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hppos : (0 : ℝ) < p := by linarith
  have hinner : ∀ P ∈ irrUpTo p N,
      (∑ j ∈ Icc 1 N,
        if j * P.natDegree ≤ N ∧ AdjoinRoot.mk Q P ^ j = AdjoinRoot.mk Q a then
          1 / ((j : ℝ) * (p : ℝ) ^ (j * P.natDegree)) else 0) ≤
      (if AdjoinRoot.mk Q P = AdjoinRoot.mk Q a then 1 / (p : ℝ) ^ P.natDegree else 0) +
        8 / ((p : ℝ) ^ P.natDegree) ^ 2 := by
    intro P hP
    have hd : 0 < P.natDegree := ((mem_irrUpTo p).mp hP).2.1.natDegree_pos
    set r : ℝ := 1 / (p : ℝ) ^ P.natDegree with hr
    have hr0 : 0 ≤ r := by positivity
    have hr2 : r ≤ 1 / 2 := by
      rw [hr]
      apply one_div_le_one_div_of_le (by norm_num)
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ (p : ℝ) ^ 1 := by simpa using hp2
        _ ≤ (p : ℝ) ^ P.natDegree := pow_le_pow_right₀ (by linarith) hd
    set v : ℝ := if AdjoinRoot.mk Q P = AdjoinRoot.mk Q a then r else 0 with hv
    have hv0 : 0 ≤ v := by
      rw [hv]
      split_ifs
      · exact hr0
      · exact le_rfl
    have hterm : ∀ j ∈ Icc 1 N,
        (if j * P.natDegree ≤ N ∧ AdjoinRoot.mk Q P ^ j = AdjoinRoot.mk Q a then
          1 / ((j : ℝ) * (p : ℝ) ^ (j * P.natDegree)) else 0) ≤
        (if j = 1 then v else 0) + r ^ 2 * 4 * (1 / 2 : ℝ) ^ j := by
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hpos : 0 ≤ r ^ 2 * 4 * (1 / 2 : ℝ) ^ j := by positivity
      rcases Nat.eq_or_lt_of_le hj1 with h1 | h2
      · subst h1
        simp only [one_mul, pow_one, Nat.cast_one, ↓reduceIte]
        by_cases hc : P.natDegree ≤ N ∧ AdjoinRoot.mk Q P = AdjoinRoot.mk Q a
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), hv, ite_eq_left_of_eq_true _ _ (eq_true hc.2)]
          linarith
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
          linarith
      · have hj1' : j ≠ 1 := by omega
        simp only [hj1', ↓reduceIte, zero_add]
        split_ifs
        · have hrj : r ^ j = 1 / (p : ℝ) ^ (j * P.natDegree) := by
            rw [hr, one_div_pow, ← pow_mul, mul_comm]
          have h3 : (1 : ℝ) / ((j : ℝ) * (p : ℝ) ^ (j * P.natDegree)) ≤ r ^ j := by
            rw [hrj]
            apply one_div_le_one_div_of_le (by positivity)
            have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
            nlinarith [pow_pos hppos (j * P.natDegree)]
          have h4 : r ^ j ≤ r ^ 2 * 4 * (1 / 2 : ℝ) ^ j := by
            obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
            have h5 : r ^ i ≤ (1 / 2 : ℝ) ^ i := pow_le_pow_left₀ hr0 hr2 i
            calc r ^ (i + 2) = r ^ 2 * r ^ i := by ring
              _ ≤ r ^ 2 * (1 / 2 : ℝ) ^ i := mul_le_mul_of_nonneg_left h5 (by positivity)
              _ = r ^ 2 * 4 * (1 / 2 : ℝ) ^ (i + 2) := by ring
          linarith
        · exact hpos
    have hgeom : ∑ j ∈ Icc 1 N, (1 / 2 : ℝ) ^ j ≤ 2 :=
      (sum_le_sum_of_subset_of_nonneg
        (fun j hj => mem_range.mpr (by have := (mem_Icc.mp hj).2; omega))
        (fun _ _ _ => by positivity)).trans (sum_geometric_two_le (N + 1))
    have hfirst : ∑ j ∈ Icc 1 N, (if j = 1 then v else 0) ≤ v := by
      rw [sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact hv0
    calc (∑ j ∈ Icc 1 N,
          if j * P.natDegree ≤ N ∧ AdjoinRoot.mk Q P ^ j = AdjoinRoot.mk Q a then
            1 / ((j : ℝ) * (p : ℝ) ^ (j * P.natDegree)) else 0)
        ≤ ∑ j ∈ Icc 1 N, ((if j = 1 then v else 0) + r ^ 2 * 4 * (1 / 2 : ℝ) ^ j) :=
          sum_le_sum hterm
      _ = ∑ j ∈ Icc 1 N, (if j = 1 then v else 0) +
            r ^ 2 * 4 * ∑ j ∈ Icc 1 N, (1 / 2 : ℝ) ^ j := by
          rw [sum_add_distrib, mul_sum]
      _ ≤ v + r ^ 2 * 4 * 2 :=
          add_le_add hfirst (mul_le_mul_of_nonneg_left hgeom (by positivity))
      _ = v + 8 / ((p : ℝ) ^ P.natDegree) ^ 2 := by
          rw [hr]
          field_simp
          ring
  calc primePowerSum p Q (AdjoinRoot.mk Q a) N
      ≤ ∑ P ∈ irrUpTo p N,
          ((if AdjoinRoot.mk Q P = AdjoinRoot.mk Q a then 1 / (p : ℝ) ^ P.natDegree else 0) +
            8 / ((p : ℝ) ^ P.natDegree) ^ 2) := sum_le_sum hinner
    _ = ∑ P ∈ ffClassIrredUpTo p Q a N, 1 / (p : ℝ) ^ P.natDegree +
          ∑ P ∈ irrUpTo p N, 8 / ((p : ℝ) ^ P.natDegree) ^ 2 := by
        rw [sum_add_distrib, ← sum_filter, ffClassIrredUpTo_eq p Q hQm]
    _ ≤ ∑ P ∈ ffClassIrredUpTo p Q a N, 1 / (p : ℝ) ^ P.natDegree + 16 :=
        add_le_add le_rfl (sum_irrUpTo_inv_sq_le p N)

end Assembly

/-! ## Kornblum's theorem and the unconditional headline -/

/-- **Kornblum's theorem** (Dirichlet's theorem for `F_p[t]`): for every monic
    irreducible `Q` and every `a` with `Q ∤ a`, the sum of `p^{-deg P}` over the
    monic irreducible `P ≡ a (mod Q)` of degree `≤ Y` tends to infinity with `Y`.
    This discharges the hypothesis `FFDirichletDensity` of `DensityMC.lean`. -/
theorem ffDirichletDensity : FFDirichletDensity p := by
  intro Q hQm hQi a ha
  have : Fact (Irreducible Q) := ⟨hQi⟩
  have hx : AdjoinRoot.mk Q a ≠ 0 := fun h => ha (AdjoinRoot.mk_eq_zero.mp h)
  obtain ⟨C, hC⟩ := main_lower p Q hQm hx
  have hc : (0 : ℝ) < (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hlow : ∀ N : ℕ,
      (∑ n ∈ range N, 1 / ((n : ℝ) + 1) + -C) /
          (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℝ) + -16 ≤
        ∑ P ∈ ffClassIrredUpTo p Q a N, 1 / (p : ℝ) ^ P.natDegree := by
    intro N
    have h1 := hC N
    have h2 := primePowerSum_le p Q hQm a N
    have h3 : (∑ n ∈ range N, 1 / ((n : ℝ) + 1) + -C) /
        (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℝ) ≤
          primePowerSum p Q (AdjoinRoot.mk Q a) N := by
      rw [div_le_iff₀ hc]
      linarith
    linarith
  refine Filter.tendsto_atTop_mono hlow ?_
  exact Filter.tendsto_atTop_add_const_right _ _
    ((Filter.tendsto_atTop_add_const_right _ _
      Real.tendsto_sum_range_one_div_nat_succ_atTop).atTop_div_const hc)

/-- **Unconditional headline**: the trapped density of the function-field mixed
    walk tends to `0` for every monic irreducible target. This is
    `ff_almost_all_genmixed_density` with its only hypothesis (Kornblum's
    theorem) discharged. -/
theorem ff_almost_all_genmixed_density_unconditional : FFAlmostAllGenMixedDensity p :=
  ff_almost_all_genmixed_density p (ffDirichletDensity p)

end FunctionFieldAnalog.Kornblum
