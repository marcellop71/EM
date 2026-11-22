import EM.FunctionField.KornblumSeries
import EM.FunctionField.KornblumVonMangoldt
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.AdjoinRoot

/-!
# Kornblum's theorem, part 3: `L`-functions of characters mod `Q` and `L(1/q, χ) ≠ 0`

Let `Q` be a monic irreducible polynomial of degree `d` over `F_p`, and let
`F = F_p[t]/(Q) = AdjoinRoot Q`, a finite field. A multiplicative character
`χ : MulChar F ℂ` gives the completely multiplicative function
`f ↦ χ(f mod Q)` on polynomials (`charHom`), with `L`-series
`L(u, χ) = ∑_n A_n(χ) u^n` (`lSer`) and logarithmic derivative
`Ψ(u, χ) = ∑_n Ψ_n(χ) u^n` (`psiSer`); see `KornblumVonMangoldt.lean`.

Main results.

* `charSum_eq_zero`: **exact cancellation**. For `χ ≠ 1` and `n ≥ d`,
  `A_n(χ) = 0`: every residue class mod `Q` contains exactly `p^{n-d}` monic
  polynomials of degree `n`, so `A_n(χ) = p^{n-d} ∑_{x ∈ F} χ(x) = 0`. Thus
  `L(u, χ)` is a polynomial of degree `< d`.
* `one_sub_mul_lSer_one`: for the trivial character,
  `(1 - p u) · L(u, 1) = 1 - u^d`.
* `sum_char_eq`: orthogonality, `∑_χ χ(y) = #characters` if `y = 1`, else `0`.
* `lPoly_eval_ne_zero`: **non-vanishing**, `L(1/p, χ) = ∑_{k<d} A_k(χ) p^{-k} ≠ 0`
  for `χ ≠ 1`.
* `bounded_psi_sums`: for `χ ≠ 1` the partial sums of `∑_n Ψ_n(χ) / (n p^n)`
  are bounded.

Proof of non-vanishing. Let `LL(u) = ∏_χ L(u, χ)`. Its logarithmic derivative is
`∑_χ Ψ(u, χ)`, whose `n`-th coefficient is, by orthogonality,
`#characters · ∑ deg P` over the pairs `(P, j)` with `j deg P = n` and
`P^j ≡ 1 (mod Q)`. This is `≥ 0`, and it is `> 0` whenever `n` is a multiple of
`#F - 1` (take `P` linear, `P ≠ Q`: then `P^{#F-1} ≡ 1`). By
`coeff_nonneg_of_theta` the coefficients `LL_n` are non-negative and non-zero for
all multiples `n` of `#F - 1`: `LL` is not a polynomial. But if `L(1/p, χ) = 0`
for some `χ ≠ 1`, then `L(u, χ) = (1 - p u) T(u)` with `T` a polynomial, and
`LL = (1 - p u) L(u, 1) · T · ∏_{χ' ≠ 1, χ} L(u, χ') = (1 - u^d) · T · ∏ …` is a
polynomial. Contradiction. (This is the classical argument; the Euler product is
replaced by the logarithmic-derivative recursion.)
-/

namespace FunctionFieldAnalog.Kornblum

open Polynomial Finset

open scoped Classical

variable (p : ℕ) [hp : Fact (Nat.Prime p)]
variable (Q : Polynomial (ZMod p)) [hQ : Fact (Irreducible Q)]

/-! ## The residue field and its characters -/

theorem finite_adjoinRoot : Finite (AdjoinRoot Q) := by
  have : Module.Finite (ZMod p) (AdjoinRoot Q) :=
    (AdjoinRoot.powerBasis hQ.out.ne_zero).finite
  exact Module.finite_of_finite (ZMod p)

/-- The residue field `F_p[t]/(Q)` is finite. -/
noncomputable scoped instance fintypeAdjoinRoot : Fintype (AdjoinRoot Q) :=
  haveI := finite_adjoinRoot p Q
  Fintype.ofFinite _

/-- There are finitely many characters of `F_p[t]/(Q)`. -/
noncomputable scoped instance fintypeMulChar : Fintype (MulChar (AdjoinRoot Q) ℂ) :=
  Fintype.ofFinite _

/-- The completely multiplicative function `f ↦ χ(f mod Q)` on polynomials. -/
noncomputable def charHom (χ : MulChar (AdjoinRoot Q) ℂ) : Polynomial (ZMod p) →* ℂ :=
  χ.toMonoidHom.comp (AdjoinRoot.mk Q : Polynomial (ZMod p) →+* AdjoinRoot Q).toMonoidHom

omit hQ in
@[simp] theorem charHom_apply (χ : MulChar (AdjoinRoot Q) ℂ) (f : Polynomial (ZMod p)) :
    charHom p Q χ f = χ (AdjoinRoot.mk Q f) := rfl

/-- Character values have modulus at most `1`. -/
theorem norm_char_le_one (χ : MulChar (AdjoinRoot Q) ℂ) (y : AdjoinRoot Q) : ‖χ y‖ ≤ 1 := by
  by_cases hy : IsUnit y
  · have h : χ y ^ Fintype.card (AdjoinRoot Q)ˣ = 1 := by
      obtain ⟨u, rfl⟩ := hy
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero).le
  · rw [χ.map_nonunit hy, norm_zero]
    exact zero_le_one

/-- **Orthogonality of characters**: `∑_χ χ(y)` is the number of characters if
    `y = 1` and `0` otherwise. -/
theorem sum_char_eq (y : AdjoinRoot Q) :
    ∑ χ : MulChar (AdjoinRoot Q) ℂ, χ y =
      if y = 1 then (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℂ) else 0 := by
  split_ifs with hy
  · simp [hy]
  · obtain ⟨χ, hχ⟩ :=
      MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (AdjoinRoot Q) ℂ hy
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

/-- The trivial character, as a function on polynomials, is the indicator of
    `Q ∤ f`. -/
theorem charHom_one_apply (f : Polynomial (ZMod p)) :
    charHom p Q 1 f = if Q ∣ f then 0 else 1 := by
  rw [charHom_apply]
  split_ifs with h
  · rw [AdjoinRoot.mk_eq_zero.mpr h]
    exact MulChar.map_zero _
  · have hu : IsUnit (AdjoinRoot.mk Q f) :=
      isUnit_iff_ne_zero.mpr fun h0 => h (AdjoinRoot.mk_eq_zero.mp h0)
    exact MulChar.one_apply hu

/-! ## The coefficients `A_n(χ)` -/

theorem psi_zero (φ : Polynomial (ZMod p) →* ℂ) : psi p φ 0 = 0 := by
  simp [psi]

theorem charSum_zero (φ : Polynomial (ZMod p) →* ℂ) : charSum p φ 0 = 1 := by
  have h : ffMonicDeg p 0 = {1} := by
    ext f
    rw [mem_ffMonicDeg, mem_singleton]
    constructor
    · rintro ⟨hm, hd⟩
      exact eq_one_of_monic_natDegree_zero hm hd
    · rintro rfl
      exact ⟨monic_one, natDegree_one⟩
  rw [charSum, h, sum_singleton, map_one]

/-- **Exact cancellation**: for a non-trivial character `χ` mod `Q` and `n ≥ deg Q`,
    the sum of `χ` over the monic polynomials of degree `n` vanishes. -/
theorem charSum_eq_zero (hQm : Q.Monic) {χ : MulChar (AdjoinRoot Q) ℂ} (hχ : χ ≠ 1) {n : ℕ}
    (hn : Q.natDegree ≤ n) : charSum p (charHom p Q χ) n = 0 := by
  unfold charSum
  rw [← Finset.sum_fiberwise (ffMonicDeg p n) (fun f => AdjoinRoot.mk Q f)]
  have h : ∀ x : AdjoinRoot Q,
      ∑ f ∈ (ffMonicDeg p n).filter (fun f => AdjoinRoot.mk Q f = x), charHom p Q χ f =
        (p : ℂ) ^ (n - Q.natDegree) * χ x := by
    intro x
    obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective x
    have hc : ∀ f ∈ (ffMonicDeg p n).filter (fun f => AdjoinRoot.mk Q f = AdjoinRoot.mk Q r),
        charHom p Q χ f = χ (AdjoinRoot.mk Q r) := fun f hf => by
      rw [charHom_apply, (mem_filter.mp hf).2]
    rw [sum_congr rfl hc, sum_const, nsmul_eq_mul]
    congr 1
    have hfil : (ffMonicDeg p n).filter (fun f => AdjoinRoot.mk Q f = AdjoinRoot.mk Q r) =
        (ffMonicDeg p n).filter (fun f => Q ∣ f - r) := by
      ext f
      simp [AdjoinRoot.mk_eq_mk]
    rw [hfil, ffMonicDeg_residue_card p hQm r hn]
    push_cast
    rfl
  rw [sum_congr rfl fun x _ => h x, ← mul_sum, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

/-- For the trivial character, `A_n(1) = p^n - p^{n-d}` if `n ≥ d = deg Q`, and
    `A_n(1) = p^n` otherwise. -/
theorem charSum_one_char (hQm : Q.Monic) (n : ℕ) :
    charSum p (charHom p Q 1) n =
      (p : ℂ) ^ n - if Q.natDegree ≤ n then (p : ℂ) ^ (n - Q.natDegree) else 0 := by
  have h1 : ∀ f : Polynomial (ZMod p),
      charHom p Q 1 f = 1 - if Q ∣ f then 1 else 0 := by
    intro f
    rw [charHom_one_apply]
    split_ifs <;> simp
  unfold charSum
  rw [sum_congr rfl fun f _ => h1 f, sum_sub_distrib, sum_const, ffMonicDeg_card, nsmul_eq_mul,
    mul_one, sum_boole]
  congr 1
  · push_cast
    rfl
  · split_ifs with hle
    · have h := ffMonicDeg_residue_card p hQm (0 : Polynomial (ZMod p)) hle
      simp only [sub_zero] at h
      rw [h]
      push_cast
      rfl
    · rw [filter_dvd_eq_empty p (not_le.mp hle)]
      simp

/-! ## The `L`-series as power series -/

/-- `L(u, χ) = ∑_n A_n(χ) u^n`. -/
noncomputable def lSer (χ : MulChar (AdjoinRoot Q) ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (charSum p (charHom p Q χ))

/-- `Ψ(u, χ) = ∑_n Ψ_n(χ) u^n`, the logarithmic derivative of `L(u, χ)`. -/
noncomputable def psiSer (χ : MulChar (AdjoinRoot Q) ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (psi p (charHom p Q χ))

omit hQ in
/-- `u L'(u, χ) = L(u, χ) Ψ(u, χ)`. -/
theorem theta_lSer (χ : MulChar (AdjoinRoot Q) ℂ) :
    theta (lSer p Q χ) = lSer p Q χ * psiSer p Q χ := by
  rw [mul_comm]
  ext n
  simp only [lSer, psiSer, coeff_theta, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [vonMangoldt_identity,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => psi p (charHom p Q χ) k * charSum p (charHom p Q χ) l)]

/-- The polynomial `∑_{k < deg Q} A_k(χ) u^k`. -/
noncomputable def lPoly (χ : MulChar (AdjoinRoot Q) ℂ) : Polynomial ℂ :=
  ∑ k ∈ range Q.natDegree, monomial k (charSum p (charHom p Q χ) k)

/-- For `χ ≠ 1` the series `L(u, χ)` is the polynomial `lPoly χ` of degree `< deg Q`. -/
theorem lSer_eq_coe_lPoly (hQm : Q.Monic) {χ : MulChar (AdjoinRoot Q) ℂ} (hχ : χ ≠ 1) :
    lSer p Q χ = ((lPoly p Q χ : Polynomial ℂ) : PowerSeries ℂ) := by
  ext n
  rw [Polynomial.coeff_coe, lPoly, finsetSum_coeff]
  simp only [coeff_monomial, sum_ite_eq', mem_range, lSer, PowerSeries.coeff_mk]
  split_ifs with h
  · rfl
  · exact charSum_eq_zero p Q hQm hχ (not_lt.mp h)

omit hp in
/-- The geometric series: `(1 - p u) · ∑_n p^n u^n = 1`. -/
theorem one_sub_mul_geom :
    (1 - PowerSeries.C (p : ℂ) * PowerSeries.X) * PowerSeries.mk (fun n => (p : ℂ) ^ n) = 1 := by
  ext n
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [PowerSeries.coeff_one, pow_succ, mul_comm]

/-- For the trivial character, `(1 - p u) L(u, 1) = 1 - u^d`. -/
theorem one_sub_mul_lSer_one (hQm : Q.Monic) :
    (1 - PowerSeries.C (p : ℂ) * PowerSeries.X) * lSer p Q 1 =
      1 - PowerSeries.X ^ Q.natDegree := by
  set G : PowerSeries ℂ := PowerSeries.mk fun n => (p : ℂ) ^ n with hG
  have h1 : lSer p Q 1 = (1 - PowerSeries.X ^ Q.natDegree) * G := by
    ext n
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
    simp only [lSer, hG, PowerSeries.coeff_mk]
    exact charSum_one_char p Q hQm n
  have h2 : (1 - PowerSeries.C (p : ℂ) * PowerSeries.X) * G = 1 := one_sub_mul_geom p
  rw [h1, mul_left_comm, h2, mul_one]

/-! ## The coefficients of `∑_χ Ψ(u, χ)` -/

/-- By orthogonality, `∑_χ Ψ_n(χ)` is `#characters` times the sum of `deg P` over
    the pairs `(P, j)` with `j deg P = n` and `P^j ≡ 1 (mod Q)`. -/
theorem sum_psi_char (n : ℕ) :
    ∑ χ : MulChar (AdjoinRoot Q) ℂ, psi p (charHom p Q χ) n =
      ∑ P ∈ irrUpTo p n, ∑ j ∈ Icc 1 n,
        if j * P.natDegree = n then
          (P.natDegree : ℂ) * (if AdjoinRoot.mk Q P ^ j = 1 then
            (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℂ) else 0)
        else 0 := by
  unfold psi
  rw [sum_comm]
  refine sum_congr rfl fun P _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : j * P.natDegree = n
  · simp only [h, ↓reduceIte, charHom_apply, ← map_pow]
    rw [← mul_sum, sum_char_eq]
  · simp [h]

open ComplexOrder in
/-- `∑_χ Ψ_n(χ)` is a non-negative real number. -/
theorem sum_psi_char_nonneg (n : ℕ) :
    0 ≤ ∑ χ : MulChar (AdjoinRoot Q) ℂ, psi p (charHom p Q χ) n := by
  rw [sum_psi_char]
  refine sum_nonneg fun P _ => sum_nonneg fun j _ => ?_
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact mul_nonneg (Nat.cast_nonneg _) le_rfl
  · exact le_rfl

/-- There is a monic irreducible polynomial of degree `1` different from `Q`. -/
theorem exists_linear_not_dvd (hQm : Q.Monic) :
    ∃ P0 : Polynomial (ZMod p), P0.Monic ∧ Irreducible P0 ∧ P0.natDegree = 1 ∧ ¬Q ∣ P0 := by
  have key : ∀ c : ZMod p, Q ∣ (X + C c) → Q = X + C c := fun c h =>
    eq_of_monic_of_associated hQm (monic_X_add_C c)
      (hQ.out.associated_of_dvd (irreducible_of_degree_eq_one (degree_X_add_C c)) h)
  by_cases h0 : Q ∣ X + C (0 : ZMod p)
  · refine ⟨X + C 1, monic_X_add_C 1, irreducible_of_degree_eq_one (degree_X_add_C 1),
      natDegree_X_add_C 1, fun h1 => ?_⟩
    have h := (key 0 h0).symm.trans (key 1 h1)
    exact zero_ne_one (C_injective (add_left_cancel h))
  · exact ⟨X + C 0, monic_X_add_C 0, irreducible_of_degree_eq_one (degree_X_add_C 0),
      natDegree_X_add_C 0, h0⟩

open ComplexOrder in
/-- `∑_χ Ψ_n(χ) > 0` when `n` is a positive multiple of `#F - 1`. -/
theorem sum_psi_char_pos (hQm : Q.Monic) {j0 : ℕ} (hj0 : 0 < j0) :
    0 < ∑ χ : MulChar (AdjoinRoot Q) ℂ,
      psi p (charHom p Q χ) ((Fintype.card (AdjoinRoot Q) - 1) * j0) := by
  obtain ⟨P0, hP0m, hP0i, hP0d, hP0Q⟩ := exists_linear_not_dvd p Q hQm
  set m := Fintype.card (AdjoinRoot Q) - 1 with hm
  have hm1 : 1 ≤ m := by
    have := Fintype.one_lt_card (α := AdjoinRoot Q)
    omega
  have hn1 : 1 ≤ m * j0 := Nat.mul_pos hm1 hj0
  have hcard : (0 : ℂ) < (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℂ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hnn : ∀ (P : Polynomial (ZMod p)) (j : ℕ),
      (0 : ℂ) ≤ if j * P.natDegree = m * j0 then
          (P.natDegree : ℂ) * (if AdjoinRoot.mk Q P ^ j = 1 then
            (Fintype.card (MulChar (AdjoinRoot Q) ℂ) : ℂ) else 0)
        else 0 := by
    intro P j
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact mul_nonneg (Nat.cast_nonneg _) le_rfl
    · exact le_rfl
  rw [sum_psi_char]
  refine sum_pos' (fun P _ => sum_nonneg fun j _ => hnn P j) ⟨P0, ?_, ?_⟩
  · rw [mem_irrUpTo]
    exact ⟨hP0m, hP0i, hP0d ▸ hn1⟩
  · refine sum_pos' (fun j _ => hnn P0 j) ⟨m * j0, mem_Icc.mpr ⟨hn1, le_rfl⟩, ?_⟩
    have hne : AdjoinRoot.mk Q P0 ≠ 0 := fun h0 => hP0Q (AdjoinRoot.mk_eq_zero.mp h0)
    have hpow : AdjoinRoot.mk Q P0 ^ (m * j0) = 1 := by
      rw [pow_mul, hm, FiniteField.pow_card_sub_one_eq_one _ hne, one_pow]
    simp only [hP0d, mul_one, hpow, ↓reduceIte, Nat.cast_one, one_mul]
    exact hcard

/-! ## Non-vanishing of `L(1/p, χ)` -/

open ComplexOrder in
/-- **Non-vanishing at the pole of the zeta function**: for a non-trivial
    character `χ` mod `Q`, `L(1/p, χ) = ∑_{k < deg Q} A_k(χ) p^{-k} ≠ 0`. -/
theorem lPoly_eval_ne_zero (hQm : Q.Monic) {χ : MulChar (AdjoinRoot Q) ℂ} (hχ : χ ≠ 1) :
    ∑ k ∈ range Q.natDegree, charSum p (charHom p Q χ) k * ((p : ℂ)⁻¹) ^ k ≠ 0 := by
  intro hzero
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set d := Q.natDegree with hd
  set T : MulChar (AdjoinRoot Q) ℂ → Polynomial ℂ := fun χ' => lPoly p Q χ' with hT
  -- `1/p` is a root of the polynomial `L(u, χ)`
  have hroot : (T χ).IsRoot (p : ℂ)⁻¹ := by
    rw [IsRoot.def, ← hzero]
    simp [hT, lPoly, eval_finsetSum, eval_monomial, hd]
  obtain ⟨T0, hT0⟩ := dvd_iff_isRoot.mpr hroot
  have hfac : T χ = (1 - C (p : ℂ) * X) * (C (-(p : ℂ)⁻¹) * T0) := by
    have hCC : (C (p : ℂ) * C ((p : ℂ)⁻¹) : Polynomial ℂ) = 1 := by
      rw [← C_mul, mul_inv_cancel₀ hp0, C_1]
    rw [hT0, C_neg]
    linear_combination (-(X : Polynomial ℂ) * T0) * hCC
  -- the product of all `L`-series and its logarithmic derivative
  set LL : PowerSeries ℂ := ∏ χ' : MulChar (AdjoinRoot Q) ℂ, lSer p Q χ' with hLLdef
  have hθ : theta LL = LL * ∑ χ' : MulChar (AdjoinRoot Q) ℂ, psiSer p Q χ' :=
    theta_prod _ _ _ fun χ' _ => theta_lSer p Q χ'
  -- `LL` is a polynomial
  set W : Polynomial ℂ :=
    (1 - X ^ d) * ((C (-(p : ℂ)⁻¹) * T0) * ∏ χ' ∈ (univ.erase 1).erase χ, T χ') with hW
  have hLL : LL = (W : PowerSeries ℂ) := by
    have h1 : (1 - PowerSeries.C (p : ℂ) * PowerSeries.X) * LL =
        (1 - PowerSeries.C (p : ℂ) * PowerSeries.X) * (W : PowerSeries ℂ) := by
      have hsplit : LL = lSer p Q 1 * ∏ χ' ∈ univ.erase 1, lSer p Q χ' :=
        (mul_prod_erase univ _ (mem_univ 1)).symm
      have hrest : ∏ χ' ∈ univ.erase (1 : MulChar (AdjoinRoot Q) ℂ), lSer p Q χ' =
          ((∏ χ' ∈ univ.erase 1, T χ' : Polynomial ℂ) : PowerSeries ℂ) := by
        rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
        refine prod_congr rfl fun χ' hχ' => ?_
        exact lSer_eq_coe_lPoly p Q hQm (ne_of_mem_erase hχ')
      have hsplit2 : ∏ χ' ∈ univ.erase (1 : MulChar (AdjoinRoot Q) ℂ), T χ' =
          T χ * ∏ χ' ∈ (univ.erase 1).erase χ, T χ' :=
        (mul_prod_erase _ _ (mem_erase.mpr ⟨hχ, mem_univ _⟩)).symm
      rw [hsplit, ← mul_assoc, one_sub_mul_lSer_one p Q hQm, hrest, hsplit2, hfac]
      simp only [hW, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
        Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C]
      ring
    have h3 := congrArg (fun S => PowerSeries.mk (fun n => (p : ℂ) ^ n) * S) h1
    simp only [← mul_assoc] at h3
    rwa [mul_comm (PowerSeries.mk fun n => (p : ℂ) ^ n), one_sub_mul_geom p, one_mul,
      one_mul] at h3
  -- but its coefficients are positive at all multiples of `#F - 1`
  have hcoef0 : PowerSeries.coeff 0 LL = 1 := by
    simp [hLLdef, PowerSeries.coeff_zero_eq_constantCoeff, map_prod, lSer, charSum_zero]
  have hcoefB : ∀ n, PowerSeries.coeff n (∑ χ' : MulChar (AdjoinRoot Q) ℂ, psiSer p Q χ') =
      ∑ χ' : MulChar (AdjoinRoot Q) ℂ, psi p (charHom p Q χ') n := by
    intro n
    simp [psiSer, map_sum]
  have hB0 : PowerSeries.coeff 0 (∑ χ' : MulChar (AdjoinRoot Q) ℂ, psiSer p Q χ') = 0 := by
    rw [hcoefB]
    simp [psi_zero]
  have hBn : ∀ n, 0 ≤ PowerSeries.coeff n (∑ χ' : MulChar (AdjoinRoot Q) ℂ, psiSer p Q χ') := by
    intro n
    rw [hcoefB]
    exact sum_psi_char_nonneg p Q n
  have hpos := sum_psi_char_pos p Q hQm (Nat.succ_pos W.natDegree)
  set n := (Fintype.card (AdjoinRoot Q) - 1) * (W.natDegree + 1) with hn
  have h2 := (coeff_nonneg_of_theta hcoef0 hB0 hθ hBn n).2
  have hlt : W.natDegree < n := by
    have hm1 : 1 ≤ Fintype.card (AdjoinRoot Q) - 1 := by
      have := Fintype.one_lt_card (α := AdjoinRoot Q)
      omega
    have := Nat.le_mul_of_pos_left (W.natDegree + 1) hm1
    omega
  have hLLn : PowerSeries.coeff n LL = 0 := by
    rw [hLL, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  rw [hLLn, mul_zero, hcoefB] at h2
  exact absurd (hpos.trans_le h2) (lt_irrefl _)

/-! ## Bounded partial sums of `Ψ_n(χ) / (n p^n)` -/

/-- For a non-trivial character `χ` mod `Q`, the partial sums of
    `∑_n Ψ_n(χ) / (n p^n)` are bounded. -/
theorem bounded_psi_sums (hQm : Q.Monic) {χ : MulChar (AdjoinRoot Q) ℂ} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ range N, psi p (charHom p Q χ) n / ((n : ℂ) * (p : ℂ) ^ n)‖ ≤ C := by
  set φ := charHom p Q χ with hφ
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hppos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hφ1 : ∀ f, ‖φ f‖ ≤ 1 := fun f => norm_char_le_one p Q χ _
  have hb : ∀ n, ‖psi p φ n * ((p : ℂ)⁻¹) ^ n‖ ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [psi_zero]
    · have h1 := norm_psi_le p φ hφ1 n
      rw [psiNat_eq p hn] at h1
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, inv_pow, ← div_eq_mul_inv,
        div_le_one (pow_pos hppos n)]
      exact_mod_cast h1
  have hrec : ∀ n, Q.natDegree ≤ n → ∑ k ∈ range Q.natDegree,
      (charSum p φ k * ((p : ℂ)⁻¹) ^ k) * (psi p φ (n - k) * ((p : ℂ)⁻¹) ^ (n - k)) = 0 := by
    intro n hn
    have hvm := vonMangoldt_identity p φ n
    rw [charSum_eq_zero p Q hQm hχ hn, mul_zero, ← Finset.sum_range_reflect] at hvm
    have hsub : range Q.natDegree ⊆ range (n + 1) :=
      range_subset_range.mpr (by omega)
    have h3 : ∑ k ∈ range Q.natDegree, charSum p φ k * psi p φ (n - k) = 0 := by
      rw [sum_subset hsub]
      · refine Eq.trans ?_ hvm.symm
        refine sum_congr rfl fun k hk => ?_
        have hk' := mem_range.mp hk
        have h4 : n - (n + 1 - 1 - k) = k := by omega
        rw [h4, Nat.add_sub_cancel, mul_comm]
      · intro k hk hk'
        rw [charSum_eq_zero p Q hQm hχ (not_lt.mp fun h => hk' (mem_range.mpr h)), zero_mul]
    have h5 : ∀ k ∈ range Q.natDegree,
        (charSum p φ k * ((p : ℂ)⁻¹) ^ k) * (psi p φ (n - k) * ((p : ℂ)⁻¹) ^ (n - k)) =
          ((p : ℂ)⁻¹) ^ n * (charSum p φ k * psi p φ (n - k)) := by
      intro k hk
      have hk' : k ≤ n := by have := mem_range.mp hk; omega
      conv_rhs => rw [← Nat.add_sub_cancel' hk', pow_add]
      rw [Nat.add_sub_cancel' hk']
      ring
    rw [sum_congr rfl h5, ← mul_sum, h3, mul_zero]
  obtain ⟨C, hC⟩ := bounded_partial_sums (d := Q.natDegree)
    (fun k => charSum p φ k * ((p : ℂ)⁻¹) ^ k) (fun n => psi p φ n * ((p : ℂ)⁻¹) ^ n)
    hb hrec (lPoly_eval_ne_zero p Q hQm hχ)
  refine ⟨C, fun N => ?_⟩
  have heq : ∑ n ∈ range N, psi p φ n / ((n : ℂ) * (p : ℂ) ^ n) =
      ∑ n ∈ range N, psi p φ n * ((p : ℂ)⁻¹) ^ n / n := by
    refine sum_congr rfl fun n _ => ?_
    rw [inv_pow, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
    ring
  rw [heq]
  exact hC N

end FunctionFieldAnalog.Kornblum
