import EM.FunctionField.RunMonodromy

/-!
# The first composite stage over `𝔽_2`: the product becomes indecomposable

Over `𝔽_2` every Euclid–Mullin sequence starts `X, X+1, X²+X+1, X⁴+X+1`, and the products
`P_0, …, P_3` are the additive polynomials `X, X²+X, X⁴+X, X⁸+X⁴+X²+X` (a tower of
compositions of `g = X² + X`; `RunMonodromy.lean`). Stage 3 is the first composite stage:

  `P_3 + 1 = (X⁴ + X³ + 1)(X⁴ + X³ + X² + X + 1)`,

and the next term is one of the two quartics (a tie; the two choices differ by `X ↦ X + 1`).

## Main results

* `ffSeq_four` — the next term is one of the two quartics.
* `derivative_ffProd_four` — `P_4' = s²` with `s = X⁵ + X³ + 1` or `s = X⁵ + X⁴ + X³ + X² + 1`.
* `natDegree_eq_one_of_comp` — a polynomial of degree 12 over `𝔽_2` whose derivative is the
  square of a quintic without roots in `𝔽_2` is indecomposable.
* `ffProd_four_indecomposable` — **`P_4` is indecomposable over `𝔽_2`**: if
  `P_4 = h ∘ q` then `deg q = 1` or `deg h = 1`.

## Reading

Before the composite stage the product is a three-fold composition and the monodromy group
of `P_3(x) − y` is a 2-group. One composite stage later no intermediate field is left
between `𝔽_2(P_4)` and `𝔽_2(x)`: the monodromy group of `P_4(x) − y` over `𝔽_2(y)` is a
primitive group of degree 12. The proof uses only the derivative: in characteristic 2 every
derivative is a square, so `P_4' = h'(q)·q'` forces `s = b(q)·a` with `a² = q'`, `b² = h'`,
and the degrees `deg a < (deg q)/2`, `deg b < (deg h)/2` leave only the trivial splittings.

Not formalized (see `docs/analysis/fibre_rule_2026-11-15.md` §6): the Frobenius class at the
base point `0` has cycle type `(1,1,2,4,4)`, an odd permutation whose square fixes four
points; together with primitivity and the list of primitive groups of degree 12 this gives
the full symmetric group `S_12` as arithmetic monodromy group.
-/

namespace FunctionFieldAnalog

namespace FirstComposite

open Polynomial CompositeFloors FunctionFieldAnalog.CharTwo AutonomousThreshold

/-! ## Derivatives in characteristic two are squares -/

theorem derivative_derivative_eq_zero (f : (ZMod 2)[X]) : derivative (derivative f) = 0 := by
  ext n
  rw [coeff_derivative, coeff_derivative, coeff_zero]
  have h : (((n + 1) * (n + 1 + 1) : ℕ) : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff _ 2).mpr (even_iff_two_dvd.mp (Nat.even_mul_succ_self (n + 1)))
  push_cast at h ⊢
  linear_combination (f.coeff (n + 1 + 1)) * h

/-- Over `𝔽_2` every derivative is a square. -/
theorem exists_sq_eq_derivative (f : (ZMod 2)[X]) : ∃ a : (ZMod 2)[X], derivative f = a ^ 2 :=
  ⟨contract 2 (derivative f), by
    rw [← ZMod.expand_card, expand_contract 2 (derivative_derivative_eq_zero f) two_ne_zero]⟩

/-! ## The indecomposability criterion -/

private theorem arith {m n da db : ℕ} (h12 : n * m = 12) (ha : 2 * da < m) (hb : 2 * db < n)
    (h5 : db * m + da = 5) : m = 1 ∨ n = 1 ∨ (m = 4 ∧ da = 1) := by
  have hm : m ≤ 12 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left n h12)
  interval_cases m <;> omega

/-- A polynomial of degree 12 over `𝔽_2` whose derivative is the square of a quintic without
    roots in `𝔽_2` is indecomposable. -/
theorem natDegree_eq_one_of_comp {P s : (ZMod 2)[X]} (hdeg : P.natDegree = 12)
    (hs : derivative P = s ^ 2) (hs5 : s.natDegree = 5) (hroot : ∀ x : ZMod 2, eval x s ≠ 0)
    {h q : (ZMod 2)[X]} (hP : P = h.comp q) : q.natDegree = 1 ∨ h.natDegree = 1 := by
  obtain ⟨a, ha⟩ := exists_sq_eq_derivative q
  obtain ⟨b, hb⟩ := exists_sq_eq_derivative h
  have h12 : h.natDegree * q.natDegree = 12 := by rw [← natDegree_comp, ← hP, hdeg]
  have hq0 : q.natDegree ≠ 0 := by
    intro h0
    rw [h0] at h12
    omega
  have hh0 : h.natDegree ≠ 0 := by
    intro h0
    rw [h0] at h12
    omega
  have hda : 2 * a.natDegree < q.natDegree := by
    have := natDegree_derivative_lt hq0
    rwa [ha, natDegree_pow] at this
  have hdb : 2 * b.natDegree < h.natDegree := by
    have := natDegree_derivative_lt hh0
    rwa [hb, natDegree_pow] at this
  have hsq : s ^ 2 = (b.comp q * a) ^ 2 := by
    rw [← hs, hP, derivative_comp, ha, hb, pow_comp, mul_pow, mul_comm]
  have hsb : s = b.comp q * a := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · exact h1
    · rwa [CharTwo.neg_eq] at h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs5
  have hba : b.comp q ≠ 0 ∧ a ≠ 0 := by
    rw [hsb] at hs0
    exact mul_ne_zero_iff.mp hs0
  have h5 : b.natDegree * q.natDegree + a.natDegree = 5 := by
    rw [← natDegree_comp, ← natDegree_mul hba.1 hba.2, ← hsb, hs5]
  rcases arith h12 hda hdb h5 with h1 | h1 | ⟨-, ha1⟩
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have hdeg1 : a.degree = 1 := by
      rw [degree_eq_natDegree hba.2, ha1]
      rfl
    obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one hdeg1
    exact hroot x (hx.dvd ⟨b.comp q, by rw [hsb, mul_comm]⟩)

/-! ## The first composite stage -/

/-- The term chosen at the first composite stage is one of the two quartic factors. -/
theorem ffSeq_four (d : FFEMData 2) :
    d.ffSeq 4 = X ^ 4 + X ^ 3 + 1 ∨ d.ffSeq 4 = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  obtain ⟨hπm, hπi, hπd⟩ := d.ffSeq_succ 3
  obtain ⟨h0, h1, h2, -⟩ := ff_two_attains_three d
  have hrun : ∀ j, j < 3 → Irreducible (d.ffProd (0 + j) + 1) := by
    intro j hj
    interval_cases j <;> simpa
  have h4 : 2 ^ (1 + 1) ∣ (d.ffSeq (3 + 1)).natDegree :=
    two_pow_succ_dvd_natDegree_of_run d 0 3 1 hrun (by norm_num) hπi (by simpa using hπd)
  have hpos : 0 < (d.ffSeq (3 + 1)).natDegree := hπi.natDegree_pos
  have hA : (X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).natDegree = 4 := by compute_degree!
  have hB : (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 4 := by compute_degree!
  have hAm : (X ^ 4 + X ^ 3 + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hBm : (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by monicity!
  rw [euclid_three_factor] at hπd
  obtain ⟨t, ht⟩ := h4
  rcases hπi.prime.dvd_mul.mp hπd with hd | hd
  · left
    have hle := natDegree_le_of_dvd hd hAm.ne_zero
    exact (eq_of_monic_of_dvd_of_natDegree_le hπm hAm hd (by omega)).symm
  · right
    have hle := natDegree_le_of_dvd hd hBm.ne_zero
    exact (eq_of_monic_of_dvd_of_natDegree_le hπm hBm hd (by omega)).symm

private theorem C8 : (C ((8 : ℕ) : ZMod 2) : (ZMod 2)[X]) = 0 := by
  rw [show ((8 : ℕ) : ZMod 2) = 0 from by decide, C_0]

private theorem C4 : (C ((4 : ℕ) : ZMod 2) : (ZMod 2)[X]) = 0 := by
  rw [show ((4 : ℕ) : ZMod 2) = 0 from by decide, C_0]

private theorem C2 : (C ((2 : ℕ) : ZMod 2) : (ZMod 2)[X]) = 0 := by
  rw [show ((2 : ℕ) : ZMod 2) = 0 from by decide, C_0]

private theorem C3 : (C ((3 : ℕ) : ZMod 2) : (ZMod 2)[X]) = 1 := by
  rw [show ((3 : ℕ) : ZMod 2) = 1 from by decide, C_1]

private theorem derivative_A :
    derivative ((X ^ 8 + X ^ 4 + X ^ 2 + X) * (X ^ 4 + X ^ 3 + 1) : (ZMod 2)[X]) =
      (X ^ 5 + X ^ 3 + 1) ^ 2 := by
  simp only [derivative_mul, derivative_add, derivative_X_pow, derivative_X, derivative_one,
    C8, C4, C2, C3, Nat.reduceSub, zero_mul, one_mul, add_zero, zero_add]
  linear_combination (X ^ 4 - X ^ 8 - X ^ 5 : (ZMod 2)[X]) * two_eq_zero_poly

private theorem derivative_B :
    derivative ((X ^ 8 + X ^ 4 + X ^ 2 + X) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) : (ZMod 2)[X]) =
      (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1) ^ 2 := by
  simp only [derivative_mul, derivative_add, derivative_X_pow, derivative_X, derivative_one,
    C8, C4, C2, C3, Nat.reduceSub, zero_mul, one_mul, add_zero, zero_add]
  linear_combination
    (X - X ^ 9 - X ^ 8 - 2 * X ^ 7 - X ^ 6 - 2 * X ^ 5 : (ZMod 2)[X]) * two_eq_zero_poly

/-- The derivative of `P_4` is the square of a quintic, in either branch of the tie. -/
theorem derivative_ffProd_four (d : FFEMData 2) :
    derivative (d.ffProd 4) = (X ^ 5 + X ^ 3 + 1) ^ 2 ∨
      derivative (d.ffProd 4) = (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + 1) ^ 2 := by
  have hP : d.ffProd 4 = d.ffProd 3 * d.ffSeq 4 := d.ffProd_succ 3
  rcases ffSeq_four d with h | h
  · left
    rw [hP, ffProd_three, h]
    exact derivative_A
  · right
    rw [hP, ffProd_three, h]
    exact derivative_B

theorem ffProd_four_natDegree (d : FFEMData 2) : (d.ffProd 4).natDegree = 12 := by
  have hP : d.ffProd 4 = d.ffProd 3 * d.ffSeq 4 := d.ffProd_succ 3
  have h3 : (d.ffProd 3).natDegree = 8 := by
    rw [ffProd_three]
    compute_degree!
  have h4 : (d.ffSeq 4).natDegree = 4 := by
    rcases ffSeq_four d with h | h <;> rw [h] <;> compute_degree!
  rw [hP, (ffProd_monic 2 d 3).natDegree_mul (ffSeq_monic 2 d 4), h3, h4]

/-- **After the first composite stage the product is indecomposable.** If `P_4 = h ∘ q` over
    `𝔽_2`, then `q` or `h` is linear. Compare `P_3 = g ∘ g ∘ g`. -/
theorem ffProd_four_indecomposable (d : FFEMData 2) {h q : (ZMod 2)[X]}
    (hP : d.ffProd 4 = h.comp q) : q.natDegree = 1 ∨ h.natDegree = 1 := by
  rcases derivative_ffProd_four d with hs | hs
  · refine natDegree_eq_one_of_comp (ffProd_four_natDegree d) hs (by compute_degree!) ?_ hP
    intro x
    simp only [eval_add, eval_pow, eval_X, eval_one]
    revert x
    decide
  · refine natDegree_eq_one_of_comp (ffProd_four_natDegree d) hs (by compute_degree!) ?_ hP
    intro x
    simp only [eval_add, eval_pow, eval_X, eval_one]
    revert x
    decide

end FirstComposite

end FunctionFieldAnalog
