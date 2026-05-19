import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic

/-!
# Parseval / Plancherel for `ZMod.dft` (Mathlib-only)

`∑_k ‖𝓕 Φ k‖² = N · ∑_j ‖Φ j‖²` and its complex inner-product form, for the discrete Fourier
transform `ZMod.dft` on `ZMod N`.  Mathlib (v4.33.0) has the algebraic API of `ZMod.dft` but no
norm-level identity.  Extracted 2026-08-18 from `EM/LargeSieve/Harmonic.lean` (candidate for
upstreaming; Mathlib-style names `ZMod.dft_mul_conj_sum`, `ZMod.dft_norm_sq_sum` are provided).
-/

section ParsevalZModDFT

open scoped ZMod

variable {N : ℕ} [NeZero N]

open Classical in
/-- **Additive character orthogonality on `ZMod N`**: the sum
    `sum_{k : ZMod N} stdAddChar(a * k)` equals `N` when `a = 0`
    and `0` otherwise.

    This is a direct corollary of `AddChar.sum_mulShift` applied to
    the primitive character `stdAddChar` on `ZMod N`. -/
theorem stdAddChar_sum_eq (a : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (a * k) =
    if a = (0 : ZMod N) then (N : ℂ) else 0 := by
  have hprim := ZMod.isPrimitive_stdAddChar N
  conv_lhs => arg 2; ext k; rw [mul_comm]
  have h := AddChar.sum_mulShift a hprim
  simp only [ZMod.card] at h
  exact_mod_cast h

/-- **Parseval identity for `ZMod.dft` (complex inner product form)**.

    `sum_k (F Phi k) * conj(F Phi k) = N * sum_j Phi j * conj(Phi j)`

    where `F` denotes the discrete Fourier transform `ZMod.dft`.

    **Proof**: Expand both DFTs, distribute the product of sums,
    swap summation order, combine character factors using `map_add_eq_mul`,
    and apply character orthogonality (`stdAddChar_sum_eq`) to collapse
    the diagonal. -/
theorem zmod_dft_parseval_complex (Phi : ZMod N → ℂ) :
    ∑ k : ZMod N, (𝓕 Phi k * starRingEnd ℂ (𝓕 Phi k)) =
    (N : ℂ) * ∑ j : ZMod N, (Phi j * starRingEnd ℂ (Phi j)) := by
  -- Step 1: Expand DFT definition
  simp_rw [ZMod.dft_apply, smul_eq_mul]
  -- Step 2: Distribute conjugation over sums and products
  simp_rw [map_sum (starRingEnd ℂ), map_mul (starRingEnd ℂ)]
  -- Step 3: Simplify conj(stdAddChar(-(j'*k))) = stdAddChar(j'*k)
  -- using map_neg_eq_conj and starRingEnd_self_apply (conj of conj = id)
  simp_rw [show ∀ (j' k : ZMod N), (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * k))) =
    ZMod.stdAddChar (j' * k) from fun j' k => by
    rw [AddChar.map_neg_eq_conj, starRingEnd_self_apply]]
  -- Step 4: Distribute product of sums (Cauchy product)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Step 5: Swap summation order: sum_k sum_j sum_j' -> sum_j sum_j' sum_k
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  -- Step 6: Rearrange each term to isolate character sum
  conv_lhs => arg 2; ext j; arg 2; ext j'; arg 2; ext k
              rw [show ZMod.stdAddChar (-(j * k)) * Phi j *
                (ZMod.stdAddChar (j' * k) * starRingEnd ℂ (Phi j')) =
                (Phi j * starRingEnd ℂ (Phi j')) *
                (ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k)) by ring]
  -- Step 7: Combine character factors: stdAddChar(-(j*k)) * stdAddChar(j'*k) = stdAddChar((j'-j)*k)
  simp_rw [show ∀ (j j' k : ZMod N),
    ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k) =
    ZMod.stdAddChar ((j' - j) * k) from fun j j' k => by
    rw [← AddChar.map_add_eq_mul]; ring_nf]
  -- Step 8: Factor constant out of inner sum
  simp_rw [← Finset.mul_sum]
  -- Step 9: Apply character orthogonality
  simp_rw [stdAddChar_sum_eq, sub_eq_zero]
  -- Step 10: Collapse diagonal
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  ring

/-- **Parseval identity for `ZMod.dft` (real norm-squared form)**.

    `sum_k ||F Phi k||^2 = N * sum_j ||Phi j||^2`

    This is the standard Parseval/Plancherel identity for the DFT on `ZMod N`.
    Derived from the complex inner product form using `RCLike.mul_conj`:
    `z * conj(z) = ||z||^2` (as a complex-valued identity). -/
theorem zmod_dft_parseval (Phi : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖𝓕 Phi k‖ ^ 2 =
    (N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2 := by
  have key := zmod_dft_parseval_complex Phi
  simp_rw [RCLike.mul_conj] at key
  have lhs_cast : (↑(∑ k : ZMod N, ‖𝓕 Phi k‖ ^ 2) : ℂ) =
      ∑ k : ZMod N, (↑‖𝓕 Phi k‖ : ℂ) ^ 2 := by
    push_cast; rfl
  have rhs_cast : (↑((N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2) : ℂ) =
      (↑N : ℂ) * ∑ j : ZMod N, (↑‖Phi j‖ : ℂ) ^ 2 := by
    push_cast; rfl
  exact Complex.ofReal_injective (by rw [lhs_cast, rhs_cast]; exact key)

end ParsevalZModDFT

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- Mathlib-style name for `zmod_dft_parseval_complex`. -/
theorem dft_mul_conj_sum (Phi : ZMod N → ℂ) :
    ∑ k : ZMod N, (dft Phi k * starRingEnd ℂ (dft Phi k)) =
    (N : ℂ) * ∑ j : ZMod N, (Phi j * starRingEnd ℂ (Phi j)) :=
  zmod_dft_parseval_complex Phi

/-- Mathlib-style name for `zmod_dft_parseval`. -/
theorem dft_norm_sq_sum (Phi : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖dft Phi k‖ ^ 2 = (N : ℝ) * ∑ j : ZMod N, ‖Phi j‖ ^ 2 :=
  zmod_dft_parseval Phi

end ZMod
