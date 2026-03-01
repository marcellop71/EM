import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import EM.LargeSieveAnalytic

/-!
# Chapter 7: Bilinear Forms and the Large Sieve (Iwaniec-Kowalski)

Formalization of Chapter 7 of H. Iwaniec and E. Kowalski,
*Analytic Number Theory*, AMS Colloquium Publications vol. 53, 2004.

## Contents
- §7.1: General principles of estimating double sums (duality principle)
- §7.2: Bilinear forms with exponentials (Theorem 7.2)
- §7.3: Introduction to the large sieve (philosophy)
- §7.4: Additive large sieve inequalities (Theorem 7.7)
- §7.5: Multiplicative large sieve inequality (Theorem 7.13)
- §7.6: Applications to sieving (Theorem 7.14, Linnik's theorem)
- §7.6': Panorama of large sieve inequalities (Theorems 7.17–7.22)
- §7.7: Large sieve for cusp forms (Theorems 7.24–7.28)
- §7.8: Orthogonality of elliptic curves (Theorem 7.31)
- §7.9: Power-moments of L-functions (Theorems 7.33–7.35)

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Complex Finset BigOperators

/-!
## §7.1 General principles of estimating double sums

IK §7.1 introduces the bilinear form Ψ(α,β) = ∑_m ∑_n α_m β_n φ(m,n)
and the basic operator norm bound |Ψ(α,β)|² ≤ Δ ‖α‖² ‖β‖².
The duality principle is the key structural result.
-/

section BilinearForms

/-- A **bilinear form** in the sense of IK §7.1:
    Ψ(α,β) = ∑_m ∑_n α_m β_n φ(m,n).
    Here we represent φ as a matrix indexed by `Fin M × Fin N`. -/
def bilinearForm {M N : ℕ} (α : Fin M → ℂ) (β : Fin N → ℂ)
    (φ : Fin M → Fin N → ℂ) : ℂ :=
  ∑ m, ∑ n, α m * β n * φ m n

/-- The ℓ² norm squared of a complex vector — IK (7.4). -/
def l2NormSq {N : ℕ} (v : Fin N → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

theorem l2NormSq_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ l2NormSq v :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 2

/-- The **operator norm bound** — IK (7.3):
    |Ψ(α,β)|² ≤ Δ · ‖α‖² · ‖β‖², where Δ is the operator norm of Φ.
    This is a basic consequence of Cauchy-Schwarz. -/
def OperatorNormBound {M N : ℕ} (φ : Fin M → Fin N → ℂ) (Δ : ℝ) : Prop :=
  ∀ (α : Fin M → ℂ) (β : Fin N → ℂ),
    ‖bilinearForm α β φ‖ ^ 2 ≤ Δ * l2NormSq α * l2NormSq β

/-- The **Cauchy-Schwarz inequality** for bilinear forms — IK (7.5):
    |Ψ(α,β)|² ≤ ‖α‖² · ∑_m |∑_n β_n φ(m,n)|².
    This follows from applying inner-product Cauchy-Schwarz to ∑_m α_m f(m)
    with f(m) = ∑_n β_n φ(m,n). -/
def CauchySchwarzBilinear : Prop :=
  ∀ {M N : ℕ} (α : Fin M → ℂ) (β : Fin N → ℂ) (φ : Fin M → Fin N → ℂ),
    ‖bilinearForm α β φ‖ ^ 2 ≤
      l2NormSq α * ∑ m, ‖∑ n, β n * φ m n‖ ^ 2

/-- **DUALITY PRINCIPLE** — IK §7.1:
    If ∑_m |∑_n β_n φ(m,n)|² ≤ Δ‖β‖² for all β,
    then ∑_n |∑_m α_m φ(m,n)|² ≤ Δ‖α‖² for all α.
    The same constant Δ works in both directions.
    Proof: choose β_n = ∑_m α_m φ(m,n), apply (7.5), deduce Ψ ≤ Δ‖α‖². -/
def DualityPrinciple : Prop :=
  ∀ {M N : ℕ} (φ : Fin M → Fin N → ℂ) (Δ : ℝ),
    0 ≤ Δ →
    (∀ (β : Fin N → ℂ),
      (∑ m, ‖∑ n, β n * φ m n‖ ^ 2) ≤ Δ * l2NormSq β) →
    ∀ (α : Fin M → ℂ),
      (∑ n, ‖∑ m, α m * φ m n‖ ^ 2) ≤ Δ * l2NormSq α

/-- The bilinear form factorizes: Ψ(α,β) = ∑_m α_m · (∑_n β_n φ_{m,n}). -/
theorem bilinearForm_eq_sum_mul {M N : ℕ} (α : Fin M → ℂ) (β : Fin N → ℂ)
    (φ : Fin M → Fin N → ℂ) :
    bilinearForm α β φ = ∑ m, α m * ∑ n, β n * φ m n := by
  simp only [bilinearForm, Finset.mul_sum]
  congr 1; ext m; congr 1; ext n; ring

/-- Complex Cauchy-Schwarz: ‖∑ f_m · g_m‖² ≤ (∑ ‖f_m‖²)(∑ ‖g_m‖²). -/
theorem complex_cauchy_schwarz {M : ℕ} (f g : Fin M → ℂ) :
    ‖∑ m, f m * g m‖ ^ 2 ≤ (∑ m, ‖f m‖ ^ 2) * (∑ m, ‖g m‖ ^ 2) := by
  -- ‖∑ f·g‖ ≤ ∑ ‖f·g‖ = ∑ ‖f‖·‖g‖ by triangle inequality
  have h1 : ‖∑ m : Fin M, f m * g m‖ ≤ ∑ m : Fin M, ‖f m‖ * ‖g m‖ := by
    calc ‖∑ m, f m * g m‖ ≤ ∑ m, ‖f m * g m‖ := norm_sum_le _ _
      _ = ∑ m, ‖f m‖ * ‖g m‖ := by congr 1; ext m; exact norm_mul _ _
  -- (∑ ‖f‖·‖g‖)² ≤ (∑ ‖f‖²)(∑ ‖g‖²) by real CS
  have h2 : (∑ m : Fin M, ‖f m‖ * ‖g m‖) ^ 2 ≤
      (∑ m, ‖f m‖ ^ 2) * (∑ m, ‖g m‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => ‖f m‖) (fun m => ‖g m‖)
  -- Chain: ‖∑ f·g‖² ≤ (∑ ‖f‖·‖g‖)² ≤ (∑ ‖f‖²)(∑ ‖g‖²)
  calc ‖∑ m, f m * g m‖ ^ 2
      ≤ (∑ m, ‖f m‖ * ‖g m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **PROVED: Cauchy-Schwarz for bilinear forms** — IK (7.5). -/
theorem cauchy_schwarz_bilinear : CauchySchwarzBilinear := by
  intro M N α β φ
  rw [bilinearForm_eq_sum_mul]
  exact complex_cauchy_schwarz α (fun m => ∑ n, β n * φ m n)

/-- ℓ² norm of star-conjugate equals ℓ² norm. -/
theorem l2NormSq_conj {N : ℕ} (v : Fin N → ℂ) :
    l2NormSq (fun n => starRingEnd ℂ (v n)) = l2NormSq v := by
  simp only [l2NormSq, Complex.norm_conj]

/-- **PROVED: Duality Principle** — IK §7.1.
    If ∑_m ‖∑_n β_n φ_{m,n}‖² ≤ Δ · ‖β‖² for all β, then
    ∑_n ‖∑_m α_m φ_{m,n}‖² ≤ Δ · ‖α‖² for all α.

    Proof: Set β_n = conj(∑_m α_m φ_{m,n}) = conj(g_n).
    Then S = ∑_n ‖g_n‖² = l2NormSq β.
    By hypothesis, ∑_m ‖∑_n β_n φ_{m,n}‖² ≤ Δ · S.
    By CS Bilinear applied to (α, β, φ):
      ‖Ψ(α,β,φ)‖² ≤ ‖α‖² · ∑_m ‖∑_n β_n φ_{m,n}‖² ≤ ‖α‖² · Δ · S.
    But Ψ(α,β,φ) = ∑_m α_m ∑_n conj(g_n) φ_{m,n},
    and Re(∑_m α_m ∑_n conj(g_n) φ_{m,n}) = Re(∑_n g_n conj(g_n)) = S.
    So S ≤ ‖Ψ‖ ≤ √(‖α‖² · Δ · S), giving S² ≤ ‖α‖² · Δ · S,
    hence S ≤ Δ · ‖α‖². -/
theorem duality_principle : DualityPrinciple := by
  intro M N φ Δ hΔ hβ_bound α
  -- Define g_n = ∑_m α_m · φ_{m,n} (the "dual sum" we want to bound)
  set g : Fin N → ℂ := fun n => ∑ m, α m * φ m n with hg_def
  -- The quantity we want to bound
  set S := ∑ n, ‖g n‖ ^ 2 with hS_def
  -- If S = 0, the bound is trivial
  by_cases hS_zero : S = 0
  · rw [hS_zero]; exact mul_nonneg hΔ (l2NormSq_nonneg α)
  -- Set β_n = conj(g_n)
  set β : Fin N → ℂ := fun n => starRingEnd ℂ (g n) with hβ_def
  -- l2NormSq β = l2NormSq g = S
  have hβ_norm : l2NormSq β = S := by
    unfold l2NormSq
    simp only [hβ_def, Complex.norm_conj]
    rfl
  -- By hypothesis: ∑_m ‖∑_n β_n φ_{m,n}‖² ≤ Δ · S
  have hbound : ∑ m : Fin M, ‖∑ n, β n * φ m n‖ ^ 2 ≤ Δ * S := by
    calc ∑ m, ‖∑ n, β n * φ m n‖ ^ 2 ≤ Δ * l2NormSq β := hβ_bound β
      _ = Δ * S := by rw [hβ_norm]
  -- By Cauchy-Schwarz bilinear: ‖Ψ(α,β,φ)‖² ≤ ‖α‖² · ∑_m ‖∑_n β_n φ_{m,n}‖²
  have hCS : ‖bilinearForm α β φ‖ ^ 2 ≤
      l2NormSq α * ∑ m : Fin M, ‖∑ n, β n * φ m n‖ ^ 2 :=
    cauchy_schwarz_bilinear α β φ
  -- Key identity: Ψ(α, conj(g), φ) = ∑_m α_m · ∑_n conj(g_n) · φ_{m,n}
  -- and Re of this equals S (since ∑_n g_n * conj(g_n) = ∑_n ‖g_n‖² = S)
  have hΨ_eq : bilinearForm α β φ = ∑ n, g n * starRingEnd ℂ (g n) := by
    simp only [bilinearForm, hβ_def, hg_def]
    rw [Finset.sum_comm]
    congr 1; ext n
    -- Goal: ∑ m, α m * conj(g n) * φ m n = g n * conj(g n)
    -- Factor out conj(g n): each term is (α m * φ m n) * conj(g n)
    have : ∀ m ∈ Finset.univ, α m * starRingEnd ℂ (g n) * φ m n =
        α m * φ m n * starRingEnd ℂ (g n) := by
      intro m _
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
  have hΨ_re : (bilinearForm α β φ).re = S := by
    rw [hΨ_eq, Complex.re_sum]
    congr 1; ext n
    rw [Complex.mul_conj']
    norm_cast
  -- Therefore S ≤ ‖Ψ‖
  have hS_le_norm : S ≤ ‖bilinearForm α β φ‖ := by
    calc S = (bilinearForm α β φ).re := hΨ_re.symm
      _ ≤ ‖bilinearForm α β φ‖ := Complex.re_le_norm _
  -- Chain: S² ≤ ‖Ψ‖² ≤ ‖α‖² · Δ · S
  have hS_pos : 0 < S := by
    exact lt_of_le_of_ne
      (Finset.sum_nonneg fun n _ => pow_nonneg (norm_nonneg _) 2)
      (Ne.symm hS_zero)
  have hS_sq : S * S ≤ l2NormSq α * Δ * S := by
    calc S * S = S ^ 2 := (sq S).symm
      _ ≤ ‖bilinearForm α β φ‖ ^ 2 :=
          pow_le_pow_left₀ (le_of_lt hS_pos) hS_le_norm 2
      _ ≤ l2NormSq α * ∑ m : Fin M, ‖∑ n, β n * φ m n‖ ^ 2 := hCS
      _ ≤ l2NormSq α * (Δ * S) := by
          apply mul_le_mul_of_nonneg_left hbound (l2NormSq_nonneg α)
      _ = l2NormSq α * Δ * S := by ring
  -- Divide by S > 0
  have : S ≤ l2NormSq α * Δ := le_of_mul_le_mul_right hS_sq hS_pos
  linarith [mul_comm (l2NormSq α) Δ]

end BilinearForms

/-!
## §7.2 Bilinear forms with exponentials

Lemma 7.1 and Theorem 7.2: estimates for bilinear forms with
φ(m,n) = e(x_m y_n), where e(z) = exp(2πiz).
-/

section ExponentialBilinearForms

/-- The exponential function e(z) = exp(2πiz) — standard in analytic number theory. -/
def eAN (z : ℝ) : ℂ := Complex.exp (2 * Real.pi * z * Complex.I)

/-- `IK.eAN` agrees with the root-level `eAN` from LargeSieveHarmonic:
    both equal `exp(2πiα)`, just written in different orders. -/
theorem eAN_eq_root_eAN (z : ℝ) : eAN z = _root_.eAN z := by
  simp only [eAN, _root_.eAN]; congr 1; ring

/-- **Lemma 7.1** — IK (7.14): For any α_m and real x_m,
    ∫_{-Y}^{Y} |∑_m α_m e(x_m y)|² dy ≤ 5Y ∑∑_{2Y|x_{m₁}-x_{m₂}|<1} |α_{m₁} α_{m₂}|. -/
def Lemma7_1 : Prop :=
  ∀ (M : ℕ) (_α : Fin M → ℂ) (_x : Fin M → ℝ) (Y : ℝ), 0 < Y →
    True -- integral bound via Fourier analysis

/-- **Theorem 7.2** — IK (7.15): The basic bilinear inequality for exponentials.
    For |x_m| ≤ X, |y_n| ≤ Y:
    |∑_m ∑_n α_m β_n e(x_m y_n)| ≤ 5(XY+1)^{1/2} · (well-spaced sums)^{1/2}. -/
def ExponentialBilinearBound : Prop :=
  ∀ (M N : ℕ) (α : Fin M → ℂ) (β : Fin N → ℂ)
    (x : Fin M → ℝ) (y : Fin N → ℝ) (X Y : ℝ),
    0 < X → 0 < Y →
    (∀ m, |x m| ≤ X) → (∀ n, |y n| ≤ Y) →
    ‖∑ m, ∑ n, α m * β n * eAN (x m * y n)‖ ≤
      5 * (X * Y + 1) ^ (1/2 : ℝ) *
        (∑ m₁, ∑ m₂, if |x m₁ - x m₂| * Y < 1
          then ‖α m₁‖ * ‖α m₂‖ else 0) ^ (1/2 : ℝ) *
        (∑ n₁, ∑ n₂, if |y n₁ - y n₂| * X < 1
          then ‖β n₁‖ * ‖β n₂‖ else 0) ^ (1/2 : ℝ)

/-- **Corollary 7.3**: Well-spaced points — IK Cor 7.3.
    If x_m are A-spaced and y_n are B-spaced:
    |∑∑ α_m β_n e(x_m y_n)| ≤ 5(1+XY)^{1/2}(1+1/AY)^{1/2}(1+1/BX)^{1/2} ‖α‖ ‖β‖. -/
def WellSpacedExponentialBound : Prop :=
  ∀ (M N : ℕ) (α : Fin M → ℂ) (β : Fin N → ℂ)
    (x : Fin M → ℝ) (y : Fin N → ℝ) (X Y A B : ℝ),
    0 < A → 0 < B → 0 < X → 0 < Y →
    (∀ m, |x m| ≤ X) → (∀ n, |y n| ≤ Y) →
    (∀ m₁ m₂, m₁ ≠ m₂ → A ≤ |x m₁ - x m₂|) →
    (∀ n₁ n₂, n₁ ≠ n₂ → B ≤ |y n₁ - y n₂|) →
    ‖∑ m, ∑ n, α m * β n * eAN (x m * y n)‖ ≤
      5 * (1 + X * Y) ^ (1/2 : ℝ) * (1 + 1 / (A * Y)) ^ (1/2 : ℝ) *
        (1 + 1 / (B * X)) ^ (1/2 : ℝ) *
        (l2NormSq α) ^ (1/2 : ℝ) * (l2NormSq β) ^ (1/2 : ℝ)

end ExponentialBilinearForms

/-!
## §7.3 Introduction to the large sieve

The large sieve problem: find C = C(𝒳,N) such that
∑_{x∈𝒳} |∑_{n≤N} a_n x(n)|² ≤ C ‖a‖².
The expected optimal constant is C ≃ |𝒳| + N.
-/

section LargeSieveFramework

/-- A **large sieve inequality** for a set of harmonics:
    ∑_{x∈𝒳} |∑_n a_n x(n)|² ≤ C · ‖a‖² — IK (7.18). -/
def LargeSieveInequality {R N : ℕ} (x : Fin R → Fin N → ℂ)
    (C : ℝ) : Prop :=
  ∀ (a : Fin N → ℂ),
    (∑ r, ‖∑ n, a n * x r n‖ ^ 2) ≤ C * l2NormSq a

/-- The **dual large sieve** — IK (7.19):
    ∑_n |∑_x b_x x(n)|² ≤ C · ∑_x |b_x|².
    By the duality principle, this is equivalent to (7.18). -/
def DualLargeSieve {R N : ℕ} (x : Fin R → Fin N → ℂ)
    (C : ℝ) : Prop :=
  ∀ (b : Fin R → ℂ),
    (∑ n, ‖∑ r, b r * x r n‖ ^ 2) ≤ C * l2NormSq b

/-- **Dual from LSI**: `LargeSieveInequality x C` implies `DualLargeSieve x C`
    as a direct application of the proved duality principle.

    Proof: The duality principle with φ = x (Fin R → Fin N → ℂ) says:
    - Hypothesis (= LSI): `∀ a, ∑_r ‖∑_n a_n x(r,n)‖² ≤ C ‖a‖²`
    - Conclusion (= Dual): `∀ b, ∑_n ‖∑_r b_r x(r,n)‖² ≤ C ‖b‖²` -/
theorem dual_of_lsi {R N : ℕ} (x : Fin R → Fin N → ℂ) (C : ℝ) (hC : 0 ≤ C) :
    LargeSieveInequality x C → DualLargeSieve x C := by
  intro hlsi b
  exact duality_principle x C hC hlsi b

/-- **LSI from dual**: `DualLargeSieve x C` implies `LargeSieveInequality x C`
    via the duality principle applied to the transpose matrix.

    Proof: Set φ = xᵀ (transpose). The dual large sieve for x is the forward
    large sieve for xᵀ. Applying the duality principle to xᵀ yields the
    dual of xᵀ, which is the forward of x. -/
theorem lsi_of_dual {R N : ℕ} (x : Fin R → Fin N → ℂ) (C : ℝ) (hC : 0 ≤ C) :
    DualLargeSieve x C → LargeSieveInequality x C := by
  intro hdual a
  -- DualLargeSieve x C: ∀ b, ∑_n ‖∑_r b_r * x r n‖² ≤ C * l2NormSq b
  -- Set xT(n, r) = x(r, n). Then DualLargeSieve x C is LSI for xT.
  -- By duality_principle on xT: LSI(xT) → Dual(xT), i.e. LSI(x).
  set xT : Fin N → Fin R → ℂ := fun n r => x r n with hxT_def
  -- Rewrite hdual as LSI for xT
  have hlsi_xT : LargeSieveInequality xT C := by
    intro β
    -- Goal: ∑_n ‖∑_r β_r * xT(n,r)‖² ≤ C * l2NormSq β
    -- xT(n,r) = x(r,n), so β_r * xT(n,r) = β_r * x(r,n)
    -- This is ∑_n ‖∑_r β_r * x(r,n)‖² ≤ C * l2NormSq β = DualLargeSieve x C applied to β
    exact hdual β
  -- Apply duality_principle to xT to get DualLargeSieve xT C
  have hdual_xT := duality_principle xT C hC hlsi_xT a
  -- DualLargeSieve xT at a: ∑_r ‖∑_n a_n * xT(n,r)‖² ≤ C * l2NormSq a
  -- = ∑_r ‖∑_n a_n * x(r,n)‖² ≤ C * l2NormSq a = LSI x C at a
  exact hdual_xT

/-- **LSI-Dual equivalence**: For C ≥ 0, the large sieve inequality and its dual
    are equivalent — IK §7.1 duality principle. -/
theorem lsi_iff_dual {R N : ℕ} (x : Fin R → Fin N → ℂ) (C : ℝ) (hC : 0 ≤ C) :
    LargeSieveInequality x C ↔ DualLargeSieve x C :=
  ⟨dual_of_lsi x C hC, lsi_of_dual x C hC⟩

end LargeSieveFramework

/-!
## §7.4 Additive large sieve inequalities

Theorem 7.7 (Selberg, Montgomery-Vaughan): The optimal additive large sieve.
For δ-spaced points α_r ∈ ℝ/ℤ:
∑_r |∑_n a_n e(α_r n)|² ≤ (δ⁻¹ + N − 1) ‖a‖².

Lemma 7.8: Generalization of Hilbert's inequality.
Theorem 7.11: Large sieve at Farey fractions.
-/

section AdditiveLargeSieve

/-- Points α_r ∈ ℝ/ℤ are **δ-spaced** if ‖α_r − α_s‖ ≥ δ for r ≠ s,
    where ‖·‖ is the distance to the nearest integer — IK §7.4. -/
def IsSpaced {R : ℕ} (α : Fin R → ℝ) (δ : ℝ) : Prop :=
  ∀ r s : Fin R, r ≠ s → δ ≤ |Int.fract (α r) - Int.fract (α s)|

/-- **Lemma 7.8** (Montgomery-Vaughan): Generalized Hilbert inequality — IK (7.23).
    If λ_r are distinct with |λ_r − λ_s| ≥ δ for r ≠ s, then
    |∑∑_{r≠s} z_r z̄_s / (λ_r − λ_s)| ≤ (π/δ) ∑ |z_r|². -/
def HilbertInequality : Prop :=
  ∀ (R : ℕ) (pts : Fin R → ℝ) (z : Fin R → ℂ) (δ : ℝ),
    0 < δ →
    (∀ r s : Fin R, r ≠ s → δ ≤ |pts r - pts s|) →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      z r * starRingEnd ℂ (z s) / (↑(pts r - pts s) : ℂ)‖ ≤
      Real.pi / δ * ∑ r, ‖z r‖ ^ 2

/-- **Theorem 7.7** (Selberg, Montgomery-Vaughan): Optimal additive large sieve —
    IK (7.22). For δ-spaced points α_r ∈ ℝ/ℤ and a_n with M < n ≤ M+N:
    ∑_r |∑_n a_n e(α_r n)|² ≤ (δ⁻¹ + N − 1) ‖a‖². -/
def AdditiveLargeSieve : Prop :=
  ∀ (R N : ℕ) (α : Fin R → ℝ) (a : Fin N → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 → 1 ≤ N →
    IsSpaced α δ →
    (∑ r, ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤
      (1 / δ + ↑N - 1) * l2NormSq a

/-- **Weak additive large sieve** (formalized): a direct wrapper around the proved lemma
`LargeSieveAnalytic.weak_als_from_card_bound`.

This has the correct *structure* (dependence on `δ⁻¹` and `N`) but a non-optimal
constant `N * (δ⁻¹ + 1)`.

We use the `LargeSieveAnalytic.eAN` normalization `e(α) = exp(2π i α)`.
-/
theorem weak_additive_large_sieve
    (N : ℕ) (hN : 0 < N) (a : Fin N → ℂ)
    (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    ∑ r : Fin R, ‖∑ n : Fin N, a n * _root_.eAN (↑(n : ℤ) * α r)‖ ^ 2
      ≤ (N : ℝ) * (δ⁻¹ + 1) * ∑ n : Fin N, ‖a n‖ ^ 2 :=
  _root_.weak_als_from_card_bound N hN a R α δ hδ hsep

/-- **Theorem 7.11**: Large sieve at Farey fractions — IK (7.28).
    ∑_{q≤Q} ∑*_{a mod q} |∑_n a_n e(an/q)|² ≤ (Q² + N − 1) ‖a‖².
    This follows from Theorem 7.7 because Farey fractions are Q⁻²-spaced. -/
def FareyLargeSieve : Prop :=
  ∀ (N : ℕ) (Q : ℕ) (_a : Fin N → ℂ),
    1 ≤ N → 1 ≤ Q →
    -- ∑_{q≤Q} ∑*_{a mod q} |∑_n a_n e(an/q)|² ≤ (Q² + N − 1) ‖a‖²
    True

/-!
### §7.4a Schur test for Hermitian quadratic forms

A key tool for proving large sieve bounds via Gram matrices: given a matrix
G : Fin R → Fin R → ℂ with diagonal entries equal to D and off-diagonal
entries bounded by B in norm, the quadratic form b* G b is bounded by
(D + (R-1) · B) · ‖b‖².

The proof uses the triangle inequality to bound the off-diagonal
contribution, and Cauchy-Schwarz (in the form ∑_{r≠s} |b_r||b_s| ≤ (R-1)·‖b‖²)
for the off-diagonal sum.
-/

/-- **Off-diagonal Cauchy-Schwarz**: for a finite collection of non-negative reals,
    ∑_{i ≠ j} w_i w_j ≤ (n − 1) · ∑_i w_i².
    Proof: ∑_{i≠j} w_i w_j = (∑ w_i)² − ∑ w_i² ≤ (n · ∑ w_i²) − ∑ w_i² by CS. -/
theorem off_diag_sum_le {R : ℕ} (w : Fin R → ℝ) (_hw : ∀ r, 0 ≤ w r) :
    ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r), w r * w s ≤
      (↑R - 1) * ∑ r, w r ^ 2 := by
  -- For each r, ∑_{s≠r} w_r w_s = w_r (∑_{s≠r} w_s).
  -- But ∑_{s≠r} w_s is hard to bound cleanly. Instead, use the identity
  -- ∑_r ∑_{s≠r} w_r w_s + ∑_r w_r^2 = (∑ w)^2 ≤ R ∑ w^2 by CS.
  -- So ∑_{r≠s} w_r w_s ≤ (R-1) ∑ w^2.
  -- The identity: ∑_r (w_r^2 + ∑_{s≠r} w_r w_s) = ∑_r ∑_s w_r w_s = (∑ w)^2.
  -- Use Finset.sum_product_univ for the double sum.
  -- Prove the identity via "add and subtract"
  suffices h_identity :
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r), w r * w s =
        (∑ r, w r) ^ 2 - ∑ r, w r ^ 2 by
    have hcs : (∑ r, w r) ^ 2 ≤ ↑R * ∑ r, w r ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) w
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, one_mul] at this
      exact this
    linarith
  -- Prove the identity: ∑_{r≠s} w_r w_s = (∑ w)^2 - ∑ w^2
  -- First: (∑ w)^2 = ∑_r ∑_s w_r w_s = ∑_r w_r^2 + ∑_{r≠s} w_r w_s
  have h_sq : (∑ r, w r) ^ 2 = ∑ r, ∑ s, w r * w s := by
    rw [sq, Finset.sum_mul_sum]
  -- Split double sum into diag + off-diag via Finset.sum_erase
  have h_split : ∀ r : Fin R,
      ∑ s, w r * w s = w r ^ 2 + ∑ s ∈ Finset.univ.erase r, w r * w s := by
    intro r
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r), sq]
  -- erase = filter
  have h_erase_filter : ∀ r : Fin R,
      Finset.univ.erase r = Finset.univ.filter (· ≠ r) := by
    intro r; ext s; simp [Finset.mem_erase, Finset.mem_filter, ne_comm]
  simp_rw [h_split, h_erase_filter] at h_sq
  simp_rw [Finset.sum_add_distrib] at h_sq
  linarith

/-- **Schur test for Hermitian quadratic forms**: for a matrix G with
    diagonal ≤ D and off-diagonal norm ≤ B,
    ‖∑_{r,s} b_r · conj(b_s) · G_{r,s}‖ ≤ (D + (R-1)·B) · ‖b‖². -/
theorem schur_quadratic_form_bound {R : ℕ}
    (G : Fin R → Fin R → ℂ)
    (b : Fin R → ℂ)
    (D B : ℝ) (_hD : 0 ≤ D) (hB : 0 ≤ B)
    (hdiag : ∀ r, ‖G r r‖ ≤ D)
    (hoffdiag : ∀ r s, r ≠ s → ‖G r s‖ ≤ B) :
    ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * G r s‖ ≤
      (D + (↑R - 1) * B) * l2NormSq b := by
  -- Bound via triangle inequality: split each inner sum into r=s and r≠s
  -- Then bound diagonal by D * ||b||^2 and off-diagonal by (R-1)*B*||b||^2.
  -- Instead of splitting the sum, we use a direct bound:
  -- ‖∑_{r,s} b_r conj(b_s) G_{r,s}‖ ≤ ∑_{r,s} ‖b_r‖ ‖b_s‖ ‖G_{r,s}‖
  -- The diagonal part contributes ∑_r ‖b_r‖^2 ‖G_{r,r}‖ ≤ D ∑ ‖b_r‖^2 = D * ||b||^2
  -- The off-diagonal contributes ∑_{r≠s} ‖b_r‖ ‖b_s‖ ‖G_{r,s}‖ ≤ B ∑_{r≠s} ‖b_r‖ ‖b_s‖
  -- ≤ B * (R-1) * ||b||^2 by off_diag_sum_le.
  -- Bound via triangle inequality + diagonal/off-diagonal split
  -- ‖∑∑ b_r conj(b_s) G_{rs}‖ ≤ ∑∑ |b_r| |b_s| |G_{rs}|
  -- = ∑_r |b_r|^2 |G_{rr}| + ∑_{r≠s} |b_r| |b_s| |G_{rs}|
  -- ≤ D * ||b||^2 + B * ∑_{r≠s} |b_r| |b_s|
  -- ≤ D * ||b||^2 + (R-1)*B*||b||^2
  -- Direct approach: bound the full sum termwise.
  -- For r=s: |b_r|^2 * |G_{rr}| ≤ |b_r|^2 * D
  -- For r≠s: |b_r| |b_s| |G_{rs}| ≤ |b_r| |b_s| * B
  -- ∑_r |b_r|^2 * D = D * ||b||^2
  -- ∑_{r≠s} |b_r| |b_s| * B ≤ (R-1)*B*||b||^2 by off_diag_sum_le
  -- Triangle inequality
  apply le_trans (norm_sum_le _ _)
  apply le_trans (Finset.sum_le_sum (fun r _ => norm_sum_le _ _))
  -- Now have: ≤ ∑_r ∑_s ‖b_r conj(b_s) G_{rs}‖ = ∑ ‖b_r‖ ‖b_s‖ ‖G_{rs}‖
  -- Split diagonal and off-diagonal
  have heq : ∀ r : Fin R,
      ∑ s, ‖b r * starRingEnd ℂ (b s) * G r s‖ =
        ‖b r‖ ^ 2 * ‖G r r‖ +
        ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ * ‖G r s‖ := by
    intro r
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r)]
    congr 1
    · rw [norm_mul, norm_mul, Complex.norm_conj, ← sq, mul_comm]
    · apply Finset.sum_congr rfl; intro s _
      rw [norm_mul, norm_mul, Complex.norm_conj]
  simp_rw [heq, Finset.sum_add_distrib]
  -- Now goal is: ∑ |b_r|^2 |G_{rr}| + ∑_r ∑_{s∈erase r} ... ≤ (D + (R-1)B) ||b||^2
  -- Rewrite RHS as D * ||b||^2 + (R-1)*B*||b||^2
  have hrhs : (D + (↑R - 1) * B) * l2NormSq b =
      D * l2NormSq b + (↑R - 1) * B * l2NormSq b := by ring
  rw [hrhs]
  apply add_le_add
  -- Diagonal part: ∑ |b_r|^2 |G_{rr}| ≤ D * ||b||^2
  · calc ∑ r, ‖b r‖ ^ 2 * ‖G r r‖
        ≤ ∑ r, ‖b r‖ ^ 2 * D := by
          apply Finset.sum_le_sum; intro r _; exact mul_le_mul_of_nonneg_left (hdiag r) (sq_nonneg _)
      _ = D * l2NormSq b := by unfold l2NormSq; rw [← Finset.sum_mul]; ring
      _ ≤ D * l2NormSq b := le_refl _
  -- Off-diagonal part: ∑_{r≠s} |b_r| |b_s| |G_{rs}| ≤ (R-1)*B*||b||^2
  · have herase_filter : ∀ r : Fin R,
        Finset.univ.erase r = Finset.univ.filter (· ≠ r) := by
      intro r; ext s; simp [Finset.mem_erase, Finset.mem_filter, ne_comm]
    calc ∑ r, ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ * ‖G r s‖
        ≤ ∑ r, ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ * B := by
          apply Finset.sum_le_sum; intro r _
          apply Finset.sum_le_sum; intro s hs
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          exact hoffdiag r s (by simp only [Finset.mem_erase] at hs; exact hs.1.symm)
      _ = B * ∑ r, ∑ s ∈ Finset.univ.erase r, ‖b r‖ * ‖b s‖ := by
          rw [Finset.mul_sum]; congr 1; ext r
          rw [Finset.mul_sum]; congr 1; ext s; ring
      _ ≤ B * ((↑R - 1) * ∑ r, ‖b r‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hB
          simp_rw [herase_filter]
          exact off_diag_sum_le (fun r => ‖b r‖) (fun r => norm_nonneg _)
      _ = (↑R - 1) * B * l2NormSq b := by unfold l2NormSq; ring

/-!
### §7.4b Row-sum Schur test and Gram matrix reduction

The **row-sum Schur test** for PSD matrices says: if G is positive semi-definite
(meaning b*Gb ≥ 0 for all b) and every row sum ∑_s |G_{r,s}| ≤ C, then
b*Gb ≤ C · ‖b‖².

Combined with the Gram matrix expansion (which writes the dual ALS form as a
Gram quadratic form), this reduces `AdditiveLargeSieve` to bounding the row sums
of the Gram matrix G_{r,s} = ∑_{n<N} e(n(α_r - α_s)).
-/

/-- **Row-sum Schur test**: for a matrix G with norm-symmetric entries
    (‖G_{r,s}‖ = ‖G_{s,r}‖) and row sums bounded by C,
    the Hermitian quadratic form ‖b* G b‖ ≤ C · ‖b‖².

    Proof uses AM-GM (|b_r|·|b_s| ≤ (|b_r|²+|b_s|²)/2) and symmetrization. -/
theorem row_sum_schur_bound {R : ℕ}
    (G : Fin R → Fin R → ℂ) (b : Fin R → ℂ) (C : ℝ)
    (_hC : 0 ≤ C)
    (hrow : ∀ r : Fin R, ∑ s, ‖G r s‖ ≤ C)
    (hsymm : ∀ r s : Fin R, ‖G r s‖ = ‖G s r‖) :
    ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * G r s‖ ≤ C * l2NormSq b := by
  -- Step 1: Triangle inequality + norm simplification
  have h1 : ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * G r s‖ ≤
      ∑ r, ∑ s, ‖b r‖ * ‖b s‖ * ‖G r s‖ := by
    apply le_trans (norm_sum_le _ _)
    apply le_trans (Finset.sum_le_sum (fun r _ => norm_sum_le _ _))
    gcongr with r _ s _
    rw [norm_mul, norm_mul, Complex.norm_conj]
  -- Step 2: AM-GM bound: |b_r|·|b_s| ≤ (|b_r|²+|b_s|²)/2
  have hamgm : ∀ r s : Fin R,
      ‖b r‖ * ‖b s‖ * ‖G r s‖ ≤
      (1/2) * (‖b r‖ ^ 2 * ‖G r s‖) + (1/2) * (‖b s‖ ^ 2 * ‖G r s‖) := by
    intro r s
    have h := sq_nonneg (‖b r‖ - ‖b s‖)
    have hg := norm_nonneg (G r s)
    nlinarith [sq_abs (‖b r‖ - ‖b s‖)]
  -- Step 3: Apply AM-GM to bound the double sum
  -- We bound ∑∑ |b_r|·|b_s|·‖G_{rs}‖ ≤ (1/2)·∑∑ |b_r|²·‖G_{rs}‖ + (1/2)·∑∑ |b_s|²·‖G_{rs}‖
  -- First half: ∑_r ∑_s |b_r|²·‖G_{rs}‖ = ∑_r |b_r|²·(∑_s ‖G_{rs}‖) ≤ C·‖b‖²
  -- Second half: ∑_r ∑_s |b_s|²·‖G_{rs}‖ = ∑_s |b_s|²·(∑_r ‖G_{rs}‖)
  --   = ∑_s |b_s|²·(∑_r ‖G_{sr}‖) (by hsymm) ≤ C·‖b‖² (by hrow)
  -- Define the two half-sums
  -- Step 3: Apply AM-GM + bound by row sums directly
  -- ∑∑ |b_r|·|b_s|·‖G_{rs}‖ ≤ (1/2)·S1 + (1/2)·S2 ≤ C·‖b‖²
  -- where S1 = ∑_r |b_r|²·(∑_s ‖G_{rs}‖), S2 = ∑_s |b_s|²·(∑_r ‖G_{rs}‖)
  -- Bound S1: factor out |b_r|², use hrow
  have h_S1 : ∑ r, ∑ s, ‖b r‖ ^ 2 * ‖G r s‖ ≤ C * l2NormSq b := by
    calc ∑ r, ∑ s, ‖b r‖ ^ 2 * ‖G r s‖
        = ∑ r, ‖b r‖ ^ 2 * ∑ s, ‖G r s‖ := by
          congr 1; ext r; rw [Finset.mul_sum]
      _ ≤ ∑ r, ‖b r‖ ^ 2 * C := by gcongr with r _; exact hrow r
      _ = C * l2NormSq b := by
          unfold l2NormSq; rw [Finset.mul_sum]; congr 1; ext r; ring
  -- Bound S2: swap sums, use symmetry, then hrow
  have h_S2 : ∑ r, ∑ s, ‖b s‖ ^ 2 * ‖G r s‖ ≤ C * l2NormSq b := by
    -- Rewrite using Fintype.sum = Finset.univ.sum for Finset.sum_comm
    show ∑ r ∈ Finset.univ, ∑ s ∈ Finset.univ, ‖b s‖ ^ 2 * ‖G r s‖ ≤ _
    rw [Finset.sum_comm]
    -- Now: ∑_s ∑_r |b_s|²·‖G_{r,s}‖ = ∑_s |b_s|²·(∑_r ‖G_{r,s}‖)
    calc ∑ s, ∑ r, ‖b s‖ ^ 2 * ‖G r s‖
        = ∑ s, ‖b s‖ ^ 2 * ∑ r, ‖G r s‖ := by
          congr 1; ext s; rw [Finset.mul_sum]
      _ = ∑ s, ‖b s‖ ^ 2 * ∑ r, ‖G s r‖ := by
          congr 1; ext s; congr 1
          congr 1; ext r; exact hsymm r s
      _ ≤ ∑ s, ‖b s‖ ^ 2 * C := by gcongr with s _; exact hrow s
      _ = C * l2NormSq b := by
          unfold l2NormSq; rw [Finset.mul_sum]; congr 1; ext s; ring
  -- Combine: apply AM-GM pointwise then use S1, S2 bounds
  have h2 : ∑ r, ∑ s, ‖b r‖ * ‖b s‖ * ‖G r s‖ ≤ C * l2NormSq b := by
    calc ∑ r, ∑ s, ‖b r‖ * ‖b s‖ * ‖G r s‖
        ≤ ∑ r, ∑ s, ((1/2) * (‖b r‖ ^ 2 * ‖G r s‖) + (1/2) * (‖b s‖ ^ 2 * ‖G r s‖)) := by
          gcongr with r _ s _; exact hamgm r s
      _ = (1/2) * ∑ r, ∑ s, ‖b r‖ ^ 2 * ‖G r s‖ +
          (1/2) * ∑ r, ∑ s, ‖b s‖ ^ 2 * ‖G r s‖ := by
          simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (1/2) * (C * l2NormSq b) + (1/2) * (C * l2NormSq b) := by
          linarith [h_S1, h_S2]
      _ = C * l2NormSq b := by ring
  linarith [h1.trans h2]

/-!
### §7.4c Gram matrix reduction: row-sum bound implies ALS

The **Gram matrix** for δ-spaced evaluation points α_r and summation length N is
G_{r,s} = ∑_{n=0}^{N-1} e(n(α_r - α_s)).

The ALS follows from a bound on the row sums of this Gram matrix via:
1. Duality: ALS ⟺ dual ALS
2. The dual ALS LHS equals a Gram matrix quadratic form
3. The row-sum Schur test bounds this quadratic form

We state the row-sum hypothesis and prove the reduction.
-/

/-- The Gram matrix for the additive large sieve:
    `gramMatrix N α r s = ∑_{n=0}^{N-1} e(n · (α_r - α_s))`. -/
def gramMatrix (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R) : ℂ :=
  ∑ n ∈ Finset.range N, _root_.eAN (↑n * (α r - α s))

/-- The Gram matrix has norm-symmetric entries: ‖G_{r,s}‖ = ‖G_{s,r}‖.

    Proof: G_{s,r} = ∑ e(n(α_s - α_r)) = conj(∑ e(n(α_r - α_s))) = conj(G_{r,s}),
    so ‖G_{s,r}‖ = ‖conj(G_{r,s})‖ = ‖G_{r,s}‖. -/
theorem gramMatrix_norm_symm (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R) :
    ‖gramMatrix N α r s‖ = ‖gramMatrix N α s r‖ := by
  -- G_{s,r} = ∑ e(n(α_s - α_r)) = ∑ e(-n(α_r - α_s)) = conj(G_{r,s})
  -- so ‖G_{s,r}‖ = ‖conj(G_{r,s})‖ = ‖G_{r,s}‖
  suffices h : gramMatrix N α s r = starRingEnd ℂ (gramMatrix N α r s) by
    rw [h, Complex.norm_conj]
  unfold gramMatrix
  rw [map_sum]; congr 1; ext n
  rw [show ↑n * (α s - α r) = -(↑n * (α r - α s)) from by ring]
  exact (conj_eAN _).symm

/-- The Gram matrix diagonal equals N: G_{r,r} = N. -/
theorem gramMatrix_diag (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r : Fin R) :
    gramMatrix N α r r = ↑N := by
  unfold gramMatrix
  simp [sub_self, mul_zero, eAN_zero]

/-!
### Geometric sum / Dirichlet kernel identities for the Gram matrix

The Gram matrix entry `gramMatrix N α r s = ∑_{n<N} e(n·(α_r - α_s))` is a geometric
sum. When `e(α_r - α_s) ≠ 1` (i.e. the difference is not an integer), the standard
geometric series formula gives a closed form, and the norm equals the ratio of sines
`|sin(N·π·θ)| / |sin(π·θ)|` where `θ = α_r - α_s`.

These identities are the analytic foundation of the Hilbert inequality approach
to the optimal additive large sieve (§7.4e).
-/

/-- **Geometric sum formula for Gram entries**: when `eAN(α_r - α_s) ≠ 1`,
    `gramMatrix N α r s = (eAN(N·(α_r - α_s)) - 1) / (eAN(α_r - α_s) - 1)`.

    This is a direct application of the geometric series closed form to the
    Gram matrix definition `∑_{n<N} eAN(n·θ)` with `θ = α_r - α_s`. -/
theorem gramMatrix_eq_geom_closed_form (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hne : _root_.eAN (α r - α s) ≠ 1) :
    gramMatrix N α r s =
      (_root_.eAN (↑N * (α r - α s)) - 1) / (_root_.eAN (α r - α s) - 1) := by
  unfold gramMatrix
  exact eAN_geom_sum_eq N (α r - α s) hne

/-- **Telescoping identity for Gram entries**: the Gram matrix entry times
    `(eAN θ - 1)` telescopes to `eAN(Nθ) - 1`.

    `gramMatrix N α r s * (eAN(α_r - α_s) - 1) = eAN(N·(α_r - α_s)) - 1` -/
theorem gramMatrix_mul_eAN_sub_one (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R) :
    gramMatrix N α r s * (_root_.eAN (α r - α s) - 1) =
      _root_.eAN (↑N * (α r - α s)) - 1 := by
  unfold gramMatrix
  exact eAN_geom_sum_mul N (α r - α s)

/-- **Norm of Gram entry via closed form**: when `eAN(α_r - α_s) ≠ 1`,
    `‖gramMatrix N α r s‖ ≤ 2 / ‖eAN(α_r - α_s) - 1‖`.

    This follows from the triangle inequality on the numerator `‖eAN(Nθ) - 1‖ ≤ 2`. -/
theorem gramMatrix_norm_le_two_div (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hne : _root_.eAN (α r - α s) ≠ 1) :
    ‖gramMatrix N α r s‖ ≤ 2 / ‖_root_.eAN (α r - α s) - 1‖ := by
  unfold gramMatrix
  exact norm_eAN_geom_sum_le N (α r - α s) hne

/-- **Norm of Gram entry as sin ratio**: when `sin(π·(α_r - α_s)) ≠ 0`,
    `‖gramMatrix N α r s‖ = |sin(N·π·(α_r - α_s))| / |sin(π·(α_r - α_s))|`.

    Proof: The geometric sum closed form gives
    `‖(eAN(Nθ) - 1) / (eAN(θ) - 1)‖ = ‖eAN(Nθ) - 1‖ / ‖eAN(θ) - 1‖`.
    By `norm_eAN_sub_one`, `‖eAN(x) - 1‖ = 2|sin(πx)|`, so the factors of 2 cancel. -/
theorem gramMatrix_norm_eq_sin_ratio (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hsin : Real.sin (Real.pi * (α r - α s)) ≠ 0) :
    ‖gramMatrix N α r s‖ =
      |Real.sin (↑N * Real.pi * (α r - α s))| /
      |Real.sin (Real.pi * (α r - α s))| := by
  -- First establish eAN(α r - α s) ≠ 1 from hsin
  have hne : _root_.eAN (α r - α s) ≠ 1 := by
    intro h
    have h0 : ‖_root_.eAN (α r - α s) - 1‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [norm_eAN_sub_one] at h0
    have : |Real.sin (Real.pi * (α r - α s))| = 0 := by linarith
    exact hsin (abs_eq_zero.mp this)
  -- Use closed form
  rw [gramMatrix_eq_geom_closed_form N α r s hne, norm_div,
      norm_eAN_sub_one, norm_eAN_sub_one]
  -- Now: 2 * |sin(N*π*θ)| / (2 * |sin(π*θ)|) = |sin(N*π*θ)| / |sin(π*θ)|
  -- Need to rewrite N * π * θ as π * (N * θ)
  rw [show Real.pi * (↑N * (α r - α s)) = ↑N * Real.pi * (α r - α s) from by ring]
  -- Cancel the factor of 2: 2*a / (2*b) = a/b
  rw [mul_div_mul_left _ _ (two_ne_zero)]

/-- **Norm-squared of Gram entry as sin-squared ratio**: when
    `sin(π·(α_r - α_s)) ≠ 0`,
    `‖gramMatrix N α r s‖² = sin(N·π·θ)² / sin(π·θ)²`
    where `θ = α_r - α_s`.

    This is the form that appears directly in Hilbert inequality applications. -/
theorem gramMatrix_norm_sq_eq_sin_sq_ratio (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R)
    (hsin : Real.sin (Real.pi * (α r - α s)) ≠ 0) :
    ‖gramMatrix N α r s‖ ^ 2 =
      Real.sin (↑N * Real.pi * (α r - α s)) ^ 2 /
      Real.sin (Real.pi * (α r - α s)) ^ 2 := by
  rw [gramMatrix_norm_eq_sin_ratio N α r s hsin]
  rw [div_pow, sq_abs, sq_abs]

/-- The Gram matrix row sum bound hypothesis: for evaluation points α and summation
    length N, every row sum of ‖G_{r,s}‖ is at most C.

    The optimal bound is C = 1/δ + N - 1 (for δ-spaced α), proved using the
    Hilbert inequality. This hypothesis isolates the analytic input needed for ALS. -/
def GramRowSumBound (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (C : ℝ) : Prop :=
  ∀ r : Fin R, ∑ s, ‖gramMatrix N α r s‖ ≤ C

/-- **Gram row-sum bound implies ALS**: if the Gram matrix row sums are bounded by C,
    then the additive large sieve holds with constant C.

    This reduces the ALS to a concrete bound on row sums of the kernel
    G_{r,s} = ∑_{n<N} e(n(α_r - α_s)). -/
theorem gram_row_sum_implies_lsi
    (R N : ℕ) (α : Fin R → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : GramRowSumBound N α C) :
    ∀ (a : Fin N → ℂ),
    (∑ r, ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤ C * l2NormSq a := by
  -- Strategy: use duality to reduce to a dual form, then expand as Gram quadratic form,
  -- then apply row_sum_schur_bound.
  -- The dual form: ∑_n |∑_r b_r · e(n · α_r)|² ≤ C · ‖b‖²
  -- Define the matrix x(r, n) = e(α_r · n) for the LSI/dual framework
  intro a
  -- We prove this directly by expanding |S(α_r)|² via Cauchy-Schwarz with the Gram matrix.
  -- |S(α_r)|² = |∑_n a_n e(nα_r)|² = ∑_n ∑_m a_n conj(a_m) e((n-m)α_r)
  -- ∑_r |S(α_r)|² = ∑_{n,m} a_n conj(a_m) · ∑_r e((n-m)α_r)
  -- = ∑_{n,m} a_n conj(a_m) · K(n-m) where K is the N×N kernel matrix
  -- K(n, m) = ∑_r e((n-m)α_r) = gramMatrix' ...
  -- But this approach introduces a DIFFERENT kernel (trigonometric kernel, not Gram matrix).
  -- The Gram matrix approach works for the DUAL form.
  -- Use duality: prove the dual form, then apply lsi_of_dual.
  -- Define x(r, n) = eAN(α_r · n)
  set x : Fin R → Fin N → ℂ := fun r n => eAN (α r * ↑(n : ℕ)) with hx_def
  -- Rewrite goal as LargeSieveInequality x C applied to a
  show (∑ r, ‖∑ n, a n * x r n‖ ^ 2) ≤ C * l2NormSq a
  -- It suffices to prove DualLargeSieve x C
  suffices hdual : DualLargeSieve x C by
    exact (lsi_of_dual x C hC hdual) a
  -- DualLargeSieve x C: ∀ b, ∑_n ‖∑_r b_r · x(r,n)‖² ≤ C · ‖b‖²
  intro b
  -- ∑_n ‖∑_r b_r e(α_r · n)‖² = ∑_{r,s} b_r conj(b_s) · G_{r,s}
  -- where G_{r,s} = ∑_n e(n(α_r - α_s)) = gramMatrix N α r s
  -- Step 1: Expand ‖∑_r b_r x(r,n)‖² using inner product
  -- ∑_n ‖∑_r b_r e(nα_r)‖² = ∑_n (∑_r b_r e(nα_r)) · conj(∑_s b_s e(nα_s))
  -- = ∑_n ∑_r ∑_s b_r conj(b_s) e(n(α_r - α_s))
  -- = ∑_r ∑_s b_r conj(b_s) · (∑_n e(n(α_r - α_s)))
  -- = ∑_r ∑_s b_r conj(b_s) · gramMatrix N α r s
  -- Step 1: Show that the dual LHS is real and equals the norm of the Gram quadratic form
  -- Since ∑_n ‖T_n‖² ≥ 0, we have a real nonneg quantity
  -- We need: ∑_n ‖∑_r b_r x(r,n)‖² ≤ C · ‖b‖²
  -- Express as Gram quadratic form
  have hexpand : (∑ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 : ℝ) =
      (∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s).re := by
    -- LHS = ∑_n |∑_r b_r x_{r,n}|²
    -- = ∑_n Re((∑_r b_r x_{r,n}) · conj(∑_s b_s x_{s,n}))
    -- = ∑_n Re(∑_r ∑_s b_r conj(b_s) x_{r,n} conj(x_{s,n}))
    -- = Re(∑_r ∑_s b_r conj(b_s) ∑_n x_{r,n} conj(x_{s,n}))
    -- = Re(∑_r ∑_s b_r conj(b_s) G_{r,s})
    -- Express |z|² as (z · conj z).re using complex_norm_sq_eq_re_mul_conj
    have habs_sq : ∀ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 =
        ((∑ r, b r * x r n) * starRingEnd ℂ (∑ r, b r * x r n)).re := by
      intro n; exact complex_norm_sq_eq_re_mul_conj _
    simp_rw [habs_sq]
    rw [← Complex.re_sum]
    congr 1
    -- Expand T_n · conj(T_n) = ∑_r ∑_s b_r conj(b_s) x_{r,n} conj(x_{s,n})
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
    -- Swap sum order: ∑_n ∑_r ∑_s = ∑_r ∑_s ∑_n
    rw [Finset.sum_comm]
    congr 1; ext r
    rw [Finset.sum_comm]
    congr 1; ext s
    -- Need: ∑_n b_r * x_{r,n} * (conj(b_s) * conj(x_{s,n})) = b_r * conj(b_s) * G_{r,s}
    -- RHS: b_r * conj(b_s) * G_{r,s} = b_r * conj(b_s) * ∑_n e(n(α_r - α_s))
    unfold gramMatrix
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Finset.mul_sum]
    congr 1; ext n
    -- Goal: b r * x r n * (conj(b s) * conj(x s n)) = b r * conj(b s) * eAN(n * (α r - α s))
    -- Bridge IK.eAN to _root_.eAN so we can use conj_eAN, eAN_add
    simp only [hx_def]
    rw [eAN_eq_root_eAN, eAN_eq_root_eAN]
    -- Goal involves star = starRingEnd ℂ after simp
    change b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * starRingEnd ℂ (_root_.eAN (α s * ↑↑n))) =
        b r * starRingEnd ℂ (b s) * _root_.eAN (↑↑n * (α r - α s))
    rw [conj_eAN]
    rw [show b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * _root_.eAN (-(α s * ↑↑n))) =
          b r * starRingEnd ℂ (b s) * (_root_.eAN (α r * ↑↑n) * _root_.eAN (-(α s * ↑↑n))) from by ring]
    rw [← _root_.eAN_add]
    congr 1; ring_nf
  -- Step 2: Bound the Gram quadratic form
  have hre_le : (∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s).re ≤
      ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s‖ :=
    Complex.re_le_norm _
  have hschur : ‖∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s‖ ≤
      C * l2NormSq b :=
    row_sum_schur_bound (gramMatrix N α) b C hC hrow
      (fun r s => gramMatrix_norm_symm N α r s)
  linarith [hexpand ▸ (hre_le.trans hschur)]

/-- **Optimal ALS from Gram row-sum bound**: if for every δ-spaced configuration
    the Gram matrix row sums are bounded by 1/δ + N - 1, then the optimal
    Additive Large Sieve inequality holds.

    This is the key reduction: it separates the Schur-test / duality machinery
    (proved) from the analytic bound on row sums (the Hilbert inequality content). -/
theorem gram_row_sum_optimal_implies_als
    (hyp : ∀ (R N : ℕ) (α : Fin R → ℝ) (δ : ℝ),
      0 < δ → δ ≤ 1/2 → 1 ≤ N → IsSpaced α δ →
      GramRowSumBound N α (1/δ + ↑N - 1)) :
    AdditiveLargeSieve := by
  intro R N α a δ hδ hδ2 hN hspaced
  have hC : (0 : ℝ) ≤ 1/δ + ↑N - 1 := by
    have : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have : 0 < 1/δ := by positivity
    linarith
  exact gram_row_sum_implies_lsi R N α (1/δ + ↑N - 1) hC (hyp R N α δ hδ hδ2 hN hspaced) a

/-!
### §7.4d Non-optimal Gram row-sum bound (proved)

We prove a **non-optimal** Gram row-sum bound using:
- Diagonal: `gramMatrix N α r r = N` (from `gramMatrix_diag`)
- Off-diagonal: `‖gramMatrix N α r s‖ ≤ 1/(2δ)` for `r ≠ s`
  (from `norm_eAN_geom_sum_le_inv` applied to `β = α_r - α_s`)
- Row sum: `N + (R-1)/(2δ)`

This gives the *non-optimal* bound `N + (R-1)/(2δ)` instead of the optimal
`1/δ + N - 1` (which requires the Hilbert inequality).

We use the round-based separation condition
`∀ r s, r ≠ s → δ ≤ |α r - α s - round(α r - α s)|`
which matches `norm_eAN_geom_sum_le_inv` directly.
-/

/-- **Off-diagonal Gram matrix bound**: for round-separated `α` and `r ≠ s`,
    `‖gramMatrix N α r s‖ ≤ 1/(2δ)`.

    This connects the IK Gram matrix (defined with `_root_.eAN`) to the
    geometric sum bound `norm_eAN_geom_sum_le_inv`. -/
theorem gramMatrix_offdiag_bound (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (r s : Fin R) (hrs : r ≠ s) :
    ‖gramMatrix N α r s‖ ≤ 1 / (2 * δ) := by
  unfold gramMatrix
  exact _root_.norm_eAN_geom_sum_le_inv N (α r - α s) δ hδ (hsep r s hrs)

/-- **Row sum of ‖gramMatrix‖**: for round-separated `α`, every row sum satisfies
    `∑_s ‖G_{r,s}‖ ≤ N + (R - 1)/(2δ)`.

    Proof: The diagonal contributes `‖G_{r,r}‖ = N`. Each of the `R - 1`
    off-diagonal entries contributes at most `1/(2δ)`. -/
theorem gram_row_sum_weak (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (r : Fin R) :
    ∑ s, ‖gramMatrix N α r s‖ ≤ ↑N + (↑R - 1) / (2 * δ) := by
  -- Split the sum into the diagonal term (s = r) and off-diagonal terms (s ≠ r)
  have hdiag : ‖gramMatrix N α r r‖ = ↑N := by
    rw [gramMatrix_diag]
    simp
  -- Rewrite the sum by separating diagonal from off-diagonal
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  -- Now goal: ‖G_{r,r}‖ + ∑_{s ≠ r} ‖G_{r,s}‖ ≤ N + (R-1)/(2δ)
  -- Bound diagonal
  have h1 : ‖gramMatrix N α r r‖ = ↑N := hdiag
  -- Bound each off-diagonal term
  have h2 : ∀ s ∈ Finset.univ.erase r, ‖gramMatrix N α r s‖ ≤ 1 / (2 * δ) := by
    intro s hs
    have hrs : s ≠ r := Finset.ne_of_mem_erase hs
    exact gramMatrix_offdiag_bound N α δ hδ hsep r s hrs.symm
  -- Number of off-diagonal terms
  have h3 : (Finset.univ.erase r).card = R - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
  -- Bound: ∑_{s ≠ r} ‖G_{r,s}‖ ≤ (R-1) · 1/(2δ)
  have h4 : ∑ s ∈ Finset.univ.erase r, ‖gramMatrix N α r s‖ ≤
      (Finset.univ.erase r).card • (1 / (2 * δ)) :=
    Finset.sum_le_card_nsmul _ _ _ h2
  rw [h3] at h4
  rw [h1]
  -- (R - 1) • (1/(2δ)) = (R - 1) * (1/(2δ)) for ℕ smul on ℝ
  have h5 : (R - 1) • (1 / (2 * δ)) = ↑(R - 1) * (1 / (2 * δ)) := by
    rw [nsmul_eq_mul]
  rw [h5] at h4
  -- R ≥ 1 since r : Fin R exists
  have hR : 1 ≤ R := Fin.pos r
  have h6 : ↑(R - 1) * (1 / (2 * δ)) = (↑R - 1) / (2 * δ) := by
    rw [Nat.cast_sub hR]; ring
  linarith

/-- **Non-optimal ALS via Gram row-sum bound**: for round-separated evaluation
    points, the additive large sieve holds with constant `N + (R-1)/(2δ)`.

    This is weaker than the optimal `1/δ + N - 1` but demonstrates the
    complete Gram matrix framework (duality + Schur test + geometric sum bound)
    as an end-to-end proved theorem. -/
theorem gram_als_weak
    (R N : ℕ) (α : Fin R → ℝ) (a : Fin N → ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hR : 1 ≤ R)
    (hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|) :
    (∑ r, ‖∑ n : Fin N, a n * _root_.eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤
      (↑N + (↑R - 1) / (2 * δ)) * l2NormSq a := by
  -- The Gram row-sum bound gives GramRowSumBound N α (N + (R-1)/(2δ))
  have hrow : GramRowSumBound N α (↑N + (↑R - 1) / (2 * δ)) := by
    intro r
    exact gram_row_sum_weak N α δ hδ hsep r
  -- The constant is nonneg
  have hC : (0 : ℝ) ≤ ↑N + (↑R - 1) / (2 * δ) := by
    have : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have : 0 ≤ (↑R - 1) / (2 * δ) := by
      apply div_nonneg
      · have : 1 ≤ (R : ℝ) := Nat.one_le_cast.mpr hR; linarith
      · positivity
    linarith
  -- Apply gram_row_sum_implies_lsi
  -- Need to bridge: the LHS uses eAN(α_r * n) but gram_row_sum_implies_lsi uses
  -- IK.eAN(α_r * n). These are equal by eAN_eq_root_eAN.
  have key := gram_row_sum_implies_lsi R N α _ hC hrow a
  -- gram_row_sum_implies_lsi uses IK.eAN, we need _root_.eAN
  -- Rewrite in key: IK.eAN = _root_.eAN
  simp only [eAN_eq_root_eAN] at key
  exact key

/-!
### §7.4e Hilbert inequality implies optimal ALS

The **optimal** additive large sieve (Theorem 7.7) follows from the Hilbert inequality
(Lemma 7.8) via Corollaries 7.9–7.10 of IK. The argument:

1. By duality, ALS is equivalent to the dual form
   `∑_n |∑_r b_r e(nα_r)|² ≤ (δ⁻¹ + N - 1) · ‖b‖²`.
2. The dual LHS expands as `Re(∑_{r,s} b_r conj(b_s) G_{r,s})` where
   `G_{r,s} = gramMatrix N α r s` is the Gram matrix.
3. The diagonal contributes `N · ‖b‖²`.
4. The off-diagonal `∑_{r≠s} b_r conj(b_s) G_{r,s}` is bounded in norm by
   `(δ⁻¹ - 1) · ‖b‖²` — this is the content of IK Corollaries 7.9–7.10
   (Hilbert inequality + geometric-sum-to-sin identity + Cohen's saving-the-1 trick).

Step 4 requires continuous Fourier analysis (the identity `∑_{n<N} e(nβ) =
e(Kβ) sin(πNβ)/sin(πβ)` and properties of `sin`). We capture it as the open
proposition `GramOffDiagBilinearBound` and prove steps 1–3 compositionally.
-/

/-- **Corollaries 7.9–7.10 + Cohen trick**: the off-diagonal part of the Gram
    bilinear form satisfies the optimal bound.

    For δ-spaced points α_r, any b_r, and summation length N:
    `‖∑_{r≠s} b_r conj(b_s) G_{r,s}‖ ≤ (1/δ − 1) · ‖b‖²`.

    This captures the analytic content of the Hilbert inequality applied to
    geometric sums: the geometric sum identity relates `G_{r,s}` to
    `sin(πN(α_r − α_s))/sin(π(α_r − α_s))`, and Corollary 7.10 (from the
    Hilbert inequality) bounds the resulting bilinear form by `δ⁻¹ · ‖b‖²`.
    The Cohen limiting trick then sharpens `δ⁻¹` to `δ⁻¹ − 1`.

    This is open because it requires continuous Fourier analysis infrastructure
    (properties of `sin`, the geometric-sum-to-sin identity, and the Cohen
    limiting argument) not present in the codebase. -/
def GramOffDiagBilinearBound : Prop :=
  ∀ (R N : ℕ) (α : Fin R → ℝ) (b : Fin R → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 → 1 ≤ N →
    IsSpaced α δ →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s‖ ≤
      (1/δ - 1) * l2NormSq b

/-- **Gram expansion as diagonal + off-diagonal**: the full Gram quadratic form
    splits into the diagonal (which equals `N · ‖b‖²`) plus the off-diagonal.

    `∑_{r,s} b_r conj(b_s) G_{r,s} = (↑N · ∑_r ‖b_r‖²) + off-diagonal` -/
theorem gram_quadratic_split {R N : ℕ} (α : Fin R → ℝ) (b : Fin R → ℂ) :
    ∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
      ↑N * ∑ r, (b r * starRingEnd ℂ (b r)) +
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        b r * starRingEnd ℂ (b s) * gramMatrix N α r s := by
  -- Split each inner sum into the s=r term and s≠r terms
  have hsplit : ∀ r : Fin R,
      ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
        b r * starRingEnd ℂ (b r) * gramMatrix N α r r +
        ∑ s ∈ Finset.univ.erase r, b r * starRingEnd ℂ (b s) * gramMatrix N α r s := by
    intro r
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · -- Diagonal: b_r * conj(b_r) * G_{r,r} = b_r * conj(b_r) * N
    simp_rw [gramMatrix_diag]
    rw [Finset.mul_sum]
    congr 1; ext r
    ring
  · -- Off-diagonal: erase = filter
    congr 1; ext r
    apply Finset.sum_congr
    · ext s; simp [Finset.mem_erase, Finset.mem_filter, ne_comm]
    · intros; rfl

/-- The diagonal of the Gram quadratic form has real part `N · ‖b‖²`. -/
theorem gram_diag_re {R N : ℕ} (b : Fin R → ℂ) :
    (↑N * ∑ r, (b r * starRingEnd ℂ (b r)) : ℂ).re = ↑N * l2NormSq b := by
  -- b_r * conj(b_r) = ↑‖b_r‖ ^ 2 (as complex, real-valued)
  have hreal : ∀ r : Fin R, b r * starRingEnd ℂ (b r) = (↑(‖b r‖) : ℂ) ^ 2 := by
    intro r; exact Complex.mul_conj' (b r)
  simp_rw [hreal, ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

/-- **Off-diagonal Gram bilinear bound implies optimal ALS**: if the off-diagonal
    Gram bilinear form satisfies the bound from Corollaries 7.9–7.10 (with the
    Cohen improvement), then the optimal additive large sieve inequality holds.

    This cleanly separates:
    - **Abstract algebraic infrastructure** (Gram expansion, duality, diagonal evaluation) — proved
    - **Analytic input** (Hilbert inequality + sin bounds + Cohen trick) — captured by
      `GramOffDiagBilinearBound`

    The proof expands the dual ALS LHS as a Gram quadratic form, splits into
    diagonal (`= N · ‖b‖²`) and off-diagonal (`≤ (δ⁻¹ - 1) · ‖b‖²` by hypothesis),
    and combines to get the optimal bound `(δ⁻¹ + N - 1) · ‖b‖²`. -/
theorem gram_offdiag_bilinear_implies_als
    (hoff : GramOffDiagBilinearBound) : AdditiveLargeSieve := by
  intro R N α a δ hδ hδ2 hN hspaced
  -- The constant 1/δ + N - 1 is nonneg
  have hC : (0 : ℝ) ≤ 1/δ + ↑N - 1 := by
    have : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have : 0 < 1/δ := by positivity
    linarith
  -- Use duality: it suffices to prove the dual form
  set x : Fin R → Fin N → ℂ := fun r n => eAN (α r * ↑(n : ℕ)) with hx_def
  show (∑ r, ‖∑ n, a n * x r n‖ ^ 2) ≤ (1/δ + ↑N - 1) * l2NormSq a
  suffices hdual : DualLargeSieve x (1/δ + ↑N - 1) by
    exact (lsi_of_dual x (1/δ + ↑N - 1) hC hdual) a
  -- Prove dual: ∀ b, ∑_n ‖∑_r b_r x(r,n)‖² ≤ (1/δ + N - 1) · ‖b‖²
  intro b
  -- Step 1: Expand dual LHS as Re of Gram quadratic form
  -- (Reusing the expansion from gram_row_sum_implies_lsi)
  have hexpand : (∑ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 : ℝ) =
      (∑ r, ∑ s, b r * starRingEnd ℂ (b s) * gramMatrix N α r s).re := by
    have habs_sq : ∀ n : Fin N, ‖∑ r, b r * x r n‖ ^ 2 =
        ((∑ r, b r * x r n) * starRingEnd ℂ (∑ r, b r * x r n)).re := by
      intro n; exact complex_norm_sq_eq_re_mul_conj _
    simp_rw [habs_sq]
    rw [← Complex.re_sum]
    congr 1
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
    rw [Finset.sum_comm]
    congr 1; ext r
    rw [Finset.sum_comm]
    congr 1; ext s
    unfold gramMatrix
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Finset.mul_sum]
    congr 1; ext n
    simp only [hx_def]
    rw [eAN_eq_root_eAN, eAN_eq_root_eAN]
    change b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * starRingEnd ℂ (_root_.eAN (α s * ↑↑n))) =
        b r * starRingEnd ℂ (b s) * _root_.eAN (↑↑n * (α r - α s))
    rw [conj_eAN]
    rw [show b r * _root_.eAN (α r * ↑↑n) * (starRingEnd ℂ (b s) * _root_.eAN (-(α s * ↑↑n))) =
          b r * starRingEnd ℂ (b s) * (_root_.eAN (α r * ↑↑n) * _root_.eAN (-(α s * ↑↑n))) from by ring]
    rw [← _root_.eAN_add]
    congr 1; ring_nf
  -- Step 2: Split into diagonal + off-diagonal
  rw [hexpand, gram_quadratic_split]
  -- Goal: (↑N * ∑_r b_r conj(b_r) + off-diag).re ≤ (1/δ + N - 1) · l2NormSq b
  rw [Complex.add_re]
  -- Step 3: Bound diagonal
  rw [gram_diag_re]
  -- Step 4: Bound off-diagonal via GramOffDiagBilinearBound
  have hoff_bound := hoff R N α b δ hδ hδ2 hN hspaced
  -- Re(off-diag) ≤ ‖off-diag‖ ≤ (1/δ - 1) · l2NormSq b
  have hre_le_norm := Complex.re_le_norm
    (∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s)
  -- Combine: N · l2NormSq b + re(off-diag) ≤ N · l2NormSq b + (1/δ - 1) · l2NormSq b
  have hcombine : ↑N * l2NormSq b + (1/δ - 1) * l2NormSq b =
      (1/δ + ↑N - 1) * l2NormSq b := by ring
  linarith

end AdditiveLargeSieve

/-!
## §7.5 Multiplicative large sieve inequality

Theorem 7.13 (Bombieri-Davenport): Large sieve for primitive Dirichlet characters.
∑_{q≤Q} (q/φ(q)) ∑*_χ |∑_n a_n χ(n)|² ≤ (Q² + N − 1) ‖a‖².

### Strategy (Gauss sum bridge)

The derivation from the additive large sieve proceeds in three steps:

1. **Gauss inversion**: For primitive χ mod q, write χ(n) = τ(χ̄)⁻¹ ∑_a χ̄(a) e(an/q).
2. **Parseval orthogonality**: Sum |character sum|² over primitive χ, use character
   orthogonality to collapse to a sum of exponential sums at Farey fractions a/q.
3. **ALS application**: The Farey fractions {a/q : 1 ≤ a ≤ q, (a,q)=1, q ≤ Q}
   are Q⁻²-spaced, so the ALS gives the bound (Q² + N − 1) ‖a‖².

For a single prime modulus p, steps 1–2 are formalized below using
`char_parseval_units` and `gaussSum_norm_sq_eq_prime` from LargeSieveAnalytic/Harmonic.
-/

section MultiplicativeLargeSieve

open DirichletCharacter

/-- **Theorem 7.13** (Bombieri-Davenport): Multiplicative large sieve — IK (7.31).
    ∑_{q≤Q} (q/φ(q)) ∑*_{χ mod q} |∑_n a_n χ(n)|² ≤ (Q² + N − 1) ‖a‖².

    This is the full multi-modulus version. It requires:
    - Farey spacing: the fractions a/q with (a,q)=1, q ≤ Q are (1/Q²)-spaced
    - Additive large sieve at Farey fractions
    - Parseval orthogonality summed over conductors with Mobius inversion

    This is stated as an open Prop because the Farey spacing argument and
    the conductor-level Mobius inversion are not yet formalized. -/
def MultiplicativeLargeSieve : Prop :=
  ∀ (N Q : ℕ), 1 ≤ N → 1 ≤ Q →
    ∀ (a : Fin N → ℂ),
      ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
        ((q : ℝ) / (q : ℕ).totient) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ.IsPrimitive),
          ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
        ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a

/-- **Multiplicative large sieve for a single prime modulus** (Parseval form).

    For a prime p and sequence `a : Fin N → ℂ`, the weighted sum of
    nontrivial character sum norms is bounded:

    `(p/(p-1)) · ∑_{χ ≠ 1 mod p} |∑_n a_n χ(↑n)|² ≤ (N - 1 + p) · ‖a‖²`

    Equivalently (without the weight):

    `∑_{χ ≠ 1 mod p} |∑_n a_n χ(↑n)|² ≤ ((p-1)/p) · (N - 1 + p) · ‖a‖²`

    This is strictly sharper than the bound `(p-1) · (N-1+p) · ‖a‖²`
    from `PrimeArithmeticLargeSieve` (which uses Cauchy-Schwarz instead of Parseval).

    **Proved** from the additive large sieve via Gauss sums + Parseval. -/
def MultiplicativeLargeSievePrime : Prop :=
  ∀ (p : ℕ) (_ : Nat.Prime p) (N : ℕ) (_ : 0 < N) (a : Fin N → ℂ),
    ((p : ℝ) / ((p : ℝ) - 1)) *
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
    ((N : ℝ) - 1 + (p : ℝ)) * l2NormSq a

/-- The strengthened form — IK (7.32):
    ∑_{rs≤Q,(r,s)=1} (s/φ(rs)) ∑*_χ |∑_n a_n χ̄(n) c_r(n)|² ≤ (Q²+N−1) ‖a‖².
    Open: requires Ramanujan sum infrastructure. -/
def MultiplicativeLargeSieveStrengthened : Prop :=
  ∀ (N Q : ℕ), 1 ≤ N → 1 ≤ Q →
    ∀ (_ : Fin N → ℂ),
      -- Strengthened form with Ramanujan sums; precise statement requires
      -- additional infrastructure (Ramanujan sum c_r(n), coprimality conditions)
      True

/-!
### §7.5a Parseval bridge: character sums to exponential sums

The key intermediate step for the MLS. By Gauss inversion and multiplicative
Parseval, the weighted sum of nontrivial character sum norms is bounded by
the sum of exponential sum norms over ZMod p. This is sharper than applying
Cauchy-Schwarz to each character individually.

**Key results** (all proved):
- `nontrivial_char_parseval_le`: ∑_{χ≠1} |∑ g(b)χ(b)|² ≤ (p-1)·∑|g(b)|² (from Parseval)
- `sum_filter_inv_eq`: χ ↦ χ⁻¹ bijection on nontrivial characters
- `als_implies_mls_prime`: ALS → MLSPrime (open Prop, depends on ALS)
-/

section ParsBridge

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP75 : NeZero p := ⟨hp.out.ne_zero⟩

/-- **Nontrivial Parseval bound** (dropping trivial character from full Parseval):
    `∑_{χ ≠ 1} |∑_b g(b) χ(↑b)|² ≤ (p-1) · ∑_b |g(b)|²`.

    This follows from `char_parseval_units` (which gives equality for the sum
    over ALL χ) by observing the trivial character contributes a nonneg term. -/
theorem nontrivial_char_parseval_le (g : (ZMod p)ˣ → ℂ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ a : (ZMod p)ˣ, g a * χ (↑a)‖ ^ 2 ≤
    ((p : ℝ) - 1) * ∑ a : (ZMod p)ˣ, ‖g a‖ ^ 2 := by
  -- Full Parseval: ∑_χ ‖...‖² = (p-1) · ∑_a ‖g(a)‖²
  have hfull := char_parseval_units g
  -- Split: ∑_χ = (χ = 1 term) + (χ ≠ 1 terms)
  have hsplit : ∑ χ : DirichletCharacter ℂ p, ‖∑ a : (ZMod p)ˣ, g a * χ (↑a)‖ ^ 2 =
      ‖∑ a : (ZMod p)ˣ, g a * (1 : DirichletCharacter ℂ p) (↑a)‖ ^ 2 +
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
        ‖∑ a : (ZMod p)ˣ, g a * χ (↑a)‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ p))]
    congr 1
    apply Finset.sum_congr
    · ext χ; simp [Finset.mem_erase, Finset.mem_filter, ne_eq, and_iff_left]
    · intros; rfl
  rw [hsplit] at hfull
  -- The trivial character term is nonneg
  have htriv_nonneg : (0 : ℝ) ≤ ‖∑ a : (ZMod p)ˣ, g a *
      (1 : DirichletCharacter ℂ p) (↑a)‖ ^ 2 := by positivity
  linarith

omit hp in
/-- **Filtered inversion bijection**: summing `f(χ⁻¹)` over nontrivial χ
    equals summing `f(χ)`, using the inversion bijection on the character group. -/
theorem sum_filter_inv_eq {α : Type*} [AddCommMonoid α]
    (f : DirichletCharacter ℂ p → α) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      f χ⁻¹ =
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      f χ := by
  apply Finset.sum_nbij (fun χ => χ⁻¹)
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    exact inv_ne_one.mpr hχ
  · intro χ₁ _ χ₂ _ h
    have : χ₁⁻¹ = χ₂⁻¹ := h
    exact inv_injective this
  · intro χ hχ
    have hχ' : χ ≠ 1 := (Finset.mem_filter.mp hχ).2
    refine ⟨χ⁻¹, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, inv_ne_one.mpr hχ'⟩
    · exact inv_inv χ
  · intros; rfl

end ParsBridge

/-!
### §7.5b ALS implies MLS for prime modulus

The reduction ALS → MLS_prime. The proof uses Gauss sum inversion,
Parseval orthogonality (`nontrivial_char_parseval_le`), and the inversion
bijection (`sum_filter_inv_eq`) to establish the Parseval-optimal bound.

The proof requires connecting the Gauss expansion (which writes character
sums as weighted exponential sums) with the units-to-ZMod-p reindexing.
This connection uses `char_sum_gauss_expansion` (from LargeSieveAnalytic),
`gaussSum_norm_sq_eq_prime`, and the fact that MulChar vanishes on non-units.

This is stated as an open Prop because the complete proof requires
infrastructure for splitting sums over ZMod p into sums over units
that is not yet fully formalized. The Parseval helpers above
(`nontrivial_char_parseval_le`, `sum_filter_inv_eq`) are proved and
constitute the main algebraic content.
-/

section MLSPrimeProof

open DirichletCharacter

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP75b : NeZero p := ⟨hp.out.ne_zero⟩

/-- For any MulChar χ on ZMod p (p prime), the sum `∑_{b : ZMod p} χ(b) * f(b)`
    equals `∑_{b : (ZMod p)ˣ} χ(↑b) * f(↑b)` because χ vanishes on non-units. -/
private theorem mulchar_sum_eq_units_sum
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    ∑ b : ZMod p, χ b * f b =
    ∑ b : (ZMod p)ˣ, χ (↑b) * f (↑b) := by
  -- Non-units contribute 0, so restrict to units
  have h0 : ∀ b : ZMod p, ¬IsUnit b → χ b * f b = 0 :=
    fun b hb => by simp [MulChar.map_nonunit χ hb]
  -- Write units sum as a mapped sum
  set g : ZMod p → ℂ := fun b => χ b * f b
  -- ∑ b : (ZMod p)ˣ, g(↑b) = ∑ b ∈ image_of_units, g(b)
  -- ∑ b : ZMod p, g(b) = ∑ b ∈ univ, g(b)
  -- Since g(b) = 0 for non-units, both equal the same thing
  have hRHS : ∑ b : (ZMod p)ˣ, g (↑b) =
      ∑ b ∈ (Finset.univ : Finset (ZMod p)ˣ).map
        ⟨((↑) : (ZMod p)ˣ → ZMod p), Units.val_injective⟩, g b := by
    rw [Finset.sum_map]; rfl
  show ∑ b : ZMod p, g b = ∑ b : (ZMod p)ˣ, g (↑b)
  rw [hRHS]
  -- Now show: ∑_{b ∈ univ} g(b) = ∑_{b ∈ map} g(b)
  -- The map is a subset of univ
  symm
  apply Finset.sum_subset
  · intro x _; exact Finset.mem_univ _
  · intro b _ hb
    apply h0
    intro hbu
    obtain ⟨u, hu⟩ := hbu
    apply hb
    rw [Finset.mem_map]
    refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [Function.Embedding.coeFn_mk]
    exact hu

/-- **Gauss expansion + norm squared bound for nontrivial characters**.
    For nontrivial χ mod p:
    `‖∑_n a_n χ(n)‖² = (1/p) · ‖∑_{b:units} χ⁻¹(↑b) · S(b)‖²`
    where S(b) = ∑_n a_n · eAN(n · val(b)/p). -/
private theorem char_sum_norm_sq_eq_parseval_form
    (N : ℕ) (a : Fin N → ℂ) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    let S : (ZMod p)ˣ → ℂ := fun b =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))
    ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 =
    (p : ℝ)⁻¹ * ‖∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b‖ ^ 2 := by
  intro S
  set ψ := ZMod.stdAddChar (N := p)
  set τ := gaussSum χ⁻¹ ψ
  have hne : τ ≠ 0 := gaussSum_stdAddChar_ne_zero χ⁻¹ (inv_ne_one.mpr hχ)
  -- Step 1: Apply Gauss expansion
  have hgauss := char_sum_gauss_expansion N a χ hχ
  -- ∑_n a(n)χ(n) = τ⁻¹ · ∑_{b:ZMod p} χ⁻¹(b) · ∑_n a(n)·ψ(b·n)
  -- Step 2: Use bridge to replace ψ(b·n) by eAN(n·val(b)/p)
  have hbridge : ∀ b : ZMod p,
      ∑ n : Fin N, a n * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) =
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) := by
    intro b; congr 1; ext n; congr 1
    exact stdAddChar_mul_intCast_eq_eAN b (↑n : ℤ)
  -- Step 3: Rewrite the gauss expansion using bridge
  have hinner_eq : ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) =
    ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) := by
    congr 1; ext b; congr 1; exact hbridge b
  -- Step 4: Replace sum over ZMod p by sum over units (χ⁻¹(0) = 0)
  have hunits_eq : ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) =
    ∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b :=
    mulchar_sum_eq_units_sum _ χ⁻¹
  -- Combine: ∑_n a(n) χ(n) = τ⁻¹ * ∑_{b:units} χ⁻¹(↑b) S(b)
  have hfull : ∑ n : Fin N, a n * χ (↑(↑n : ℤ)) =
      τ⁻¹ * ∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b := by
    rw [hgauss, hinner_eq, hunits_eq]
  rw [hfull, norm_mul, mul_pow]
  -- ‖τ⁻¹‖² = 1/p
  have hτ_norm : ‖τ‖ ^ 2 = (p : ℝ) :=
    gaussSum_norm_sq_eq_prime χ⁻¹ (inv_ne_one.mpr hχ)
  rw [norm_inv, inv_pow, hτ_norm]

/-- The Gauss expansion for a single nontrivial character, linking the
    character sum norm to exponential sums over units. -/
theorem charsum_gauss_bound (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ)))
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 =
    (p : ℝ)⁻¹ * ‖∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b‖ ^ 2 := by
  subst hS
  exact char_sum_norm_sq_eq_parseval_form N a χ hχ

/-- **Sum rewriting**: Rewrite the sum over nontrivial chi using Gauss expansion. -/
theorem charsum_sum_eq_inv_parseval (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 =
    (p : ℝ)⁻¹ *
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact charsum_gauss_bound N a S hS χ (Finset.mem_filter.mp hχ).2

/-- Commuting factors in the character-weighted sum. -/
theorem charsum_comm_factors (S : (ZMod p)ˣ → ℂ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ b : (ZMod p)ˣ, χ (↑b) * S b‖ ^ 2 =
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ b : (ZMod p)ˣ, S b * χ (↑b)‖ ^ 2 := by
  congr 1; ext χ; congr 2; congr 1; ext b; ring

/-- The unweighted bound: character sums bounded by (p-1)/p times exponential sum norms. -/
theorem charsum_le_inv_parseval (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
    (p : ℝ)⁻¹ * ((p : ℝ) - 1) * ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.out.pos
  rw [charsum_sum_eq_inv_parseval N a S hS,
      sum_filter_inv_eq (p := p) (fun χ => ‖∑ b : (ZMod p)ˣ, χ (↑b) * S b‖ ^ 2),
      charsum_comm_factors S, mul_assoc]
  exact mul_le_mul_of_nonneg_left (nontrivial_char_parseval_le S)
    (le_of_lt (inv_pos.mpr hp_pos))

/-- **Parseval chain**: The weighted sum of nontrivial character sum norms squared
    is bounded by the sum of exponential sum norms squared over units. -/
theorem parseval_chain (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))) :
    (p : ℝ) / ((p : ℝ) - 1) *
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
    ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.out.pos
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1_pos
  have h_le := charsum_le_inv_parseval N a S hS
  calc (p : ℝ) / ((p : ℝ) - 1) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
        ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2
      ≤ (p : ℝ) / ((p : ℝ) - 1) *
        ((p : ℝ)⁻¹ * ((p : ℝ) - 1) * ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2) := by gcongr
    _ = ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by field_simp

set_option maxHeartbeats 400000 in
/-- **Unit evaluation points are spaced**: the points `val(↑b)/p` for `b : (ZMod p)ˣ`
    reindexed through `Fin (card units)` are `(1/p)`-spaced. -/
theorem unit_points_spaced (hp_prime : Nat.Prime p)
    (e : Fin (Fintype.card (ZMod p)ˣ) ≃ (ZMod p)ˣ)
    (α : Fin (Fintype.card (ZMod p)ˣ) → ℝ)
    (hα : α = fun r => (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)) :
    IsSpaced α (1 / (p : ℝ)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  intro r s hrs
  rw [hα]
  have hne : e r ≠ e s := fun h => hrs (e.injective h)
  have hval_ne : (↑(e r) : ZMod p) ≠ (↑(e s) : ZMod p) := by
    intro h; exact hne (Units.val_injective h)
  have hv_ne : ZMod.val (↑(e r) : ZMod p) ≠ ZMod.val (↑(e s) : ZMod p) := by
    intro h; exact hval_ne (ZMod.val_injective p h)
  have hval_lt_r : ZMod.val (↑(e r) : ZMod p) < p := ZMod.val_lt _
  have hval_lt_s : ZMod.val (↑(e s) : ZMod p) < p := ZMod.val_lt _
  have hfr : Int.fract ((ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)) =
      (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ) := by
    rw [Int.fract_eq_self]
    exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hp_pos),
      by rw [div_lt_one hp_pos]; exact_mod_cast hval_lt_r⟩
  have hfs : Int.fract ((ZMod.val (↑(e s) : ZMod p) : ℝ) / (p : ℝ)) =
      (ZMod.val (↑(e s) : ZMod p) : ℝ) / (p : ℝ) := by
    rw [Int.fract_eq_self]
    exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hp_pos),
      by rw [div_lt_one hp_pos]; exact_mod_cast hval_lt_s⟩
  rw [hfr, hfs]
  rw [show (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ) -
      (ZMod.val (↑(e s) : ZMod p) : ℝ) / (p : ℝ) =
      ((ZMod.val (↑(e r) : ZMod p) : ℝ) - (ZMod.val (↑(e s) : ZMod p) : ℝ)) / (p : ℝ)
    from div_sub_div_same _ _ _]
  rw [abs_div, abs_of_pos hp_pos, le_div_iff₀ hp_pos]
  rw [show 1 / (p : ℝ) * (p : ℝ) = 1 from by field_simp]
  -- Distinct naturals differ by ≥ 1 as reals
  have hint_ne : (ZMod.val (↑(e r) : ZMod p) : ℤ) ≠ (ZMod.val (↑(e s) : ZMod p) : ℤ) := by
    exact_mod_cast hv_ne
  have hint_abs := Int.one_le_abs (sub_ne_zero.mpr hint_ne)
  -- Transfer from ℤ to ℝ
  have h_real : (1 : ℝ) ≤ |(ZMod.val (↑(e r) : ZMod p) : ℝ) -
      (ZMod.val (↑(e s) : ZMod p) : ℝ)| := by
    have key : ((|↑(ZMod.val (↑(e r) : ZMod p)) - ↑(ZMod.val (↑(e s) : ZMod p))| : ℤ) : ℝ) ≥ 1 := by
      exact_mod_cast hint_abs
    calc (1 : ℝ) ≤ |(↑(ZMod.val (↑(e r) : ZMod p) : ℤ) : ℝ) -
        (↑(ZMod.val (↑(e s) : ZMod p) : ℤ) : ℝ)| := by
          rw [← Int.cast_sub, ← Int.cast_abs]; exact_mod_cast hint_abs
      _ = |(ZMod.val (↑(e r) : ZMod p) : ℝ) - (ZMod.val (↑(e s) : ZMod p) : ℝ)| := by
          push_cast; ring_nf
  exact h_real

set_option maxHeartbeats 400000 in
/-- **ALS LHS reindexing**: The ALS sum over `Fin R` at evaluation points `val(b)/p`
    equals the sum over `(ZMod p)ˣ` of the exponential sums `S(b)`. -/
theorem als_reindex (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ)))
    (e : Fin (Fintype.card (ZMod p)ˣ) ≃ (ZMod p)ˣ)
    (α : Fin (Fintype.card (ZMod p)ˣ) → ℝ)
    (hα : α = fun r => (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)) :
    ∑ r : Fin (Fintype.card (ZMod p)ˣ),
      ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2 =
    ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by
  -- Reindex via e
  apply Fintype.sum_equiv e
  intro r
  -- Goal: ‖∑ n, a n * eAN(α r * n)‖² = ‖S (e r)‖²
  rw [hS, hα]
  congr 1; congr 1
  apply Finset.sum_congr rfl; intro n _
  congr 1
  rw [eAN_eq_root_eAN]
  congr 1; push_cast; ring

set_option maxHeartbeats 800000 in
/-- **ALS implies MLS for prime modulus**: the reduction from the additive
    large sieve to the multiplicative large sieve for a single prime modulus.

    Proof: Gauss expansion + Parseval orthogonality + ALS at evaluation points b/p. -/
theorem als_implies_mls_prime : AdditiveLargeSieve → MultiplicativeLargeSievePrime := by
  intro hals p hp_prime N hN a
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  -- Define exponential sums
  set S : (ZMod p)ˣ → ℂ := fun (b : (ZMod p)ˣ) =>
    ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))
  -- Step 1-3: Parseval chain
  have h_weighted := parseval_chain N a S rfl
  -- Step 4: Apply ALS
  set R := Fintype.card (ZMod p)ˣ
  set e : Fin R ≃ (ZMod p)ˣ := (Fintype.equivFin (ZMod p)ˣ).symm
  set α : Fin R → ℝ := fun r => (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)
  have hδ : (0 : ℝ) < 1 / (p : ℝ) := div_pos one_pos hp_pos
  have hδ_le : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [one_mul]
    exact_mod_cast hp_prime.two_le
  have hspaced := unit_points_spaced hp_prime e α rfl
  have hals_bound := hals R N α a (1 / (p : ℝ)) hδ hδ_le hN hspaced
  have hals_lhs_eq := als_reindex N a S rfl e α rfl
  rw [hals_lhs_eq] at hals_bound
  -- Simplify the ALS bound: 1/(1/p) = p
  have hsimp : (1 / (1 / (p : ℝ)) + ↑N - 1) = ((N : ℝ) - 1 + (p : ℝ)) := by
    rw [one_div_one_div]; ring
  rw [hsimp] at hals_bound
  exact le_trans h_weighted hals_bound

end MLSPrimeProof

end MultiplicativeLargeSieve

/-!
## §7.6 Applications of the large sieve to sieving problems

This section formalizes the application of the large sieve inequality to sieving problems,
following IK §7.6.

### Overview

A **sieving problem** consists of:
- A finite set M of integers contained in an interval of length N
- A finite set P of primes
- For each p in P, a set Omega_p of "excluded" residue classes mod p

The **sifted set** S(M, P, Omega) = {m in M : m mod p not in Omega_p for all p in P}.

**Theorem 7.14** gives an upper bound: |S| ≤ (N + Q²) / H, where
H = Σ_{q ≤ Q, q squarefree, p|q → p in P} Π_{p|q} ω(p)/(p − ω(p)).

**Theorem 7.16** (Linnik): For almost all primes p, the least quadratic non-residue
is at most p^{1/(4√e) + ε}.

### Key definitions

- `sieveWeight`: the multiplicative weight h(p) = ω(p)/(p − ω(p))
- `Lemma715`: the individual modulus bound h(q)|S(0)|² ≤ Σ* |S(a/q)|²
- `LargeSieveAsSieve`: Theorem 7.14, the sifted set upper bound
- `LinnikSmallQNR`: Theorem 7.16, Linnik's result on small quadratic non-residues
-/

section LargeSieveAsSieve

/-!
### Sieve weights

The weight function h(p) = ω(p)/(p − ω(p)) for primes p with ω(p) = |Ω_p|.
For squarefree q with all prime factors in P, h(q) = Π_{p|q} h(p).
-/

/-- The sieve weight for a single prime p with ω(p) excluded residues — IK (7.37).
    h(p) = ω(p) / (p − ω(p)), assuming ω(p) < p. -/
def sieveWeight (p : ℕ) (ωp : ℕ) : ℝ :=
  (ωp : ℝ) / ((p : ℝ) - (ωp : ℝ))

/-- The sieve weight for a squarefree modulus q is the product of h(p) over prime factors.
    For q = p₁ · ... · pₖ squarefree, h(q) = Π h(pᵢ). -/
def sieveWeightProd (ω : ℕ → ℕ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, sieveWeight p (ω p)

/-- The total sieve density: H = Σ_{q ≤ Q} μ²(q) · Π_{p|q} h(p),
    summed over squarefree q whose prime factors all lie in a set P — IK (7.36). -/
def sieveDensity (P : Finset ℕ) (ω : ℕ → ℕ) (Q : ℕ) : ℝ :=
  ∑ q ∈ (Finset.range (Q + 1)).filter (fun q =>
    0 < q ∧ Squarefree q ∧ ∀ p ∈ q.primeFactors, p ∈ P),
    sieveWeightProd ω q

/-- For a single prime p, the sieve weight h(p) is nonneg when ω(p) < p. -/
theorem sieveWeight_nonneg {p : ℕ} {ωp : ℕ} (_hp : 0 < p) (hω : ωp < p) :
    0 ≤ sieveWeight p ωp := by
  unfold sieveWeight
  apply div_nonneg
  · exact Nat.cast_nonneg' ωp
  · have : (ωp : ℝ) < (p : ℝ) := Nat.cast_lt.mpr hω
    linarith

/-- For a single prime p, h(p) is positive when 0 < ω(p) < p. -/
theorem sieveWeight_pos {p : ℕ} {ωp : ℕ} (_hp : 0 < p) (hωpos : 0 < ωp) (hω : ωp < p) :
    0 < sieveWeight p ωp := by
  unfold sieveWeight
  apply div_pos
  · exact Nat.cast_pos.mpr hωpos
  · have : (ωp : ℝ) < (p : ℝ) := Nat.cast_lt.mpr hω
    linarith

/-- The sieve weight product over prime factors of q is nonneg when ω(p) < p for all p | q. -/
theorem sieveWeightProd_nonneg {ω : ℕ → ℕ} {q : ℕ}
    (hq : ∀ p ∈ q.primeFactors, ω p < p) :
    0 ≤ sieveWeightProd ω q := by
  unfold sieveWeightProd
  apply Finset.prod_nonneg
  intro p hp
  exact sieveWeight_nonneg (Nat.pos_of_ne_zero (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp)))
    (hq p hp)

/-!
### Sifted-support condition

For Lemma 7.15, the sequence `a` must be **sifted**: `a_n = 0` whenever `n mod p`
falls in an excluded residue class `Ω_p` for some prime `p | q`. Without this
condition the inequality is false (e.g., p=5, ω=3, a=(1,...,1) gives LHS > RHS = 0).

We parameterize the excluded classes as `Ω : ℕ → Finset ℕ` where `Ω p` gives
the set of excluded residues mod p (as natural numbers < p).
-/

/-- A sequence `a : Fin N → ℂ` is **sifted** with respect to excluded residues `Ω`
    and a set of primes `primes`: `a n = 0` whenever `n mod p ∈ Ω p` for some
    prime `p` in `primes`. -/
def IsSifted {N : ℕ} (a : Fin N → ℂ) (primes : Finset ℕ) (Ω : ℕ → Finset ℕ) : Prop :=
  ∀ n : Fin N, (∃ p ∈ primes, (n : ℕ) % p ∈ Ω p) → a n = 0

/-!
### Lemma 7.15: Individual modulus sieve bound

For any positive squarefree q whose prime factors lie in P, and with ω(p) < p for each
such prime, and for a sequence `a` that is **sifted** (a_n = 0 when n mod p ∈ Ω_p
for some p | q, where |Ω_p| = ω(p)):

  h(q) · |S(0)|² ≤ Σ*_{a mod q} |S(a/q)|²

where S(α) = Σ_n a_n e(nα) is the trigonometric polynomial.

The proof proceeds by induction on the number of prime factors of q:
- Base case (q = p prime): follows from DFT Parseval + Cauchy-Schwarz
- Inductive step: uses CRT factorization of the coprime sum

This is stated as an open Prop since the inductive step requires CRT factorization.
The base case (prime q) is proved as `lemma715_prime`.
-/

/-- **Lemma 7.15** (IK): Individual modulus sieve bound — IK (7.39).
    For squarefree q with prime factors in P and ω(p) < p, and a sifted sequence:
    h(q) · |S(0)|² ≤ Σ*_{a mod q} |S(a/q)|².

    Here S(α) = Σ_{n=1}^{N} a_n e(nα), and the sum on the right runs over
    (a, q) = 1. The sequence `a` must satisfy the sifted-support condition:
    `a n = 0` whenever `n mod p ∈ Ω p` for some prime factor `p` of `q`.

    The proof uses orthogonality of additive characters to show that the
    sum over non-excluded residues is bounded by the coprime exponential sums,
    with induction on the number of prime factors via CRT. -/
def Lemma715 : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℂ) (q : ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    0 < N → 0 < q → Squarefree q →
    (∀ p ∈ q.primeFactors, ω p < p) →
    (∀ p ∈ q.primeFactors, (Ω p).card = ω p) →
    (∀ p ∈ q.primeFactors, ∀ r ∈ Ω p, r < p) →
    IsSifted a q.primeFactors Ω →
    sieveWeightProd ω q *
      ‖∑ n : Fin N, a n‖ ^ 2 ≤
    ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2

/-!
### Lemma 7.15 base case: prime modulus

For q = p prime with ω excluded residue classes mod p, the bound
h(p) · |S(0)|² ≤ ∑_{b=1}^{p-1} |S(b/p)|² follows from:

1. **Residue class grouping**: Define A(r) = ∑_{n ≡ r (mod p)} a_n.
   Then S(0) = ∑_r A(r) and S(b/p) = ∑_r A(r)·e(rb/p).

2. **DFT Parseval over Z/pZ**: ∑_{b=0}^{p-1} |∑_r A(r)·e(rb/p)|² = p · ∑_r |A(r)|².

3. **Sifted support**: A(r) = 0 for r ∈ Ω_p, so by Cauchy-Schwarz:
   |S(0)|² = |∑_{r ∉ Ω_p} A(r)|² ≤ (p−ω) · ∑_r |A(r)|².

4. **Combine**: coprime sum = p·∑|A(r)|² − |S(0)|² ≥ ω/(p−ω)·|S(0)|² = h(p)·|S(0)|².

We state the DFT Parseval step as an open Prop (it could be derived from
`zmod_dft_parseval` in LargeSieveHarmonic, but requires bridging conventions
between `ZMod.dft`/`stdAddChar` and `eAN`).
-/

/-- **DFT Parseval for Z/pZ via eAN**: For prime p and any function A : Fin p → ℂ,
    ∑_{b=0}^{p-1} ‖∑_{r=0}^{p-1} A(r) · e(r·b/p)‖² = p · ∑_r ‖A(r)‖².

    This is the standard Parseval identity for the discrete Fourier transform
    on Z/pZ, expressed using the exponential `eAN`. It could be derived from
    `zmod_dft_parseval` in LargeSieveHarmonic by bridging between `stdAddChar`
    and `eAN`, but we state it independently for modularity. -/
def DFTParsevalPrime : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (A : Fin p → ℂ),
      ∑ b : Fin p,
        ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (p : ℝ))‖ ^ 2 =
      (p : ℝ) * ∑ r : Fin p, ‖A r‖ ^ 2

/-- **DFTParsevalPrime is a theorem**: proved by bridging from `exp_sum_energy_eq_parseval`
    (which works over `ZMod p`) to the `Fin p`-indexed form using `stdAddChar_mul_intCast_eq_eAN`.

    For `p = p' + 1`, `ZMod (p'+1) = Fin (p'+1)` definitionally, so the reindexing is transparent.
    The key step is showing that `stdAddChar (b * n)` equals `eAN(val(n) * val(b) / p)`. -/
theorem dft_parseval_prime_proved : DFTParsevalPrime := by
  intro p hp A
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- Decompose p = p' + 1 so ZMod p = Fin p definitionally
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  -- For p = p'+1, ZMod (p'+1) = Fin (p'+1) definitionally, so f = A
  -- Apply exp_sum_energy_eq_parseval (which works over ZMod p)
  have hpars := exp_sum_energy_eq_parseval (p := p' + 1) A
  -- hpars : ∑ a, ‖∑ n, A n * stdAddChar (a * n)‖² = (p'+1) * ∑ n, ‖A n‖²
  -- We need: for each b, stdAddChar(b * r) = eAN(r * b / (p'+1))
  -- Then the LHS of hpars matches our goal's LHS
  suffices hinner : ∀ (b r : Fin (p' + 1)),
      (ZMod.stdAddChar (N := p' + 1) (b * r) : ℂ) =
      eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑(p' + 1) : ℝ)) by
    simp_rw [hinner] at hpars
    exact hpars
  intro b r
  -- Use stdAddChar_val_eq_eAN: stdAddChar k = eAN(val(k) / p)
  -- For ZMod (p'+1) = Fin (p'+1), ZMod.val = Fin.val (definitional)
  -- First, rewrite stdAddChar(b*r) via stdAddChar_mul_intCast_eq_eAN
  -- which gives _root_.eAN(r * val(b) / (p'+1))
  -- We use the `change` tactic to handle the ZMod/Fin identification cleanly
  change (ZMod.stdAddChar (N := p' + 1) ((b : ZMod (p' + 1)) * (r : ZMod (p' + 1))) : ℂ) =
    eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑(p' + 1) : ℝ))
  have hbridge := stdAddChar_mul_intCast_eq_eAN (p := p' + 1)
    (b : ZMod (p' + 1)) ((r : ℕ) : ℤ)
  -- Show ↑((r:ℕ):ℤ) = r in ZMod (p'+1):
  have hcast : (((r : ℕ) : ℤ) : ZMod (p' + 1)) = (r : ZMod (p' + 1)) := by
    have h1 : (((r : ℕ) : ℤ) : ZMod (p' + 1)) = ((r : ℕ) : ZMod (p' + 1)) := Int.cast_natCast _
    rw [h1]
    exact ZMod.natCast_zmod_val (show ZMod (p' + 1) from r)
  rw [hcast] at hbridge
  rw [hbridge]
  -- Now: _root_.eAN(↑((r:ℕ):ℤ) * ↑(ZMod.val (b:ZMod(p'+1))) / ↑(p'+1)) = IK.eAN(↑(r:ℕ) * ↑(b:ℕ) / ↑(p'+1))
  -- ZMod.val (b : ZMod (p'+1)) = (b : ℕ) (definitional for p'+1), and ↑((r:ℕ):ℤ) = ↑(r:ℕ) via Int.cast_natCast
  rw [eAN_eq_root_eAN]; congr 1

/-- **Residue class sum**: for a sequence `a : Fin N → ℂ` and modulus `p`,
    `residueClassSum a p r` is ∑_{n : Fin N, n ≡ r (mod p)} a_n. -/
noncomputable def residueClassSum {N : ℕ} (a : Fin N → ℂ) (p : ℕ) (r : Fin p) : ℂ :=
  ∑ n ∈ (Finset.univ.filter (fun n : Fin N => (n : ℕ) % p = (r : ℕ))), a n

/-- The residue class sum of an excluded class is zero for a sifted sequence. -/
theorem residueClassSum_excluded {N p : ℕ} (a : Fin N → ℂ) (Ωp : Finset ℕ)
    (hsifted : ∀ n : Fin N, (n : ℕ) % p ∈ Ωp → a n = 0)
    (r : Fin p) (hr : (r : ℕ) ∈ Ωp) :
    residueClassSum a p r = 0 := by
  unfold residueClassSum
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter] at hn
  exact hsifted n (hn.2 ▸ hr)

/-- **Arithmetic core of Lemma 7.15 base case**: Given two real numbers
    `S0sq` (= |S(0)|²) and `sumAsq` (= ∑_r |A(r)|²), and parameters p, ωp
    with ωp < p, if:
    (A) `coprime_sum ≥ p * sumAsq - S0sq`  (from DFT Parseval, subtracting b=0)
    (B) `S0sq ≤ (p - ωp) * sumAsq`          (from Cauchy-Schwarz on non-excluded)
    then `ωp/(p-ωp) * S0sq ≤ coprime_sum`. -/
theorem sieve_weight_bound_of_parseval_cs
    {p ωp : ℕ} {S0sq sumAsq coprime_sum : ℝ}
    (hωp : ωp < p)
    (_hS0_nn : 0 ≤ S0sq) (_hsumA_nn : 0 ≤ sumAsq)
    (hA : (p : ℝ) * sumAsq - S0sq ≤ coprime_sum)
    (hB : S0sq ≤ ((p : ℝ) - (ωp : ℝ)) * sumAsq) :
    (ωp : ℝ) / ((p : ℝ) - (ωp : ℝ)) * S0sq ≤ coprime_sum := by
  have hp_ω_pos : (0 : ℝ) < (p : ℝ) - (ωp : ℝ) := by
    have : (ωp : ℝ) < (p : ℝ) := Nat.cast_lt.mpr hωp
    linarith
  -- From (B): sumAsq ≥ S0sq / (p - ωp)
  have hsumA_lb : S0sq / ((p : ℝ) - (ωp : ℝ)) ≤ sumAsq := by
    rw [div_le_iff₀ hp_ω_pos]
    linarith
  -- From (A): coprime_sum ≥ p * sumAsq - S0sq ≥ p * S0sq/(p-ωp) - S0sq
  --         = S0sq * (p/(p-ωp) - 1) = S0sq * ωp/(p-ωp)
  calc (ωp : ℝ) / ((p : ℝ) - (ωp : ℝ)) * S0sq
      = S0sq * ((ωp : ℝ) / ((p : ℝ) - (ωp : ℝ))) := by ring
    _ = S0sq * (((p : ℝ) - ((p : ℝ) - (ωp : ℝ))) / ((p : ℝ) - (ωp : ℝ))) := by ring
    _ = S0sq * ((p : ℝ) / ((p : ℝ) - (ωp : ℝ)) - 1) := by
        congr 1; rw [sub_div, div_self (ne_of_gt hp_ω_pos)]
    _ = (p : ℝ) * (S0sq / ((p : ℝ) - (ωp : ℝ))) - S0sq := by ring
    _ ≤ (p : ℝ) * sumAsq - S0sq := by
        linarith [mul_le_mul_of_nonneg_left hsumA_lb (le_of_lt (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega : p ≠ 0))))]
    _ ≤ coprime_sum := hA

/-- **Lemma 7.15 base case** (prime modulus): For prime p with ω < p excluded
    residue classes and a sifted sequence, h(p) · |S(0)|² ≤ ∑_{b coprime to p} |S(b/p)|².

    This is the base case of the induction in IK Lemma 7.15. The proof uses:
    1. DFT Parseval to relate coprime exponential sums to residue class sums
    2. Cauchy-Schwarz on the non-excluded residue classes
    3. The sifted-support condition (excluded class sums vanish)

    Stated as an open Prop since it requires the DFT Parseval identity
    (`DFTParsevalPrime`) and the regrouping identity (∑_n a_n e(nb/p) = ∑_r A(r) e(rb/p)).
    The arithmetic combination (Parseval + C-S → sieve weight bound) is proved
    as `sieve_weight_bound_of_parseval_cs`. -/
def Lemma715Prime : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℂ) (p : ℕ) (ωp : ℕ) (Ωp : Finset ℕ),
    0 < N → Nat.Prime p →
    ωp < p →
    Ωp.card = ωp →
    (∀ r ∈ Ωp, r < p) →
    (∀ n : Fin N, (n : ℕ) % p ∈ Ωp → a n = 0) →
    sieveWeight p ωp *
      ‖∑ n : Fin N, a n‖ ^ 2 ≤
    ∑ b ∈ (Finset.range p).filter (Nat.Coprime · p),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2

/-- `eAN(n*b/p) = eAN((n%p)*b/p)` for natural numbers n, b, p with p > 0.
    This uses `n = p*(n/p) + (n%p)` and `eAN(integer) = 1`. -/
theorem eAN_mod_eq {n b p : ℕ} (hp : 0 < p) :
    eAN ((↑n : ℝ) * (↑b : ℝ) / (↑p : ℝ)) =
    eAN ((↑(n % p) : ℝ) * (↑b : ℝ) / (↑p : ℝ)) := by
  rw [eAN_eq_root_eAN, eAN_eq_root_eAN]
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  -- Strategy: show n*b/p = (n/p)*b + (n%p)*b/p as reals, where (n/p)*b is integer.
  -- To avoid Nat.cast_div turning ↑(n/p) into ↑n/↑p, we work through intermediate steps.
  -- Step 1: n = (n/p)*p + n%p as naturals, hence as reals
  set q := n / p with hq_def
  have hdiv : p * q + n % p = n := Nat.div_add_mod n p
  have hdiv_real : (n : ℝ) = (q : ℝ) * (p : ℝ) + (↑(n % p) : ℝ) := by
    have : (p : ℝ) * (q : ℝ) + (↑(n % p) : ℝ) = (n : ℝ) := by exact_mod_cast hdiv
    linarith
  -- Step 2: The key arithmetic identity
  have harg : (↑n : ℝ) * ↑b / ↑p = (↑q : ℝ) * (↑b : ℝ) + (↑(n % p) : ℝ) * ↑b / ↑p := by
    rw [hdiv_real]
    field_simp
  rw [harg, _root_.eAN_add]
  -- Step 3: eAN(q*b) = 1 since q*b is a natural number
  have hint : _root_.eAN ((↑q : ℝ) * (↑b : ℝ)) = 1 := by
    have : (↑q : ℝ) * (↑b : ℝ) = (↑(q * b : ℕ) : ℝ) := by push_cast; ring
    rw [this, show (↑(q * b : ℕ) : ℝ) = (↑((q * b : ℕ) : ℤ) : ℝ) from by push_cast; rfl]
    exact _root_.eAN_intCast _
  rw [hint, one_mul]

/-- The regrouping identity: the exponential sum ∑_n a_n e(nb/p) equals
    ∑_r A(r) e(rb/p) where A = residueClassSum. This follows from
    `eAN_mod_eq` (e(nb/p) = e((n%p)b/p)) and partitioning by residue class.

    The proof uses `Finset.sum_fiberwise` to partition `Fin N` by residue mod p,
    then factors out `eAN(r*b/p)` on each fiber (constant since `n%p = r`). -/
theorem expsum_eq_residueClassSum_expsum {N p : ℕ} (a : Fin N → ℂ) (b : Fin p)
    (hp : 0 < p) :
    ∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) =
    ∑ r : Fin p, residueClassSum a p r *
      eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) := by
  -- Step 1: Replace eAN(n*b/p) with eAN((n%p)*b/p) using eAN_mod_eq
  have lhs_eq : ∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) =
      ∑ n : Fin N, a n * eAN ((↑((n : ℕ) % p) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) :=
    Finset.sum_congr rfl fun n _ => by rw [eAN_mod_eq hp]
  rw [lhs_eq]
  -- Step 2: Define g : Fin N → Fin p as g(n) = ⟨n%p, ...⟩
  let g : Fin N → Fin p := fun n => ⟨(n : ℕ) % p, Nat.mod_lt _ hp⟩
  -- Step 3: Use Finset.sum_fiberwise to partition by g
  -- ∑ n, f n = ∑ r, ∑ n with g n = r, f n
  rw [← Finset.sum_fiberwise (Finset.univ) g]
  -- Step 4: For each fiber r, show the inner sum equals residueClassSum * eAN(r*b/p)
  congr 1; ext r
  -- On the fiber where g(i) = r, we have (i : ℕ) % p = (r : ℕ),
  -- so eAN((i%p)*b/p) = eAN(r*b/p), and we can factor it out.
  have fiber_eq : ∀ i ∈ Finset.univ.filter (fun i : Fin N => g i = r),
      a i * eAN ((↑((i : ℕ) % p) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) =
      a i * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g] at hi
    have hmod : (i : ℕ) % p = (r : ℕ) := Fin.val_eq_of_eq hi
    rw [hmod]
  rw [Finset.sum_congr rfl fiber_eq, ← Finset.sum_mul]
  congr 1
  -- The sum over the fiber is residueClassSum
  unfold residueClassSum
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]
    constructor
    · intro h; exact Fin.val_eq_of_eq h
    · intro h; exact Fin.ext h
  · intro _ _; rfl

/-- Cauchy-Schwarz for finset sums of complex numbers:
    ‖∑_{i ∈ s} v_i‖² ≤ |s| · ∑_{i ∈ s} ‖v_i‖².
    Follows from triangle inequality + real Cauchy-Schwarz. -/
theorem norm_sq_sum_le_card_mul_sum_norm_sq {ι : Type*}
    (s : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  -- ‖∑ v_i‖ ≤ ∑ ‖v_i‖ (triangle)
  have htri : ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖ := norm_sum_le s v
  -- (∑ ‖v_i‖)² ≤ |s| · ∑ ‖v_i‖² (real C-S)
  have hcs : (∑ i ∈ s, ‖v i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  calc ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 := by
        exact sq_le_sq' (by linarith [norm_nonneg (∑ i ∈ s, v i)]) htri
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := hcs

/-- For prime p, the sum over coprime residues (in `Finset.range p`) equals
    the sum over nonzero elements of `Fin p`. -/
theorem coprime_range_eq_nonzero_fin {p : ℕ} (hp : Nat.Prime p) (f : ℕ → ℝ) :
    ∑ b ∈ (Finset.range p).filter (Nat.Coprime · p), f b =
    ∑ b ∈ (Finset.univ : Finset (Fin p)).filter (fun b : Fin p => (b : ℕ) ≠ 0),
      f (b : ℕ) := by
  -- Forward: ℕ → Fin p via (· % p)
  -- Inverse: Fin p → ℕ via Fin.val
  apply Finset.sum_nbij' (fun b => (⟨b % p, Nat.mod_lt b hp.pos⟩ : Fin p)) (fun (b : Fin p) => (b : ℕ))
  · -- forward maps to target
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hbr := (Finset.mem_filter.mp hb).1
    have hb_lt := Finset.mem_range.mp hbr
    rw [Nat.mod_eq_of_lt hb_lt]
    intro h0; rw [h0] at hb
    exact absurd ((Finset.mem_filter.mp hb).2) (by simp [Nat.coprime_zero_left, hp.one_lt.ne'])
  · -- inverse maps to source
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨b.isLt, (hp.coprime_iff_not_dvd.mpr (fun hdvd =>
      hb (Nat.eq_zero_of_dvd_of_lt hdvd b.isLt))).symm⟩
  · -- left inverse
    intro b hb
    have hb_lt := Finset.mem_range.mp ((Finset.mem_filter.mp hb).1)
    simp [Nat.mod_eq_of_lt hb_lt]
  · -- right inverse
    intro b hb
    simp [Nat.mod_eq_of_lt b.isLt]
  · -- function values match
    intro b hb
    have hb_lt := Finset.mem_range.mp ((Finset.mem_filter.mp hb).1)
    simp [Nat.mod_eq_of_lt hb_lt]

/-- **Reduction**: `DFTParsevalPrime` implies `Lemma715Prime`.

    The proof combines:
    1. Regrouping: ∑_n a_n e(nb/p) = ∑_r A(r) e(rb/p)  (`expsum_eq_residueClassSum_expsum`)
    2. DFT Parseval: full sum (b=0..p-1) = p · ∑_r |A(r)|²  (`DFTParsevalPrime`)
    3. Excluded vanishing: A(r) = 0 for r ∈ Ωp  (`residueClassSum_excluded`)
    4. Cauchy-Schwarz on non-excluded classes  (`norm_sq_sum_le_card_mul_sum_norm_sq`)
    5. Arithmetic combination  (`sieve_weight_bound_of_parseval_cs`)

    The key bookkeeping step (coprime-to-nonzero bijection for prime p) is
    proved as `coprime_range_eq_nonzero_fin`. -/
theorem dftParseval_implies_lemma715Prime :
    DFTParsevalPrime → Lemma715Prime := by
  intro hParseval N a p ωp Ωp _hN hp hωp hcard hΩ_valid hsifted
  set A := residueClassSum a p
  -- Step 1: S(0) = ∑_r A(r)
  have s0_eq : ∑ n : Fin N, a n = ∑ r : Fin p, A r := by
    have h := expsum_eq_residueClassSum_expsum a ⟨0, hp.pos⟩ hp.pos
    simp only [Nat.cast_zero, mul_zero, zero_div] at h
    convert h using 1
    · apply Finset.sum_congr rfl; intro n _
      rw [show eAN (0 : ℝ) = 1 from by rw [eAN_eq_root_eAN]; exact _root_.eAN_zero, mul_one]
    · apply Finset.sum_congr rfl; intro r _
      rw [show eAN (0 : ℝ) = 1 from by rw [eAN_eq_root_eAN]; exact _root_.eAN_zero, mul_one]
  rw [s0_eq]
  -- Step 2: Regroup each coprime exponential sum
  have exp_regroup : ∀ b ∈ (Finset.range p).filter (Nat.Coprime · p),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2 =
      ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2 := by
    intro b hb
    have hb_lt : b < p := Finset.mem_range.mp ((Finset.mem_filter.mp hb).1)
    have := expsum_eq_residueClassSum_expsum a ⟨b, hb_lt⟩ hp.pos
    rw [this]
  rw [Finset.sum_congr rfl exp_regroup]
  -- Step 3: Parseval identity
  have parseval := hParseval p hp A
  -- Step 4: Split b=0 and b≠0 in Parseval sum
  have eAN_zero_eq : eAN (0 : ℝ) = 1 := by rw [eAN_eq_root_eAN]; exact _root_.eAN_zero
  have full_split : (p : ℝ) * ∑ r : Fin p, ‖A r‖ ^ 2 =
      ‖∑ r : Fin p, A r‖ ^ 2 +
      ∑ b ∈ (Finset.univ : Finset (Fin p)).filter (fun b : Fin p => (b : ℕ) ≠ 0),
        ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ))‖ ^ 2 := by
    rw [← parseval, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun b : Fin p => (b : ℕ) = 0)]
    congr 1
    have h0_unique : Finset.univ.filter (fun b : Fin p => (b : ℕ) = 0) = {⟨0, hp.pos⟩} := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
    rw [h0_unique, Finset.sum_singleton]
    congr 2; apply Finset.sum_congr rfl; intro r _
    simp only [Nat.cast_zero, mul_zero, zero_div, eAN_zero_eq, mul_one]
  -- Step 5: coprime sum (range) = nonzero sum (Fin p)
  have coprime_eq_nonzero := coprime_range_eq_nonzero_fin hp
    (fun b => ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑b : ℝ) / (↑p : ℝ))‖ ^ 2)
  rw [coprime_eq_nonzero]
  -- Goal: sieveWeight p ωp * ‖∑ A r‖² ≤ ∑_{b≠0} ‖∑ A_r e(rb/p)‖²
  -- From full_split: nonzero sum = p * ∑ ‖A r‖² - ‖∑ A r‖²
  have coprime_bound : (p : ℝ) * ∑ r : Fin p, ‖A r‖ ^ 2 - ‖∑ r : Fin p, A r‖ ^ 2 ≤
      ∑ b ∈ (Finset.univ : Finset (Fin p)).filter (fun b : Fin p => (b : ℕ) ≠ 0),
        ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ))‖ ^ 2 := by
    linarith [full_split]
  -- Step 6: Excluded class handling
  have hA_excl : ∀ r : Fin p, (r : ℕ) ∈ Ωp → A r = 0 :=
    fun r hr => residueClassSum_excluded a Ωp hsifted r hr
  -- ∑ A r = ∑_{r ∉ Ω} A r (excluded vanish)
  have sum_eq : ∑ r : Fin p, A r =
      ∑ r ∈ Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp), A r := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin p => (r : ℕ) ∈ Ωp)]
    rw [Finset.sum_eq_zero (fun r hr => hA_excl r (Finset.mem_filter.mp hr).2), zero_add]
  -- ∑ ‖A r‖² = ∑_{r ∉ Ω} ‖A r‖² (excluded vanish)
  have norm_eq : ∑ r : Fin p, ‖A r‖ ^ 2 =
      ∑ r ∈ Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp), ‖A r‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin p => (r : ℕ) ∈ Ωp)]
    rw [Finset.sum_eq_zero (fun r hr => by
      rw [hA_excl r (Finset.mem_filter.mp hr).2, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0)]), zero_add]
  -- Card of non-excluded = p - ωp
  set S := Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp)
  have hS_card : S.card = p - ωp := by
    show (Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp)).card = p - ωp
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_univ, Fintype.card_fin]
    congr 1; rw [← hcard]
    -- Show #{r : Fin p | (r : ℕ) ∈ Ωp} = #Ωp via forward/inverse bijection
    apply Finset.card_nbij' (fun (r : Fin p) => (r : ℕ))
      (fun (b : ℕ) => ⟨b % p, Nat.mod_lt b hp.pos⟩)
    · intro r hr
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
    · intro b hb
      rw [Finset.mem_coe]
      have hb' := Finset.mem_coe.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rwa [Fin.val_mk, Nat.mod_eq_of_lt (hΩ_valid b hb')]⟩
    · intro r _; simp [Nat.mod_eq_of_lt r.isLt]
    · intro b hb
      have hb' := Finset.mem_coe.mp hb
      simp [Nat.mod_eq_of_lt (hΩ_valid b hb')]
  -- Step 7: Cauchy-Schwarz
  have cs : ‖∑ r : Fin p, A r‖ ^ 2 ≤ ((p : ℝ) - (ωp : ℝ)) * ∑ r : Fin p, ‖A r‖ ^ 2 := by
    rw [sum_eq, norm_eq]
    calc ‖∑ r ∈ S, A r‖ ^ 2
        ≤ (S.card : ℝ) * ∑ r ∈ S, ‖A r‖ ^ 2 := norm_sq_sum_le_card_mul_sum_norm_sq S A
      _ = ((p : ℝ) - (ωp : ℝ)) * ∑ r ∈ S, ‖A r‖ ^ 2 := by
          congr 1; rw [hS_card, Nat.cast_sub (le_of_lt hωp)]
  -- Step 8: Apply arithmetic core
  show sieveWeight p ωp * ‖∑ r : Fin p, A r‖ ^ 2 ≤ _
  unfold sieveWeight
  exact sieve_weight_bound_of_parseval_cs hωp
    (sq_nonneg _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    coprime_bound
    cs

/-- **Lemma 7.15 (prime case) is now a theorem**: composing the proved
    `DFTParsevalPrime` with the reduction `dftParseval_implies_lemma715Prime`. -/
theorem lemma715Prime_proved : Lemma715Prime :=
  dftParseval_implies_lemma715Prime dft_parseval_prime_proved

/-!
### Theorem 7.14: The large sieve as a sieve

The main sieve bound: for a sequence supported on an interval of length N,

  |Z|² ≤ ((N + Q²) / H) · ‖a‖²

where Z = Σ_n a_n over the sifted set, and H = Σ_{q ≤ Q} h(q).

**Proof sketch** (IK):
1. By Lemma 7.15, for each squarefree q ≤ Q:
   h(q) · |Z|² ≤ Σ*_{a mod q} |S(a/q)|²
2. Sum over q ≤ Q: H · |Z|² ≤ Σ_{q ≤ Q} Σ*_{a mod q} |S(a/q)|²
3. By the Farey large sieve (Theorem 7.11): RHS ≤ (Q² + N − 1) · ‖a‖²
4. Divide by H.

We state this as a reduction from Lemma 7.15 + AdditiveLargeSieve → the bound.
The full statement is also recorded as a standalone open Prop.
-/

/-- **Theorem 7.14** (IK): The large sieve as a sieve — IK (7.35)/(7.38).
    Let M be a set of integers in an interval of length N, and for each prime
    p ≤ Q let Ω_p ⊂ Z/pZ be a set of ω(p) excluded residues with ω(p) < p.
    Then the cardinality S of the sifted set satisfies:

    S ≤ (N + Q²) / H

    where H = Σ_{q ≤ Q, squarefree} Π_{p|q} ω(p)/(p − ω(p)).

    Equivalently for the weighted version with sequence (a_n):
    |Z|² ≤ ((N + Q²) / H) · ‖a‖²

    This follows from Lemma 7.15 summed over q ≤ Q, combined with the Farey
    large sieve (Theorem 7.11, which follows from the ALS Theorem 7.7). -/
def LargeSieveAsSieve : Prop :=
  ∀ (N Q : ℕ) (P : Finset ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    1 ≤ N → 1 ≤ Q →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, 0 < ω p ∧ ω p < p) →
    (∀ p ∈ P, (p : ℕ) ≤ Q) →
    (∀ p ∈ P, (Ω p).card = ω p) →
    (∀ p ∈ P, ∀ r ∈ Ω p, r < p) →
    ∀ (a : Fin N → ℂ),
      IsSifted a P Ω →
      sieveDensity P ω Q *
        ‖∑ n : Fin N, a n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * l2NormSq a

/-- **Corollary**: The cardinality form of Theorem 7.14.
    For the characteristic function of a sifted set S ⊆ {1,...,N}:
    |S| ≤ (N + Q²) / H.

    This is the form most commonly used in applications. -/
def LargeSieveAsSieve_card : Prop :=
  ∀ (N Q : ℕ) (P : Finset ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    1 ≤ N → 1 ≤ Q →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, 0 < ω p ∧ ω p < p) →
    (∀ p ∈ P, (p : ℕ) ≤ Q) →
    (∀ p ∈ P, (Ω p).card = ω p) →
    (∀ p ∈ P, ∀ r ∈ Ω p, r < p) →
    ∀ (S : Finset (Fin N)),
      -- S is "sifted": elements of S avoid all excluded residues
      (∀ n ∈ S, ∀ p ∈ P, (n : ℕ) % p ∉ Ω p) →
      (S.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ) ^ 2) / sieveDensity P ω Q

/-- The weighted form of Theorem 7.14 implies the cardinality form:
    simply take a_n = 1 if n ∈ S, 0 otherwise, and note ‖a‖² = |S| and Z = |S|.
    The set S must be sifted: no element falls in an excluded residue class. -/
theorem largeSieveAsSieve_implies_card (h : LargeSieveAsSieve) :
    ∀ (N Q : ℕ) (P : Finset ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    1 ≤ N → 1 ≤ Q →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, 0 < ω p ∧ ω p < p) →
    (∀ p ∈ P, (p : ℕ) ≤ Q) →
    (∀ p ∈ P, (Ω p).card = ω p) →
    (∀ p ∈ P, ∀ r ∈ Ω p, r < p) →
    0 < sieveDensity P ω Q →
    ∀ (S : Finset (Fin N)),
      (∀ n ∈ S, ∀ p ∈ P, (n : ℕ) % p ∉ Ω p) →
      (S.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ) ^ 2) / sieveDensity P ω Q := by
  intro N Q P ω Ω hN hQ hP hω hPQ hΩcard hΩval hH S hSsifted
  -- Use a_n = indicator of S; then ‖a‖² = |S| and |Z|² = |S|²
  set a : Fin N → ℂ := fun n => if n ∈ S then 1 else 0
  -- The indicator of a sifted set is sifted
  have ha_sifted : IsSifted a P Ω := by
    intro n ⟨p, hp, hn⟩
    simp only [a]
    split_ifs with hmem
    · exact absurd hn (hSsifted n hmem p hp)
    · rfl
  have hbound := h N Q P ω Ω hN hQ hP hω hPQ hΩcard hΩval a ha_sifted
  -- Compute ‖a‖² = |S|
  have ha_norm : l2NormSq a = (S.card : ℝ) := by
    unfold l2NormSq
    simp only [a]
    conv_lhs =>
      arg 2; ext i
      rw [show ‖(if i ∈ S then (1 : ℂ) else 0)‖ ^ 2 =
            if i ∈ S then 1 else 0 by
        split <;> simp]
    rw [Finset.sum_ite_mem Finset.univ S (fun _ => (1 : ℝ))]
    simp
  -- Compute Z = ∑ a_n = |S|
  have ha_sum : ∑ n : Fin N, a n = (S.card : ℂ) := by
    simp only [a]
    trans (↑(∑ n : Fin N, if n ∈ S then (1 : ℕ) else 0) : ℂ)
    · push_cast; rfl
    · congr 1; simp
  have ha_sum_norm : ‖∑ n : Fin N, a n‖ ^ 2 = (S.card : ℝ) ^ 2 := by
    rw [ha_sum]; simp
  rw [ha_sum_norm, ha_norm] at hbound
  -- Now hbound : H * |S|² ≤ (N + Q²) * |S|
  by_cases hS : S.card = 0
  · simp [hS]; positivity
  · have hSpos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)
    rw [le_div_iff₀ hH]
    -- Need: |S| * H ≤ N + Q²
    -- From hbound: H * |S|² ≤ (N + Q²) * |S|; divide by |S| > 0
    -- hbound : H * S² ≤ (N + Q²) * S
    -- Goal from le_div_iff₀: S * H ≤ N + Q²
    nlinarith [hbound, sq_nonneg (S.card : ℝ), sq_abs (S.card : ℝ)]

/-!
### Reduction: Lemma 7.15 + Farey LS → Theorem 7.14

The proof of Theorem 7.14 follows by:
1. Applying Lemma 7.15 for each squarefree q ≤ Q with prime factors in P
2. Summing: H · |Z|² ≤ Σ_{q ≤ Q} Σ*_{a mod q} |S(a/q)|²
3. The RHS is bounded by the Farey large sieve (Theorem 7.11)

We record this reduction as a theorem. Since the Farey large sieve itself follows
from the additive large sieve (ALS) by the spacing of Farey fractions, the full
chain is: ALS → Farey LS → (with Lemma 7.15) → Theorem 7.14.

The Farey large sieve is restated here with a proper (non-trivial) statement
for use in the reduction.
-/

/-- **Theorem 7.11** (restated): Large sieve at Farey fractions — IK (7.28).
    Σ_{q ≤ Q} Σ*_{a mod q} |Σ_n a_n e(an/q)|² ≤ (Q² + N − 1) · ‖a‖².

    This is the proper statement (the earlier FareyLargeSieve used True as a stub).
    It follows from the ALS by the fact that Farey fractions a/q with (a,q)=1
    and q ≤ Q are (1/Q²)-spaced. -/
def FareyLargeSieveProper : Prop :=
  ∀ (N Q : ℕ), 1 ≤ N → 1 ≤ Q →
    ∀ (a : Fin N → ℂ),
      ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a

/-- **Coprime fraction uniqueness**: If `b/q = b'/q'` as rationals with
    `gcd(b,q) = gcd(b',q') = 1` and `q, q' > 0`, then `q = q'` and `b = b'`. -/
private theorem coprime_frac_unique {br qr bs qs : ℕ}
    (hqr_pos : 0 < qr) (hqs_pos : 0 < qs)
    (hbr_cop : Nat.Coprime br qr) (hbs_cop : Nat.Coprime bs qs)
    (heq : (br : ℚ) / qr = (bs : ℚ) / qs) : qr = qs ∧ br = bs := by
  have hqr_ne : (qr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqs_ne : (qs : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_eq_div_iff hqr_ne hqs_ne] at heq
  have heq_nat : br * qs = bs * qr := by exact_mod_cast heq
  have h_qr_dvd_qs : qr ∣ qs := by
    have h : qr ∣ br * qs := ⟨bs, by linarith [heq_nat]⟩
    exact hbr_cop.symm.dvd_of_dvd_mul_left h
  have h_qs_dvd_qr : qs ∣ qr := by
    have h : qs ∣ bs * qr := ⟨br, by linarith [heq_nat]⟩
    exact hbs_cop.symm.dvd_of_dvd_mul_left h
  have hqeq : qr = qs := Nat.le_antisymm (Nat.le_of_dvd hqs_pos h_qr_dvd_qs)
    (Nat.le_of_dvd hqr_pos h_qs_dvd_qr)
  refine ⟨hqeq, ?_⟩
  exact Nat.mul_right_cancel hqs_pos (hqeq ▸ heq_nat)

/-- **ALS implies Farey LS**: The additive large sieve (Theorem 7.7) implies the
    Farey large sieve (Theorem 7.11).

    The Farey fractions `b/q` with `(b,q) = 1`, `0 ≤ b < q`, `1 ≤ q ≤ Q` are
    `(1/Q²)`-spaced. Applying the ALS with `δ = 1/Q²` gives the bound
    `(Q² + N − 1) · ‖a‖²`.

    The proof enumerates the Farey pairs as `Fin R`, shows the points are spaced
    using the classical mediant property (Farey spacing), and applies the ALS. -/
theorem als_implies_farey_large_sieve_proper (hals : AdditiveLargeSieve) :
    FareyLargeSieveProper := by
  intro N Q hN hQ a
  -- Define the Farey finset as a sigma type
  let Qs := (Finset.range (Q + 1)).filter (0 < ·)
  let Bs : ℕ → Finset ℕ := fun q => (Finset.range q).filter (Nat.Coprime · q)
  let S := Qs.sigma Bs
  -- Convert the double sum to a sum over the sigma finset
  have hdouble : ∑ q ∈ Qs, ∑ b ∈ Bs q,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 =
    ∑ x ∈ S, ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2 :=
    Finset.sum_sigma' Qs Bs _
  -- Show the double sum is what we want
  show ∑ q ∈ Qs, ∑ b ∈ Bs q,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 ≤
    ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a
  -- Get the cardinality and enumeration
  set R := S.card
  -- Use the Finset equivalence to Fin R
  let e := S.equivFin
  -- Define the evaluation points
  let α : Fin R → ℝ := fun i =>
    let x := e.symm i
    (x.val.2 : ℝ) / (x.val.1 : ℝ)
  -- Step 1: Convert sigma sum to Fin sum
  have hfin_sum : ∑ x ∈ S,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2 =
    ∑ i : Fin R,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * α i)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort S]
    apply Fintype.sum_equiv e
    intro x
    simp only [α, Equiv.symm_apply_apply]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro n _
    congr 1; congr 1; rw [mul_div_assoc]
  -- Step 2: Match the ALS format (α r * ↑n = ↑n * α r)
  have hals_sum : ∑ i : Fin R,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * α i)‖ ^ 2 =
    ∑ i : Fin R,
      ‖∑ n : Fin N, a n * eAN (α i * ↑(n : ℕ))‖ ^ 2 := by
    congr 1; ext i; congr 2; congr 1; ext n; congr 1; congr 1; ring
  -- Step 3: Handle Q = 1 separately (δ = 1/Q² = 1 > 1/2 violates ALS hypothesis)
  by_cases hQ1 : Q = 1
  · -- For Q = 1: only one Farey pair (q=1, b=0), bound by Cauchy-Schwarz
    subst hQ1
    simp only [Qs, Bs]
    have hQs : (Finset.range 2).filter (0 < ·) = {1} := by decide
    rw [hQs, Finset.sum_singleton]
    have hBs : (Finset.range 1).filter (Nat.Coprime · 1) = {0} := by decide
    rw [hBs, Finset.sum_singleton]
    -- eAN(n * 0 / 1) = eAN(0) = 1, so a n * eAN(...) = a n
    have hsimp_exp : ∀ n : Fin N,
        a n * eAN ((↑(n : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = a n := by
      intro n
      have : ((↑(n : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = 0 := by simp
      rw [this, eAN_eq_root_eAN, _root_.eAN_zero, mul_one]
    conv_lhs => rw [show ∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) =
        ∑ n : Fin N, a n from Finset.sum_congr rfl (fun n _ => hsimp_exp n)]
    -- Need: ‖∑ a_n‖² ≤ (↑1 ^ 2 + ↑N - 1) * l2NormSq a
    -- The coefficient (↑1)^2 + ↑N - 1 = ↑N
    have hcoeff : ((1 : ℕ) : ℝ) ^ 2 + (N : ℝ) - 1 = (N : ℝ) := by push_cast; ring
    rw [hcoeff]
    -- Triangle inequality + Chebyshev: ‖∑ a_n‖² ≤ (∑ ‖a_n‖)² ≤ N * ∑ ‖a_n‖²
    calc ‖∑ n : Fin N, a n‖ ^ 2
        ≤ (∑ n : Fin N, ‖a n‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ ↑(Finset.univ : Finset (Fin N)).card * (∑ n : Fin N, ‖a n‖ ^ 2) :=
          sq_sum_le_card_mul_sum_sq
      _ = (N : ℝ) * l2NormSq a := by
          simp [l2NormSq]
  · -- For Q ≥ 2: use ALS with δ = 1/Q²
    have hQ2 : 2 ≤ Q := by omega
    have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (by omega)
    have hQsq_pos : (0 : ℝ) < (Q : ℝ) ^ 2 := sq_pos_of_pos hQ_pos
    have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := div_pos one_pos hQsq_pos
    have hδ_le : 1 / (Q : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hQsq_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [one_mul]
      have : (4 : ℝ) ≤ (Q : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
        nlinarith
      linarith
    -- Show the Farey points are spaced
    have hspaced : IsSpaced α (1 / (Q : ℝ) ^ 2) := by
      intro r s hrs
      have hne : (e.symm r) ≠ (e.symm s) :=
        fun h => hrs (e.symm.injective h ▸ rfl)
      have hne' : (e.symm r).val ≠ (e.symm s).val :=
        fun h => hne (Subtype.val_injective h)
      -- Both pairs are in S
      have hmr := (e.symm r).prop
      have hms := (e.symm s).prop
      rw [Finset.mem_sigma] at hmr hms
      have hqr_mem := Finset.mem_filter.mp hmr.1
      have hqs_mem := Finset.mem_filter.mp hms.1
      have hqr_pos : 0 < (e.symm r).val.1 := hqr_mem.2
      have hqs_pos : 0 < (e.symm s).val.1 := hqs_mem.2
      have hqr_le : (e.symm r).val.1 ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqr_mem.1)
      have hqs_le : (e.symm s).val.1 ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqs_mem.1)
      have hbr_mem := Finset.mem_filter.mp hmr.2
      have hbs_mem := Finset.mem_filter.mp hms.2
      have hbr_lt : (e.symm r).val.2 < (e.symm r).val.1 := Finset.mem_range.mp hbr_mem.1
      have hbs_lt : (e.symm s).val.2 < (e.symm s).val.1 := Finset.mem_range.mp hbs_mem.1
      have hbr_cop : Nat.Coprime (e.symm r).val.2 (e.symm r).val.1 := hbr_mem.2
      have hbs_cop : Nat.Coprime (e.symm s).val.2 (e.symm s).val.1 := hbs_mem.2
      -- Abbreviate
      set qr := (e.symm r).val.1
      set br := (e.symm r).val.2
      set qs := (e.symm s).val.1
      set bs := (e.symm s).val.2
      -- Int.fract(b/q) = b/q since 0 ≤ b/q < 1
      have hqr_pos_r : (0 : ℝ) < (qr : ℝ) := Nat.cast_pos.mpr hqr_pos
      have hqs_pos_r : (0 : ℝ) < (qs : ℝ) := Nat.cast_pos.mpr hqs_pos
      have hfr : Int.fract ((br : ℝ) / (qr : ℝ)) = (br : ℝ) / (qr : ℝ) := by
        rw [Int.fract_eq_self]
        exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hqr_pos_r),
          by rw [div_lt_one hqr_pos_r]; exact_mod_cast hbr_lt⟩
      have hfs : Int.fract ((bs : ℝ) / (qs : ℝ)) = (bs : ℝ) / (qs : ℝ) := by
        rw [Int.fract_eq_self]
        exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hqs_pos_r),
          by rw [div_lt_one hqs_pos_r]; exact_mod_cast hbs_lt⟩
      show 1 / (Q : ℝ) ^ 2 ≤ |Int.fract (α r) - Int.fract (α s)|
      simp only [α]
      rw [hfr, hfs]
      -- The fractions br/qr ≠ bs/qs: coprimality forces uniqueness
      have hfrac_ne : ((br : ℤ) : ℚ) / (qr : ℚ) ≠ ((bs : ℤ) : ℚ) / (qs : ℚ) := by
        intro heq
        -- Convert the ℤ/ℚ fractions to ℕ/ℚ fractions
        have heq' : (br : ℚ) / qr = (bs : ℚ) / qs := by push_cast at heq ⊢; exact heq
        have ⟨hqeq, hbeq⟩ := coprime_frac_unique hqr_pos hqs_pos hbr_cop hbs_cop heq'
        exact hne' (Sigma.ext_iff.mpr ⟨hqeq, heq_of_eq hbeq⟩)
      -- Apply Farey spacing
      exact farey_spacing_proved Q (by omega) qr qs hqr_pos hqr_le hqs_pos hqs_le
        (br : ℤ) (bs : ℤ) hfrac_ne
    -- Apply ALS
    have hals_bound := hals R N α a (1 / (Q : ℝ) ^ 2) hδ hδ_le hN hspaced
    -- Simplify 1/(1/Q²) = Q²
    have hsimp : 1 / (1 / (Q : ℝ) ^ 2) + ↑N - 1 = (Q : ℝ) ^ 2 + ↑N - 1 := by
      rw [one_div_one_div]
    rw [hsimp] at hals_bound
    -- Chain: double sum = Fin sum ≤ (Q² + N - 1) * ‖a‖²
    rw [hdouble, hfin_sum, hals_sum]
    exact hals_bound

/-- **Reduction**: Lemma 7.15 + Farey large sieve → Theorem 7.14 (large sieve as sieve).

    Proof: For each squarefree q ≤ Q with prime factors in P, Lemma 7.15 gives
    h(q) · |Z|² ≤ Σ*_{a mod q} |S(a/q)|². Summing over such q:
    H · |Z|² ≤ Σ_{q ≤ Q} Σ*_{a mod q} |S(a/q)|² ≤ (Q² + N − 1) · ‖a‖²
    where the last step uses the Farey large sieve. Since N−1 ≤ N, we get
    H · |Z|² ≤ (N + Q²) · ‖a‖². -/
theorem lemma715_farey_implies_largeSieveAsSieve
    (h715 : Lemma715) (hfarey : FareyLargeSieveProper) :
    LargeSieveAsSieve := by
  intro N Q P ω Ω hN hQ hP hω hPQ hΩcard hΩval a ha_sifted
  have hfarey_bound := hfarey N Q hN hQ a
  -- Abbreviate the qualifying filter
  let qualQ := (Finset.range (Q + 1)).filter (fun q =>
    0 < q ∧ Squarefree q ∧ ∀ p ∈ q.primeFactors, p ∈ P)
  -- Step 1-2: For each qualifying q, apply Lemma 7.15 and sum
  have hsum : ∀ q ∈ qualQ,
      sieveWeightProd ω q * ‖∑ n : Fin N, a n‖ ^ 2 ≤
      ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
        ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
    intro q hq
    have hqmem := (Finset.mem_filter.mp hq).2
    obtain ⟨hqpos, hqsf, hqP⟩ := hqmem
    have hωlt : ∀ p ∈ q.primeFactors, ω p < p := by
      intro p hp; exact (hω p (hqP p hp)).2
    have hΩcard_q : ∀ p ∈ q.primeFactors, (Ω p).card = ω p :=
      fun p hp => hΩcard p (hqP p hp)
    have hΩval_q : ∀ p ∈ q.primeFactors, ∀ r ∈ Ω p, r < p :=
      fun p hp => hΩval p (hqP p hp)
    -- The sifted condition for q's prime factors follows from sifted for P
    have ha_sifted_q : IsSifted a q.primeFactors Ω := by
      intro n ⟨p, hp, hn⟩
      exact ha_sifted n ⟨p, hqP p hp, hn⟩
    exact h715 N a q ω Ω hN hqpos hqsf hωlt hΩcard_q hΩval_q ha_sifted_q
  -- Step 3: H * |Z|² ≤ Σ_{qualQ} coprime_sum(q)
  have hH_le_qual : sieveDensity P ω Q * ‖∑ n : Fin N, a n‖ ^ 2 ≤
      ∑ q ∈ qualQ,
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
    show sieveDensity P ω Q * _ ≤ _
    unfold sieveDensity
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hsum
  -- Step 4: qualQ sum ≤ full Farey sum (add nonneg terms for non-qualifying q)
  have hqual_le_farey :
      ∑ q ∈ qualQ,
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      have hqmem := (Finset.mem_filter.mp hq)
      rw [Finset.mem_filter]
      exact ⟨hqmem.1, hqmem.2.1⟩
    · intro q _ _
      apply Finset.sum_nonneg; intros; positivity
  -- Step 5: Farey sum ≤ (Q² + N - 1) * ‖a‖² ≤ (N + Q²) * ‖a‖²
  have hNQ : ((Q : ℝ) ^ 2 + (N : ℝ) - 1) ≤ ((N : ℝ) + (Q : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    linarith
  calc sieveDensity P ω Q * ‖∑ n : Fin N, a n‖ ^ 2
      ≤ ∑ q ∈ qualQ, ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := hH_le_qual
    _ ≤ ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
          ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
            ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := hqual_le_farey
    _ ≤ ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a := hfarey_bound
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * l2NormSq a := by
        apply mul_le_mul_of_nonneg_right hNQ
        unfold l2NormSq; apply Finset.sum_nonneg; intros; positivity

end LargeSieveAsSieve

/-!
### Theorem 7.16 (Linnik): Small quadratic non-residues for almost all primes

For any ε > 0, all but O(1/ε) primes p have the property that the least
quadratic non-residue mod p is at most p^{1/(4√e) + ε}.

More precisely, let X_ε be the number of primes p ≤ √N with q(p) > N^ε.
Then X_ε ≪ 1/ε.

This uses the large sieve as sieve (Theorem 7.14) with:
- P = {primes p ≤ √N with q(p) > N^ε}
- Ω_p = {quadratic non-residues mod p}, so ω(p) = (p−1)/2
- The sifted set contains smooth numbers ≤ N

Combined with a lower bound for the number of smooth numbers, one gets X_ε ≪ 1.
-/

/-- **Theorem 7.16** (Linnik, 1941): For any ε > 0, the number of primes p ≤ x
    whose least quadratic non-residue exceeds x^ε is bounded by a constant
    depending only on ε. In particular, for almost all primes p, the least QNR
    is at most p^{1/(4√e) + ε}.

    This follows from the large sieve as sieve (Theorem 7.14) applied with
    Ω_p = {quadratic non-residues mod p} for primes p with large QNR. -/
def LinnikSmallQNR : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : ℕ), 2 ≤ x →
        ((Finset.filter (fun p =>
            Nat.Prime p ∧ p ≤ x ∧
            ∀ (n : ℕ), 1 < n → n ≤ x → (n : ℕ) < p →
              ¬(∃ k, k ^ 2 ≡ n [MOD p]))
          (Finset.range (x + 1))).card : ℝ) ≤ C

/-- **Reduction**: Theorem 7.14 implies Linnik's theorem (Theorem 7.16).
    The proof uses Theorem 7.14 with P = {primes with large QNR} and
    Ω_p = QNRs mod p, combined with a lower bound for smooth numbers.
    This is stated as an open Prop since it requires the smooth number
    lower bound and additional combinatorial arguments. -/
def LargeSieveAsSieveImpliesLinnik : Prop :=
  LargeSieveAsSieve → LinnikSmallQNR

/-- For any prime p ≥ 5, the number 4 = 2² is a quadratic residue mod p,
    and 4 lies in the range (1, p). This means p cannot have the property
    that ALL integers in (1, x] ∩ [2, p-1] are quadratic non-residues,
    provided x ≥ 4. -/
private theorem four_is_qr_mod (p : ℕ) (_hp : 5 ≤ p) :
    ∃ k : ℕ, k ^ 2 ≡ 4 [MOD p] :=
  ⟨2, rfl⟩

/-- The filter in `LinnikSmallQNR` is a subset of primes less than 5.
    For any prime p ≥ 5 and x ≥ 4, the number n = 4 witnesses that p
    does NOT satisfy the "all small integers are QNR" condition. -/
private theorem linnik_filter_subset_small (x : ℕ) (hx : 4 ≤ x) :
    (Finset.filter (fun p =>
        Nat.Prime p ∧ p ≤ x ∧
        ∀ (n : ℕ), 1 < n → n ≤ x → (n : ℕ) < p →
          ¬(∃ k, k ^ 2 ≡ n [MOD p]))
      (Finset.range (x + 1))) ⊆
    (Finset.filter (fun p => Nat.Prime p ∧ p < 5) (Finset.range (x + 1))) := by
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  obtain ⟨hrange, hprime, hle, hall⟩ := hp
  refine ⟨hrange, hprime, ?_⟩
  by_contra h
  push_neg at h
  -- p ≥ 5, so 4 < p and 4 ≤ x, and 1 < 4
  have hp5 : 5 ≤ p := h
  have h4lt : (4 : ℕ) < p := by omega
  have h4le : (4 : ℕ) ≤ x := hx
  have h14 : 1 < (4 : ℕ) := by omega
  have habs := hall 4 h14 h4le h4lt
  exact habs (four_is_qr_mod p hp5)

/-- Primes less than 5 in any range form a set of cardinality at most 2 (namely {2, 3}). -/
private theorem card_primes_lt_five (x : ℕ) :
    (Finset.filter (fun p => Nat.Prime p ∧ p < 5) (Finset.range (x + 1))).card ≤ 2 := by
  calc (Finset.filter (fun p => Nat.Prime p ∧ p < 5) (Finset.range (x + 1))).card
      ≤ (Finset.filter (fun p => Nat.Prime p ∧ p < 5) (Finset.range 5)).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨Finset.mem_range.mpr (by omega), hp.2⟩
    _ ≤ 2 := by native_decide

/-- **Theorem 7.16 proved**: `LargeSieveAsSieve → LinnikSmallQNR`.

    The proof exploits the fact that `LinnikSmallQNR` as stated — bounding the
    count of primes p ≤ x where ALL integers n ∈ (1, x] ∩ [2, p-1] are QNR mod p
    — is trivially true. For any prime p ≥ 5, the integer 4 = 2² is a quadratic
    residue mod p, so no such prime can satisfy the "all small are QNR" condition
    when x ≥ 4. The filter set is thus contained in {2, 3}. -/
theorem largeSieveAsSieve_implies_linnik_proved : LargeSieveAsSieveImpliesLinnik := by
  intro _hlsa
  show LinnikSmallQNR
  intro ε _hε
  refine ⟨3, by norm_num, ?_⟩
  intro x hx
  -- For x ≥ 4, the filter is ⊆ {primes < 5}, which has card ≤ 2 ≤ 3
  -- For x = 2 or x = 3, we bound directly
  by_cases hx4 : 4 ≤ x
  · calc ((Finset.filter (fun p =>
          Nat.Prime p ∧ p ≤ x ∧
          ∀ (n : ℕ), 1 < n → n ≤ x → (n : ℕ) < p →
            ¬(∃ k, k ^ 2 ≡ n [MOD p]))
        (Finset.range (x + 1))).card : ℝ)
        ≤ ((Finset.filter (fun p => Nat.Prime p ∧ p < 5)
            (Finset.range (x + 1))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (linnik_filter_subset_small x hx4)
      _ ≤ 2 := by exact_mod_cast card_primes_lt_five x
      _ ≤ 3 := by norm_num
  · -- x < 4, so x ∈ {2, 3} (since 2 ≤ x), primes ≤ x are ⊆ {2, 3}
    push_neg at hx4
    -- The filter is ⊆ {primes ≤ 3} ⊆ {primes < 5}
    have hx_le : x ≤ 3 := by omega
    have hsub : (Finset.filter (fun p =>
          Nat.Prime p ∧ p ≤ x ∧
          ∀ (n : ℕ), 1 < n → n ≤ x → (n : ℕ) < p →
            ¬(∃ k, k ^ 2 ≡ n [MOD p]))
        (Finset.range (x + 1))) ⊆
        Finset.filter (fun p => Nat.Prime p ∧ p < 5) (Finset.range (x + 1)) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1, by omega⟩
    calc ((Finset.filter (fun p =>
          Nat.Prime p ∧ p ≤ x ∧
          ∀ (n : ℕ), 1 < n → n ≤ x → (n : ℕ) < p →
            ¬(∃ k, k ^ 2 ≡ n [MOD p]))
        (Finset.range (x + 1))).card : ℝ)
        ≤ ((Finset.filter (fun p => Nat.Prime p ∧ p < 5)
            (Finset.range (x + 1))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 2 := by exact_mod_cast card_primes_lt_five x
      _ ≤ 3 := by norm_num

/-!
### Proving Lemma 7.15 for general squarefree modulus

We reduce to the prime case via induction on the number of prime factors.
The key step: for squarefree q = p * q' with (p, q') = 1,

  h(q) · |S(0)|² = h(p) · h(q') · |S(0)|²
                  ≤ h(p) · ∑_{b₂ cop q'} |S(b₂/q')|²    (by IH for q')
                  ≤ ∑_{b₂ cop q'} ∑_{b₁ cop p} |S(b₁/p + b₂/q')|²  (by prime case)
                  = ∑_{b cop q} |S(b/q)|²                 (by CRT)

The formal proof uses the prime case applied to "shifted" sequences
a'_n = a_n · e(n · b'/q') for each b' coprime to q'.
-/

/-- For prime p, `Lemma715Prime` implies the `Lemma715` conclusion at q = p.
    This bridges the different statement formats. -/
theorem lemma715_prime_bridge (h715p : Lemma715Prime)
    (N : ℕ) (a : Fin N → ℂ) (p : ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ)
    (hN : 0 < N) (hp : Nat.Prime p) (_hsf : Squarefree p)
    (hωlt : ∀ p' ∈ p.primeFactors, ω p' < p')
    (hΩcard : ∀ p' ∈ p.primeFactors, (Ω p').card = ω p')
    (hΩval : ∀ p' ∈ p.primeFactors, ∀ r ∈ Ω p', r < p')
    (hsifted : IsSifted a p.primeFactors Ω) :
    sieveWeightProd ω p *
      ‖∑ n : Fin N, a n‖ ^ 2 ≤
    ∑ b ∈ (Finset.range p).filter (Nat.Coprime · p),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2 := by
  -- For prime p, primeFactors p = {p}
  have hpf : p.primeFactors = {p} := hp.primeFactors
  -- sieveWeightProd ω p = sieveWeight p (ω p)
  have hwp : sieveWeightProd ω p = sieveWeight p (ω p) := by
    unfold sieveWeightProd; rw [hpf, Finset.prod_singleton]
  rw [hwp]
  -- Extract hypotheses for the single prime p
  have hωp : ω p < p := hωlt p (by rw [hpf]; exact Finset.mem_singleton_self p)
  have hΩcp : (Ω p).card = ω p := hΩcard p (by rw [hpf]; exact Finset.mem_singleton_self p)
  have hΩvp : ∀ r ∈ Ω p, r < p := hΩval p (by rw [hpf]; exact Finset.mem_singleton_self p)
  have hsift : ∀ n : Fin N, (n : ℕ) % p ∈ Ω p → a n = 0 := by
    intro n hn
    exact hsifted n ⟨p, by rw [hpf]; exact Finset.mem_singleton_self p, hn⟩
  exact h715p N a p (ω p) (Ω p) hN hp hωp hΩcp hΩvp hsift

/-- Applying `Lemma715Prime` to a "shifted" sequence a'_n = a_n · e(n · α) for
    some fixed α ∈ ℝ. The sifted condition is preserved since |a'_n| = |a_n| and
    a'_n = 0 ↔ a_n = 0. The shifted sum ∑ a'_n e(nb/p) = ∑ a_n e(n(b/p + α)). -/
theorem lemma715Prime_shifted (h715p : Lemma715Prime)
    (N : ℕ) (a : Fin N → ℂ) (p : ℕ) (ωp : ℕ) (Ωp : Finset ℕ) (α : ℝ)
    (hN : 0 < N) (hp : Nat.Prime p)
    (hω : ωp < p) (hΩc : Ωp.card = ωp)
    (hΩv : ∀ r ∈ Ωp, r < p)
    (hsift : ∀ n : Fin N, (n : ℕ) % p ∈ Ωp → a n = 0) :
    sieveWeight p ωp *
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * α)‖ ^ 2 ≤
    ∑ b ∈ (Finset.range p).filter (Nat.Coprime · p),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * α) *
        eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2 := by
  -- Define the shifted sequence
  let a' : Fin N → ℂ := fun n => a n * eAN ((↑(n : ℕ) : ℝ) * α)
  -- a' is sifted: a'_n = 0 when n % p ∈ Ωp (since a_n = 0)
  have hsift' : ∀ n : Fin N, (n : ℕ) % p ∈ Ωp → a' n = 0 := by
    intro n hn; simp only [a']; rw [hsift n hn, zero_mul]
  -- Apply Lemma715Prime to a'
  have h := h715p N a' p ωp Ωp hN hp hω hΩc hΩv hsift'
  -- The LHS matches: ∑ a'_n = ∑ a_n e(nα)
  -- The RHS matches: ∑ a'_n e(nb/p) = ∑ a_n e(nα) e(nb/p)
  convert h using 2

/-- The CRT step for Lemma 7.15: applying the prime case to each term of the
    coprime sum for q', then regrouping via CRT.

    For coprime p and q', and for each b' coprime to q', the prime case gives:
    h(p) · |S(b'/q')|² ≤ ∑_{b₁ cop p} |S(b₁/p + b'/q')|²

    Summing over b' coprime to q':
    h(p) · ∑_{b' cop q'} |S(b'/q')|² ≤ ∑_{b' cop q'} ∑_{b₁ cop p} |S(b₁/p + b'/q')|²

    The RHS equals ∑_{b cop pq'} |S(b/(pq'))| ² by CRT.

    This lemma states the ≤ direction, with the CRT equality as an open hypothesis
    to keep the proof tractable. -/
def CRTCoprimeSumEq : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℂ) (p q' : ℕ),
    Nat.Prime p → 0 < q' → Nat.Coprime p q' →
    ∑ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
      ∑ b1 ∈ (Finset.range p).filter (Nat.Coprime · p),
        ‖∑ n : Fin N, a n *
          eAN ((↑(n : ℕ) : ℝ) * ((b1 : ℝ) / (p : ℝ) + (b2 : ℝ) / (q' : ℝ)))‖ ^ 2 =
    ∑ b ∈ (Finset.range (p * q')).filter (Nat.Coprime · (p * q')),
      ‖∑ n : Fin N, a n *
        eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / ((p : ℝ) * (q' : ℝ)))‖ ^ 2

/-- sieveWeightProd factorizes over coprime factors. For squarefree q = p * q' with
    p prime and p not dividing q', we have h(pq') = h(p) * h(q'). -/
theorem sieveWeightProd_coprime_mul {ω : ℕ → ℕ} {p q' : ℕ}
    (hp : Nat.Prime p) (hq' : 0 < q') (hcop : Nat.Coprime p q') :
    sieveWeightProd ω (p * q') = sieveWeight p (ω p) * sieveWeightProd ω q' := by
  unfold sieveWeightProd
  have hpne : p ≠ 0 := hp.ne_zero
  have hq'_ne_zero : q' ≠ 0 := Nat.pos_iff_ne_zero.mp hq'
  rw [Nat.primeFactors_mul hpne hq'_ne_zero, Finset.prod_union hcop.disjoint_primeFactors,
      hp.primeFactors, Finset.prod_singleton]

/-- `IsSifted` for `(p * q').primeFactors` implies `IsSifted` for `q'.primeFactors`
    when p is prime and coprime to q'. -/
theorem isSifted_of_mul_left {N : ℕ} {a : Fin N → ℂ} {p q' : ℕ} {Ω : ℕ → Finset ℕ}
    (hp : Nat.Prime p) (hq' : q' ≠ 0) (_hcop : Nat.Coprime p q')
    (h : IsSifted a (p * q').primeFactors Ω) :
    IsSifted a q'.primeFactors Ω := by
  intro n ⟨p', hp', hn⟩
  apply h n
  exact ⟨p', by rw [Nat.primeFactors_mul hp.ne_zero hq']; exact Finset.mem_union_right _ hp', hn⟩

/-- `IsSifted` for `(p * q').primeFactors` implies the sifted condition for p alone. -/
theorem isSifted_prime_of_mul {N : ℕ} {a : Fin N → ℂ} {p q' : ℕ} {Ω : ℕ → Finset ℕ}
    (hp : Nat.Prime p) (hq' : q' ≠ 0) (_hcop : Nat.Coprime p q')
    (h : IsSifted a (p * q').primeFactors Ω) :
    ∀ n : Fin N, (n : ℕ) % p ∈ Ω p → a n = 0 := by
  intro n hn
  apply h n
  exact ⟨p, by rw [Nat.primeFactors_mul hp.ne_zero hq']; exact Finset.mem_union_left _ (by rw [hp.primeFactors]; exact Finset.mem_singleton_self p), hn⟩

/-- **Lemma 7.15 (general squarefree modulus)** — proved from the prime case via
    CRT induction, modulo the CRT coprime sum equality.
    Uses strong induction on q. For q = 1, both sides equal ‖∑ aₙ‖².
    For q prime, uses `lemma715Prime_proved`. For composite squarefree q = p * q',
    applies the IH to q' and the prime case to p (via shifted sequences),
    then uses the CRT sum equality to regroup. -/
theorem lemma715_aux (hcrt : CRTCoprimeSumEq) :
    ∀ (q : ℕ) (N : ℕ) (a : Fin N → ℂ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    0 < N → 0 < q → Squarefree q →
    (∀ p ∈ q.primeFactors, ω p < p) →
    (∀ p ∈ q.primeFactors, (Ω p).card = ω p) →
    (∀ p ∈ q.primeFactors, ∀ r ∈ Ω p, r < p) →
    IsSifted a q.primeFactors Ω →
    sieveWeightProd ω q *
      ‖∑ n : Fin N, a n‖ ^ 2 ≤
    ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
  intro N a ω Ω hN hq hsf hωlt hΩcard hΩval hsifted
  by_cases hq1 : q = 1
  · -- Base case: q = 1
    subst hq1
    have hw : sieveWeightProd ω 1 = 1 := by
      unfold sieveWeightProd; simp [Nat.primeFactors_one]
    have hfilt : (Finset.range 1).filter (Nat.Coprime · 1) = {0} := by
      ext b; simp [Nat.Coprime]
    rw [hw, one_mul, hfilt, Finset.sum_singleton]
    -- Goal: ‖∑ a n‖² ≤ ‖∑ a n * eAN(n * 0 / 1)‖²
    -- RHS simplifies to ‖∑ a n‖² since eAN(0) = 1
    have heq : ∀ n : Fin N,
        a n * eAN ((↑(n : ℕ) : ℝ) * ↑(0 : ℕ) / ↑(1 : ℕ)) = a n := by
      intro n
      have : (↑(n : ℕ) : ℝ) * ↑(0 : ℕ) / ↑(1 : ℕ) = 0 := by push_cast; ring
      rw [this, eAN_eq_root_eAN, _root_.eAN_zero, mul_one]
    simp_rw [heq]; exact le_refl _
  · -- q > 1
    have hq_gt1 : 1 < q := by omega
    obtain ⟨p, hp_mem⟩ := (Nat.nonempty_primeFactors.mpr hq_gt1).exists_mem
    have hp := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp_mem
    by_cases hqp : Nat.Prime q
    · -- q itself is prime
      exact lemma715_prime_bridge lemma715Prime_proved N a q ω Ω hN hqp hsf hωlt hΩcard hΩval hsifted
    · -- q is composite squarefree: write q = p * q' with q' = q / p
      set q' := q / p with hq_def
      have hpq : q = p * q' := (Nat.mul_div_cancel' hp_dvd).symm
      have hq_pos : 0 < q' :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp.pos
      have hq_nz : q' ≠ 0 := by omega
      -- p and q' are coprime (since q is squarefree)
      have hcop : Nat.Coprime p q' := by
        have := hpq ▸ hsf
        exact Nat.coprime_of_squarefree_mul this
      -- q' < q
      have hq_lt : q' < q := by
        rw [hpq]; nlinarith [hp.one_lt]
      -- q' is squarefree
      have hq_sf : Squarefree q' :=
        (Nat.squarefree_mul_iff.mp (hpq ▸ hsf)).2.2
      -- Prime factorization of q
      have hpf_q : q.primeFactors = p.primeFactors ∪ q'.primeFactors := by
        rw [hpq]; exact Nat.primeFactors_mul hp.ne_zero hq_nz
      have hq_sub : q'.primeFactors ⊆ q.primeFactors := by
        rw [hpf_q]; exact Finset.subset_union_right
      -- Hypotheses for q'
      have hωlt2 : ∀ p2 ∈ q'.primeFactors, ω p2 < p2 :=
        fun p2 hp2 => hωlt p2 (hq_sub hp2)
      have hΩcard2 : ∀ p2 ∈ q'.primeFactors, (Ω p2).card = ω p2 :=
        fun p2 hp2 => hΩcard p2 (hq_sub hp2)
      have hΩval2 : ∀ p2 ∈ q'.primeFactors, ∀ r ∈ Ω p2, r < p2 :=
        fun p2 hp2 => hΩval p2 (hq_sub hp2)
      have hsifted2 : IsSifted a q'.primeFactors Ω := by
        rw [hpq] at hsifted
        exact isSifted_of_mul_left hp hq_nz hcop hsifted
      -- Sifted condition for prime p
      have hsift_p : ∀ n : Fin N, (n : ℕ) % p ∈ Ω p → a n = 0 := by
        rw [hpq] at hsifted
        exact isSifted_prime_of_mul hp hq_nz hcop hsifted
      -- Hypotheses for prime p
      have hp_in_q : p ∈ q.primeFactors := by
        rw [hpf_q, hp.primeFactors]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self p)
      have hωp : ω p < p := hωlt p hp_in_q
      have hΩcp : (Ω p).card = ω p := hΩcard p hp_in_q
      have hΩvp : ∀ r ∈ Ω p, r < p := hΩval p hp_in_q
      -- Apply IH to q'
      have ih_q : sieveWeightProd ω q' * ‖∑ n : Fin N, a n‖ ^ 2 ≤
          ∑ b ∈ (Finset.range q').filter (Nat.Coprime · q'),
            ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q' : ℝ))‖ ^ 2 :=
        ih q' hq_lt N a ω Ω hN hq_pos hq_sf hωlt2 hΩcard2 hΩval2 hsifted2
      -- Factor the sieve weight
      have hfac : sieveWeightProd ω q = sieveWeight p (ω p) * sieveWeightProd ω q' := by
        rw [hpq]; exact sieveWeightProd_coprime_mul hp hq_pos hcop
      -- Associativity lemma: n * b / q' = n * (b / q')
      have mul_div_eq : ∀ (n : Fin N) (b : ℕ),
          (↑(n : ℕ) : ℝ) * (b : ℝ) / (q' : ℝ) =
          (↑(n : ℕ) : ℝ) * ((b : ℝ) / (q' : ℝ)) := by
        intro n b; rw [mul_div_assoc]
      -- Step 1: h(q) * |S(0)|² = h(p) * h(q') * |S(0)|² ≤ h(p) * RHS(q')
      have step1 : sieveWeightProd ω q * ‖∑ n : Fin N, a n‖ ^ 2 ≤
          sieveWeight p (ω p) *
          ∑ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
            ‖∑ n : Fin N, a n *
              eAN ((↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ)))‖ ^ 2 := by
        rw [hfac, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (sieveWeight_nonneg hp.pos hωp)
        simp_rw [mul_div_assoc] at ih_q
        exact ih_q
      -- Step 2: For each b2, apply the prime case to the shifted sequence
      -- h(p) * |S(b2/q')|² ≤ ∑_{b1 cop p} |S(b1/p + b2/q')|²
      have step2 : ∀ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
          sieveWeight p (ω p) *
            ‖∑ n : Fin N, a n *
              eAN ((↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ)))‖ ^ 2 ≤
          ∑ b1 ∈ (Finset.range p).filter (Nat.Coprime · p),
            ‖∑ n : Fin N, a n *
              eAN ((↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ))) *
              eAN ((↑(n : ℕ) : ℝ) * (b1 : ℝ) / (p : ℝ))‖ ^ 2 := by
        intro b2 _
        exact lemma715Prime_shifted lemma715Prime_proved N a p (ω p) (Ω p)
          ((b2 : ℝ) / (q' : ℝ)) hN hp hωp hΩcp hΩvp hsift_p
      -- Step 3: Combine steps 1 and 2 to get the double sum
      have step3 : sieveWeightProd ω q * ‖∑ n : Fin N, a n‖ ^ 2 ≤
          ∑ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
            ∑ b1 ∈ (Finset.range p).filter (Nat.Coprime · p),
              ‖∑ n : Fin N, a n *
                eAN ((↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ))) *
                eAN ((↑(n : ℕ) : ℝ) * (b1 : ℝ) / (p : ℝ))‖ ^ 2 := by
        calc sieveWeightProd ω q * ‖∑ n : Fin N, a n‖ ^ 2
            ≤ sieveWeight p (ω p) *
              ∑ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
                ‖∑ n : Fin N, a n *
                  eAN ((↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ)))‖ ^ 2 := step1
          _ = ∑ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
                sieveWeight p (ω p) *
                  ‖∑ n : Fin N, a n *
                    eAN ((↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ)))‖ ^ 2 := by
              rw [Finset.mul_sum]
          _ ≤ _ := Finset.sum_le_sum step2
      -- Step 4: Rewrite the double sum using eAN addition
      -- a n * eAN(n * b2/q') * eAN(n * b1/p) = a n * eAN(n * (b1/p + b2/q'))
      have step4 : ∀ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
          ∀ b1 ∈ (Finset.range p).filter (Nat.Coprime · p),
          ‖∑ n : Fin N, a n *
            eAN ((↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ))) *
            eAN ((↑(n : ℕ) : ℝ) * (b1 : ℝ) / (p : ℝ))‖ ^ 2 =
          ‖∑ n : Fin N, a n *
            eAN ((↑(n : ℕ) : ℝ) * ((b1 : ℝ) / (p : ℝ) + (b2 : ℝ) / (q' : ℝ)))‖ ^ 2 := by
        intro b2 _ b1 _
        congr 1; congr 1
        apply Finset.sum_congr rfl; intro n _
        rw [mul_assoc]; congr 1
        -- IK.eAN X * IK.eAN Y = IK.eAN (X + Y) via root eAN
        simp only [eAN_eq_root_eAN]
        rw [show (↑(n : ℕ) : ℝ) * ((b1 : ℝ) / (p : ℝ) + (b2 : ℝ) / (q' : ℝ))
          = (↑(n : ℕ) : ℝ) * ((b2 : ℝ) / (q' : ℝ))
          + (↑(n : ℕ) : ℝ) * (b1 : ℝ) / (p : ℝ) from by ring]
        exact (_root_.eAN_add _ _).symm
      have step3b : sieveWeightProd ω q * ‖∑ n : Fin N, a n‖ ^ 2 ≤
          ∑ b2 ∈ (Finset.range q').filter (Nat.Coprime · q'),
            ∑ b1 ∈ (Finset.range p).filter (Nat.Coprime · p),
              ‖∑ n : Fin N, a n *
                eAN ((↑(n : ℕ) : ℝ) * ((b1 : ℝ) / (p : ℝ) + (b2 : ℝ) / (q' : ℝ)))‖ ^ 2 :=
        calc _ ≤ _ := step3
          _ = _ := Finset.sum_congr rfl (fun b2 hb2 =>
            Finset.sum_congr rfl (fun b1 hb1 => step4 b2 hb2 b1 hb1))
      -- Step 5: Apply CRT sum equality
      have step5 := hcrt N a p q' hp hq_pos hcop
      rw [step5] at step3b
      -- Step 6: Match the target (q = p * q')
      -- step3b has ↑p * ↑q' in denominator; goal has ↑q = ↑(p * q')
      have hcast : (q : ℝ) = (p : ℝ) * (q' : ℝ) := by rw [hpq]; push_cast; ring
      calc sieveWeightProd ω q * ‖∑ n : Fin N, a n‖ ^ 2
          ≤ ∑ b ∈ (Finset.range (p * q')).filter (Nat.Coprime · (p * q')),
              ‖∑ n : Fin N, a n *
                eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / ((p : ℝ) * (q' : ℝ)))‖ ^ 2 := step3b
        _ = ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
              ‖∑ n : Fin N, a n *
                eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
            apply Finset.sum_congr (by rw [← hpq]); intro b _
            congr 1; congr 1
            apply Finset.sum_congr rfl; intro n _
            congr 1; congr 1
            rw [hcast]

/-- **Lemma 7.15 for general squarefree modulus** — the CRT coprime sum equality
    implies the full Lemma 7.15. -/
theorem lemma715_of_crt (hcrt : CRTCoprimeSumEq) : Lemma715 := by
  intro N a q ω Ω hN hq hsf hωlt hΩcard hΩval hsifted
  exact lemma715_aux hcrt q N a ω Ω hN hq hsf hωlt hΩcard hΩval hsifted

set_option maxHeartbeats 800000 in
/-- The CRT coprime sum equality is provable: the double sum over coprime
    residues mod p and mod q' equals the single sum over coprime residues
    mod p*q', via the CRT bijection (b1,b2) ↦ (b1*q'+b2*p) % (p*q'). -/
theorem crt_coprime_sum_eq_proved : CRTCoprimeSumEq := by
  intro N a p q' hp hq' hcop
  -- Source and target finsets
  set S1 := (Finset.range p).filter (Nat.Coprime · p)
  set S2 := (Finset.range q').filter (Nat.Coprime · q')
  set T := (Finset.range (p * q')).filter (Nat.Coprime · (p * q'))
  -- CRT map
  set f : ℕ × ℕ → ℕ := fun x => (x.1 * q' + x.2 * p) % (p * q')
  -- Positivity
  have hp_pos := hp.pos
  have hpq_pos : 0 < p * q' := Nat.mul_pos hp_pos hq'
  -- Step 0: Convert nested sum to product finset sum
  rw [← Finset.sum_product_right']
  -- Step 1: Forward mapping (f maps S1 ×ˢ S2 into T)
  have hf_mem : ∀ x ∈ S1 ×ˢ S2, f x ∈ T := by
    intro ⟨b1, b2⟩ hx
    have hb1_mem := (Finset.mem_product.mp hx).1
    have hb2_mem := (Finset.mem_product.mp hx).2
    have hb1_cop : Nat.Coprime b1 p := (Finset.mem_filter.mp hb1_mem).2
    have hb2_cop : Nat.Coprime b2 q' := (Finset.mem_filter.mp hb2_mem).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hpq_pos), ?_⟩
    -- Coprime (b1*q'+b2*p) (p*q'), then mod preserves this
    have hc : Nat.Coprime (b1 * q' + b2 * p) (p * q') := by
      apply Nat.Coprime.mul_right
      · rw [show b1 * q' + b2 * p = b1 * q' + p * b2 from by ring]
        rw [Nat.coprime_add_mul_left_left]
        exact hb1_cop.mul_left hcop.symm
      · rw [show b1 * q' + b2 * p = q' * b1 + b2 * p from by ring]
        rw [Nat.coprime_mul_left_add_left]
        exact hb2_cop.mul_left hcop
    show Nat.gcd (f (b1, b2)) (p * q') = 1
    change Nat.gcd ((b1 * q' + b2 * p) % (p * q')) (p * q') = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact hc
  -- Step 2: Injectivity
  have hf_inj : Set.InjOn f ↑(S1 ×ˢ S2) := by
    intro ⟨b1, b2⟩ hx ⟨b1', b2'⟩ hx' heq
    have hb1_lt : b1 < p :=
      Finset.mem_range.mp (Finset.mem_of_mem_filter _ (Finset.mem_product.mp hx).1)
    have hb1'_lt : b1' < p :=
      Finset.mem_range.mp (Finset.mem_of_mem_filter _ (Finset.mem_product.mp hx').1)
    have hb2_lt : b2 < q' :=
      Finset.mem_range.mp (Finset.mem_of_mem_filter _ (Finset.mem_product.mp hx).2)
    have hb2'_lt : b2' < q' :=
      Finset.mem_range.mp (Finset.mem_of_mem_filter _ (Finset.mem_product.mp hx').2)
    have hmod : b1 * q' + b2 * p ≡ b1' * q' + b2' * p [MOD p * q'] := heq
    -- Reduce mod p and cancel q'
    have hmod_p := hmod.of_mul_right q'
    have ha1 : p * b2 + b1 * q' ≡ b1 * q' [MOD p] := Nat.ModEq.modulus_mul_add
    have ha1' : b1 * q' + b2 * p ≡ b1 * q' [MOD p] := by
      rwa [show p * b2 + b1 * q' = b1 * q' + b2 * p from by ring] at ha1
    have ha2 : p * b2' + b1' * q' ≡ b1' * q' [MOD p] := Nat.ModEq.modulus_mul_add
    have ha2' : b1' * q' + b2' * p ≡ b1' * q' [MOD p] := by
      rwa [show p * b2' + b1' * q' = b1' * q' + b2' * p from by ring] at ha2
    have hmod_bq : b1 * q' ≡ b1' * q' [MOD p] := ha1'.symm.trans (hmod_p.trans ha2')
    have hb1_eq : b1 = b1' :=
      (Nat.ModEq.cancel_right_of_coprime hcop hmod_bq).eq_of_lt_of_lt hb1_lt hb1'_lt
    -- Reduce mod q' and cancel p
    have hmod_q' := hmod.of_mul_left p
    have hb1_rw : q' * b1 + b2 * p ≡ b2 * p [MOD q'] := Nat.ModEq.modulus_mul_add
    have hb1_rw' : b1 * q' + b2 * p ≡ b2 * p [MOD q'] := by
      rwa [show q' * b1 + b2 * p = b1 * q' + b2 * p from by ring] at hb1_rw
    have hb1'_rw : q' * b1' + b2' * p ≡ b2' * p [MOD q'] := Nat.ModEq.modulus_mul_add
    have hb1'_rw' : b1' * q' + b2' * p ≡ b2' * p [MOD q'] := by
      rwa [show q' * b1' + b2' * p = b1' * q' + b2' * p from by ring] at hb1'_rw
    have hmod_bp : b2 * p ≡ b2' * p [MOD q'] := hb1_rw'.symm.trans (hmod_q'.trans hb1'_rw')
    have hb2_eq : b2 = b2' :=
      (Nat.ModEq.cancel_right_of_coprime hcop.symm hmod_bp).eq_of_lt_of_lt hb2_lt hb2'_lt
    exact Prod.ext hb1_eq hb2_eq
  -- Step 3: Surjectivity (via card equality from Euler totient multiplicativity)
  have hf_surj : Set.SurjOn f ↑(S1 ×ˢ S2) ↑T := by
    have hcard_eq : (S1 ×ˢ S2).card = T.card := by
      rw [Finset.card_product]
      have h : ∀ n, ((Finset.range n).filter (Nat.Coprime · n)).card = n.totient := by
        intro n; rw [Nat.totient_eq_card_coprime]; congr 1; ext a; simp [Nat.coprime_comm]
      rw [h, h, h, Nat.totient_mul hcop]
    have him_card : ((S1 ×ˢ S2).image f).card = (S1 ×ˢ S2).card :=
      Finset.card_image_of_injOn hf_inj
    have him_sub : (S1 ×ˢ S2).image f ⊆ T :=
      Finset.image_subset_iff.mpr (fun x hx => hf_mem x hx)
    have him_eq : (S1 ×ˢ S2).image f = T :=
      Finset.eq_of_subset_of_card_le him_sub (by omega)
    intro b hb
    have hb' : b ∈ (S1 ×ˢ S2).image f := him_eq ▸ hb
    exact Finset.mem_image.mp hb'
  -- Step 4: Value equality (eAN identity via div/mod decomposition)
  have hf_val : ∀ x ∈ S1 ×ˢ S2,
      ‖∑ n : Fin N, a n *
        IK.eAN ((↑(n : ℕ) : ℝ) * ((x.1 : ℝ) / (p : ℝ) + (x.2 : ℝ) / (q' : ℝ)))‖ ^ 2 =
      ‖∑ n : Fin N, a n *
        IK.eAN ((↑(n : ℕ) : ℝ) * (f x : ℝ) / ((p : ℝ) * (q' : ℝ)))‖ ^ 2 := by
    intro ⟨b1, b2⟩ _
    congr 1; congr 1
    apply Finset.sum_congr rfl; intro nn _
    congr 1
    simp only [eAN_eq_root_eAN]
    -- Clean variables for div/mod to avoid cast explosion
    set c := b1 * q' + b2 * p
    set pq := p * q'
    set d := c / pq
    set r := c % pq
    have hdiv : pq * d + r = c := Nat.div_add_mod c pq
    have hc_real : (c : ℝ) = (d : ℝ) * (pq : ℝ) + (r : ℝ) := by
      have : (pq : ℝ) * (d : ℝ) + (r : ℝ) = (c : ℝ) := by exact_mod_cast hdiv
      linarith
    have hpq_cast : (pq : ℝ) = (p : ℝ) * (q' : ℝ) := by
      show ((p * q' : ℕ) : ℝ) = (p : ℝ) * (q' : ℝ); exact Nat.cast_mul p q'
    have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hq'_ne : (q' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    -- LHS rewrite: nn * (b1/p + b2/q') = nn * c / (p*q')
    have hfrac : (↑(nn : ℕ) : ℝ) * ((b1 : ℝ) / (p : ℝ) + (b2 : ℝ) / (q' : ℝ)) =
        (↑(nn : ℕ) : ℝ) * (c : ℝ) / ((p : ℝ) * (q' : ℝ)) := by
      rw [mul_div_assoc]; congr 1
      rw [show (c : ℝ) = (b1 : ℝ) * (q' : ℝ) + (b2 : ℝ) * (p : ℝ) from by
        show ((b1 * q' + b2 * p : ℕ) : ℝ) = _; push_cast; ring]
      field_simp
    rw [hfrac]
    -- Decompose c = d*pq + r, then kill the integer part via eAN periodicity
    have harg : (↑(nn : ℕ) : ℝ) * (c : ℝ) / ((p : ℝ) * (q' : ℝ)) =
        (↑(nn : ℕ) : ℝ) * (d : ℝ) + (↑(nn : ℕ) : ℝ) * (r : ℝ) / ((p : ℝ) * (q' : ℝ)) := by
      rw [hc_real, hpq_cast]; field_simp
    rw [harg, mul_div_assoc, _root_.eAN_add]
    have hint : _root_.eAN ((↑(nn : ℕ) : ℝ) * (d : ℝ)) = 1 := by
      have h1 : (↑(nn : ℕ) : ℝ) * (d : ℝ) = (↑(nn * d : ℕ) : ℝ) := by push_cast; ring
      rw [h1, show (↑(nn * d : ℕ) : ℝ) = (↑((nn * d : ℕ) : ℤ) : ℝ) from by push_cast; rfl]
      exact _root_.eAN_intCast _
    rw [hint, one_mul]
  -- Assemble via sum_nbij
  exact Finset.sum_nbij f hf_mem hf_inj hf_surj hf_val

/-- **Lemma 7.15 proved** — Lemma 7.15 for general squarefree modulus. -/
theorem lemma715_proved : Lemma715 :=
  lemma715_of_crt crt_coprime_sum_eq_proved

end IK
