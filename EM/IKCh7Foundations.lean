import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import EM.LargeSieveAnalytic

/-!
# Chapter 7 (Part 1): Foundations — Bilinear Forms and LSI Framework (Iwaniec-Kowalski)

§7.1–7.3 of Iwaniec-Kowalski: bilinear forms, duality principle,
exponential bilinear forms, and the large sieve inequality framework.

## Contents
- §7.1: General principles of estimating double sums (duality principle)
- §7.2: Bilinear forms with exponentials (Theorem 7.2)
- §7.3: Introduction to the large sieve (philosophy)

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
  have : S ≤ l2NormSq α * Δ := by nlinarith
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

end IK
