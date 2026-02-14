import EM.IK.Ch7AdditiveLS

/-!
# Chapter 7 (Part 5): Hilbert Inequality and Product-Index Trick (Iwaniec-Kowalski)

§7.4f and §7.9–7.10 of Iwaniec-Kowalski: Hilbert inequality rescaling,
Csc bilinear bound, Mittag-Leffler expansion, product-index trick for the
bridge from HilbertInequality to CscBilinearBound and optimal ALS.

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Complex Finset BigOperators

/-!
### §7.4f Hilbert inequality: rescaling reduction

The **generalized Hilbert inequality** (`HilbertInequality`) asserts a bound
for δ-separated points. The **δ=1 case** (`HilbertInequality1`) is the core:
1-separated real points satisfy `‖∑∑_{r≠s} z_r z̄_s / (λ_r - λ_s)‖ ≤ π ∑ |z|²`.

By a simple rescaling `λ_r ↦ λ_r/δ`, the general case follows from the δ=1 case
with a factor of `1/δ`. This is `hilbert_rescale` below.

The core δ=1 statement itself requires Fourier analysis (Schur 1911, or
Montgomery-Vaughan's approach via the Fourier transform of 1/x); we capture
it as the open proposition `HilbertInequality1`.
-/

/-- **Hilbert inequality for 1-separated points**: the core δ=1 case.
    For 1-separated real points λ_r,
    `‖∑∑_{r≠s} z_r z̄_s / (λ_r − λ_s)‖ ≤ π · ∑ |z_r|²`.

    This is the analytic core requiring Fourier analysis. The general
    δ-separated case follows by rescaling (`hilbert_rescale`). -/
def HilbertInequality1 : Prop :=
  ∀ (R : ℕ) (pts : Fin R → ℝ) (z : Fin R → ℂ),
    (∀ r s : Fin R, r ≠ s → 1 ≤ |pts r - pts s|) →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      z r * starRingEnd ℂ (z s) / (↑(pts r - pts s) : ℂ)‖ ≤
      Real.pi * ∑ r, ‖z r‖ ^ 2

/-- **Schur's bound for integer points** (1911): The Hilbert bilinear form
    on distinct integer points is bounded by π. This is the minimal analytic
    input requiring Fourier analysis of the kernel 1/n on ℤ.

    More precisely: for any map `z : Fin R → ℂ` and integer points
    `pts : Fin R → ℤ` (implicitly cast to ℂ via ℝ), the off-diagonal
    bilinear form is bounded by `π · ∑|z_r|²`. -/
def HilbertIntegerBound : Prop :=
  ∀ (R : ℕ) (pts : Fin R → ℤ) (z : Fin R → ℂ),
    (∀ r s : Fin R, r ≠ s → pts r ≠ pts s) →
    ‖∑ r : Fin R, ∑ s ∈ Finset.univ.filter (· ≠ r),
      z r * starRingEnd ℂ (z s) / ((↑(pts r : ℤ) : ℂ) - (↑(pts s : ℤ) : ℂ))‖ ≤
      Real.pi * ∑ r, ‖z r‖ ^ 2

/-- Helper: the Hilbert bilinear form term identity under rescaling.
    If `pts' r = pts r / δ`, then `1/(pts r - pts s) = (1/δ) · 1/(pts' r - pts' s)`. -/
private theorem hilbert_term_rescale {δ : ℝ} (hδ : 0 < δ)
    (pts : Fin R → ℝ) (r s : Fin R) (_hrs : r ≠ s)
    (hsep : δ ≤ |pts r - pts s|) :
    (↑(pts r - pts s) : ℂ) ≠ 0 ∧
    ((↑(pts r - pts s) : ℂ))⁻¹ =
      (↑δ : ℂ)⁻¹ * ((↑(pts r / δ - pts s / δ) : ℂ))⁻¹ := by
  have hne : pts r - pts s ≠ 0 := by
    intro h; simp [h] at hsep; linarith
  have hδne : δ ≠ 0 := ne_of_gt hδ
  constructor
  · exact Complex.ofReal_ne_zero.mpr hne
  · have hδ' : (↑δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδne
    have hscale : pts r - pts s = δ * (pts r / δ - pts s / δ) := by
      field_simp
    rw [show (↑(pts r - pts s) : ℂ) = (↑δ : ℂ) * (↑(pts r / δ - pts s / δ) : ℂ) by
      push_cast [hscale]; ring]
    rw [mul_inv_rev, mul_comm]

/-- **Rescaling reduction**: the δ=1 case implies the general Hilbert inequality.

    Given δ-separated points, rescale by `pts' r = pts r / δ`. Then the
    points are 1-separated and the bilinear form scales by `1/δ`:
    `∑∑ z_r z̄_s/(λ_r - λ_s) = (1/δ) · ∑∑ z_r z̄_s/(λ'_r - λ'_s)`.
    Applying the δ=1 bound and distributing `1/δ` gives `(π/δ) · ∑|z|²`. -/
theorem hilbert_rescale (h1 : HilbertInequality1) : HilbertInequality := by
  intro R pts z δ hδ hsep
  -- Define rescaled points
  set pts' : Fin R → ℝ := fun r => pts r / δ with hpts'_def
  -- The rescaled points are 1-separated
  have hsep' : ∀ r s : Fin R, r ≠ s → 1 ≤ |pts' r - pts' s| := by
    intro r s hrs
    simp only [hpts'_def]
    rw [show pts r / δ - pts s / δ = (pts r - pts s) / δ from by ring,
      abs_div, abs_of_pos hδ, le_div_iff₀ hδ, one_mul]
    exact hsep r s hrs
  -- Apply the δ=1 case to get bound on rescaled sum
  have hbound := h1 R pts' z hsep'
  -- Now relate the original sum to the rescaled sum
  -- Key: each term satisfies z r * conj(z s) / (pts r - pts s)
  --     = (1/δ) * z r * conj(z s) / (pts' r - pts' s)
  have hδne : δ ≠ 0 := ne_of_gt hδ
  -- Rewrite each term
  have hsum_eq : ∀ r : Fin R,
      ∑ s ∈ Finset.univ.filter (· ≠ r),
        z r * starRingEnd ℂ (z s) / (↑(pts r - pts s) : ℂ) =
      (↑δ : ℂ)⁻¹ * ∑ s ∈ Finset.univ.filter (· ≠ r),
        z r * starRingEnd ℂ (z s) / (↑(pts' r - pts' s) : ℂ) := by
    intro r
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hrs : r ≠ s := Ne.symm hs
    have ⟨_, hinv⟩ := hilbert_term_rescale hδ pts r s hrs (hsep r s hrs)
    rw [div_eq_mul_inv, div_eq_mul_inv, hinv]
    ring
  -- Combine: the full sum = (1/δ) * rescaled sum
  have hfull_eq :
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        z r * starRingEnd ℂ (z s) / (↑(pts r - pts s) : ℂ) =
      (↑δ : ℂ)⁻¹ * ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        z r * starRingEnd ℂ (z s) / (↑(pts' r - pts' s) : ℂ) := by
    simp_rw [hsum_eq, ← Finset.mul_sum]
  -- Take norms
  rw [hfull_eq, norm_mul]
  have hnorm_inv : ‖(↑δ : ℂ)⁻¹‖ = δ⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  rw [hnorm_inv]
  -- ‖original‖ = (1/δ) * ‖rescaled‖ ≤ (1/δ) * π * ∑|z|²
  calc δ⁻¹ * ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          z r * starRingEnd ℂ (z s) / (↑(pts' r - pts' s) : ℂ)‖
      ≤ δ⁻¹ * (Real.pi * ∑ r, ‖z r‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (le_of_lt hδ))
    _ = Real.pi / δ * ∑ r, ‖z r‖ ^ 2 := by ring

/-- **Hilbert inequality from δ=1 case**: `HilbertInequality1 → HilbertInequality`. -/
theorem hilbert1_implies_hilbert : HilbertInequality1 → HilbertInequality :=
  hilbert_rescale

/-- **Hilbert → ALS chain**: the Hilbert inequality, combined with the
    Gram off-diagonal bilinear bound (which follows from the Hilbert inequality
    via geometric sum / Dirichlet kernel identities + the Cohen trick),
    yields the optimal additive large sieve.

    Chain: HilbertInequality → GramOffDiagBilinearBound → AdditiveLargeSieve.

    Note: the step HilbertInequality → GramOffDiagBilinearBound is itself an
    open proposition (`HilbertCscBilinearBridge`) requiring the geometric-sum-to-sin
    identity and Cohen's limiting argument. The assembly here takes both as input. -/
theorem hilbert_chain_als
    (_hhilbert : HilbertInequality)
    (hoff : GramOffDiagBilinearBound) : AdditiveLargeSieve :=
  gram_offdiag_bilinear_implies_als hoff

/-!
### §7.9–7.10 Csc bilinear bound → off-diagonal Gram bilinear bound

The chain from the `1/sin(πθ)` bilinear bound to the optimal off-diagonal Gram bound
proceeds via the **Dirichlet kernel half-phase splitting**:

For `θ = α_r − α_s`, the Gram entry satisfies the algebraic identity
`G_{r,s} · (eAN(θ/2) − eAN(−θ/2)) = eAN((2N−1)θ/2) − eAN(−θ/2)`

(derived from the telescoping `G · (eAN(θ) − 1) = eAN(Nθ) − 1` and
`eAN(θ) − 1 = eAN(θ/2) · (eAN(θ/2) − eAN(−θ/2))`).

Since `eAN(θ/2) − eAN(−θ/2) = 2i·sin(πθ)`, dividing gives:
`G_{r,s} = [eAN((2N−1)θ/2) − eAN(−θ/2)] / (2i·sin(πθ))`

Inserting into the bilinear form and defining phase-shifted coefficients
`d_r = b_r · eAN((2N−1)α_r/2)` and `d'_r = b_r · eAN(−α_r/2)`:

`∑_{r≠s} b_r · conj(b_s) · G_{r,s}
  = (2i)⁻¹ · [∑_{r≠s} d_r·conj(d_s)/sin(πθ) − ∑_{r≠s} d'_r·conj(d'_s)/sin(πθ)]`

Triangle inequality and CscBilinearBound on each term, plus `l2NormSq d = l2NormSq b`,
gives the optimal `(1/δ − 1) · l2NormSq b`.
-/

/-- **Csc bilinear bound** (IK Corollary 7.10 + Cohen trick): For δ-spaced
    points α_r ∈ ℝ/ℤ, the bilinear form with `1/sin(π·(α_r − α_s))` kernel
    satisfies:

    `‖∑_{r≠s} c_r · conj(c_s) / sin(π · (α_r − α_s))‖ ≤ (1/δ − 1) · ∑ ‖c_r‖²`

    This combines the Hilbert inequality (applied via Mittag-Leffler / product-index
    trick to convert the `1/(λ_r − λ_s)` kernel into `1/sin`) with the Cohen limiting
    argument that sharpens `1/δ` to `1/δ − 1`.

    The `sin` in the denominator is `Real.sin(π · (α_r − α_s))` — note this uses
    the actual real difference, not the fract difference. -/
def CscBilinearBound : Prop :=
  ∀ (R : ℕ) (α : Fin R → ℝ) (c : Fin R → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 →
    IsSpaced α δ →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      c r * starRingEnd ℂ (c s) /
      (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖ ≤
      (1/δ - 1) * l2NormSq c

/-- **Hilbert → Csc bilinear bridge** (IK Corollaries 7.9–7.10):
    The Hilbert inequality implies the csc bilinear bound via the
    Mittag-Leffler expansion of `π · csc(π · z)` and the Cohen limiting trick.

    The proof uses:
    1. The Mittag-Leffler series `π·csc(πz) = ∑_{n∈ℤ} (−1)ⁿ/(z−n)`.
    2. The product-index trick: lift R points on ℝ/ℤ to R·(2K+1) points on ℝ.
    3. Apply HilbertInequality to the lifted points.
    4. Take K → ∞ and use Mittag-Leffler convergence.
    5. The Cohen trick sharpens `1/δ` to `1/δ − 1`. -/
def HilbertCscBilinearBridge : Prop :=
  HilbertInequality → CscBilinearBound

/-!
### §7.9–7.10 Infrastructure: Product-index trick for HilbertCscBilinearBridge

The bridge from HilbertInequality to CscBilinearBound uses the **product-index trick**
(IK Corollaries 7.9–7.10):

1. Lift R δ-spaced points on ℝ/ℤ to R·(2K+1) δ-separated points on ℝ
2. Apply HilbertInequality to the lifted system
3. The cross terms (r ≠ s) give a Cesaro partial sum of `π/sin(πθ)`
4. The self terms (r = s, k ≠ l) cancel by antisymmetry
5. Divide by (2K+1) and take K → ∞

**Note on spacing conditions**: The product-index trick requires the ℝ/ℤ
**circular distance** `|α_r − α_s − round(α_r − α_s)| ≥ δ`, which is
stronger than the `IsSpaced` condition `|fract(α_r) − fract(α_s)| ≥ δ`.
The circular distance condition guarantees all lifted point pairs are
δ-separated on ℝ. In all applications (unit points for prime p ≥ 3,
Farey fractions), the circular distance condition is satisfied.

We define `IsCircularSpaced` for the stronger condition, prove the bridge
under it, and show the key applications satisfy it.
-/

/-- **Circular spacing**: points α_r ∈ ℝ/ℤ are **circularly δ-spaced** if
    their ℝ/ℤ distance (distance to nearest integer of α_r − α_s) is ≥ δ
    for all r ≠ s. This is the standard IK definition (stronger than `IsSpaced`). -/
def IsCircularSpaced {R : ℕ} (α : Fin R → ℝ) (δ : ℝ) : Prop :=
  ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|

/-- `IsCircularSpaced` implies `IsSpaced`: circular distance ≥ δ implies
    |fract diff| ≥ δ, since circular distance ≤ |fract diff| and when
    |fract diff| > 1/2 we use δ ≤ 1/2 < |fract diff|. -/
theorem isCircularSpaced_implies_isSpaced {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ2 : δ ≤ 1/2)
    (hcirc : IsCircularSpaced α δ) : IsSpaced α δ := by
  intro r s hrs
  -- Either |fract diff| > 1/2 ≥ δ, or |fract diff| ≤ 1/2 and we use round_le.
  by_cases hf : 1 / 2 < |Int.fract (α r) - Int.fract (α s)|
  · linarith
  · -- |fract diff| ≤ 1/2
    push Not at hf
    -- In this case, |fract diff| = circular distance of (α r - α s)
    -- because round(fract diff + floor diff) = floor diff when |fract diff| ≤ 1/2
    -- So δ ≤ |α r - α s - round(α r - α s)| ≤ |fract diff| (via round_le with floor diff)
    set f := Int.fract (α r) - Int.fract (α s)
    set n₀ := ⌊α r⌋ - ⌊α s⌋
    have hD : α r - α s = f + ↑n₀ := by
      simp only [f, n₀, Int.fract]; push_cast; ring
    have hcirc_rs := hcirc r s hrs
    -- |α r - α s - round(α r - α s)| ≤ |α r - α s - n₀| = |f| by round_le
    have hle : |α r - α s - ↑(round (α r - α s))| ≤ |f| := by
      calc |α r - α s - ↑(round (α r - α s))| ≤ |α r - α s - ↑n₀| := round_le _ n₀
        _ = |f| := by rw [hD]; ring_nf
    linarith

/-- **Lifted points**: given α : Fin R → ℝ and K : ℕ, the product-index
    lifted points are λ_{(r,j)} = fract(α_r) + (j − K) for
    (r,j) ∈ Fin R × Fin (2K+1), representing shifts from −K to K. -/
def liftedPts {R : ℕ} (α : Fin R → ℝ) (K : ℕ) : Fin R × Fin (2 * K + 1) → ℝ :=
  fun ⟨r, j⟩ => Int.fract (α r) + (↑(j : ℕ) - ↑K)

/-- **Lifted coefficients**: z_{(r,j)} = (-1)^j · c_r for the product-index trick. -/
def liftedCoeffs {R : ℕ} (c : Fin R → ℂ) (K : ℕ) : Fin R × Fin (2 * K + 1) → ℂ :=
  fun ⟨r, j⟩ => (-1 : ℂ) ^ (j : ℕ) * c r

/-- **Lifted l2 norm**: the l2 norm of lifted coefficients equals (2K+1) times
    the original l2 norm, since |(-1)^j|² = 1 for all j. -/
theorem liftedCoeffs_l2NormSq {R : ℕ} (c : Fin R → ℂ) (K : ℕ) :
    ∑ p : Fin R × Fin (2 * K + 1), ‖liftedCoeffs c K p‖ ^ 2 =
      (2 * ↑K + 1) * l2NormSq c := by
  unfold liftedCoeffs l2NormSq
  rw [Fintype.sum_prod_type]
  simp_rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- **Lifted point differences**: the difference of lifted points decomposes as
    fract difference plus integer shift difference. -/
theorem liftedPts_diff {R : ℕ} (α : Fin R → ℝ) (K : ℕ)
    (r s : Fin R) (j l : Fin (2 * K + 1)) :
    liftedPts α K (r, j) - liftedPts α K (s, l) =
      (Int.fract (α r) - Int.fract (α s)) + ((↑(j : ℕ) : ℝ) - ↑(l : ℕ)) := by
  unfold liftedPts; ring

/-- **Lifted point separation for same r**: when r = s and j ≠ l,
    the lifted points differ by a nonzero integer, hence |difference| ≥ 1 ≥ δ. -/
theorem liftedPts_sep_same {R : ℕ} (α : Fin R → ℝ) (K : ℕ)
    (r : Fin R) (j l : Fin (2 * K + 1)) (hjl : j ≠ l) (δ : ℝ) (_hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    δ ≤ |liftedPts α K (r, j) - liftedPts α K (r, l)| := by
  rw [liftedPts_diff, sub_self, zero_add]
  have hjl' : (j : ℕ) ≠ (l : ℕ) := Fin.val_ne_of_ne hjl
  have : (1 : ℝ) ≤ |(↑(j : ℕ) : ℝ) - ↑(l : ℕ)| := by
    have h_int : 1 ≤ |((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)| := by
      rcases Nat.lt_or_gt_of_ne hjl' with h | h
      · rw [abs_of_nonpos (by omega : ((j : ℕ) : ℤ) - (l : ℕ) ≤ 0)]; omega
      · rw [abs_of_nonneg (by omega : 0 ≤ ((j : ℕ) : ℤ) - (l : ℕ))]; omega
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ |(((j : ℕ) : ℤ) : ℝ) - (((l : ℕ) : ℤ) : ℝ)| := by exact_mod_cast h_int
      _ = |(↑(j : ℕ) : ℝ) - ↑(l : ℕ)| := by simp [Int.cast_natCast]
  linarith

/-- **Fract-to-round distance bound**: for f ∈ (−1, 1) with
    `min(|f|, 1 − |f|) ≥ δ`, the shifted value `|f + m| ≥ δ` for all integers m.

    This is the key fact that makes the product-index trick work:
    the circular distance condition ensures ALL integer translates
    of the fract difference are bounded away from 0.

    The proof uses: `|f + m|` for integer m ≥ dist(f, ℤ) = min(|f|, 1−|f|) ≥ δ`. -/
theorem fract_shift_lower_bound {f : ℝ} {m : ℤ}
    (_hf_bound : |f| < 1) (hf_circ : ∀ n : ℤ, δ ≤ |f - ↑n|) :
    δ ≤ |f + ↑m| := by
  have := hf_circ (-m)
  simp only [Int.cast_neg, sub_neg_eq_add] at this
  exact this

/-- **Lifted point separation for different r (circular spacing)**: when r ≠ s
    and the α's are **circularly** δ-spaced, the lifted points are δ-separated.

    This is the critical step that requires `IsCircularSpaced` (not just `IsSpaced`). -/
theorem liftedPts_sep_diff_circular {R : ℕ} {δ : ℝ} (α : Fin R → ℝ) (K : ℕ)
    (hcirc : IsCircularSpaced α δ)
    (r s : Fin R) (hrs : r ≠ s) (j l : Fin (2 * K + 1))
    (_hδ : 0 < δ) (_hδ2 : δ ≤ 1 / 2) :
    δ ≤ |liftedPts α K (r, j) - liftedPts α K (s, l)| := by
  rw [liftedPts_diff]
  set f := Int.fract (α r) - Int.fract (α s)
  set m_nat := ((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)
  -- The key: the circular distance condition says |α_r - α_s - n| ≥ δ for the nearest integer n.
  -- This translates to: for ALL integers n, |f + n| ≥ δ
  -- (since α_r - α_s = f + (⌊α_r⌋ - ⌊α_s⌋), and fract is periodic under integer shifts).
  -- Actually, |α_r - α_s - round(α_r - α_s)| ≥ δ means:
  -- the distance from α_r - α_s to the nearest integer is ≥ δ.
  -- This means for ALL integers n: |α_r - α_s - n| ≥ δ.
  -- Since α_r - α_s = f + floor_diff, this gives |f + floor_diff - n| ≥ δ for all n.
  -- Setting n' = n - floor_diff: |f + n'| ≥ δ for all integers n' (rename n to n').
  -- Wait, that's wrong. Let me be more careful.
  -- Let D = α_r - α_s. The circular distance condition says |D - round(D)| ≥ δ.
  -- round(D) is the nearest integer to D.
  -- For ANY integer n: |D - n| ≥ |D - round(D)| (by definition of round as nearest integer).
  -- So |D - n| ≥ δ for all n ∈ ℤ.
  -- Now D = f + (⌊α_r⌋ - ⌊α_s⌋), so |f + ⌊α_r⌋ - ⌊α_s⌋ - n| ≥ δ for all n.
  -- Setting m = n - (⌊α_r⌋ - ⌊α_s⌋): |f - m| ≥ δ for all m ∈ ℤ.
  -- Equivalently: |f + k| ≥ δ for all k ∈ ℤ.
  -- In particular: |f + m_nat| ≥ δ.
  have hD := hcirc r s hrs
  -- |D - round(D)| ≥ δ where D = α r - α s
  -- For all integers n, |D - n| ≥ |D - round(D)| ≥ δ
  -- D = f + floor_diff
  -- We need |f + (j - l)| ≥ δ, which is |D - floor_diff + (j-l)| = |D - (floor_diff - j + l)| ≥ δ
  -- since floor_diff - j + l is an integer.
  have hfloor_diff_int : ∃ n : ℤ, (α r - α s : ℝ) = f + ↑n := by
    use ⌊α r⌋ - ⌊α s⌋
    simp only [f, Int.fract]; push_cast; ring
  obtain ⟨n₀, hn₀⟩ := hfloor_diff_int
  -- For any integer k: |α r - α s - k| ≥ δ
  have hall : ∀ k : ℤ, δ ≤ |α r - α s - ↑k| := by
    intro k
    calc δ ≤ |α r - α s - round (α r - α s)| := hD
      _ ≤ |α r - α s - ↑k| := round_le _ k
  -- So |f + n₀ - k| ≥ δ for all k, hence |f + m| ≥ δ for all m
  -- (by setting k = n₀ - m, i.e., m = n₀ - k)
  have hall_f : ∀ m : ℤ, δ ≤ |f + ↑m| := by
    intro m
    have := hall (n₀ - m)
    rw [hn₀] at this
    -- this : δ ≤ |f + ↑n₀ - ↑(n₀ - m)|
    rwa [show (↑(n₀ - m) : ℝ) = ↑n₀ - ↑m from by push_cast; ring,
      show f + ↑n₀ - (↑n₀ - ↑m) = f + ↑m from by ring] at this
  -- Apply to our specific m_nat = (j : ℤ) - (l : ℤ)
  have key := hall_f m_nat
  -- key : δ ≤ |f + ↑m_nat| where m_nat = (↑j : ℤ) - ↑l
  -- Rewrite ↑m_nat to match the goal form (↑j : ℝ) - ↑l
  have heq : (↑m_nat : ℝ) = (↑(j : ℕ) : ℝ) - ↑(l : ℕ) := by
    simp only [m_nat]; push_cast; ring
  rwa [heq] at key

/-- **Full lifted system separation (circular)**: for circularly δ-spaced α,
    ALL distinct pairs of lifted points are δ-separated. -/
theorem liftedPts_sep_all_circular {R : ℕ} {δ : ℝ} (α : Fin R → ℝ) (K : ℕ)
    (hcirc : IsCircularSpaced α δ)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (p q : Fin R × Fin (2 * K + 1)) (hpq : p ≠ q) :
    δ ≤ |liftedPts α K p - liftedPts α K q| := by
  obtain ⟨r, j⟩ := p
  obtain ⟨s, l⟩ := q
  by_cases hrs : r = s
  · subst hrs
    have hjl : j ≠ l := by intro h; exact hpq (Prod.ext rfl h)
    exact liftedPts_sep_same α K r j l hjl δ hδ hδ2
  · exact liftedPts_sep_diff_circular α K hcirc r s hrs j l hδ hδ2

/-- **CscBilinearBound with circular spacing**: the csc bilinear form is bounded
    by `(1/δ) · l2NormSq c` when the points are circularly δ-spaced.

    This is the `1/δ` version (without the Cohen trick's `−1` improvement).
    The proof uses the product-index trick with the Mittag-Leffler expansion
    of `π·csc(πθ)` as a Cesaro limit.

    **Open hypothesis**: the Cesaro convergence of the Mittag-Leffler series
    `∑_{m=-K}^{K} (−1)^m/(θ+m) → π/sin(πθ)` as K → ∞, needed for the
    limit step of the product-index trick. -/
def CscBilinearBoundCircular : Prop :=
  ∀ (R : ℕ) (α : Fin R → ℝ) (c : Fin R → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 →
    IsCircularSpaced α δ →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      c r * starRingEnd ℂ (c s) /
      (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖ ≤
      (1/δ) * l2NormSq c

/-- **Circular spacing → sin ≠ 0**: for circularly δ-spaced points with δ > 0,
    `sin(π · (α_r − α_s)) ≠ 0` for r ≠ s.

    Proof: circular distance ≥ δ > 0 means α_r − α_s is not an integer,
    hence sin(π·(α_r − α_s)) ≠ 0. -/
theorem isCircularSpaced_sin_ne_zero {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hcirc : IsCircularSpaced α δ)
    (r s : Fin R) (hrs : r ≠ s) :
    Real.sin (Real.pi * (α r - α s)) ≠ 0 := by
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨n, hn⟩ := hsin
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hαint : α r - α s = (n : ℝ) := by field_simp at hn; linarith
  have hcs := hcirc r s hrs
  rw [hαint] at hcs
  -- hcs : δ ≤ |(n : ℝ) - ↑(round (n : ℝ))|
  -- round(n : ℝ) = n since n is an integer
  have hround : round (n : ℝ) = n := round_intCast n
  rw [hround, sub_self, abs_zero] at hcs
  linarith

/-- **Mittag-Leffler expansion of csc**: for θ ∉ ℤ, the series
    `∑_{n∈ℤ} (−1)^n/(θ+n)` converges (in the Cesaro sense) to `π/sin(πθ)`.

    Here we state the partial sum version: the alternating sum
    `∑_{m=-K}^{K} (−1)^m/(θ+m)` converges to `π/sin(πθ)` as K → ∞. -/
def MittagLefflerCsc : Prop :=
  ∀ (θ : ℝ), (∀ n : ℤ, θ + ↑n ≠ 0) →
    Filter.Tendsto
      (fun K : ℕ => ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (-1 : ℝ) ^ m.natAbs / (θ + ↑m))
      Filter.atTop (nhds (Real.pi / Real.sin (Real.pi * θ)))

-- ==========================================
-- Section: Proof of MittagLefflerCsc
-- ==========================================

private theorem ofReal_not_int_of_ne_int {θ : ℝ} (hθ : ∀ n : ℤ, θ + ↑n ≠ 0) :
    (↑θ : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range]
  intro ⟨n, hn⟩
  have hre : θ = (n : ℝ) := by
    have := congr_arg Complex.re hn; simp at this; exact this.symm
  have : θ + ↑(-n) = 0 := by push_cast; linarith
  exact hθ (-n) this

private theorem ofReal_half_not_int_of_ne_int {θ : ℝ} (hθ : ∀ n : ℤ, θ + ↑n ≠ 0) :
    (↑(θ / 2) : ℂ) ∈ Complex.integerComplement := by
  apply ofReal_not_int_of_ne_int
  intro n hn
  have : θ + ↑(2 * n) = 0 := by push_cast at hn ⊢; linarith
  exact hθ (2 * n) this

private theorem theta_add_ne_zero {θ : ℝ} (hθ : ∀ n : ℤ, θ + ↑n ≠ 0) (j : ℕ) :
    θ + (↑j + 1) ≠ 0 := by
  intro h; have := hθ (↑j + 1); apply this; push_cast; linarith

private theorem theta_sub_ne_zero {θ : ℝ} (hθ : ∀ n : ℤ, θ + ↑n ≠ 0) (j : ℕ) :
    θ - (↑j + 1) ≠ 0 := by
  intro h; have := hθ (-(↑j + 1 : ℤ)); apply this; push_cast; linarith

private theorem theta_ne_zero {θ : ℝ} (hθ : ∀ n : ℤ, θ + ↑n ≠ 0) : θ ≠ 0 := by
  have := hθ 0; simp at this; exact this

/-- The alternating symmetric sum expressed in terms of a sum over ℕ. -/
private theorem alternating_sum_eq {θ : ℝ} (_hθ : ∀ n : ℤ, θ + ↑n ≠ 0) (K : ℕ) :
    ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (-1 : ℝ) ^ m.natAbs / (θ + ↑m) =
      1 / θ + ∑ j ∈ Finset.range K,
        (-1 : ℝ) ^ (j + 1) * (1 / (θ + (↑j + 1)) + 1 / (θ - (↑j + 1))) := by
  -- Split Icc(-K, K) = {0} ∪ {1,...,K} ∪ {-K,...,-1}
  -- and pair m with -m for m > 0
  induction K with
  | zero => simp [Int.natAbs]
  | succ K ih =>
    -- Icc(-(K+1), K+1) = Icc(-K, K) ∪ {K+1} ∪ {-(K+1)}
    have h_mem_K1 : (↑(K + 1) : ℤ) ∈ Finset.Icc (-(↑(K + 1) : ℤ)) (↑(K + 1)) := by
      simp [Finset.mem_Icc]; omega
    have h_mem_nK1 : (-(↑(K + 1) : ℤ)) ∈ Finset.Icc (-(↑(K + 1) : ℤ)) (↑(K + 1)) := by
      simp [Finset.mem_Icc]; omega
    -- Show Icc(-(K+1), K+1) \ {K+1} = Icc(-(K+1), K)
    have h_erase1 : (Finset.Icc (-(↑(K + 1) : ℤ)) (↑(K + 1))).erase (↑(K + 1)) =
        Finset.Icc (-(↑(K + 1) : ℤ)) (↑K) := by
      ext x; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
    have h_erase2 : (Finset.Icc (-(↑(K + 1) : ℤ)) (↑K)).erase (-(↑(K + 1) : ℤ)) =
        Finset.Icc (-(↑K : ℤ)) (↑K) := by
      ext x; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
    rw [← Finset.add_sum_erase _ _ h_mem_K1, h_erase1,
        ← Finset.add_sum_erase _ _ (by simp only [Finset.mem_Icc]; omega :
          (-(↑(K + 1) : ℤ)) ∈ Finset.Icc (-(↑(K + 1) : ℤ)) (↑K)), h_erase2, ih]
    rw [Finset.range_add_one, Finset.sum_insert (by simp)]
    -- Simplify the natAbs terms
    have hna_pos : (↑(K + 1) : ℤ).natAbs = K + 1 := by omega
    have hna_neg : (-(↑(K + 1) : ℤ)).natAbs = K + 1 := by omega
    simp only [hna_pos, hna_neg]
    push_cast
    ring

/-- **MittagLefflerCsc is a theorem**: the symmetric partial sums of
    `(-1)^|m|/(θ+m)` over `m ∈ [-K, K]` converge to `π/sin(πθ)`. -/
theorem mittag_leffler_csc_proved : MittagLefflerCsc := by
  intro θ hθ
  -- Convert to complex integerComplement membership
  have hθ_ic := ofReal_not_int_of_ne_int hθ
  have hθ2_ic := ofReal_half_not_int_of_ne_int hθ
  have hθ_ne := theta_ne_zero hθ

  -- Step 1: Express the partial sum in terms of a ℕ-indexed sum
  have hK_eq := alternating_sum_eq hθ

  -- From Mathlib: cotTerm series at θ is summable (in ℂ)
  have h_sumC := summable_cotTerm hθ_ic
  have h_sumC_half := summable_cotTerm hθ2_ic

  -- Step 3: The cotTerm partial sums converge (in ℂ)
  have T_cot := tendsto_logDeriv_euler_cot_sub hθ_ic

  -- Step 4: Extract real convergence
  -- cotTerm(↑θ, j) = ↑(1/(θ-(j+1)) + 1/(θ+(j+1))) for real θ
  have h_cotTerm_real : ∀ j : ℕ, cotTerm ((↑θ : ℂ)) j =
      (↑(1 / (θ - (↑j + 1)) + 1 / (θ + (↑j + 1))) : ℂ) := by
    intro j; simp only [cotTerm]; push_cast; ring

  -- The real partial sums converge
  -- Bridge ℂ → ℝ: use Complex.isometry_ofReal.isEmbedding.tendsto_nhds_iff
  have T_real : Filter.Tendsto
      (fun K : ℕ => ∑ j ∈ Finset.range K, (1 / (θ - (↑j + 1)) + 1 / (θ + (↑j + 1))))
      Filter.atTop (nhds (Real.pi * Real.cot (Real.pi * θ) - 1 / θ)) := by
    rw [Complex.isometry_ofReal.isEmbedding.tendsto_nhds_iff]
    have h_eq : ∀ K, Complex.ofReal (∑ j ∈ Finset.range K,
        (1 / (θ - (↑j + 1)) + 1 / (θ + (↑j + 1)))) =
        ∑ j ∈ Finset.range K, cotTerm ((↑θ : ℂ)) j := by
      intro K; simp only [h_cotTerm_real, Complex.ofReal_sum]
    have h_lim : Complex.ofReal (Real.pi * Real.cot (Real.pi * θ) - 1 / θ) =
        ↑Real.pi * Complex.cot (↑Real.pi * ↑θ) - 1 / (↑θ : ℂ) := by
      push_cast [Complex.ofReal_cot]; ring
    simp_rw [Function.comp_def, h_eq, h_lim]
    exact T_cot

  -- Similarly at θ/2
  have T_cot_half := tendsto_logDeriv_euler_cot_sub hθ2_ic
  have h_cotTerm_half_real : ∀ j : ℕ, cotTerm ((↑(θ / 2) : ℂ)) j =
      (↑(1 / (θ / 2 - (↑j + 1)) + 1 / (θ / 2 + (↑j + 1))) : ℂ) := by
    intro j; simp only [cotTerm]; push_cast; ring

  have T_half_real : Filter.Tendsto
      (fun K : ℕ => ∑ j ∈ Finset.range K, (1 / (θ / 2 - (↑j + 1)) + 1 / (θ / 2 + (↑j + 1))))
      Filter.atTop (nhds (Real.pi * Real.cot (Real.pi * (θ / 2)) - 1 / (θ / 2))) := by
    rw [Complex.isometry_ofReal.isEmbedding.tendsto_nhds_iff]
    have h_eq : ∀ K, Complex.ofReal (∑ j ∈ Finset.range K,
        (1 / (θ / 2 - (↑j + 1)) + 1 / (θ / 2 + (↑j + 1)))) =
        ∑ j ∈ Finset.range K, cotTerm ((↑(θ / 2) : ℂ)) j := by
      intro K; simp only [h_cotTerm_half_real, Complex.ofReal_sum]
    have h_lim : Complex.ofReal (Real.pi * Real.cot (Real.pi * (θ / 2)) - 1 / (θ / 2)) =
        ↑Real.pi * Complex.cot (↑Real.pi * ↑(θ / 2)) - 1 / (↑(θ / 2) : ℂ) := by
      push_cast [Complex.ofReal_cot]; ring
    simp_rw [Function.comp_def, h_eq, h_lim]
    exact T_cot_half

  -- Step 5: Strategy — express A_K in terms of cot partial sums

  -- Define real cotTerm and half-cotTerm
  set g : ℕ → ℝ := fun j => 1 / (θ - (↑j + 1)) + 1 / (θ + (↑j + 1)) with hg_def
  set gh : ℕ → ℝ := fun j => 1 / (θ / 2 - (↑j + 1)) + 1 / (θ / 2 + (↑j + 1)) with hgh_def

  -- Rewrite A_K = 1/θ - ∑_{j<K} (-1)^j g(j)
  have hK_eq' : ∀ K : ℕ, ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (-1 : ℝ) ^ m.natAbs / (θ + ↑m) =
    1 / θ - ∑ j ∈ Finset.range K, (-1 : ℝ) ^ j * g j := by
    intro K; rw [hK_eq K]
    have : ∀ j ∈ Finset.range K,
        (-1 : ℝ) ^ (j + 1) * (1 / (θ + (↑j + 1)) + 1 / (θ - (↑j + 1))) =
        -((-1 : ℝ) ^ j * g j) := by
      intro j _; simp only [hg_def, pow_succ]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]; ring

  -- Key: g(2k+1) = (1/2) * gh(k)
  have g_odd_eq : ∀ k : ℕ, g (2 * k + 1) = (1 / 2) * gh k := by
    intro k; simp only [hg_def, hgh_def]
    have h1 : (↑(2 * k + 1) : ℝ) + 1 = 2 * ((↑k : ℝ) + 1) := by push_cast; ring
    rw [h1]
    have h2 : θ - 2 * (↑k + 1) = 2 * (θ / 2 - (↑k + 1)) := by ring
    have h3 : θ + 2 * (↑k + 1) = 2 * (θ / 2 + (↑k + 1)) := by ring
    rw [h2, h3]; field_simp

  -- Step 6: Show ∑ (-1)^j g(j) is summable in ℝ
  have h_g_summable : Summable g := by
    rw [← Complex.summable_ofReal]
    have : (fun j => (↑(g j) : ℂ)) = (fun j => cotTerm (↑θ) j) := by
      ext j; rw [h_cotTerm_real]
    rw [this]; exact h_sumC

  have h_alt_summable : Summable (fun j => (-1 : ℝ) ^ j * g j) := h_g_summable.alternating

  -- Step 7: Compute the tsum value
  -- ∑' g(j) = π cot(πθ) - 1/θ  (by uniqueness of limits)
  have h_tsum_g : ∑' j, g j = Real.pi * Real.cot (Real.pi * θ) - 1 / θ :=
    tendsto_nhds_unique h_g_summable.hasSum.tendsto_sum_nat T_real

  -- ∑' gh(j) = π cot(πθ/2) - 2/θ
  have h_gh_summable : Summable gh := by
    rw [← Complex.summable_ofReal]
    have : (fun j => (↑(gh j) : ℂ)) = (fun j => cotTerm (↑(θ / 2)) j) := by
      ext j; rw [h_cotTerm_half_real]
    rw [this]; exact h_sumC_half

  have h_tsum_gh : ∑' j, gh j = Real.pi * Real.cot (Real.pi * (θ / 2)) - 1 / (θ / 2) :=
    tendsto_nhds_unique h_gh_summable.hasSum.tendsto_sum_nat T_half_real

  -- Odd part: ∑' g(2k+1) = (1/2) ∑' gh(k)
  have h_odd_summable : Summable (fun k => g (2 * k + 1)) :=
    h_g_summable.comp_injective (fun a b h => by omega)

  have h_tsum_odd : ∑' k, g (2 * k + 1) = (1 / 2) * ∑' k, gh k := by
    simp_rw [g_odd_eq]; exact tsum_mul_left

  -- Even part summable
  have h_even_summable : Summable (fun k => g (2 * k)) :=
    h_g_summable.comp_injective (fun a b h => by omega)

  -- Even + odd = total: ∑' g(2k) + ∑' g(2k+1) = ∑' g(j)
  have h_even_odd : ∑' k, g (2 * k) + ∑' k, g (2 * k + 1) = ∑' j, g j :=
    tsum_even_add_odd h_even_summable h_odd_summable

  -- Compute ∑' (-1)^j g(j) = ∑' g(2k) - ∑' g(2k+1)
  have h_alt_value : ∑' j, (-1 : ℝ) ^ j * g j =
      ∑' k, g (2 * k) - ∑' k, g (2 * k + 1) := by
    have h_even_hs : HasSum (fun k => (-1 : ℝ) ^ (2 * k) * g (2 * k))
        (∑' k, g (2 * k)) := by
      have : (fun k => (-1 : ℝ) ^ (2 * k) * g (2 * k)) = (fun k => g (2 * k)) := by
        ext k; simp [pow_mul]
      rw [this]; exact h_even_summable.hasSum
    have h_odd_hs : HasSum (fun k => (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1))
        (-(∑' k, g (2 * k + 1))) := by
      have : (fun k => (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1)) =
          (fun k => -(g (2 * k + 1))) := by
        ext k; simp [pow_succ, pow_mul]
      rw [this]; exact h_odd_summable.hasSum.neg
    have h_alt : HasSum (fun j => (-1 : ℝ) ^ j * g j)
        (∑' k, g (2 * k) + -(∑' k, g (2 * k + 1))) :=
      h_even_hs.even_add_odd h_odd_hs
    exact (h_alt.tsum_eq).trans (by ring)

  -- Now compute the numerical value
  have h_alt_val : ∑' j, (-1 : ℝ) ^ j * g j =
      Real.pi * Real.cot (Real.pi * θ) - Real.pi * Real.cot (Real.pi * (θ / 2)) + 1 / θ := by
    rw [h_alt_value]
    have h1 : ∑' k, g (2 * k) = ∑' j, g j - ∑' k, g (2 * k + 1) := by linarith [h_even_odd]
    rw [h1, h_tsum_odd, h_tsum_g, h_tsum_gh]
    field_simp; ring

  -- Step 8: Trig identity: π cot(πθ/2) - π cot(πθ) = π/sin(πθ)

  -- sin(πθ) ≠ 0
  have hsin : Real.sin (Real.pi * θ) ≠ 0 := by
    intro h; rw [Real.sin_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    -- hn : ↑n * π = π * θ, so θ = n
    have hθn : θ = ↑n := by
      have hpi := Real.pi_ne_zero
      field_simp at hn; linarith
    have : θ + ↑(-n) = 0 := by push_cast; linarith
    exact hθ (-n) this

  -- sin(πθ/2) ≠ 0
  have hsin2 : Real.sin (Real.pi * (θ / 2)) ≠ 0 := by
    intro h; rw [Real.sin_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hθn : θ / 2 = ↑n := by
      have hpi := Real.pi_ne_zero
      field_simp at hn; linarith
    have : θ + ↑(-2 * n) = 0 := by push_cast; linarith
    exact hθ (-2 * n) this

  have h_trig : Real.pi * Real.cot (Real.pi * (θ / 2)) - Real.pi * Real.cot (Real.pi * θ) =
      Real.pi / Real.sin (Real.pi * θ) := by
    -- Use substitution a = πθ/2 so π(θ/2) = a, πθ = 2a
    set a := Real.pi * θ / 2 with ha_def
    have ha_eq : Real.pi * (θ / 2) = a := by rw [ha_def]; ring
    have h2a : Real.pi * θ = 2 * a := by rw [ha_def]; ring
    have hsa : Real.sin a ≠ 0 := by rwa [ha_eq] at hsin2
    have hs2a : Real.sin (2 * a) ≠ 0 := by rwa [← h2a]
    have h_sin2a := Real.sin_two_mul a
    -- sin(2a) = 2 sin(a) cos(a), so cos(a) ≠ 0
    have hca : Real.cos a ≠ 0 := by
      intro hc
      have : Real.sin (2 * a) = 0 := by
        rw [h_sin2a]; simp [hc]
      exact hs2a this
    -- cot(a) = cos(a)/sin(a), cot(2a) = cos(2a)/sin(2a) = cos(2a)/(2 sin(a) cos(a))
    -- cot(a) - cot(2a) = cos(a)/sin(a) - cos(2a)/(2 sin(a) cos(a))
    --   = (2 cos²(a) - cos(2a)) / (2 sin(a) cos(a))
    --   = (2 cos²(a) - (2cos²(a) - 1)) / (2 sin(a) cos(a))
    --   = 1 / (2 sin(a) cos(a)) = 1/sin(2a)
    -- So π·cot(a) - π·cot(2a) = π/sin(2a)
    rw [ha_eq, h2a]
    -- Goal: π * cot(a) - π * cot(2a) = π / sin(2a)
    have key : Real.cot a - Real.cot (2 * a) = 1 / Real.sin (2 * a) := by
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
      have hd := mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hsa) hca
      rw [h_sin2a]
      rw [div_sub_div _ _ hsa hd, div_eq_div_iff (mul_ne_zero hsa hd) hd]
      rw [one_mul, Real.cos_two_mul]
      ring
    have := congr_arg (· * Real.pi) key
    simp only [sub_mul, one_div, inv_mul_eq_div] at this
    linarith

  -- Step 9: Assemble the final result
  -- A_K = 1/θ - ∑_{j<K} (-1)^j g(j) → 1/θ - ∑' (-1)^j g(j) = π/sin(πθ)

  have h_target : 1 / θ - ∑' j, (-1 : ℝ) ^ j * g j = Real.pi / Real.sin (Real.pi * θ) := by
    rw [h_alt_val]; linarith [h_trig]

  apply Filter.Tendsto.congr (fun K => (hK_eq' K).symm)
  rw [show Real.pi / Real.sin (Real.pi * θ) =
    1 / θ - ∑' j, (-1 : ℝ) ^ j * g j from h_target.symm]
  exact Filter.Tendsto.const_sub _ h_alt_summable.hasSum.tendsto_sum_nat

end IK
