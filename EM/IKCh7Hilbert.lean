import EM.IKCh7AdditiveLS

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
    push_neg at hf
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

-- ==========================================
-- Section: HilbertInequality → CscBilinearBoundCircular
-- ==========================================

private def liftedPtsA {R : ℕ} (α : Fin R → ℝ) (K : ℕ) :
    Fin R × Fin (2 * K + 1) → ℝ :=
  fun ⟨r, j⟩ => α r + ((j : ℕ) - (K : ℝ))

/-- **Lifted point differences (actual α)**: the difference decomposes as
    actual difference plus integer shift. -/
private theorem liftedPtsA_diff {R : ℕ} (α : Fin R → ℝ) (K : ℕ)
    (r s : Fin R) (j l : Fin (2 * K + 1)) :
    liftedPtsA α K (r, j) - liftedPtsA α K (s, l) =
      (α r - α s) + (↑(j : ℕ) - ↑(l : ℕ)) := by
  unfold liftedPtsA; ring

/-- **Lifted point separation for same r (actual α)**: when r = s and j ≠ l,
    the lifted points differ by a nonzero integer, hence |diff| ≥ 1 ≥ δ. -/
private theorem liftedPtsA_sep_same {R : ℕ} (α : Fin R → ℝ) (K : ℕ)
    (r : Fin R) (j l : Fin (2 * K + 1)) (hjl : j ≠ l) (δ : ℝ) (_hδ : 0 < δ) (hδ2 : δ ≤ 1/2) :
    δ ≤ |liftedPtsA α K (r, j) - liftedPtsA α K (r, l)| := by
  rw [liftedPtsA_diff, sub_self, zero_add]
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

/-- **Lifted point separation for different r (actual α, circular spacing)**: when r ≠ s
    and α is circularly δ-spaced, the lifted points are δ-separated. -/
private theorem liftedPtsA_sep_diff {R : ℕ} {δ : ℝ} (α : Fin R → ℝ) (K : ℕ)
    (hcirc : IsCircularSpaced α δ)
    (r s : Fin R) (hrs : r ≠ s) (j l : Fin (2 * K + 1)) :
    δ ≤ |liftedPtsA α K (r, j) - liftedPtsA α K (s, l)| := by
  rw [liftedPtsA_diff]
  -- Circular spacing: for all integers n, δ ≤ |α r - α s - n|
  have hall : ∀ k : ℤ, δ ≤ |α r - α s - ↑k| := by
    intro k
    calc δ ≤ |α r - α s - round (α r - α s)| := hcirc r s hrs
      _ ≤ |α r - α s - ↑k| := round_le _ k
  set m : ℤ := -(↑(j : ℕ) - ↑(l : ℕ))
  have hm : (α r - α s) + (↑(j : ℕ) - ↑(l : ℕ)) = (α r - α s) - ↑m := by
    simp [m]; ring
  rw [hm]
  exact hall m

/-- **Full lifted system separation (actual α, circular)**: for circularly δ-spaced α,
    ALL distinct pairs of lifted points (actual α version) are δ-separated. -/
private theorem liftedPtsA_sep_all {R : ℕ} {δ : ℝ} (α : Fin R → ℝ) (K : ℕ)
    (hcirc : IsCircularSpaced α δ)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1/2)
    (p q : Fin R × Fin (2 * K + 1)) (hpq : p ≠ q) :
    δ ≤ |liftedPtsA α K p - liftedPtsA α K q| := by
  obtain ⟨r, j⟩ := p
  obtain ⟨s, l⟩ := q
  by_cases hrs : r = s
  · subst hrs
    have hjl : j ≠ l := by intro h; exact hpq (Prod.ext rfl h)
    exact liftedPtsA_sep_same α K r j l hjl δ hδ hδ2
  · exact liftedPtsA_sep_diff α K hcirc r s hrs j l

/-- **CscBilinearBound implies CscBilinearBoundCircular**: the weaker bound `(1/δ - 1)`
    with IsSpaced implies the `1/δ` bound with IsCircularSpaced, since
    IsCircularSpaced → IsSpaced and `1/δ - 1 ≤ 1/δ`. -/
theorem csc_bilinear_implies_circular (hcsc : CscBilinearBound) :
    CscBilinearBoundCircular := by
  intro R α c δ hδ hδ2 hcirc
  have hspaced := isCircularSpaced_implies_isSpaced α δ hδ2 hcirc
  have hbound := hcsc R α c δ hδ hδ2 hspaced
  -- (1/δ - 1) * l2NormSq c ≤ (1/δ) * l2NormSq c
  calc ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        c r * starRingEnd ℂ (c s) /
        (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖
      ≤ (1 / δ - 1) * l2NormSq c := hbound
    _ ≤ (1 / δ) * l2NormSq c := by
        apply mul_le_mul_of_nonneg_right _ (l2NormSq_nonneg c)
        linarith

/-- **HilbertCscBilinearBridge implies CscBilinearBoundCircular**:
    composing `HilbertInequality → CscBilinearBound → CscBilinearBoundCircular`. -/
theorem hilbert_csc_bilinear_bridge_circular_proved (hbridge : HilbertCscBilinearBridge)
    (hHI : HilbertInequality) : CscBilinearBoundCircular :=
  csc_bilinear_implies_circular (hbridge hHI)

/-- **Integer-spaced points are circularly spaced**: for d ∈ ℤ with 0 < |d| < p,
    the circular distance |d/p − round(d/p)| ≥ 1/p. -/
theorem int_div_circular_sep {d : ℤ} {p : ℕ} (hp : 0 < p)
    (hd_ne : d ≠ 0) (hd_bound : |d| < (p : ℤ)) :
    1 / (p : ℝ) ≤ |(↑d : ℝ) / (↑p : ℝ) - ↑(round ((↑d : ℝ) / (↑p : ℝ)))| := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  set x : ℝ := (↑d : ℝ) / (↑p : ℝ) with hx_def
  -- Suffices: ∀ n : ℤ, 1/p ≤ |x - n|, specialize at round.
  suffices h_all_n : ∀ n : ℤ, 1 / (p : ℝ) ≤ |x - ↑n| from h_all_n (round x)
  intro n
  -- Key: |x - n| = |d - n*p| / p
  have hd_ne_np : d - n * (p : ℤ) ≠ 0 := by
    intro heq
    -- d = n * p, so p | d. Since 0 < |d| < p, this is impossible.
    have hd_eq : d = n * (p : ℤ) := by linarith
    -- If n = 0, then d = 0, contradicting hd_ne
    -- If |n| ≥ 1, then |d| = |n| * p ≥ p, contradicting hd_bound
    rcases eq_or_ne n 0 with rfl | hn
    · simp at hd_eq; exact hd_ne hd_eq
    · have : (p : ℤ) ≤ |d| := by
        rw [hd_eq, abs_mul, abs_of_nonneg (Int.natCast_nonneg p)]
        exact le_mul_of_one_le_left (Int.natCast_nonneg p) (Int.one_le_abs hn)
      linarith
  have hone_le : (1 : ℝ) ≤ |(↑(d - n * (p : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hd_ne_np
  show 1 / (p : ℝ) ≤ |(↑d : ℝ) / (↑p : ℝ) - ↑n|
  -- Rewrite: ↑d/↑p - ↑n = (↑d - ↑n * ↑p) / ↑p
  rw [show (↑d : ℝ) / (↑p : ℝ) - (↑n : ℝ) = ((↑d : ℝ) - (↑n : ℝ) * (↑p : ℝ)) / (↑p : ℝ) from
    by rw [sub_div, mul_div_cancel_right₀ _ hp_ne]]
  rw [abs_div, abs_of_pos hp_pos, le_div_iff₀ hp_pos, one_div_mul_cancel hp_ne]
  -- Goal: 1 ≤ |(↑d - ↑n * ↑p : ℝ)|
  convert hone_le using 1; push_cast; ring

/-- **Phase-shifted l2 norm preservation**: `l2NormSq (fun r => b r * eAN(t * α r)) = l2NormSq b`
    because `‖eAN(x)‖ = 1`. -/
theorem l2NormSq_mul_eAN {R : ℕ} (b : Fin R → ℂ) (t : ℝ) (α : Fin R → ℝ) :
    l2NormSq (fun r => b r * _root_.eAN (t * α r)) = l2NormSq b := by
  unfold l2NormSq
  congr 1; ext r
  rw [norm_mul, eAN_norm, mul_one]

/-- **Half-phase algebraic identity**: the Gram matrix entry times the half-phase
    difference `eAN(θ/2) − eAN(−θ/2)` equals `eAN((2N−1)θ/2) − eAN(−θ/2)`.

    Derived from the telescoping `G · (eAN(θ) − 1) = eAN(Nθ) − 1` and the
    factorization `eAN(θ) − 1 = eAN(θ/2) · (eAN(θ/2) − eAN(−θ/2))`. -/
theorem gramMatrix_mul_half_phase (N : ℕ) {R : ℕ} (α : Fin R → ℝ) (r s : Fin R) :
    gramMatrix N α r s * (_root_.eAN ((α r - α s) / 2) - _root_.eAN (-((α r - α s) / 2))) =
      _root_.eAN ((↑(2 * N) - 1) * (α r - α s) / 2) -
      _root_.eAN (-((α r - α s) / 2)) := by
  set θ := α r - α s
  -- From gramMatrix_mul_eAN_sub_one: G * (eAN(θ) - 1) = eAN(N*θ) - 1
  have htel := gramMatrix_mul_eAN_sub_one N α r s
  -- Key: eAN(θ) - 1 = eAN(θ/2) * (eAN(θ/2) - eAN(-θ/2))
  have hfactor : _root_.eAN θ - 1 =
      _root_.eAN (θ / 2) * (_root_.eAN (θ / 2) - _root_.eAN (-(θ / 2))) := by
    rw [mul_sub, ← _root_.eAN_add, ← _root_.eAN_add,
        show θ / 2 + θ / 2 = θ from by ring,
        show θ / 2 + -(θ / 2) = 0 from by ring, _root_.eAN_zero]
  -- From htel: G * (eAN(θ/2) * (eAN(θ/2) - eAN(-θ/2))) = eAN(N*θ) - 1
  rw [hfactor] at htel
  -- eAN(θ/2)⁻¹ = eAN(-θ/2) since |eAN| = 1
  have hne : _root_.eAN (θ / 2) ≠ 0 := eAN_ne_zero _
  have hinv : (_root_.eAN (θ / 2))⁻¹ = _root_.eAN (-(θ / 2)) := by
    have h1 := eAN_mul_conj (θ / 2)
    rw [conj_eAN] at h1
    -- h1 : eAN(θ/2) * eAN(-(θ/2)) = 1
    rw [eq_comm, inv_eq_of_mul_eq_one_left]
    rw [mul_comm] at h1
    exact h1
  -- Extract G * X from G * (eAN(θ/2) * X) = RHS
  -- htel : G * (eAN(θ/2) * X) = eAN(Nθ) - 1
  -- We need: G * X = eAN(θ/2)⁻¹ * (eAN(Nθ) - 1)
  have hmain : gramMatrix N α r s * (_root_.eAN (θ / 2) - _root_.eAN (-(θ / 2))) =
      (_root_.eAN (θ / 2))⁻¹ * (_root_.eAN (↑N * θ) - 1) := by
    have key : _root_.eAN (θ / 2) *
        (gramMatrix N α r s * (_root_.eAN (θ / 2) - _root_.eAN (-(θ / 2)))) =
        _root_.eAN (θ / 2) *
        ((_root_.eAN (θ / 2))⁻¹ * (_root_.eAN (↑N * θ) - 1)) := by
      rw [mul_inv_cancel_left₀ hne]
      -- htel : G * (eAN(θ/2) * X) = eAN(N*(αr-αs)) - 1
      -- LHS: eAN(θ/2) * (G * X) = G * (eAN(θ/2) * X) by ring = eAN(N*(αr-αs)) - 1
      rw [show _root_.eAN (θ / 2) *
          (gramMatrix N α r s * (_root_.eAN (θ / 2) - _root_.eAN (-(θ / 2)))) =
          gramMatrix N α r s *
          (_root_.eAN (θ / 2) * (_root_.eAN (θ / 2) - _root_.eAN (-(θ / 2)))) from by ring,
          htel]
    exact mul_left_cancel₀ hne key
  rw [hmain, hinv, mul_sub, ← _root_.eAN_add, mul_one]
  congr 1; push_cast; field_simp; ring_nf

/-- **IsSpaced implies sin ≠ 0**: for δ-spaced points with δ > 0 and r ≠ s,
    `sin(π · (α_r − α_s)) ≠ 0`. -/
theorem isSpaced_sin_ne_zero {R : ℕ} (α : Fin R → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hspaced : IsSpaced α δ)
    (r s : Fin R) (hrs : r ≠ s) :
    Real.sin (Real.pi * (α r - α s)) ≠ 0 := by
  have hfrac := hspaced r s hrs
  -- The fract difference is at least δ > 0 in absolute value
  -- Since fracts are in [0,1), the difference is in (-1,1)
  -- We need: α_r - α_s is not an integer
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨n, hn⟩ := hsin
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hαint : α r - α s = (n : ℝ) := by
    have := hn; field_simp at this; linarith
  -- Then Int.fract(α_r) - Int.fract(α_s) = α_r - α_s - (⌊α_r⌋ - ⌊α_s⌋)
  -- which is an integer. But it's in (-1,1), so it's 0.
  have hfr_lt := Int.fract_lt_one (α r)
  have hfs_lt := Int.fract_lt_one (α s)
  have hfr_nn := Int.fract_nonneg (α r)
  have hfs_nn := Int.fract_nonneg (α s)
  have hfrac_bound : |Int.fract (α r) - Int.fract (α s)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  -- fract(α_r) - fract(α_s) = (α_r - α_s) - (⌊α_r⌋ - ⌊α_s⌋) = n - (⌊α_r⌋ - ⌊α_s⌋)
  have hdecomp : Int.fract (α r) - Int.fract (α s) =
      ↑(n - (⌊α r⌋ - ⌊α s⌋)) := by
    simp only [Int.fract]
    have : α r - α s = ↑n := hαint
    push_cast; linarith
  -- An integer in (-1,1) is 0
  rw [hdecomp] at hfrac_bound
  have hm_zero : n - (⌊α r⌋ - ⌊α s⌋) = 0 := by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at hfrac_bound
  -- So fract(α_r) - fract(α_s) = 0
  have hfrac_zero : Int.fract (α r) - Int.fract (α s) = 0 := by
    rw [hdecomp, hm_zero, Int.cast_zero]
  -- But IsSpaced gives |fract diff| ≥ δ > 0
  rw [hfrac_zero, abs_zero] at hfrac
  linarith

/-- **Off-diagonal Gram bilinear bound from csc bilinear bound**:
    CscBilinearBound implies GramOffDiagBilinearBound via the Dirichlet
    kernel half-phase splitting.

    **Proof**: For `θ = α_r − α_s`:

    1. Factor: `G_{r,s} = [eAN((2N−1)θ/2) − eAN(−θ/2)] / [eAN(θ/2) − eAN(−θ/2)]`
       where the denominator is `2i·sin(πθ)`.

    2. Define phase-shifted coefficients:
       `d_r = b_r · eAN((2N−1)·α_r/2)`, `d'_r = b_r · eAN(−α_r/2)`.

    3. Then: `∑_{r≠s} b_r·conj(b_s)·G_{r,s} = (2i)⁻¹ · [Σ_d − Σ_{d'}]`
       where `Σ_c = ∑_{r≠s} c_r·conj(c_s)/sin(πθ)`.

    4. Triangle inequality: `‖sum‖ ≤ (1/2)[‖Σ_d‖ + ‖Σ_{d'}‖]`.

    5. CscBilinearBound on each: `‖Σ_c‖ ≤ (1/δ − 1)·l2NormSq c = (1/δ − 1)·l2NormSq b`.

    6. Combine: `(1/2) · 2 · (1/δ − 1) · l2NormSq b = (1/δ − 1) · l2NormSq b`. -/
theorem csc_bilinear_implies_gram_offdiag
    (hcsc : CscBilinearBound) : GramOffDiagBilinearBound := by
  intro R N α b δ hδ hδ2 _hN hspaced
  -- Define phase-shifted coefficients
  set d : Fin R → ℂ := fun r => b r * _root_.eAN ((↑(2 * N) - 1) / 2 * α r) with hd_def
  set d' : Fin R → ℂ := fun r => b r * _root_.eAN (-(1 : ℝ) / 2 * α r) with hd'_def
  -- Step 5: l2NormSq preservation
  have hl2d : l2NormSq d = l2NormSq b := l2NormSq_mul_eAN b _ α
  have hl2d' : l2NormSq d' = l2NormSq b := l2NormSq_mul_eAN b _ α
  -- Step 5: Apply CscBilinearBound to d and d'
  have hcsc_d := hcsc R α d δ hδ hδ2 hspaced
  have hcsc_d' := hcsc R α d' δ hδ hδ2 hspaced
  rw [hl2d] at hcsc_d
  rw [hl2d'] at hcsc_d'
  -- Step 3: Rewrite the Gram bilinear form
  -- We need: for each pair (r,s) with r ≠ s,
  -- b_r * conj(b_s) * G_{r,s} = (2*I)⁻¹ * [d_r * conj(d_s) - d'_r * conj(d'_s)] / sin(π*θ)
  -- First, establish sin ≠ 0 for all pairs
  have hsin_ne : ∀ r s : Fin R, r ≠ s →
      Real.sin (Real.pi * (α r - α s)) ≠ 0 :=
    fun r s hrs => isSpaced_sin_ne_zero α δ hδ hspaced r s hrs
  -- The key identity for each pair: rewrite using gram identity
  -- b_r * conj(b_s) * G_{r,s} = (2I)⁻¹ * [d_r*conj(d_s) - d'_r*conj(d'_s)] / sin(πθ)
  -- Step: first rewrite the entire double sum using gram identity
  -- Approach: show the FULL sums are equal, by rewriting the Gram sum
  -- using the factorization G = (upper - lower) / (2I sin)
  -- We work at the level of the full sum.
  --
  -- Key: show that ∑_{r≠s} b_r conj(b_s) G_{r,s}
  --   = (2I)⁻¹ * ∑_{r≠s} [d_r conj(d_s) - d'_r conj(d'_s)] / sin(πθ)
  --   = (2I)⁻¹ * [Σ_d - Σ_{d'}]
  -- where Σ_c = ∑_{r≠s} c_r conj(c_s) / sin(πθ)

  -- Helper: d products combine via eAN_add
  have hd_prod : ∀ r s : Fin R,
      d r * starRingEnd ℂ (d s) =
      b r * starRingEnd ℂ (b s) *
        _root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) := by
    intro r s
    simp only [hd_def, map_mul, conj_eAN]
    rw [show (↑(2 * N) - 1) / 2 * (α r - α s) =
        (↑(2 * N) - 1) / 2 * α r + -((↑(2 * N) - 1) / 2 * α s) from by ring,
        _root_.eAN_add]
    ring
  have hd'_prod : ∀ r s : Fin R,
      d' r * starRingEnd ℂ (d' s) =
      b r * starRingEnd ℂ (b s) *
        _root_.eAN (-(1 : ℝ) / 2 * (α r - α s)) := by
    intro r s
    simp only [hd'_def, map_mul, conj_eAN]
    rw [show -(1 : ℝ) / 2 * (α r - α s) =
        -(1 : ℝ) / 2 * α r + -(-(1 : ℝ) / 2 * α s) from by ring,
        _root_.eAN_add]
    ring

  -- Phase identity: for each pair, the difference of phase-shifted terms
  -- gives the Gram numerator times 2I·sin
  have hpair_num : ∀ r s : Fin R, r ≠ s →
      d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s) =
      b r * starRingEnd ℂ (b s) *
        (_root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) -
         _root_.eAN (-(1 : ℝ) / 2 * (α r - α s))) := by
    intro r s _
    rw [hd_prod, hd'_prod]
    ring

  -- Key numerator identity: the eAN difference equals G * 2I*sin
  have hnum_eq : ∀ r s : Fin R,
      _root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) -
      _root_.eAN (-(1 : ℝ) / 2 * (α r - α s)) =
      gramMatrix N α r s *
        (_root_.eAN ((α r - α s) / 2) - _root_.eAN (-((α r - α s) / 2))) := by
    intro r s
    have h := gramMatrix_mul_half_phase N α r s
    -- h : G * (eAN((αr-αs)/2) - eAN(-((αr-αs)/2))) = eAN((2N-1)*(αr-αs)/2) - eAN(-((αr-αs)/2))
    -- rewrite to match our LHS
    have hlhs : _root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) =
        _root_.eAN ((↑(2 * N) - 1) * (α r - α s) / 2) := by congr 1; ring
    have hrhs : _root_.eAN (-(1 : ℝ) / 2 * (α r - α s)) =
        _root_.eAN (-((α r - α s) / 2)) := by congr 1; ring
    rw [hlhs, hrhs]
    exact h.symm

  -- Phase difference = 2I * sin
  -- We use: ‖eAN(θ/2) - eAN(-θ/2)‖ = 2|sin(πθ)| (from norm_eAN_sub_one with x = θ)
  -- but we need the exact complex identity, not just the norm.
  -- Use the existing identity: eAN(x) - 1 = eAN(x/2) * (eAN(x/2) - eAN(-x/2))
  -- and ‖eAN(x) - 1‖ = 2|sin(πx)|.
  -- For the exact identity: eAN(θ/2) - eAN(-θ/2) = 2I*sin(πθ):
  -- This follows from eAN(x) = exp(2πix), so eAN(θ/2) = exp(iπθ).
  -- exp(iα) - exp(-iα) = 2i*sin(α), applied with α = πθ.
  have hphase_eq : ∀ r s : Fin R,
      _root_.eAN ((α r - α s) / 2) - _root_.eAN (-((α r - α s) / 2)) =
      2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s))) := by
    intro r s
    set θ := α r - α s
    -- eAN(θ/2) = exp(2πi·θ/2) = exp(πiθ), eAN(-θ/2) = exp(-πiθ)
    -- exp(πiθ) - exp(-πiθ) = 2i·sin(πθ)
    have h1 : _root_.eAN (θ / 2) = Complex.exp (↑(Real.pi * θ) * Complex.I) := by
      unfold _root_.eAN; congr 1; push_cast; ring
    have h2 : _root_.eAN (-(θ / 2)) = Complex.exp (↑(-(Real.pi * θ)) * Complex.I) := by
      unfold _root_.eAN; congr 1; push_cast; ring
    rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.sin_neg, Complex.cos_neg, ← Complex.ofReal_sin]
    ring

  -- Combine: for r ≠ s, G_{r,s} = (d_prod - d'_prod) / (b_r conj(b_s) * 2I * sin)
  -- Actually we need: b conj(b) * G = (d_prod - d'_prod) / (2I * sin)
  have hpair : ∀ r s : Fin R, r ≠ s →
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
      (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) := by
    intro r s hrs
    have hsin_ne_rs := hsin_ne r s hrs
    have h2Isin_ne : 2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s))) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hsin_ne_rs)
    rw [hpair_num r s hrs, hnum_eq, hphase_eq, eq_div_iff h2Isin_ne]
    ring
  -- Step 3: Rewrite the full sum using hpair
  have hsum_eq :
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s hs
    exact hpair r s ((Finset.mem_filter.mp hs).2).symm
  rw [hsum_eq]
  -- Step 3b: Split each term: (a - b) / (c * d) = a/(c*d) - b/(c*d)
  -- Then factor out (2I)⁻¹: a/(2I*sin) = (2I)⁻¹ * a/sin
  -- Rewrite the sum to factor out (2I)⁻¹
  have hterm_split : ∀ r s : Fin R, r ≠ s →
      (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
      (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
        (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
      (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
        (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
    intro r s hrs
    have hsin_ne_rs := hsin_ne r s hrs
    have hsin_C_ne : (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsin_ne_rs
    have h2I_ne : (2 : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero two_ne_zero Complex.I_ne_zero
    field_simp
  have hsum_split :
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
      (2 * Complex.I)⁻¹ *
        ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
      (2 * Complex.I)⁻¹ *
        ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
    -- Rewrite each inner term, then split the sums
    have hstep : ∀ r : Fin R,
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
          (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          ((2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
          (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) := by
      intro r
      apply Finset.sum_congr rfl
      intro s hs
      exact hterm_split r s ((Finset.mem_filter.mp hs).2).symm
    -- Direct proof: rewrite each inner term, split inner sums, factor constants
    -- Step 1: rewrite inner terms
    have hLHS :
        ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
          (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
        ∑ r, ((∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) -
        (∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ))) := by
      apply Finset.sum_congr rfl; intro r _
      rw [hstep r, Finset.sum_sub_distrib]
    rw [hLHS, Finset.sum_sub_distrib]
    -- Each side: factor (2I)⁻¹ out of both inner and outer sums
    -- LHS₁ = ∑ x, ∑ s, (2I)⁻¹ * d x * conj(d s) / sin
    --       = ∑ x, (2I)⁻¹ * ∑ s, d x * conj(d s) / sin   (by mul_sum at inner level)
    --       = (2I)⁻¹ * ∑ x, ∑ s, d x * conj(d s) / sin   (by mul_sum at outer level)
    -- Similarly for LHS₂ with d'.
    -- First, at the inner level, rewrite each summand:
    --   (2I)⁻¹ * d x * conj(d s) / sin = (2I)⁻¹ * (d x * conj(d s) / sin)
    have hinner_d : ∀ r : Fin R,
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
        (2 * Complex.I)⁻¹ * ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
      intro r
      conv_lhs =>
        arg 2; ext s
        rw [show (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
            (2 * Complex.I)⁻¹ * (d r * starRingEnd ℂ (d s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) from by ring]
      rw [← Finset.mul_sum]
    have hinner_d' : ∀ r : Fin R,
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
        (2 * Complex.I)⁻¹ * ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
      intro r
      conv_lhs =>
        arg 2; ext s
        rw [show (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
            (2 * Complex.I)⁻¹ * (d' r * starRingEnd ℂ (d' s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) from by ring]
      rw [← Finset.mul_sum]
    simp_rw [hinner_d, hinner_d', ← Finset.mul_sum]
  rw [hsum_split]
  -- Step 4: Take norms, triangle inequality
  -- Goal: ‖(2I)⁻¹ * A - (2I)⁻¹ * B‖ ≤ (1/δ - 1) * l2NormSq b
  -- Factor: (2I)⁻¹ * A - (2I)⁻¹ * B = (2I)⁻¹ * (A - B)
  rw [show (2 * Complex.I)⁻¹ *
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
      (2 * Complex.I)⁻¹ *
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
      (2 * Complex.I)⁻¹ *
      (∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
       ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ))
    from by ring]
  have h2I_norm : ‖(2 * Complex.I : ℂ)⁻¹‖ = 1/2 := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I]
    norm_num
  calc ‖(2 * Complex.I)⁻¹ *
        (∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
         ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ))‖
      ≤ ‖(2 * Complex.I : ℂ)⁻¹‖ *
        ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
         ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖ :=
        norm_mul_le _ _
    _ ≤ ‖(2 * Complex.I : ℂ)⁻¹‖ *
        (‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖ +
         ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖) := by
        apply mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ (1/2) * ((1/δ - 1) * l2NormSq b + (1/δ - 1) * l2NormSq b) := by
        rw [h2I_norm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hcsc_d hcsc_d'
    _ = (1/δ - 1) * l2NormSq b := by ring

-- ==========================================
-- Section: HilbertInequality → CscBilinearBoundCircular
-- (product-index trick + Cesaro convergence)
-- ==========================================

/-- **Hilbert bound on the lifted system**: applying HilbertInequality to the
    lifted points `liftedPtsA` and coefficients `liftedCoeffs` gives the bound
    `(π/δ) · (2K+1) · l2NormSq c` on the lifted bilinear form, provided the
    points α are circularly δ-spaced.

    This is the core application of HilbertInequality in the product-index trick.
    The reindexing via `finProdFinEquiv` translates between `Fin R × Fin (2K+1)`
    and `Fin (R · (2K+1))`. -/
private theorem hilbert_lifted_bound (hHI : HilbertInequality)
    {R : ℕ} (α : Fin R → ℝ) (c : Fin R → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hcirc : IsCircularSpaced α δ) (K : ℕ) :
    ‖∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
      liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
      (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ)‖ ≤
      Real.pi / δ * ((2 * ↑K + 1) * l2NormSq c) := by
  -- Reindex via finProdFinEquiv
  set M := R * (2 * K + 1)
  set e := finProdFinEquiv (m := R) (n := 2 * K + 1)
  set pts' : Fin M → ℝ := fun i => liftedPtsA α K (e.symm i)
  set z' : Fin M → ℂ := fun i => liftedCoeffs c K (e.symm i)
  -- Apply HilbertInequality
  have hsep' : ∀ r s : Fin M, r ≠ s → δ ≤ |pts' r - pts' s| := by
    intro r s hrs
    have hpq : e.symm r ≠ e.symm s := by
      intro h; exact hrs (e.symm.injective h ▸ rfl)
    exact liftedPtsA_sep_all α K hcirc hδ hδ2 _ _ hpq
  have hH := hHI M pts' z' δ hδ hsep'
  -- The LHS over Fin M equals the LHS over the product type (by reindexing)
  -- Key: ∑_{i : Fin M} f(i) = ∑_{p : Fin R × Fin (2K+1)} f(e p)
  -- Show the product-type sum equals the Fin M sum
  -- Use a direct proof: both sums are equal by Finset.sum_equiv
  have hLHS_eq :
      ∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
        liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
        (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ) =
      ∑ r : Fin M, ∑ s ∈ Finset.univ.filter (· ≠ r),
        z' r * starRingEnd ℂ (z' s) / (↑(pts' r - pts' s) : ℂ) := by
    -- Outer: ∑_{p} f(p) = ∑_{r : Fin M} f(e.symm r) via Finset.sum_equiv e
    -- Outer: use Fintype.sum_equiv
    apply Fintype.sum_equiv e
    intro p
    -- Inner: reindex the filtered sum
    apply Finset.sum_nbij' e e.symm
    · intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun h => (Finset.mem_filter.mp hq).2 (e.injective h)⟩
    · intro s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun h => (Finset.mem_filter.mp hs).2 (by rw [← h]; simp)⟩
    · intro q _; simp
    · intro s _; simp
    · intro q _; simp only [pts', z', Equiv.symm_apply_apply]
  -- Rewrite the l2NormSq
  have hl2 : ∑ r : Fin M, ‖z' r‖ ^ 2 = (2 * ↑K + 1) * l2NormSq c := by
    rw [show ∑ r : Fin M, ‖z' r‖ ^ 2 =
        ∑ p : Fin R × Fin (2 * K + 1), ‖liftedCoeffs c K p‖ ^ 2 from by
      symm; exact Fintype.sum_equiv e _ _ (fun p => by simp [z'])]
    exact liftedCoeffs_l2NormSq c K
  rw [hl2] at hH; rw [hLHS_eq]; exact hH

/-- **Same-r antisymmetry for the lifted bilinear form**: for fixed r, the sum
    `∑_{j≠l} (-1)^(j+l) / ((j:ℝ) - l)` vanishes by the j↔l involution.
    Specifically, each pair {j,l} contributes `(-1)^(j+l)/(j-l) + (-1)^(j+l)/(l-j) = 0`. -/
private theorem same_r_antisymmetry {K : ℕ} (α_r : ℝ) (c_val : ℂ) :
    ∑ j : Fin (2 * K + 1), ∑ l ∈ Finset.univ.filter (· ≠ j),
      ((-1 : ℂ) ^ (j : ℕ) * c_val) * starRingEnd ℂ ((-1 : ℂ) ^ (l : ℕ) * c_val) /
      (↑((α_r + (↑(j : ℕ) - ↑K)) - (α_r + (↑(l : ℕ) - ↑K))) : ℂ) = 0 := by
  -- Simplify: α_r cancels, leaving (j - l) in denominator
  have hsimp : ∀ j l : Fin (2 * K + 1),
      (↑((α_r + (↑(j : ℕ) - ↑K)) - (α_r + (↑(l : ℕ) - ↑K))) : ℂ) =
      (↑((↑(j : ℕ) : ℝ) - ↑(l : ℕ)) : ℂ) := by
    intro j l; push_cast; ring_nf
  simp_rw [hsimp]
  -- We show S = -S by swapping j ↔ l, hence S = 0.
  set N := 2 * K + 1
  -- Abbreviate the summand
  set g : Fin N → Fin N → ℂ := fun j l =>
    ((-1 : ℂ) ^ (j : ℕ) * c_val) * starRingEnd ℂ ((-1 : ℂ) ^ (l : ℕ) * c_val) /
    (↑((↑(j : ℕ) : ℝ) - ↑(l : ℕ)) : ℂ)
  -- Transposition negates the summand: g(l,j) = -g(j,l)
  have hswap : ∀ j l : Fin N, g l j = -g j l := by
    intro j l
    simp only [g]
    have hnum : ((-1 : ℂ) ^ (l : ℕ) * c_val) * starRingEnd ℂ ((-1 : ℂ) ^ (j : ℕ) * c_val) =
        ((-1 : ℂ) ^ (j : ℕ) * c_val) * starRingEnd ℂ ((-1 : ℂ) ^ (l : ℕ) * c_val) := by
      simp only [map_mul, map_pow, map_neg, map_one]; ring
    have hden : (↑((↑(l : ℕ) : ℝ) - ↑(j : ℕ)) : ℂ) = -(↑((↑(j : ℕ) : ℝ) - ↑(l : ℕ)) : ℂ) := by
      push_cast; ring
    rw [hnum, hden, div_neg]
  -- The sum S = ∑ j, ∑ l ∈ filter (· ≠ j), g j l
  -- Swapping j and l: S = ∑ l, ∑ j ∈ filter (· ≠ l), g l j
  --                     = ∑ l, ∑ j ∈ filter (· ≠ l), -g j l
  --                     = -S  (by renaming l→j, j→l)
  -- Hence 2S = 0, so S = 0.
  -- Show S + S = 0 where S = ∑ j, ∑ l ∈ filter (· ≠ j), g j l.
  -- By sum_comm', S = ∑ l, ∑ j ∈ filter (· ≠ l), g j l.
  -- Then S + S = ∑ j, ∑ l, (g j l + g l j) = 0 since g l j = -g j l.
  have hcomm : ∀ f : Fin N → Fin N → ℂ,
      ∑ j : Fin N, ∑ l ∈ Finset.univ.filter (· ≠ j), f j l =
      ∑ l : Fin N, ∑ j ∈ Finset.univ.filter (· ≠ l), f j l :=
    fun f => Finset.sum_comm' (h := by
      intro j l; constructor
      · intro ⟨_, hl⟩; exact ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ j, (Finset.mem_filter.mp hl).2.symm⟩, Finset.mem_univ l⟩
      · intro ⟨hj, _⟩; exact ⟨Finset.mem_univ j, Finset.mem_filter.mpr
          ⟨Finset.mem_univ l, (Finset.mem_filter.mp hj).2.symm⟩⟩)
  -- S + comm'd = ∑ j, ∑ l ∈ filter, (g j l + g l j) = 0
  have hSS : (∑ j : Fin N, ∑ l ∈ Finset.univ.filter (· ≠ j), g j l) +
      (∑ j : Fin N, ∑ l ∈ Finset.univ.filter (· ≠ j), g j l) = 0 := by
    nth_rw 2 [hcomm g]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [hswap j l, add_neg_cancel]
  have h2m : (2 : ℂ) * (∑ j : Fin N, ∑ l ∈ Finset.univ.filter (· ≠ j), g j l) = 0 := by
    rw [two_mul]; exact hSS
  exact (mul_eq_zero.mp h2m).resolve_left two_ne_zero

-- The full product-index trick: HilbertInequality → CscBilinearBoundCircular
-- uses:
--   (a) hilbert_lifted_bound: Hilbert bound on lifted system (PROVED above)
--   (b) same_r_antisymmetry: same-r terms vanish (PROVED above)
--   (c) Cross-r Cesaro convergence: double sum / (2K+1) → pi/sin(pi*theta)
--   (d) Limit passage: norm of limit ≤ lim sup of norms

/-- **Cross-r Cesaro convergence**: the key identity and limit that connects
    the lifted bilinear form to the csc bilinear form.

    For circularly delta-spaced alpha and K large, the cross-r contribution
    of the lifted bilinear form, divided by (2K+1), converges to the csc
    bilinear form. Combined with the Hilbert bound on the lifted form and
    same_r_antisymmetry, this gives CscBilinearBoundCircular.

    The proof requires:
    1. Decomposing the lifted form into same-r (= 0) and cross-r parts
    2. The Fejer kernel identity: double sum = Cesaro average of ML partial sums
    3. Cesaro convergence of the ML series via `mittag_leffler_csc_proved`
    4. Limit passage on norms -/
def CrossRCesaroConvergence : Prop :=
  ∀ (R : ℕ) (α : Fin R → ℝ) (c : Fin R → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 →
    IsCircularSpaced α δ →
    (∀ K : ℕ,
      ‖∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
        liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
        (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ)‖ ≤
        Real.pi / δ * ((2 * ↑K + 1) * l2NormSq c)) →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      c r * starRingEnd ℂ (c s) /
      (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖ ≤ (1/δ) * l2NormSq c

/-- **HilbertInequality + CrossRCesaroConvergence → CscBilinearBoundCircular**:
    composing the Hilbert bound on lifted points with the Cesaro convergence
    step gives the circular csc bilinear bound. -/
theorem hilbert_csc_circular_of_cesaro (hHI : HilbertInequality)
    (hces : CrossRCesaroConvergence) : CscBilinearBoundCircular := by
  intro R α c δ hδ hδ2 hcirc
  exact hces R α c δ hδ hδ2 hcirc (fun K => hilbert_lifted_bound hHI α c hδ hδ2 hcirc K)

-- ==========================================
-- Section: Proof of CrossRCesaroConvergence
-- ==========================================

/-- **Cesaro convergence of ML partial sums at a subsequence**: if ML partial sums
    converge to L, then the Cesaro means along the subsequence n = 2K+1
    also converge to L. -/
private theorem ml_cesaro_at_odd {θ L : ℝ} (hML : Filter.Tendsto
    (fun M : ℕ => ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      (-1 : ℝ) ^ m.natAbs / (θ + ↑m)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun K : ℕ => ((2 * (K : ℝ) + 1)⁻¹ *
      ∑ M ∈ Finset.range (2 * K + 1),
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          (-1 : ℝ) ^ m.natAbs / (θ + ↑m)))
    Filter.atTop (nhds L) := by
  have hces := hML.cesaro
  have h_subseq : Filter.Tendsto (fun K : ℕ => 2 * K + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun n => ⟨n, fun K hK => by omega⟩)
  have hcomp := hces.comp h_subseq
  convert hcomp using 1
  ext K; simp only [Function.comp_def]; congr 1; push_cast; ring

/-- **Fejér sum identity**: The double sum `∑_{j,l < N+1} f((j:ℤ) - l)` equals the
    sum of partial sums `∑_{M ≤ N} ∑_{m ∈ Icc(-M,M)} f(m)`.

    Proved by induction: `T_{N+1} = T_N + S_{N+1}` where `S_M = ∑_{m ∈ Icc(-M,M)} f(m)`. -/
private theorem fejer_sum_eq_cesaro_sum' (f : ℤ → ℝ) : ∀ N : ℕ,
    ∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1), f ((j : ℤ) - l) =
    ∑ M ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m := by
  intro N
  induction N with
  | zero => simp [Finset.range_one, Finset.Icc_self]
  | succ N ih =>
    -- Prove T_{N+1} = T_N + S_{N+1} on both sides
    -- RHS decomposition
    have hRHS : ∑ M ∈ Finset.range (N + 2), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m =
        (∑ m ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ), f m) +
        ∑ M ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f m := by
      rw [show (N : ℕ) + 2 = (N + 1) + 1 from by omega, Finset.range_add_one (n := N + 1)]
      rw [Finset.sum_insert (by simp : N + 1 ∉ Finset.range (N + 1))]; push_cast; ring
    -- LHS decomposition
    have hLHS : ∑ j ∈ Finset.range (N + 2), ∑ l ∈ Finset.range (N + 2), f ((j : ℤ) - l) =
        (∑ l ∈ Finset.range (N + 1), f ((N + 1 : ℤ) - l) +
         ∑ j ∈ Finset.range (N + 1), f ((j : ℤ) - (N + 1)) +
         f 0) +
        ∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1), f ((j : ℤ) - l) := by
      rw [show (N : ℕ) + 2 = (N + 1) + 1 from by omega, Finset.range_add_one (n := N + 1)]
      rw [Finset.sum_insert (by simp : N + 1 ∉ Finset.range (N + 1))]
      simp_rw [Finset.sum_insert (by simp : N + 1 ∉ Finset.range (N + 1))]
      push_cast; rw [show ((N : ℤ) + 1 - (↑N + 1)) = 0 from sub_self _]
      simp_rw [Finset.sum_add_distrib]; ring
    rw [show N + 1 + 1 = N + 2 from by omega, hLHS, hRHS, ih]
    -- Suffices: new terms = S_{N+1}
    congr 1
    -- Decompose S_{N+1} = Icc(-(N+1), N+1) into negative + {0} + positive
    have hIcc : Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ) =
        Finset.Icc (-(N + 1 : ℤ)) (-1) ∪ ({0} ∪ Finset.Icc (1 : ℤ) (N + 1)) := by
      ext m; simp [Finset.mem_Icc]; omega
    have hd1 : Disjoint (Finset.Icc (-(N + 1 : ℤ)) (-1))
        ({0} ∪ Finset.Icc (1 : ℤ) (N + 1)) := by
      apply Finset.disjoint_left.mpr; intro m hm hm'
      simp [Finset.mem_Icc] at hm hm'; omega
    have hd2 : Disjoint ({0} : Finset ℤ) (Finset.Icc (1 : ℤ) (N + 1)) := by
      apply Finset.disjoint_left.mpr; intro m hm hm'
      simp at hm; simp [Finset.mem_Icc] at hm'; omega
    rw [hIcc, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
    -- Positive part: Icc(1, N+1) ↔ range(N+1) via reversal l ↦ N+1-l
    have hpos : ∑ m ∈ Finset.Icc (1 : ℤ) (↑N + 1), f m =
        ∑ l ∈ Finset.range (N + 1), f ((↑N + 1 : ℤ) - ↑l) := by
      symm
      apply Finset.sum_nbij' (fun (l : ℕ) => (↑N + 1 : ℤ) - ↑l)
        (fun (m : ℤ) => (↑N + 1 - m).toNat)
      · intro l hl
        simp only [Finset.mem_range] at hl
        simp only [Finset.mem_Icc]; constructor <;> omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        simp only [Finset.mem_range]; omega
      · intro l hl
        simp only [Finset.mem_range] at hl; omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm; omega
      · intro l _hl; rfl
    -- Negative part: Icc(-(N+1), -1) ↔ range(N+1) via j ↦ j - (N+1)
    have hneg : ∑ m ∈ Finset.Icc (-(↑N + 1 : ℤ)) (-1), f m =
        ∑ j ∈ Finset.range (N + 1), f ((↑j : ℤ) - (↑N + 1)) := by
      symm
      apply Finset.sum_nbij' (fun (j : ℕ) => (↑j : ℤ) - (↑N + 1))
        (fun (m : ℤ) => (m + (↑N + 1)).toNat)
      · intro j hj
        simp only [Finset.mem_range] at hj
        simp only [Finset.mem_Icc]; constructor <;> omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        simp only [Finset.mem_range]; omega
      · intro j hj
        simp only [Finset.mem_range] at hj; omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm; omega
      · intro j _hj; rfl
    rw [hpos, hneg]; ring

/-- **Parity lemma**: `(-1)^(j+l) = (-1)^|(j:ℤ) - l|` for natural numbers j, l. -/
private theorem neg_one_pow_add_eq_natAbs_sub (j l : ℕ) :
    (-1 : ℝ) ^ (j + l) = (-1 : ℝ) ^ ((j : ℤ) - ↑l).natAbs := by
  -- Use neg_one_pow_congr: suffices Even (j + l) ↔ Even natAbs((j:ℤ) - l)
  exact neg_one_pow_congr (by
    rw [Int.natAbs_even, Int.even_sub, Int.even_coe_nat, Int.even_coe_nat, Nat.even_add])

/-- **ML Cesaro convergence (real)**: the Cesaro mean of ML partial sums
    converges to `π / sin(πθ)` for non-integer θ, along the full sequence. -/
private theorem ml_cesaro_convergence (θ : ℝ) (hθ : ∀ n : ℤ, θ + ↑n ≠ 0) :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ *
      ∑ M ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (-1 : ℝ) ^ m.natAbs / (θ + ↑m))
    Filter.atTop (nhds (Real.pi / Real.sin (Real.pi * θ))) := by
  -- ML partial sums converge to π/sin(πθ)
  have hML := mittag_leffler_csc_proved θ hθ
  -- Cesaro means of convergent sequence converge to same limit
  have hces := hML.cesaro
  have h_shift : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun n => ⟨n, fun K hK => by omega⟩)
  have hcomp := hces.comp h_shift
  -- hcomp uses (↑(N+1))⁻¹, we need (↑N + 1)⁻¹. Convert:
  refine (hcomp.congr ?_)
  intro N; simp only [Function.comp_def]; congr 1; push_cast; ring

/-- **Per-pair Cesaro limit (real)**: for fixed θ ∉ ℤ, the normalized double sum
    `(N+1)⁻¹ · ∑_{j,l < N+1} (-1)^(j+l) / (θ + (j-l))` converges to `π/sin(πθ)`. -/
private theorem per_pair_cesaro_limit (θ : ℝ) (hθ : ∀ n : ℤ, θ + ↑n ≠ 0) :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ *
      ∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
        (-1 : ℝ) ^ (j + l) / (θ + ↑((j : ℤ) - ↑l)))
    Filter.atTop (nhds (Real.pi / Real.sin (Real.pi * θ))) := by
  -- Rewrite using Fejer identity + parity
  have hfej : ∀ N : ℕ,
      ∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
        (-1 : ℝ) ^ (j + l) / (θ + ↑((j : ℤ) - ↑l)) =
      ∑ M ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (-1 : ℝ) ^ m.natAbs / (θ + ↑m) := by
    intro N
    have hbase := fejer_sum_eq_cesaro_sum' (fun m => (-1 : ℝ) ^ m.natAbs / (θ + ↑m)) N
    rw [← hbase]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    congr 1
    exact neg_one_pow_add_eq_natAbs_sub j l
  simp_rw [hfej]
  exact ml_cesaro_convergence θ hθ

/-- **Cross-r Cesaro convergence is a theorem**: the csc bilinear form norm is bounded
    by (1/δ) · l2NormSq c, given the Hilbert bound on all lifted systems.

    Proof strategy:
    1. ∀ K, ‖F(K)‖ ≤ (π/δ)(2K+1)L (hypothesis)
    2. F(K) = same_r(K) + cross_r(K), same_r = 0 (antisymmetry)
    3. cross_r(K) / (2K+1) → π · G (Fejér + ML Cesaro)
    4. ‖cross_r(K)‖ / (2K+1) ≤ (π/δ)L, limit gives π·‖G‖ ≤ (π/δ)L
    5. ‖G‖ ≤ L/δ

    The decomposition (step 2) and convergence (step 3) are proved inline. -/
theorem cross_r_cesaro_convergence_proved : CrossRCesaroConvergence := by
  intro R α c δ hδ hδ2 hcirc hK_bound
  -- The bound holds at each K; we pass to the limit using le_of_tendsto'.
  -- Set up notation
  set L := l2NormSq c
  set G := ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
    c r * starRingEnd ℂ (c s) /
    (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)
  -- Non-integer condition for α differences
  have hθ_ne : ∀ r s : Fin R, r ≠ s → ∀ n : ℤ, (α r - α s) + ↑n ≠ 0 := by
    intro r s hrs n h
    have hcs := hcirc r s hrs
    have heq : α r - α s = -(n : ℝ) := by linarith
    rw [heq, show -(n : ℝ) = ((-n : ℤ) : ℝ) from by push_cast; ring,
        round_intCast, sub_self, abs_zero] at hcs
    linarith
  -- Step A: the norm bound divided by (2K+1) gives a uniform bound
  have hA : ∀ K : ℕ,
      ‖∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
        liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
        (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ)‖ /
      (2 * ↑K + 1) ≤ Real.pi / δ * L := by
    intro K
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ↑K + 1)]
    have := hK_bound K; linarith
  -- The conclusion follows from the Hilbert bound via Cesaro convergence.
  -- For now we establish this via the key convergence + limit passage.
  -- Step B: convergence of F(K)/(2K+1) to π·G (the hard combinatorial step)
  -- Step C: le_of_tendsto' gives π·‖G‖ ≤ (π/δ)·L, hence ‖G‖ ≤ L/δ
  -- This is the product-index trick of Iwaniec-Kowalski (Corollaries 7.9-7.10).

  -- We use le_of_tendsto' with the convergent sequence norm(F(K))/(2K+1)
  -- But we need the norm of the limit = limit of norm (by continuity of norm).

  -- Alternative: use the bound at each K directly to get the result.
  -- The key identity: for the lifted form with the ACTUAL α (not fract):
  -- the same-r terms vanish and the cross-r terms factor as
  -- ∑_{r≠s} c_r conj(c_s) · [Cesaro partial sum of ML series for (α_r - α_s)]

  -- For a cleaner proof, we establish this as a consequence of
  -- le_of_tendsto' applied to the sequence
  --   a_K = ‖F(K)/(2K+1)‖ ≤ (π/δ)L (by hA)
  -- and convergence F(K)/(2K+1) → π·G.

  -- We need Filter.Tendsto (fun K => F(K) / (2K+1)) atTop (nhds (π * G))
  -- and then le_of_tendsto' for norms.

  -- This requires the full decomposition which is a substantial proof.
  -- We leave the technical steps as intermediate lemmas:

  -- Key convergence claim:
  suffices hconv : Filter.Tendsto (fun K : ℕ =>
      (2 * (K : ℝ) + 1)⁻¹ •
      ∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
        liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
        (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ))
    Filter.atTop (nhds (↑Real.pi * G)) by
    -- From convergence + pointwise bound, derive the conclusion
    have hnorm_conv : Filter.Tendsto (fun K : ℕ =>
        ‖(2 * (K : ℝ) + 1)⁻¹ •
        ∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
          liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
          (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ)‖)
      Filter.atTop (nhds ‖↑Real.pi * G‖) :=
      (continuous_norm.tendsto _).comp hconv
    -- Pointwise bound: ‖(2K+1)⁻¹ • F(K)‖ ≤ (π/δ)L
    have hptwse : ∀ K : ℕ,
        ‖(2 * (K : ℝ) + 1)⁻¹ •
        ∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
          liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
          (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ)‖ ≤ Real.pi / δ * L := by
      intro K
      rw [Complex.real_smul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * (K : ℝ) + 1)⁻¹)]
      rw [show (2 * (K : ℝ) + 1)⁻¹ * ‖_‖ = ‖_‖ / (2 * (K : ℝ) + 1) from by
        rw [inv_mul_eq_div]]
      exact hA K
    -- By le_of_tendsto': limit of norms ≤ bound
    have hle : ‖↑Real.pi * G‖ ≤ Real.pi / δ * L :=
      le_of_tendsto' hnorm_conv hptwse
    -- ‖π * G‖ = π * ‖G‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_nonneg] at hle
    -- π * ‖G‖ ≤ (π/δ) * L, divide by π
    have hpi := Real.pi_pos
    have hkey : Real.pi * ‖G‖ ≤ Real.pi * (1 / δ * L) := by
      calc Real.pi * ‖G‖ ≤ Real.pi / δ * L := hle
        _ = Real.pi * (1 / δ * L) := by ring
    exact by nlinarith
  -- Now prove the convergence claim: F(K)/(2K+1) → π * G
  -- This is the core of the product-index trick.
  -- The proof decomposes F(K) = same_r(K) + cross_r(K), shows same_r = 0
  -- by same_r_antisymmetry, and shows cross_r(K)/(2K+1) → π·G
  -- by Fejér identity + ML Cesaro convergence.

  -- Step 1: Decompose F(K) by expanding the product-type sum
  -- ∑_{(r,j)} ∑_{(s,l) ≠ (r,j)} = ∑_r ∑_j [∑_{l≠j} same_r_term + ∑_{s≠r} ∑_l cross_term]
  -- = ∑_r same_r(r,K) + ∑_r ∑_{s≠r} ∑_j ∑_l cross_term
  -- = 0 + cross_r(K)

  -- Define per-pair double sum (complex version)
  set D : Fin R → Fin R → ℕ → ℂ := fun r s K =>
    ∑ j : Fin (2 * K + 1), ∑ l : Fin (2 * K + 1),
      liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K (s, l)) /
      (↑(liftedPtsA α K (r, j) - liftedPtsA α K (s, l)) : ℂ)

  -- The cross-r contribution
  set CR : ℕ → ℂ := fun K =>
    ∑ r : Fin R, ∑ s ∈ Finset.univ.filter (· ≠ r), D r s K

  -- Step 2: Show F(K) = ∑_r same_r(r,K) + CR(K)
  -- and same_r = 0 by same_r_antisymmetry
  have hF_eq_CR : ∀ K : ℕ,
      ∑ p : Fin R × Fin (2 * K + 1), ∑ q ∈ Finset.univ.filter (· ≠ p),
        liftedCoeffs c K p * starRingEnd ℂ (liftedCoeffs c K q) /
        (↑(liftedPtsA α K p - liftedPtsA α K q) : ℂ) = CR K := by
    intro K
    -- Expand product type sums
    simp only [CR, D]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro r _
    -- For each r, the inner sum splits into same-r (= 0) + cross-r.
    -- Step: for each j, split {(s,l) ≠ (r,j)} = {(r,l) | l ≠ j} ∪ {(s,l) | s ≠ r}
    -- Then ∑_j (same_r + cross_r) = 0 + ∑_{s≠r} ∑_j ∑_l

    -- Split filter: (s,l) ≠ (r,j) ↔ (s = r ∧ l ≠ j) ∨ (s ≠ r)
    have hfilt_eq : ∀ j : Fin (2 * K + 1),
        Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q ≠ (r, j)) =
        (Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 = r ∧ q.2 ≠ j)) ∪
        (Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 ≠ r)) := by
      intro j; ext ⟨s, l⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Prod.mk.injEq, ne_eq, not_and_or]; tauto

    have hfilt_disj : ∀ j : Fin (2 * K + 1), Disjoint
        (Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 = r ∧ q.2 ≠ j))
        (Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 ≠ r)) := by
      intro j; apply Finset.disjoint_filter.mpr
      intro ⟨s, l⟩ _ ⟨hs, _⟩ hs2; exact hs2 (hs ▸ rfl)

    -- Split each inner sum
    have hinner_split : ∀ j : Fin (2 * K + 1),
        ∑ q ∈ Finset.univ.filter (· ≠ (r, j)),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K q) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K q) : ℂ) =
        (∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 = r ∧ q.2 ≠ j),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K q) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K q) : ℂ)) +
        (∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 ≠ r),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K q) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K q) : ℂ)) := by
      intro j; rw [hfilt_eq j, Finset.sum_union (hfilt_disj j)]
    simp_rw [hinner_split, Finset.sum_add_distrib]

    -- The same-r part: ∑_j ∑_{q.1=r, q.2≠j} term = same_r_antisymmetry
    -- Rewrite: q = (r, q.2) when q.1 = r
    have h_same_reindex : ∀ j : Fin (2 * K + 1),
        ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 = r ∧ q.2 ≠ j),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K q) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K q) : ℂ) =
        ∑ l ∈ Finset.univ.filter (· ≠ j),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K (r, l)) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K (r, l)) : ℂ) := by
      intro j
      apply Finset.sum_nbij' (fun q : Fin R × Fin (2 * K + 1) => q.2) (fun l => (r, l))
      · intro ⟨s, l⟩ hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq.2
      · intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
        exact hl
      · intro ⟨s, l⟩ hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact Prod.ext hq.1.symm rfl
      · intro l _hl; rfl
      · intro ⟨s, l⟩ hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [hq.1]
    simp_rw [h_same_reindex]

    have h_same_r_zero :
        ∑ j : Fin (2 * K + 1), ∑ l ∈ Finset.univ.filter (· ≠ j),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K (r, l)) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K (r, l)) : ℂ) = 0 :=
      same_r_antisymmetry (α r) (c r)
    rw [h_same_r_zero, zero_add]

    -- The cross-r part: ∑_j ∑_{q.1≠r} term = ∑_{s≠r} ∑_j ∑_l term
    -- Rewrite the filter as a product set
    have h_cross_reindex : ∀ j : Fin (2 * K + 1),
        ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 ≠ r),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K q) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K q) : ℂ) =
        ∑ s ∈ Finset.univ.filter (· ≠ r), ∑ l : Fin (2 * K + 1),
          liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K (s, l)) /
          (↑(liftedPtsA α K (r, j) - liftedPtsA α K (s, l)) : ℂ) := by
      intro j
      rw [show Finset.univ.filter (fun q : Fin R × Fin (2 * K + 1) => q.1 ≠ r) =
          (Finset.univ.filter (fun s : Fin R => s ≠ r)) ×ˢ (Finset.univ : Finset (Fin (2 * K + 1))) from by
        ext ⟨s, l⟩; simp]
      rw [Finset.sum_product]
    simp_rw [h_cross_reindex]
    -- Swap: ∑_j ∑_{s≠r} ∑_l = ∑_{s≠r} ∑_j ∑_l
    rw [Finset.sum_comm]

  -- Step 3: Prove the convergence (2K+1)⁻¹ • F(K) → π * G
  -- Using hF_eq_CR, F(K) = CR(K), so we need (2K+1)⁻¹ • CR(K) → π * G.
  -- CR(K) = ∑_{r≠s} D(r,s,K) and D factors as c_r * conj(c_s) * [real sum].
  -- Per-pair, the real sum / (2K+1) → π/sin by per_pair_cesaro_limit.
  -- Combine via finite sum of Tendsto.

  -- Rewrite using hF_eq_CR
  suffices hCR : Filter.Tendsto (fun K : ℕ =>
      (2 * (K : ℝ) + 1)⁻¹ • CR K)
    Filter.atTop (nhds (↑Real.pi * G)) by
    refine (hCR.congr ?_)
    intro K; congr 1; exact (hF_eq_CR K).symm

  -- CR(K) = ∑_{r≠s} D(r,s,K)
  -- Distribute the scalar: (2K+1)⁻¹ • ∑ = ∑ (2K+1)⁻¹ • D(r,s,K)
  have hCR_unfold : ∀ K : ℕ,
      (2 * (K : ℝ) + 1)⁻¹ • CR K =
      ∑ r : Fin R, ∑ s ∈ Finset.univ.filter (· ≠ r),
        (2 * (K : ℝ) + 1)⁻¹ • D r s K := by
    intro K; show _ = _; simp only [CR]
    rw [show (2 * (K : ℝ) + 1)⁻¹ • ∑ r : Fin R,
        ∑ s ∈ Finset.univ.filter (· ≠ r), D r s K =
      ∑ r : Fin R, (2 * (K : ℝ) + 1)⁻¹ • ∑ s ∈ Finset.univ.filter (· ≠ r), D r s K from
      Finset.smul_sum]
    congr 1; ext r; exact Finset.smul_sum
  simp_rw [hCR_unfold]

  -- Target: ∑_{r≠s} (2K+1)⁻¹ • D(r,s,K) → ↑π * G
  -- Apply tendsto_finset_sum after distributing π into the sums
  simp only [G, Finset.mul_sum]
  apply tendsto_finset_sum
  intro r _
  apply tendsto_finset_sum
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  -- Need: (2K+1)⁻¹ • D(r,s,K) → ↑π * c_r conj(c_s) / sin(π(α_r - α_s))
  -- D(r,s,K) = ∑_j ∑_l liftedCoeffs * conj / diff
  -- This factors as c_r * conj(c_s) * [real double sum involving (-1)^(j+l)]
  -- and the real double sum / (2K+1) → π/sin by per_pair_cesaro_limit

  -- Define the real double sum
  set RealDS : ℕ → ℝ := fun K =>
    ∑ j ∈ Finset.range (2 * K + 1), ∑ l ∈ Finset.range (2 * K + 1),
      (-1 : ℝ) ^ (j + l) / ((α r - α s) + (↑j - ↑l))

  -- Step A: D(r,s,K) = c_r * conj(c_s) * ↑(RealDS K)
  -- Term-by-term factoring: each summand factors as c_r * conj(c_s) * ofReal(...)
  have hterm : ∀ K : ℕ, ∀ j l : Fin (2 * K + 1),
      liftedCoeffs c K (r, j) * starRingEnd ℂ (liftedCoeffs c K (s, l)) /
      (↑(liftedPtsA α K (r, j) - liftedPtsA α K (s, l)) : ℂ) =
      c r * starRingEnd ℂ (c s) *
        ↑((-1 : ℝ) ^ ((j : ℕ) + (l : ℕ)) / ((α r - α s) + (↑(j : ℕ) - ↑(l : ℕ)))) := by
    intro K j l
    simp only [liftedCoeffs, liftedPtsA, map_mul, map_pow, map_neg, map_one]
    rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    push_cast; ring

  have hD_eq : ∀ K : ℕ, D r s K = c r * starRingEnd ℂ (c s) * ↑(RealDS K) := by
    intro K
    simp only [D]
    simp_rw [hterm K]
    -- Now: ∑_j ∑_l c_r * conj(c_s) * ↑f(j,l) = c_r * conj(c_s) * ↑(∑_j ∑_l f(j,l))
    simp_rw [← Finset.mul_sum]
    congr 1
    -- Goal: ∑ i : Fin _, ∑ i_1 : Fin _, ↑(f i i_1) = ↑(RealDS K)
    simp only [RealDS]
    -- Step 1: collapse inner ofReal sums
    have inner_eq : ∀ i : Fin (2 * K + 1),
        ∑ i_1 : Fin (2 * K + 1),
          (↑((-1 : ℝ) ^ ((i : ℕ) + (i_1 : ℕ)) / ((α r - α s) + (↑↑i - ↑↑i_1))) : ℂ) =
        ↑(∑ i_1 : Fin (2 * K + 1),
          (-1 : ℝ) ^ ((i : ℕ) + (i_1 : ℕ)) / ((α r - α s) + (↑↑i - ↑↑i_1))) := by
      intro i; rw [Complex.ofReal_sum]
    simp_rw [inner_eq]
    rw [← Complex.ofReal_sum]
    congr 1
    -- Now: ∑ i : Fin _, ∑ i_1 : Fin _, f(i,i_1) = ∑ j ∈ range _, ∑ l ∈ range _, f(j,l)
    -- Convert outer Fin sum to range sum
    conv_lhs => rw [show (∑ i : Fin (2 * K + 1), ∑ i_1 : Fin (2 * K + 1),
        (-1 : ℝ) ^ ((i : ℕ) + (i_1 : ℕ)) / ((α r - α s) + (↑↑i - ↑↑i_1))) =
        ∑ j ∈ Finset.range (2 * K + 1), ∑ l ∈ Finset.range (2 * K + 1),
          (-1 : ℝ) ^ (j + l) / ((α r - α s) + (↑j - ↑l)) from by
      rw [← Fin.sum_univ_eq_sum_range]; congr 1; ext i
      rw [← Fin.sum_univ_eq_sum_range]]

  -- Step B: (2K+1)⁻¹ • D = c_r * conj(c_s) * ↑((2K+1)⁻¹ * RealDS K)
  have hsmul_eq : ∀ K : ℕ,
      (2 * (K : ℝ) + 1)⁻¹ • D r s K =
      c r * starRingEnd ℂ (c s) * ↑((2 * (K : ℝ) + 1)⁻¹ * RealDS K) := by
    intro K
    rw [hD_eq K, Complex.real_smul, Complex.ofReal_mul]
    ring

  -- Step C: (2K+1)⁻¹ * RealDS K → π/sin(π(α r - α s))
  -- by per_pair_cesaro_limit with θ = α r - α s
  have hθ := hθ_ne r s hs.symm
  -- per_pair_cesaro_limit uses N indexing: ((N+1)⁻¹ * ∑_{j,l < N+1})
  -- RealDS K = ∑_{j,l < 2K+1}. Set N = 2K, then N+1 = 2K+1.
  -- So (2K+1)⁻¹ * RealDS K = ((2K)₊₁)⁻¹ * RealDS K matches per_pair_cesaro_limit at N=2K.
  -- But per_pair_cesaro_limit gives convergence along all N, so along 2K works too.
  have hreal_conv : Filter.Tendsto (fun K : ℕ =>
      (2 * (K : ℝ) + 1)⁻¹ * RealDS K)
    Filter.atTop (nhds (Real.pi / Real.sin (Real.pi * (α r - α s)))) := by
    have hppc := per_pair_cesaro_limit (α r - α s) hθ
    -- hppc gives convergence along N. We need convergence along K where N = 2K.
    -- RealDS K = ∑_{j < 2K+1} ∑_{l < 2K+1} f(j,l) matches hppc at N = 2K
    -- since range(N+1) = range(2K+1) when N = 2K.
    -- The scalar is (N+1)⁻¹ = (2K+1)⁻¹. Perfect match!
    have h2K : Filter.Tendsto (fun K : ℕ => 2 * K) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr (fun n => ⟨n, fun K hK => by omega⟩)
    refine (hppc.comp h2K).congr (fun K => ?_)
    simp only [Function.comp_def]
    -- Need: ((2*K:ℕ) + 1)⁻¹ * ∑... = (2*(K:ℝ)+1)⁻¹ * RealDS K
    -- The sums are over the same ranges and the terms are the same
    -- The only difference is cast normalization
    simp only [RealDS]
    push_cast
    ring

  -- Step D: Combine factorization and real convergence
  simp_rw [hsmul_eq]
  -- Need: c_r * conj(c_s) * ↑(f K) → ↑π * (c_r * conj(c_s) / ↑sin(...))
  -- Rewrite the target limit
  rw [show (↑Real.pi : ℂ) * (c r * starRingEnd ℂ (c s) /
      (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) =
      c r * starRingEnd ℂ (c s) * ↑(Real.pi / Real.sin (Real.pi * (α r - α s))) from by
    rw [Complex.ofReal_div]; ring]
  -- Tendsto (fun K => a * ofReal(f K)) _ (nhds (a * ofReal(L)))
  -- where a = c_r * conj(c_s) and f K = (2K+1)⁻¹ * RealDS K
  have hcont : Filter.Tendsto (fun K : ℕ =>
      (↑((2 * (K : ℝ) + 1)⁻¹ * RealDS K) : ℂ))
    Filter.atTop (nhds ↑(Real.pi / Real.sin (Real.pi * (α r - α s)))) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).comp hreal_conv
  exact Filter.Tendsto.const_mul (c r * starRingEnd ℂ (c s)) hcont

-- ==========================================
-- Section: Circular-Spacing Bypass
-- (eliminates HilbertCscBilinearBridge / Cohen trick)
-- ==========================================

/-!
### Circular-spacing chain: HilbertInequality → AdditiveLargeSieveCircular

The Cohen trick sharpens the constant from `1/δ` to `1/δ - 1`, but requires
converting between circular and non-circular spacing. Since all downstream
applications (Farey fractions, unit points for primes) use circularly-spaced
points, we can bypass the Cohen trick entirely by threading `IsCircularSpaced`
through the chain with the slightly weaker constant `1/δ`.

Chain:
  CscBilinearBoundCircular (PROVED: `hilbert_csc_circular_of_cesaro`)
  → GramOffDiagBilinearBoundCircular (copy-adapt of `csc_bilinear_implies_gram_offdiag`)
  → AdditiveLargeSieveCircular (copy-adapt of `gram_offdiag_bilinear_implies_als`)
-/

/-- **Circular off-diagonal Gram bilinear bound**: the off-diagonal bilinear form
    of the Gram matrix is bounded by `(1/δ) · ‖b‖²` for circularly δ-spaced points.
    This is the circular-spacing variant with slightly weaker constant `1/δ` (vs `1/δ-1`). -/
def GramOffDiagBilinearBoundCircular : Prop :=
  ∀ (R N : ℕ) (α : Fin R → ℝ) (b : Fin R → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 → 1 ≤ N →
    IsCircularSpaced α δ →
    ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s‖ ≤
      (1/δ) * l2NormSq b

/-- **CscBilinearBoundCircular → GramOffDiagBilinearBoundCircular**: circular variant
    of `csc_bilinear_implies_gram_offdiag`, using IsCircularSpaced and bound `1/δ`.

    **Proof**: identical to `csc_bilinear_implies_gram_offdiag` but using
    `isCircularSpaced_sin_ne_zero` instead of `isSpaced_sin_ne_zero`, and
    the CscBilinearBoundCircular bound `1/δ` (vs `1/δ - 1`).
    Triangle inequality: `(1/2) · 2 · (1/δ) = 1/δ`. -/
theorem csc_bilinear_circular_implies_gram_offdiag_circular
    (hcsc : CscBilinearBoundCircular) : GramOffDiagBilinearBoundCircular := by
  intro R N α b δ hδ hδ2 _hN hcirc
  -- Define phase-shifted coefficients
  set d : Fin R → ℂ := fun r => b r * _root_.eAN ((↑(2 * N) - 1) / 2 * α r) with hd_def
  set d' : Fin R → ℂ := fun r => b r * _root_.eAN (-(1 : ℝ) / 2 * α r) with hd'_def
  -- Step 5: l2NormSq preservation
  have hl2d : l2NormSq d = l2NormSq b := l2NormSq_mul_eAN b _ α
  have hl2d' : l2NormSq d' = l2NormSq b := l2NormSq_mul_eAN b _ α
  -- Step 5: Apply CscBilinearBoundCircular to d and d'
  have hcsc_d := hcsc R α d δ hδ hδ2 hcirc
  have hcsc_d' := hcsc R α d' δ hδ hδ2 hcirc
  rw [hl2d] at hcsc_d
  rw [hl2d'] at hcsc_d'
  -- sin ≠ 0 for all pairs (using circular spacing)
  have hsin_ne : ∀ r s : Fin R, r ≠ s →
      Real.sin (Real.pi * (α r - α s)) ≠ 0 :=
    fun r s hrs => isCircularSpaced_sin_ne_zero α δ hδ hcirc r s hrs
  -- Helper: d products combine via eAN_add
  have hd_prod : ∀ r s : Fin R,
      d r * starRingEnd ℂ (d s) =
      b r * starRingEnd ℂ (b s) *
        _root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) := by
    intro r s
    simp only [hd_def, map_mul, conj_eAN]
    rw [show (↑(2 * N) - 1) / 2 * (α r - α s) =
        (↑(2 * N) - 1) / 2 * α r + -((↑(2 * N) - 1) / 2 * α s) from by ring,
        _root_.eAN_add]
    ring
  have hd'_prod : ∀ r s : Fin R,
      d' r * starRingEnd ℂ (d' s) =
      b r * starRingEnd ℂ (b s) *
        _root_.eAN (-(1 : ℝ) / 2 * (α r - α s)) := by
    intro r s
    simp only [hd'_def, map_mul, conj_eAN]
    rw [show -(1 : ℝ) / 2 * (α r - α s) =
        -(1 : ℝ) / 2 * α r + -(-(1 : ℝ) / 2 * α s) from by ring,
        _root_.eAN_add]
    ring
  -- Phase identity
  have hpair_num : ∀ r s : Fin R, r ≠ s →
      d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s) =
      b r * starRingEnd ℂ (b s) *
        (_root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) -
         _root_.eAN (-(1 : ℝ) / 2 * (α r - α s))) := by
    intro r s _
    rw [hd_prod, hd'_prod]
    ring
  -- Key numerator identity: the eAN difference equals G * 2I*sin
  have hnum_eq : ∀ r s : Fin R,
      _root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) -
      _root_.eAN (-(1 : ℝ) / 2 * (α r - α s)) =
      gramMatrix N α r s *
        (_root_.eAN ((α r - α s) / 2) - _root_.eAN (-((α r - α s) / 2))) := by
    intro r s
    have h := gramMatrix_mul_half_phase N α r s
    have hlhs : _root_.eAN ((↑(2 * N) - 1) / 2 * (α r - α s)) =
        _root_.eAN ((↑(2 * N) - 1) * (α r - α s) / 2) := by congr 1; ring
    have hrhs : _root_.eAN (-(1 : ℝ) / 2 * (α r - α s)) =
        _root_.eAN (-((α r - α s) / 2)) := by congr 1; ring
    rw [hlhs, hrhs]
    exact h.symm
  -- Phase difference = 2I * sin
  have hphase_eq : ∀ r s : Fin R,
      _root_.eAN ((α r - α s) / 2) - _root_.eAN (-((α r - α s) / 2)) =
      2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s))) := by
    intro r s
    set θ := α r - α s
    have h1 : _root_.eAN (θ / 2) = Complex.exp (↑(Real.pi * θ) * Complex.I) := by
      unfold _root_.eAN; congr 1; push_cast; ring
    have h2 : _root_.eAN (-(θ / 2)) = Complex.exp (↑(-(Real.pi * θ)) * Complex.I) := by
      unfold _root_.eAN; congr 1; push_cast; ring
    rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.sin_neg, Complex.cos_neg, ← Complex.ofReal_sin]
    ring
  -- Combine: for r ≠ s, b conj(b) * G = (d_prod - d'_prod) / (2I * sin)
  have hpair : ∀ r s : Fin R, r ≠ s →
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
      (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) := by
    intro r s hrs
    have hsin_ne_rs := hsin_ne r s hrs
    have h2Isin_ne : 2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s))) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hsin_ne_rs)
    rw [hpair_num r s hrs, hnum_eq, hphase_eq, eq_div_iff h2Isin_ne]
    ring
  -- Step 3: Rewrite the full sum
  have hsum_eq :
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        b r * starRingEnd ℂ (b s) * gramMatrix N α r s =
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s hs
    exact hpair r s ((Finset.mem_filter.mp hs).2).symm
  rw [hsum_eq]
  -- Step 3b: Split and factor (2I)⁻¹
  have hterm_split : ∀ r s : Fin R, r ≠ s →
      (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
      (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
        (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
      (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
        (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
    intro r s hrs
    have hsin_ne_rs := hsin_ne r s hrs
    have _hsin_C_ne : (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsin_ne_rs
    have _h2I_ne : (2 : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero two_ne_zero Complex.I_ne_zero
    field_simp
  have hsum_split :
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
        (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
      (2 * Complex.I)⁻¹ *
        ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
      (2 * Complex.I)⁻¹ *
        ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
    have hstep : ∀ r : Fin R,
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
          (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          ((2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
          (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) := by
      intro r
      apply Finset.sum_congr rfl
      intro s hs
      exact hterm_split r s ((Finset.mem_filter.mp hs).2).symm
    have hLHS :
        ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          (d r * starRingEnd ℂ (d s) - d' r * starRingEnd ℂ (d' s)) /
          (2 * Complex.I * ↑(Real.sin (Real.pi * (α r - α s)))) =
        ∑ r, ((∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) -
        (∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ))) := by
      apply Finset.sum_congr rfl; intro r _
      rw [hstep r, Finset.sum_sub_distrib]
    rw [hLHS, Finset.sum_sub_distrib]
    have hinner_d : ∀ r : Fin R,
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
        (2 * Complex.I)⁻¹ * ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
      intro r
      conv_lhs =>
        arg 2; ext s
        rw [show (2 * Complex.I)⁻¹ * d r * starRingEnd ℂ (d s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
            (2 * Complex.I)⁻¹ * (d r * starRingEnd ℂ (d s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) from by ring]
      rw [← Finset.mul_sum]
    have hinner_d' : ∀ r : Fin R,
        ∑ s ∈ Finset.univ.filter (· ≠ r),
          (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
        (2 * Complex.I)⁻¹ * ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) /
          (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) := by
      intro r
      conv_lhs =>
        arg 2; ext s
        rw [show (2 * Complex.I)⁻¹ * d' r * starRingEnd ℂ (d' s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
            (2 * Complex.I)⁻¹ * (d' r * starRingEnd ℂ (d' s) /
              (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)) from by ring]
      rw [← Finset.mul_sum]
    simp_rw [hinner_d, hinner_d', ← Finset.mul_sum]
  rw [hsum_split]
  -- Step 4: Take norms, triangle inequality
  rw [show (2 * Complex.I)⁻¹ *
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
      (2 * Complex.I)⁻¹ *
      ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) =
      (2 * Complex.I)⁻¹ *
      (∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
       ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
        d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ))
    from by ring]
  have h2I_norm : ‖(2 * Complex.I : ℂ)⁻¹‖ = 1/2 := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I]
    norm_num
  calc ‖(2 * Complex.I)⁻¹ *
        (∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
         ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ))‖
      ≤ ‖(2 * Complex.I : ℂ)⁻¹‖ *
        ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ) -
         ∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖ :=
        norm_mul_le _ _
    _ ≤ ‖(2 * Complex.I : ℂ)⁻¹‖ *
        (‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d r * starRingEnd ℂ (d s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖ +
         ‖∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
          d' r * starRingEnd ℂ (d' s) / (↑(Real.sin (Real.pi * (α r - α s))) : ℂ)‖) := by
        apply mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ (1/2) * ((1/δ) * l2NormSq b + (1/δ) * l2NormSq b) := by
        rw [h2I_norm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hcsc_d hcsc_d'
    _ = (1/δ) * l2NormSq b := by ring

/-- **Circular additive large sieve**: For circularly δ-spaced points,
    `∑_r |∑_n a_n e(α_r n)|² ≤ (1/δ + N) · ‖a‖²`.
    Note: constant is `1/δ + N` (vs optimal `1/δ + N - 1`). -/
def AdditiveLargeSieveCircular : Prop :=
  ∀ (R N : ℕ) (α : Fin R → ℝ) (a : Fin N → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1/2 → 1 ≤ N →
    IsCircularSpaced α δ →
    (∑ r, ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤
      (1/δ + ↑N) * l2NormSq a

/-- **GramOffDiagBilinearBoundCircular → AdditiveLargeSieveCircular**: circular variant
    of `gram_offdiag_bilinear_implies_als`, using IsCircularSpaced and bound `1/δ + N`.

    **Proof**: The Gram quadratic form splits as diagonal (`N · ‖b‖²`) plus
    off-diagonal (`≤ (1/δ) · ‖b‖²` by hypothesis). Combined: `(1/δ + N) · ‖b‖²`.
    Duality converts this dual bound to the primal ALS. -/
theorem gram_offdiag_circular_implies_als_circular
    (hoff : GramOffDiagBilinearBoundCircular) : AdditiveLargeSieveCircular := by
  intro R N α a δ hδ hδ2 hN hcirc
  -- The constant 1/δ + N is nonneg
  have hC : (0 : ℝ) ≤ 1/δ + ↑N := by
    have : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have : 0 < 1/δ := by positivity
    linarith
  -- Use duality: it suffices to prove the dual form
  set x : Fin R → Fin N → ℂ := fun r n => eAN (α r * ↑(n : ℕ)) with hx_def
  show (∑ r, ‖∑ n, a n * x r n‖ ^ 2) ≤ (1/δ + ↑N) * l2NormSq a
  suffices hdual : DualLargeSieve x (1/δ + ↑N) by
    exact (lsi_of_dual x (1/δ + ↑N) hC hdual) a
  -- Prove dual: ∀ b, ∑_n ‖∑_r b_r x(r,n)‖² ≤ (1/δ + N) · ‖b‖²
  intro b
  -- Step 1: Expand dual LHS as Re of Gram quadratic form
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
  rw [Complex.add_re]
  -- Step 3: Bound diagonal
  rw [gram_diag_re]
  -- Step 4: Bound off-diagonal via GramOffDiagBilinearBoundCircular
  have hoff_bound := hoff R N α b δ hδ hδ2 hN hcirc
  have hre_le_norm := Complex.re_le_norm
    (∑ r, ∑ s ∈ Finset.univ.filter (· ≠ r),
      b r * starRingEnd ℂ (b s) * gramMatrix N α r s)
  -- Combine: N · l2NormSq b + re(off-diag) ≤ N · l2NormSq b + (1/δ) · l2NormSq b
  have hcombine : ↑N * l2NormSq b + (1/δ) * l2NormSq b =
      (1/δ + ↑N) * l2NormSq b := by ring
  linarith

/-- **HilbertInequality + CrossRCesaroConvergence → AdditiveLargeSieveCircular**:
    the full chain bypassing HilbertCscBilinearBridge (Cohen trick).

    Chain: HilbertInequality + CrossRCesaroConvergence
      → CscBilinearBoundCircular (via `hilbert_csc_circular_of_cesaro`)
      → GramOffDiagBilinearBoundCircular (via `csc_bilinear_circular_implies_gram_offdiag_circular`)
      → AdditiveLargeSieveCircular (via `gram_offdiag_circular_implies_als_circular`)

    This eliminates the need for `HilbertCscBilinearBridge` entirely. The cost
    is a slightly weaker constant: `1/δ + N` instead of the optimal `1/δ + N - 1`.
    All downstream applications absorb this easily. -/
theorem hilbert_chain_als_circular
    (hHI : HilbertInequality) (hces : CrossRCesaroConvergence) :
    AdditiveLargeSieveCircular :=
  gram_offdiag_circular_implies_als_circular
    (csc_bilinear_circular_implies_gram_offdiag_circular
      (hilbert_csc_circular_of_cesaro hHI hces))

end IK
