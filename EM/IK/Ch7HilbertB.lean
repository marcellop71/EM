import EM.IK.Ch7Hilbert

/-!
# Chapter 7 (Part 5b): Hilbert → CscBilinear Circular Bridge (Iwaniec-Kowalski)

Continuation of Ch7Hilbert: lifted point separation, CscBilinear → GramOffDiag circular,
phase shift and Gram matrix infrastructure.
-/

noncomputable section

open Classical

namespace IK

open Complex Finset BigOperators

-- ==========================================
-- Section: HilbertInequality → CscBilinearBoundCircular
-- ==========================================

def liftedPtsA {R : ℕ} (α : Fin R → ℝ) (K : ℕ) :
    Fin R × Fin (2 * K + 1) → ℝ :=
  fun ⟨r, j⟩ => α r + ((j : ℕ) - (K : ℝ))

/-- **Lifted point differences (actual α)**: the difference decomposes as
    actual difference plus integer shift. -/
theorem liftedPtsA_diff {R : ℕ} (α : Fin R → ℝ) (K : ℕ)
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
theorem liftedPtsA_sep_all {R : ℕ} {δ : ℝ} (α : Fin R → ℝ) (K : ℕ)
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


end IK
