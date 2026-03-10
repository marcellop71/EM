import EM.IKCh7Hilbert

/-!
# Chapter 7 (Part 5b): Cesàro Convergence and Circular ALS Chain (Iwaniec-Kowalski)

Product-index trick: Hilbert lifted bound, same-r antisymmetry involution,
CrossRCesaroConvergence proof (Fejér identity + ML Cesaro convergence),
and the circular-spacing bypass eliminating the Cohen trick.

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Complex Finset BigOperators

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

