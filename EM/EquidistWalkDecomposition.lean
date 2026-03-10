import EM.EquidistSelfCorrecting

/-!
# Walk Sum Decomposition: Quadratic and General

Quadratic walk character decomposition, escape decorrelation hypothesis,
general walk sum decomposition, and block alternation structure.

## Main Results

* `escape_telescope_order2` : escape telescope identity for order-2 characters (PROVED)
* `quadratic_ccsb_iff_kernel_ccsb` : QuadraticCCSB ↔ kernel-block CCSB (PROVED)
* `EscapeDecorrelation` : h-fold multiplier products have sums o(N) (open Prop)
* `escape_dec_implies_quadratic_ccsb` : EscapeDecorrelation → QuadraticCCSB (PROVED)
* `escape_telescope_general` : weighted escape sum = χ(w(N))−χ(w(0)) for all χ (PROVED)
* `kernel_block_walk_char_constant` : consecutive kernel steps preserve walk char (PROVED)
* `escape_values_alternate` : escape flips walk character for order-2 (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## §73. Quadratic Walk Sum Decomposition

For an **order-2 character** χ (values ±1), the walk telescope identity
(§37, `walk_telescope_identity`) yields a powerful constraint on escape
positions.

**Key identity**: splitting the telescoping sum
  ∑_{n<N} χ(w(n)) · (χ(m(n)) − 1) = χ(w(N)) − χ(w(0))
into kernel terms (contributing 0) and escape terms (contributing −2·χ(w(n)))
shows that ∑_{escape n} χ(w(n)) = (χ(w(0)) − χ(w(N))) / 2,
hence |∑_{escape n} χ(w(n))| ≤ 1.

This means the walk sum ∑_{n<N} χ(w(n)) decomposes as:
  (kernel-block contribution) + (escape-position contribution with ‖·‖ ≤ 1)

We also define `QuadraticCCSB`, the restriction of `ComplexCharSumBound` to
order-2 characters, which is strictly weaker than full CCSB.
-/

section QuadraticWalkSum

/-- **Escape-telescope identity for order-2 characters**: the telescoping sum
    restricted to escape positions (where χ(m(n)) = −1) satisfies
      −2 · ∑_{escape} χ(w(n)) = χ(w(N)) − χ(w(0)).

    **Proof**: Split the telescope sum by the predicate χ(m(n)) = 1.
    Kernel terms vanish (factor χ(m(n))−1 = 0).  Escape terms have
    χ(m(n))−1 = −2, giving the stated identity. -/
theorem escape_telescope_order2 {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    (-2 : ℂ) * ∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ) =
    (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
  -- Start from the telescope identity
  have htel := walk_telescope_identity q hq hne χ N
  -- Split the LHS sum by the predicate (χ(m(n)) = 1)
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1))).symm
  rw [hsplit] at htel
  -- Kernel terms: each χ(m(n)) = 1, so χ(m(n)) - 1 = 0, so term = 0
  have hker_zero : ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [hn.2, sub_self, mul_zero]
  rw [hker_zero, zero_add] at htel
  -- Escape terms: for order-2 χ, χ(m(n)) ∈ {1, -1}; filter says ≠ 1, so = -1
  -- Hence χ(m(n)) - 1 = -2, so term = χ(w(n)) * (-2) = -2 * χ(w(n))
  have hesc_terms : ∀ n ∈ (Finset.range N).filter
      (fun n => ¬(χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1) =
    (-2 : ℂ) * (χ (emWalkUnit q hq hne n) : ℂ) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    rcases hord2 (emMultUnit q hq hne n) with hm | hm
    · exact absurd hm hn.2
    · rw [hm]; ring
  rw [Finset.sum_congr rfl hesc_terms] at htel
  -- Factor out -2 from the sum
  rw [← Finset.mul_sum] at htel
  -- The filter predicate ¬(... = 1) is the same as (... ≠ 1)
  exact htel

/-- **Escape sum norm bound for order-2 characters**: the sum of walk
    character values at escape positions has norm at most 1.

    **Proof**: From `escape_telescope_order2`,
      2·‖∑_{escape} χ(w(n))‖ = ‖χ(w(N)) − χ(w(0))‖ ≤ 2
    so ‖∑_{escape} χ(w(n))‖ ≤ 1. -/
theorem escape_sum_order2_bounded {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ 1 := by
  -- From escape_telescope_order2: (-2) * escape_sum = χ(w(N)) - χ(w(0))
  set S := ∑ n ∈ (Finset.range N).filter
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
    (χ (emWalkUnit q hq hne n) : ℂ) with hS_def
  have hid := escape_telescope_order2 hq hne χ hord2 N
  -- Take norms: ‖(-2) * S‖ = 2 * ‖S‖
  have hnorm_lhs : ‖(-2 : ℂ) * S‖ = 2 * ‖S‖ := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat]
  -- RHS norm ≤ 2 (triangle inequality + each walk char has norm 1)
  have hnorm_rhs : ‖(χ (emWalkUnit q hq hne N) : ℂ) -
      (χ (emWalkUnit q hq hne 0) : ℂ)‖ ≤ 2 := by
    calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
        ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
      _ = 2 := by ring
  -- Combine: 2 * ‖S‖ = ‖(-2) * S‖ = ‖RHS‖ ≤ 2
  rw [hid] at hnorm_lhs
  have h2S : 2 * ‖S‖ ≤ 2 := by linarith
  linarith

/-- **Walk sum splits into kernel-block and escape contributions**: for an
    order-2 character χ, the full walk character sum equals the kernel-only sum
    plus the escape-only sum. This is just Finset.sum_filter_add_sum_filter_not
    specialized to the walk setting. -/
theorem quadratic_walk_sum_split {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
    (∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)) +
    (∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)) :=
  (Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1) _).symm

/-- **Walk sum norm bound from kernel-block sum**: for order-2 χ, the walk
    character sum norm is within 1 of the kernel-block sum norm.  More precisely:
      ‖∑_{n<N} χ(w(n))‖ ≤ ‖∑_{kernel n} χ(w(n))‖ + 1.

    **Proof**: Split the sum, apply triangle inequality, use the escape bound. -/
theorem walk_sum_le_kernel_sum_add_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
  rw [quadratic_walk_sum_split hq hne χ N]
  calc ‖(∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
        (χ (emWalkUnit q hq hne n) : ℂ)) +
        (∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
        (χ (emWalkUnit q hq hne n) : ℂ))‖
      ≤ ‖∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
        (χ (emWalkUnit q hq hne n) : ℂ)‖ +
        ‖∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
        (χ (emWalkUnit q hq hne n) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
        (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
        linarith [escape_sum_order2_bounded hq hne χ hord2 N]

/-- **QuadraticCCSB**: `ComplexCharSumBound` restricted to order-2 characters.
    This is strictly weaker than full CCSB since it only handles characters
    with values in {+1, −1} (i.e., Jacobi/Legendre symbols). -/
def QuadraticCCSB : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **CCSB implies QuadraticCCSB**: the full complex character sum bound
    implies the restriction to order-2 characters (trivial specialization). -/
theorem ccsb_implies_quadratic_ccsb (hccsb : ComplexCharSumBound) :
    QuadraticCCSB := by
  intro q _ hq hne χ hχ _hord2 ε hε
  exact hccsb q hq hne χ hχ ε hε

/-- **Reverse triangle for kernel sum**: the kernel-block sum norm is within 1
    of the full walk sum norm (reverse direction of `walk_sum_le_kernel_sum_add_one`).
    Specifically: ‖∑_{kernel} χ(w(n))‖ ≤ ‖∑_{all} χ(w(n))‖ + 1. -/
theorem kernel_sum_le_walk_sum_add_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
  set kerSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  set escSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  have hsplit : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      kerSum + escSum := quadratic_walk_sum_split hq hne χ N
  have hesc := escape_sum_order2_bounded hq hne χ hord2 N
  -- kerSum = total - escSum, so ‖kerSum‖ ≤ ‖total‖ + ‖escSum‖ ≤ ‖total‖ + 1
  have hker_eq : kerSum = (∑ n ∈ Finset.range N,
      (χ (emWalkUnit q hq hne n) : ℂ)) - escSum := by
    rw [hsplit]; ring
  calc ‖kerSum‖ = ‖(∑ n ∈ Finset.range N,
          (χ (emWalkUnit q hq hne n) : ℂ)) - escSum‖ := by rw [hker_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ +
        ‖escSum‖ := norm_sub_le _ _
    _ ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
        linarith

/-- **QuadraticCCSB equivalent to kernel-block CCSB**: for order-2 characters,
    the walk sum is o(N) iff the kernel-block sum is o(N), since they differ
    by at most 1 (the escape contribution). -/
theorem quadratic_ccsb_iff_kernel_ccsb :
    QuadraticCCSB ↔
    (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
     ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
     ∀ (ε : ℝ) (_hε : 0 < ε),
     ∃ N₀ : ℕ, ∀ N ≥ N₀,
       ‖∑ n ∈ (Finset.range N).filter
           (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
         (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N) := by
  constructor
  · -- Forward: QuadraticCCSB → kernel-block CCSB
    intro hqccsb q _ hq hne χ hχ hord2 ε hε
    -- Use ε/2 for the walk sum, then add 1
    obtain ⟨N₁, hN₁⟩ := hqccsb q hq hne χ hχ hord2 (ε / 2) (by linarith)
    -- Choose N₀ large enough that 1 ≤ (ε/2) * N₀
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have hN₁_le : N₁ ≤ N := (le_max_left N₁ N₂).trans hN
    have hN₂_le : N₂ ≤ N := (le_max_right N₁ N₂).trans hN
    calc ‖∑ n ∈ (Finset.range N).filter
            (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
          (χ (emWalkUnit q hq hne n) : ℂ)‖
        ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 :=
          kernel_sum_le_walk_sum_add_one hq hne χ hord2 N
      _ ≤ ε / 2 * N + 1 := by linarith [hN₁ N hN₁_le]
      _ ≤ ε / 2 * N + ε / 2 * N := by
          have : 1 ≤ ε / 2 * N := by
            have hN₂_le_r : (N₂ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN₂_le
            have : 2 / ε < (N : ℝ) := lt_of_lt_of_le hN₂ hN₂_le_r
            rw [div_lt_iff₀ hε] at this
            linarith
          linarith
      _ = ε * N := by ring
  · -- Backward: kernel-block CCSB → QuadraticCCSB
    intro hkccsb q _ hq hne χ hχ hord2 ε hε
    obtain ⟨N₁, hN₁⟩ := hkccsb q hq hne χ hχ hord2 (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have hN₁_le : N₁ ≤ N := (le_max_left N₁ N₂).trans hN
    have hN₂_le : N₂ ≤ N := (le_max_right N₁ N₂).trans hN
    calc ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖
        ≤ ‖∑ n ∈ (Finset.range N).filter
            (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
          (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 :=
          walk_sum_le_kernel_sum_add_one hq hne χ hord2 N
      _ ≤ ε / 2 * N + 1 := by linarith [hN₁ N hN₁_le]
      _ ≤ ε / 2 * N + ε / 2 * N := by
          have : 1 ≤ ε / 2 * N := by
            have hN₂_le_r : (N₂ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN₂_le
            have : 2 / ε < (N : ℝ) := lt_of_lt_of_le hN₂ hN₂_le_r
            rw [div_lt_iff₀ hε] at this
            linarith
          linarith
      _ = ε * N := by ring

end QuadraticWalkSum

/-! ## §74. Escape Decorrelation Hypothesis

For order-2 characters, the Van der Corput inequality (VdC, proved in §69 of
`LargeSieveAnalytic.lean`) reduces `QuadraticCCSB` to bounding h-point
correlations of the multiplier character sequence.

Specifically, the walk autocorrelation at lag h equals:
  R_h(n) = χ(w(n+h)) · χ(w(n)) = ∏_{j<h} χ(m(n+j))
using the multi-step recurrence and the order-2 identity χ(w(n))² = 1.

We define `EscapeDecorrelation` as the hypothesis that the h-fold multiplier
character products have partial sums o(N) for every h ≥ 1.  Combined with VdC,
this yields `QuadraticCCSB`.

**Key results**:
1. `local_char_walk_multi_step`: χ(w(n+h)) = χ(w(n)) · ∏_{j<h} χ(m(n+j)) (local copy of §53 result)
2. `quadratic_autocorrelation_eq_mult_product`: χ(w(n+h))·χ(w(n)) = ∏_{j<h} χ(m(n+j)) for order-2 χ
3. `EscapeDecorrelation`: open Prop — h-fold multiplier products have sums o(N)
4. `escape_dec_h1_specializes`: h=1 case simplifies to single multiplier char sum
5. `escape_dec_implies_quadratic_ccsb`: EscapeDecorrelation → QuadraticCCSB (with VdC hypothesis)
-/

section EscapeDecorrelation

/-- **Multi-step walk recurrence (local)**: χ(w(n+h)) = χ(w(n)) · ∏_{j<h} χ(m(n+j)).
    This is a local copy of `char_walk_multi_step` from LargeSieveHarmonic.lean §53,
    proved here to avoid cross-file import dependencies. -/
theorem local_char_walk_multi_step (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (n h : Nat) :
    (χ (emWalkUnit q hq hne (n + h)) : ℂ) =
    (χ (emWalkUnit q hq hne n) : ℂ) *
    ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show n + (h + 1) = (n + h) + 1 from by omega]
    rw [char_walk_recurrence q hq hne χ (n + h)]
    rw [ih]
    rw [Finset.prod_range_succ]
    ring

/-- **Quadratic autocorrelation equals multiplier product**: for an order-2
    character χ, the product χ(w(n+h)) · χ(w(n)) equals ∏_{j<h} χ(m(n+j)).

    **Proof**: By `local_char_walk_multi_step`,
      χ(w(n+h)) = χ(w(n)) · ∏_{j<h} χ(m(n+j)).
    Multiplying both sides by χ(w(n)) and using χ(w(n))² = 1 (from `order2_sq_eq_one`)
    gives: χ(w(n+h)) · χ(w(n)) = χ(w(n))² · ∏ = 1 · ∏ = ∏. -/
theorem quadratic_autocorrelation_eq_mult_product
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ)
    (n h : Nat) :
    (χ (emWalkUnit q hq hne (n + h)) : ℂ) * (χ (emWalkUnit q hq hne n) : ℂ) =
    ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ) := by
  rw [local_char_walk_multi_step q hq hne χ n h]
  -- LHS = (χ(w(n)) * ∏) * χ(w(n)) = χ(w(n))² * ∏
  have hsq : (χ (emWalkUnit q hq hne n) : ℂ) ^ 2 = 1 :=
    order2_sq_eq_one χ hord2 (emWalkUnit q hq hne n)
  -- χ(w(n))² = 1, so factor it out
  have : (χ (emWalkUnit q hq hne n) : ℂ) *
      (∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ)) *
      (χ (emWalkUnit q hq hne n) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) ^ 2 *
      (∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ)) := by ring
  rw [this, hsq, one_mul]

/-- **EscapeDecorrelation**: for every h ≥ 1, the h-fold product of consecutive
    multiplier character values has partial sums o(N).  For order-2 characters,
    this is equivalent to saying the walk autocorrelation R_h = o(N) for all h,
    via `quadratic_autocorrelation_eq_mult_product`.

    Combined with the Van der Corput inequality (§69, `van_der_corput_bound`),
    this implies `QuadraticCCSB`.

    This is weaker than `HigherOrderDecorrelation` (§69) which applies to all
    characters, not just order-2 ones.  For order-2 characters, however,
    the two are equivalent. -/
def EscapeDecorrelation : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
  ∀ (h : ℕ) (_hh : 0 < h),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N,
      ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ)‖ ≤ ε * N

/-- **h=1 specialization**: `EscapeDecorrelation` at h=1 gives
    ‖∑_{n<N} χ(m(n))‖ ≤ ε·N, the multiplier character sum bound.

    **Proof**: `∏ j ∈ Finset.range 1, χ(m(n+j)) = χ(m(n+0)) = χ(m(n))`. -/
theorem escape_dec_h1_specializes (hed : EscapeDecorrelation)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (hord2 : IsOrder2 χ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N := by
  obtain ⟨N₀, hN₀⟩ := hed q hq hne χ hχ hord2 1 one_pos ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ∀ n, ∏ j ∈ Finset.range 1, (χ (emMultUnit q hq hne (n + j)) : ℂ) =
      (χ (emMultUnit q hq hne n) : ℂ) := by
    intro n
    simp
  simp_rw [h1] at hN₀
  exact hN₀ N hN

/-- **Walk autocorrelation sum from EscapeDecorrelation**: for order-2 χ,
    `EscapeDecorrelation` at lag h implies the walk autocorrelation sum
    ∑_{n<N} χ(w(n+h))·χ(w(n)) = o(N).

    **Proof**: By `quadratic_autocorrelation_eq_mult_product`,
    χ(w(n+h))·χ(w(n)) = ∏_{j<h} χ(m(n+j)).  The result follows directly. -/
theorem escape_dec_implies_walk_autocorr_bound (hed : EscapeDecorrelation)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (hord2 : IsOrder2 χ)
    (h : ℕ) (hh : 0 < h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N,
        ((χ (emWalkUnit q hq hne (n + h)) : ℂ) *
         (χ (emWalkUnit q hq hne n) : ℂ))‖ ≤ ε * N := by
  obtain ⟨N₀, hN₀⟩ := hed q hq hne χ hχ hord2 h hh ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hcongr : ∀ n ∈ Finset.range N,
      (χ (emWalkUnit q hq hne (n + h)) : ℂ) * (χ (emWalkUnit q hq hne n) : ℂ) =
      ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ) :=
    fun n _ => quadratic_autocorrelation_eq_mult_product hq hne χ hord2 n h
  rw [Finset.sum_congr rfl hcongr]
  exact hN₀ N hN

/-- **EscapeDecorrelation implies QuadraticCCSB via VdC**: given a Van der Corput
    type bound (stated as a local hypothesis to avoid cross-file imports) and
    `EscapeDecorrelation`, we obtain `QuadraticCCSB`.

    The VdC hypothesis states: for all ε > 0, if every autocorrelation R_h is
    bounded by ε·N (for 1 ≤ h ≤ H) and H is large enough, then |S_N|² ≤ C·ε·N²
    for large N.

    This is the content of `van_der_corput_bound` (§69, `LargeSieveAnalytic.lean`),
    specialized to order-2 characters where the autocorrelation equals the
    multiplier product sum.

    The VdC hypothesis is parameterized as:
      For all (q, χ) order-2, ε > 0:
      if ∀ h ∈ [1,H], ‖R_h(N)‖ ≤ ε·N for large N, then ‖S_N‖ ≤ C(ε,H)·N for large N,
      where C(ε,H) → 0 as H → ∞ with ε → 0 appropriately. -/
theorem escape_dec_implies_quadratic_ccsb
    (hvdc : ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
      ∀ (δ : ℝ) (_hδ : 0 < δ),
      ∃ H₀ : ℕ, ∀ H ≥ H₀,
        (∀ (h : ℕ), 1 ≤ h → h ≤ H →
         ∃ N₀ : ℕ, ∀ N ≥ N₀,
           ‖∑ n ∈ Finset.range N,
             ((χ (emWalkUnit q hq hne (n + h)) : ℂ) *
              (χ (emWalkUnit q hq hne n) : ℂ))‖ ≤ δ * N) →
        ∃ N₁ : ℕ, ∀ N ≥ N₁,
          ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ δ * N)
    (hed : EscapeDecorrelation) : QuadraticCCSB := by
  intro q _ hq hne χ hχ hord2 ε hε
  -- Use VdC with δ = ε
  obtain ⟨H₀, hH₀⟩ := hvdc q hq hne χ hχ hord2 ε hε
  -- Take H = max H₀ 1 (ensuring H ≥ H₀ and H ≥ 1)
  set H := max H₀ 1 with hH_def
  have hH_ge : H ≥ H₀ := le_max_left H₀ 1
  -- Apply VdC at this H
  apply hH₀ H hH_ge
  -- Need: for all 1 ≤ h ≤ H, the walk autocorrelation is ≤ ε·N
  intro h hh1 _hhH
  -- EscapeDecorrelation at lag h gives multiplier product bound,
  -- which equals walk autocorrelation by quadratic_autocorrelation_eq_mult_product
  exact escape_dec_implies_walk_autocorr_bound hed q hq hne χ hχ hord2 h hh1 ε hε

/-- **EscapeDecorrelation implies QuadraticCCSB implies MC**: the chain from
    escape decorrelation through quadratic CCSB to Mullin's Conjecture,
    assuming the VdC bridge and CCSB → MC pathway.

    Chain: EscapeDecorrelation →[VdC]→ QuadraticCCSB → CCSB → MC
    (The last step CCSB → MC is via `complex_csb_mc'` from §34, but QuadraticCCSB
    is weaker than full CCSB. For the MC implication we need CCSB for ALL characters
    not just order-2 ones. Thus the full MC chain requires additional hypotheses
    for characters of order ≥ 3.) -/
theorem escape_dec_quadratic_ccsb_chain
    (hvdc : ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
      ∀ (δ : ℝ) (_hδ : 0 < δ),
      ∃ H₀ : ℕ, ∀ H ≥ H₀,
        (∀ (h : ℕ), 1 ≤ h → h ≤ H →
         ∃ N₀ : ℕ, ∀ N ≥ N₀,
           ‖∑ n ∈ Finset.range N,
             ((χ (emWalkUnit q hq hne (n + h)) : ℂ) *
              (χ (emWalkUnit q hq hne n) : ℂ))‖ ≤ δ * N) →
        ∃ N₁ : ℕ, ∀ N ≥ N₁,
          ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ δ * N)
    (hed : EscapeDecorrelation) : QuadraticCCSB :=
  escape_dec_implies_quadratic_ccsb hvdc hed

end EscapeDecorrelation

/-! ## §76. General Walk Sum Decomposition

This section extends the order-2 results of §73 to characters of arbitrary order.

**Key insight**: For ANY non-trivial character χ, the telescope identity
(§37) splits cleanly into kernel terms (= 0) and escape terms.  The
*weighted* escape sum `∑_{esc} χ(w(n))·(χ(m(n))−1)` has norm ≤ 2
regardless of the character order.

**What does NOT generalize**: For order-2 characters, all escape
rotations equal −1, so χ(m(n))−1 = −2 is constant, and one can divide
by −2 to bound the *unweighted* escape sum `∑_{esc} χ(w(n))` by 1.
For characters of order d ≥ 3, the escape rotations χ(m(n))−1 vary
among d−1 different non-zero values.  The unweighted escape sum
`∑_{esc} χ(w(n))` is therefore NOT bounded by O(1) in general:
adversarial phase alignment among d−1 rotations can cause constructive
interference making the escape sum Θ(N).

Consequently, for d ≥ 3, CCSB does NOT reduce to controlling the
kernel-block sum alone (unlike the d = 2 case proved in §73).

**Results proved here**:
1. `escape_telescope_general` — weighted escape sum = χ(w(N))−χ(w(0)) for all χ
2. `escape_char_val_sub_one_norm_pos` — pointwise: χ(u) ≠ 1 → ‖χ(u)−1‖ > 0
3. `escape_min_dist_pos` — finite minimum distance for nontrivial character
4. `general_walk_sum_le_kernel_sum_add_escape_sum` — ‖S_N‖ ≤ ‖S_ker‖+‖S_esc‖
5. `general_kernel_sum_le_walk_sum_add_escape_sum` — ‖S_ker‖ ≤ ‖S_N‖+‖S_esc‖
-/

section GeneralWalkSumDecomposition

/-- **General escape telescope**: for any character χ (not necessarily order 2),
    the telescope identity restricted to escape steps gives
      ∑_{esc} χ(w(n)) · (χ(m(n)) − 1) = χ(w(N)) − χ(w(0)).

    Kernel terms (χ(m(n)) = 1) contribute zero to the telescope sum,
    so only escape terms remain. -/
theorem escape_telescope_general {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1)) =
    (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
  have htel := walk_telescope_identity q hq hne χ N
  -- Split the LHS sum by the predicate (χ(m(n)) = 1)
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1))).symm
  rw [hsplit] at htel
  -- Kernel terms vanish: χ(m(n)) = 1 implies χ(m(n)) - 1 = 0
  have hker_zero : ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [hn.2, sub_self, mul_zero]
  rw [hker_zero, zero_add] at htel
  exact htel

/-- **General weighted escape norm bound**: the weighted escape sum has
    norm at most 2, for any character. This is an immediate corollary of
    `escape_telescope_general` and the triangle inequality. -/
theorem escape_telescope_general_norm_bound {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1))‖ ≤ 2 := by
  rw [escape_telescope_general hq hne χ N]
  calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
      ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
        norm_sub_le _ _
    _ = 1 + 1 := by
        rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
    _ = 2 := by ring

/-- **Pointwise escape distance**: if a character value is not 1, then
    ‖χ(u) − 1‖ > 0.  Immediate from the fact that χ(u) ≠ 1 makes
    χ(u) − 1 nonzero. -/
theorem escape_char_val_sub_one_norm_pos {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (u : (ZMod q)ˣ)
    (hne : (χ u : ℂ) ≠ 1) :
    0 < ‖(χ u : ℂ) - 1‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr hne)

/-- **Minimum escape distance**: for a non-trivial character χ, there
    exists a positive constant δ such that ‖χ(u) − 1‖ ≥ δ for every u
    with χ(u) ≠ 1.  The character image is finite (since the domain is
    finite), so the minimum over the non-empty set of non-identity
    character values is achieved and positive. -/
theorem escape_min_dist_pos {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : (ZMod q)ˣ, (χ u : ℂ) ≠ 1 → δ ≤ ‖(χ u : ℂ) - 1‖ := by
  -- Since χ ≠ 1, there exists some unit u₀ with χ(u₀) ≠ 1
  have hne_exists : ∃ u₀ : (ZMod q)ˣ, (χ u₀ : ℂ) ≠ 1 := by
    by_contra hall
    push_neg at hall
    apply hχ
    ext u
    specialize hall u
    -- χ u = 1 as ℂˣ iff (χ u : ℂ) = (1 : ℂ)
    have : χ u = 1 := Units.val_injective (by simp [Units.val_one, hall])
    simp [this]
  -- Consider the set of distances {‖χ(u) - 1‖ : u ∈ univ, χ(u) ≠ 1}
  set S := Finset.univ.filter (fun u : (ZMod q)ˣ => (χ u : ℂ) ≠ 1) with hS_def
  have hS_nonempty : S.Nonempty := by
    obtain ⟨u₀, hu₀⟩ := hne_exists
    exact ⟨u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₀⟩⟩
  -- The image set of distances
  set T := S.image (fun u => ‖(χ u : ℂ) - 1‖) with hT_def
  have hT_nonempty : T.Nonempty := hS_nonempty.image _
  -- All elements of T are positive (each χ(u) ≠ 1 means ‖χ(u)-1‖ > 0)
  have hT_pos : ∀ t ∈ T, 0 < t := by
    intro t ht
    rw [hT_def, Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact escape_char_val_sub_one_norm_pos χ u
      ((Finset.mem_filter.mp hu).2)
  -- Take δ = min of T
  set δ := T.min' hT_nonempty with hδ_def
  refine ⟨δ, ?_, ?_⟩
  · -- δ > 0: δ is the minimum of a finite set of positive reals
    exact hT_pos δ (Finset.min'_mem T hT_nonempty)
  · -- ∀ u, χ(u) ≠ 1 → δ ≤ ‖χ(u) - 1‖
    intro u hu
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩

/-- **General walk sum triangle bound**: for any character (not just order 2),
    the full walk sum norm is bounded by the kernel-block sum norm plus the
    escape sum norm.  This is simply the triangle inequality applied to
    the kernel-escape decomposition `quadratic_walk_sum_split`.

    (The name `quadratic_walk_sum_split` is historical — it does not
    require IsOrder2.) -/
theorem general_walk_sum_le_kernel_sum_add_escape_sum {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ +
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ := by
  rw [quadratic_walk_sum_split hq hne χ N]
  exact norm_add_le _ _

/-- **General kernel sum triangle bound**: the kernel-block sum norm is
    bounded by the full walk sum norm plus the escape sum norm.
    Reverse direction of `general_walk_sum_le_kernel_sum_add_escape_sum`.
    No IsOrder2 hypothesis needed. -/
theorem general_kernel_sum_le_walk_sum_add_escape_sum {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ +
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ := by
  set kerSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  set escSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  have hsplit : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      kerSum + escSum := quadratic_walk_sum_split hq hne χ N
  have hker_eq : kerSum = (∑ n ∈ Finset.range N,
      (χ (emWalkUnit q hq hne n) : ℂ)) - escSum := by
    rw [hsplit]; ring
  calc ‖kerSum‖
      = ‖(∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)) - escSum‖ := by
        rw [hker_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + ‖escSum‖ :=
        norm_sub_le _ _

end GeneralWalkSumDecomposition

/-! ## §77. Quadratic Block Alternation Structure

This section documents structural properties of the d=2 (order-2 character)
walk that are unique to the quadratic case.

**Key insight unique to d=2**: For order-2 characters, the walk character
χ(w(n)) takes values in {+1, −1}, and every escape step negates this value.
Between consecutive escapes, the walk character is constant.  The kernel-block
sum `∑_{ker} χ(w(n))` is therefore a pure alternating series of block lengths:

  s · (L₁ − L₂ + L₃ − ⋯)

where s ∈ {+1, −1} is the initial sign and Lₖ is the length of the k-th
kernel block.  CCSB for order-2 characters is thus equivalent to this
alternating block-length sum being o(N) — a much more concrete condition
than the general CCSB.

For d ≥ 3, escape rotations are NOT all the same, so no analogous
alternation structure exists (see §76 discussion).

**Results proved here**:
1. `order2_not_one_eq_neg_one` — for d=2, χ(u) ≠ 1 implies χ(u) = −1
2. `kernel_opposite_after_escape` — kernel step then escape flips walk char
3. `kernel_block_walk_char_constant` — consecutive kernel steps preserve walk char
4. `quadratic_kernel_sum_on_block` — kernel block sum = block_length · χ(w(start))
-/

section QuadraticBlockAlternation

/-- For an order-2 character, if a character value is not 1 then it must be −1.
    This is the dichotomy from `IsOrder2` with the first branch excluded. -/
theorem order2_not_one_eq_neg_one {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (u : (ZMod q)ˣ)
    (hne : (χ u : ℂ) ≠ 1) :
    (χ u : ℂ) = -1 := by
  rcases hord2 u with h | h
  · exact absurd h hne
  · exact h

/-- **Kernel-then-escape flips walk character**: if step n is a kernel step
    (χ(m(n)) = 1) and step n+1 is an escape (χ(m(n+1)) ≠ 1), then for an
    order-2 character, χ(w(n+2)) = −χ(w(n)).

    **Proof**: By `char_walk_recurrence`, χ(w(n+1)) = χ(w(n)) · χ(m(n)) = χ(w(n)) · 1
    and χ(w(n+2)) = χ(w(n+1)) · χ(m(n+1)) = χ(w(n)) · (−1) = −χ(w(n)). -/
theorem kernel_opposite_after_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (n : Nat)
    (hker_n : (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (hesc : (χ (emMultUnit q hq hne (n + 1)) : ℂ) ≠ 1) :
    (χ (emWalkUnit q hq hne (n + 2)) : ℂ) =
      -(χ (emWalkUnit q hq hne n) : ℂ) := by
  -- Step 1: χ(w(n+1)) = χ(w(n)) · χ(m(n)) = χ(w(n)) · 1 = χ(w(n))
  have h1 : (χ (emWalkUnit q hq hne (n + 1)) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) := by
    rw [char_walk_recurrence q hq hne χ n, hker_n, mul_one]
  -- Step 2: χ(m(n+1)) = -1 since it's an escape for order-2
  have h2 : (χ (emMultUnit q hq hne (n + 1)) : ℂ) = -1 :=
    order2_not_one_eq_neg_one χ hord2 _ hesc
  -- Step 3: χ(w(n+2)) = χ(w(n+1)) · χ(m(n+1)) = χ(w(n)) · (-1) = -χ(w(n))
  rw [char_walk_recurrence q hq hne χ (n + 1), h1, h2, mul_neg_one]

/-- **Consecutive kernel steps preserve walk character**: if steps n, n+1, ..., n+k-1
    are all kernel steps (χ(m(n+j)) = 1 for j < k), then χ(w(n+k)) = χ(w(n)).

    This is an induction on `kernel_preserves_walk_char`. -/
theorem kernel_block_walk_char_constant {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (n k : Nat)
    (hker : ∀ j, j < k → (χ (emMultUnit q hq hne (n + j)) : ℂ) = 1) :
    (χ (emWalkUnit q hq hne (n + k)) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hker_prev : ∀ j, j < k → (χ (emMultUnit q hq hne (n + j)) : ℂ) = 1 :=
      fun j hj => hker j (Nat.lt_succ_of_lt hj)
    rw [show n + (k + 1) = (n + k) + 1 from by omega]
    rw [char_walk_recurrence q hq hne χ (n + k)]
    rw [hker k (Nat.lt_succ_iff.mpr le_rfl), mul_one]
    exact ih hker_prev

/-- **Kernel block sum formula**: on a block of L consecutive kernel steps
    starting at index n, the sum of walk character values equals L times
    the walk character value at the start of the block.

    This is the quantitative consequence of `kernel_block_walk_char_constant`:
    since all walk character values in the block are equal, the sum is just
    the common value times the block length. -/
theorem quadratic_kernel_sum_on_block {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (n L : Nat)
    (hker : ∀ j, j < L → (χ (emMultUnit q hq hne (n + j)) : ℂ) = 1) :
    ∑ j ∈ Finset.range L, (χ (emWalkUnit q hq hne (n + j)) : ℂ) =
      L * (χ (emWalkUnit q hq hne n) : ℂ) := by
  have hcongr : ∀ j ∈ Finset.range L, (χ (emWalkUnit q hq hne (n + j)) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) := by
    intro j hj
    exact kernel_block_walk_char_constant hq hne χ n j
      (fun i hi => hker i (Nat.lt_trans hi (Finset.mem_range.mp hj)))
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_comm]

end QuadraticBlockAlternation

/-! ## §78. Escape Alternation Structure

For order-2 characters, escapes from the kernel alternate the walk character
value between +1 and −1. This section formalizes:

1. `escape_values_alternate` — if e₁ is an escape position and all steps
   between e₁ and e₂ are kernel steps, then χ(w(e₂)) = −χ(w(e₁)).
2. `kernel_sum_between_escapes` — the kernel-block sum between consecutive
   escapes e₁, e₂ equals (e₂ − e₁ − 1) · (−χ(w(e₁))).
-/

section EscapeAlternation

/-- **Escape alternation for order-2 characters**: if position e₁ is an escape
    (χ(m(e₁)) ≠ 1) and all positions strictly between e₁ and e₂ are kernel
    steps (χ(m(j)) = 1), then the walk character flips:
    χ(w(e₂)) = −χ(w(e₁)).

    Proof: The escape at e₁ gives χ(w(e₁+1)) = χ(w(e₁))·χ(m(e₁)) = −χ(w(e₁))
    (by `char_walk_recurrence` + `order2_not_one_eq_neg_one`). Then the
    kernel steps from e₁+1 to e₂ preserve the walk character
    (by `kernel_block_walk_char_constant`). -/
theorem escape_values_alternate {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (e₁ e₂ : Nat)
    (hlt : e₁ < e₂)
    (hesc₁ : (χ (emMultUnit q hq hne e₁) : ℂ) ≠ 1)
    (hker_between : ∀ j, e₁ < j → j < e₂ →
      (χ (emMultUnit q hq hne j) : ℂ) = 1) :
    (χ (emWalkUnit q hq hne e₂) : ℂ) =
      -(χ (emWalkUnit q hq hne e₁) : ℂ) := by
  -- Write e₂ = (e₁ + 1) + (e₂ - e₁ - 1)
  have hle : e₁ + 1 ≤ e₂ := hlt
  set k := e₂ - (e₁ + 1) with hk_def
  have he₂_eq : e₂ = e₁ + 1 + k := by omega
  -- Step 1: escape at e₁ flips walk char
  have hm_neg : (χ (emMultUnit q hq hne e₁) : ℂ) = -1 :=
    order2_not_one_eq_neg_one χ hord2 _ hesc₁
  have hflip : (χ (emWalkUnit q hq hne (e₁ + 1)) : ℂ) =
      -(χ (emWalkUnit q hq hne e₁) : ℂ) :=
    escape_flips_walk_char hq hne χ e₁ hm_neg
  -- Step 2: kernel steps from e₁+1 to e₂ preserve walk char
  have hker_block : ∀ j, j < k →
      (χ (emMultUnit q hq hne (e₁ + 1 + j)) : ℂ) = 1 := by
    intro j hj
    apply hker_between (e₁ + 1 + j)
    · omega
    · omega
  have hconst : (χ (emWalkUnit q hq hne (e₁ + 1 + k)) : ℂ) =
      (χ (emWalkUnit q hq hne (e₁ + 1)) : ℂ) :=
    kernel_block_walk_char_constant hq hne χ (e₁ + 1) k hker_block
  -- Combine
  rw [he₂_eq, hconst, hflip]

/-- **Kernel-block sum between consecutive escapes**: if e₁ is an escape
    position and all steps from e₁+1 to e₂−1 are kernel steps, then the
    sum of walk character values over these kernel positions equals
    (e₂ − e₁ − 1) · (−χ(w(e₁))).

    The kernel block starts at e₁+1 (after the escape flips the walk char
    to −χ(w(e₁))) and runs for e₂−e₁−1 steps. By
    `quadratic_kernel_sum_on_block`, the sum is the block length times the
    common walk char value, which is −χ(w(e₁)). -/
theorem kernel_sum_between_escapes {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (e₁ e₂ : Nat)
    (hlt : e₁ + 1 < e₂)
    (hesc₁ : (χ (emMultUnit q hq hne e₁) : ℂ) ≠ 1)
    (hker : ∀ j, e₁ < j → j < e₂ →
      (χ (emMultUnit q hq hne j) : ℂ) = 1) :
    ∑ j ∈ Finset.range (e₂ - e₁ - 1),
      (χ (emWalkUnit q hq hne (e₁ + 1 + j)) : ℂ) =
    (e₂ - e₁ - 1 : ℕ) * (-(χ (emWalkUnit q hq hne e₁) : ℂ)) := by
  -- The kernel block starts at e₁+1 with length L = e₂ - e₁ - 1
  set L := e₂ - e₁ - 1 with hL_def
  -- All steps in [e₁+1, e₁+1+L) are kernel steps
  have hker_block : ∀ j, j < L →
      (χ (emMultUnit q hq hne (e₁ + 1 + j)) : ℂ) = 1 := by
    intro j hj
    apply hker (e₁ + 1 + j)
    · omega
    · omega
  -- Apply quadratic_kernel_sum_on_block to get sum = L · χ(w(e₁+1))
  have hblock := quadratic_kernel_sum_on_block hq hne χ (e₁ + 1) L hker_block
  rw [hblock]
  -- Now show χ(w(e₁+1)) = -χ(w(e₁))
  have hm_neg : (χ (emMultUnit q hq hne e₁) : ℂ) = -1 :=
    order2_not_one_eq_neg_one χ hord2 _ hesc₁
  have hflip : (χ (emWalkUnit q hq hne (e₁ + 1)) : ℂ) =
      -(χ (emWalkUnit q hq hne e₁) : ℂ) :=
    escape_flips_walk_char hq hne χ e₁ hm_neg
  rw [hflip]

end EscapeAlternation

