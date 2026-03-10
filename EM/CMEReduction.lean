import EM.LargeSieveSpectral

/-!
# CME Reduction: Conditional Multiplier Equidistribution and Fiber Energy Bounds

Conditional multiplier equidistribution (CME), fiber energy bounds (FEB),
and hierarchy connectors extracted from LargeSieveSpectral.lean.

## Main Results

* `ConditionalMultiplierEquidist` : CME definition
* `cme_implies_ccsb`   : CME ⟹ CCSB bypassing BRE (PROVED)
* `cme_implies_mc`      : CME ⟹ MC (PROVED)
* `FiberEnergyBound`    : L² fiber control (def)
* `cme_implies_feb`     : CME → FEB (PROVED: L^∞ implies L²)
* `feb_implies_ccsb`    : FEB → CCSB (PROVED: Cauchy-Schwarz)
* `feb_implies_mc`      : FEB → MC (PROVED: composition)
* `ccsb_implies_mmcsb`  : CCSB → MMCSB with Q₀ = 0 (PROVED)
* `ccsb_implies_sve`    : CCSB → SVE (PROVED, completes CCSB ⟺ SVE)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## §70: Conditional Multiplier Equidistribution (CME)

CME captures the number-theoretic content that the EM multiplier m(n) = minFac(prod(n)+1)
has equidistributed character values CONDITIONAL on the walk position w(n).

### Position in the hierarchy:
- CME IMPLIES DecorrelationHypothesis (h=1 multiplier cancellation)
- CME IMPLIES ComplexCharSumBound (proved via telescoping identity + fiber decomposition)
- CME does NOT imply HOD for h >= 2 (Dead End #81)
- Hierarchy: PED < Dec < CME ≤ CCSB -/

section ConditionalMultiplierEquidist

open Classical

/-- **Conditional Multiplier Equidistribution**: for any prime q not in the EM
    sequence, any nontrivial character chi, and any walk position a in (ZMod q)^*,
    the multiplier character sum restricted to steps where w(n) = a is o(N).

    This captures: "the least prime factor of integers in a specific congruence
    class mod q is equidistributed among coprime residue classes."

    Position in hierarchy: PED < Dec < CME ≤ CCSB.
    CME implies both Dec and CCSB (proved via telescoping identity).
    CME does NOT imply HOD for h >= 2 (Dead End #81). -/
def ConditionalMultiplierEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- The fiber-restricted multiplier character sum: the sum of χ(m(n)) over
    indices n < N where the walk position w(n) = a.

    This is the central quantity in CME: the character sum restricted to a
    single walk-position fiber. CME says this is o(N) for all fibers. -/
noncomputable def fiberMultCharSum (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
    (χ (emMultUnit q hq hne n) : ℂ)

/-- CME is equivalent to: for all q, χ ≠ 1, a, ε > 0, eventually
    ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N.

    This is just unfolding the definition — the sum in CME is exactly
    `fiberMultCharSum`. -/
theorem cme_iff_fiber_bound :
    ConditionalMultiplierEquidist ↔
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ),
    ∀ (ε : ℝ) (_hε : 0 < ε),
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N :=
  Iff.rfl

/-- The total multiplier character sum decomposes as the sum of fiber sums
    over all walk positions.

    `∑_{n<N} χ(m(n)) = ∑_a fiberMultCharSum q hq hne χ a N` -/
theorem mult_char_sum_eq_fiber_sum (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a N := by
  simp only [fiberMultCharSum]
  rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ))]

/-- **CME implies DecorrelationHypothesis**: the total multiplier character sum
    decomposes as a sum over walk positions. By triangle inequality and the
    conditional bound from CME, the total sum is o(N).

    Proof: partition {0,...,N-1} by walk position w(n) = a, apply triangle
    inequality, bound each conditional sum by CME with epsilon/(q-1), and
    sum over at most (q-1) positions. -/
theorem cme_implies_dec (hcme : ConditionalMultiplierEquidist) :
    DecorrelationHypothesis := by
  intro q inst hq hne χ hχ ε hε
  -- Number of walk positions: Fintype.card (ZMod q)ˣ
  haveI : Fact (Nat.Prime q) := inst
  set C := Fintype.card (ZMod q)ˣ with hC_def
  -- C ≥ 1 since the group is nonempty (contains 1)
  have hC_pos : (0 : ℝ) < C := by
    have : 0 < C := Fintype.card_pos
    exact Nat.cast_pos.mpr this
  -- Set ε' = ε / C
  set ε' := ε / C with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε hC_pos
  -- For each walk position a, CME gives N₀(a) such that the conditional sum ≤ ε' * N
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε' * N :=
    fun a => hcme q hq hne χ hχ a ε' hε'_pos
  -- Choose N₀(a) for each a
  choose N₀_fn hN₀_fn using hcme_a
  -- Take the maximum N₀ over all a
  set N₀ := Finset.univ.sup N₀_fn with hN₀_def
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 1: Partition the sum by walk position using sum_fiberwise
  have hdecomp : ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
      ∑ a : (ZMod q)ˣ, ∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ) := by
    rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
      (fun n => (χ (emMultUnit q hq hne n) : ℂ))]
  rw [hdecomp]
  -- Step 2: Triangle inequality
  calc ‖∑ a : (ZMod q)ˣ, ∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ, ε' * N := by
        apply Finset.sum_le_sum
        intro a _
        apply hN₀_fn a N
        exact le_trans (Finset.le_sup (Finset.mem_univ a)) hN
    _ = C * (ε' * N) := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = ε * N := by
        rw [hε'_def]
        field_simp

/-- **Walk-multiplier product decomposes by fiber**: the sum
    `∑_{n<N} χ(w(n))·χ(m(n))` equals the fiber-weighted sum
    `∑_a χ(a) · ∑_{w(n)=a} χ(m(n))`.

    This is a direct application of `Finset.sum_fiberwise` combined with the fact
    that `χ(w(n))` is constant (equal to `χ(a)`) on the fiber `{n : w(n) = a}`. -/
theorem walk_mult_product_fiber_decomp (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ)) =
    ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
      ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ) := by
  rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))]
  congr 1
  ext a
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

/-- **CME implies CCSB**: Conditional Multiplier Equidistribution implies
    the Complex Character Sum Bound, via the telescoping identity and
    fiber decomposition.

    This is the key reduction that bypasses PEDImpliesComplexCSB entirely.
    The proof uses:
    1. The telescoping identity: `∑ χ(w(n))·(χ(m(n))-1) = χ(w(N)) - χ(w(0))`
    2. Fiber decomposition: `∑ χ(w(n))·χ(m(n)) = ∑_a χ(a) · ∑_{w(n)=a} χ(m(n))`
    3. CME bounds each fiber sum by `ε·N`
    4. Triangle inequality sums over at most `C = Fintype.card (ZMod q)ˣ` fibers

    Position in hierarchy: CME implies CCSB (proved). CME implies HOD remains false. -/
theorem cme_implies_ccsb (hcme : ConditionalMultiplierEquidist) :
    ComplexCharSumBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Step 1: Set up ε' for CME fiber bounds
  -- We need C * (ε' * N) + 2 ≤ ε * N, so set ε' = ε/(2*C) and require N ≥ 4/ε
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := by
    have : 0 < C := Fintype.card_pos
    exact Nat.cast_pos.mpr this
  set ε' := ε / (2 * C) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε (mul_pos two_pos hC_pos)
  -- Step 2: Get N₀ from CME for each fiber, take maximum
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε' * N :=
    fun a => hcme q hq hne χ hχ a ε' hε'_pos
  choose N₀_fn hN₀_fn using hcme_a
  set N₀_cme := Finset.univ.sup N₀_fn
  -- Also need N₀ large enough that 2 ≤ (ε/2) * N, i.e., N ≥ 4/ε
  set N₀_boundary := Nat.ceil (4 / ε)
  set N₀ := max N₀_cme N₀_boundary
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 3: Use the telescoping identity to express S_N
  have hSN_eq := walk_sum_eq_product_sub_boundary q hq hne χ N
  -- Step 4: Bound the product sum via fiber decomposition and CME
  have hfiber := walk_mult_product_fiber_decomp q hq hne χ N
  -- Step 5: Bound norm of product sum using triangle inequality + CME
  have hprod_bound : ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖
      ≤ C * (ε' * N) := by
    rw [hfiber]
    calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * ∑ n ∈ (Finset.range N).filter
          (fun n => emWalkUnit q hq hne n = a), (χ (emMultUnit q hq hne n) : ℂ)‖
        ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * ∑ n ∈ (Finset.range N).filter
          (fun n => emWalkUnit q hq hne n = a), (χ (emMultUnit q hq hne n) : ℂ)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ a : (ZMod q)ˣ, ‖∑ n ∈ (Finset.range N).filter
          (fun n => emWalkUnit q hq hne n = a), (χ (emMultUnit q hq hne n) : ℂ)‖ := by
            apply Finset.sum_le_sum; intro a _
            rw [norm_mul]
            calc ‖(χ a : ℂ)‖ * _ ≤ 1 * _ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  exact le_of_eq (walkTelescope_char_norm_one χ a)
              _ = _ := one_mul _
      _ ≤ ∑ _a : (ZMod q)ˣ, ε' * ↑N := by
            apply Finset.sum_le_sum; intro a _
            exact hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a))
              (le_max_left _ _ |>.trans hN))
      _ = C * (ε' * N) := by
            rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
  -- Step 6: Bound the boundary term ‖χ(w(N)) - χ(w(0))‖ ≤ 2
  have hboundary := walk_boundary_norm_le_two q hq hne χ N
  -- Step 7: N ≥ 4/ε ensures the boundary term is absorbed
  have hN_ge_boundary : (4 / ε : ℝ) ≤ N := by
    calc (4 / ε : ℝ) ≤ ↑(Nat.ceil (4 / ε)) := Nat.le_ceil _
      _ ≤ ↑N := by
          exact_mod_cast le_trans (le_max_right N₀_cme N₀_boundary) hN
  have hε_half_N : 2 ≤ ε / 2 * (N : ℝ) := by
    have h4 : 4 ≤ ε * (N : ℝ) := by
      have := (div_le_iff₀ hε).mp hN_ge_boundary
      linarith
    linarith
  -- Step 8: Combine everything
  calc ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖
      = ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))
        - ((χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ))‖ := by
          rw [hSN_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))‖ +
        ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
    _ ≤ C * (ε' * N) + 2 := by linarith [hprod_bound, hboundary]
    _ = ε / 2 * N + 2 := by
          rw [hε'_def]
          have hC_ne : (C : ℝ) ≠ 0 := ne_of_gt hC_pos
          field_simp
    _ ≤ ε * N := by linarith [hε_half_N]

/-- **CME implies MC** (single hypothesis): CME implies Mullin's Conjecture
    directly, bypassing PEDImpliesComplexCSB entirely.
    Composes `cme_implies_ccsb` with `complex_csb_mc'`. -/
theorem cme_implies_mc (hcme : ConditionalMultiplierEquidist) : MullinConjecture :=
  complex_csb_mc' (cme_implies_ccsb hcme)

/-- **CME implies MC (old chain)**: Conditional Multiplier Equidistribution implies
    Mullin's Conjecture, via the chain CME -> Dec -> PED -> CCSB -> MC.
    Requires PEDImpliesComplexCSB (the block-rotation estimate bridge).
    Superseded by `cme_implies_mc` which needs no additional hypotheses. -/
theorem cme_chain_mc (hcme : ConditionalMultiplierEquidist)
    (hped_csb : PEDImpliesComplexCSB) : MullinConjecture :=
  decorrelation_mc' (cme_implies_dec hcme) hped_csb

end ConditionalMultiplierEquidist

/-! ## S80. Fiber Energy Bounds

The **Fiber Energy Bound** is the L² version of CME: instead of controlling
each fiber multiplier sum individually (L^∞), we control the sum of squares
∑_a ‖F(a)‖² (L² energy).

### Key Results

* `FiberEnergyBound`     : L² fiber control (def)
* `cme_implies_feb`      : CME → FEB (PROVED: L^∞ implies L²)
* `feb_implies_ccsb`     : FEB → CCSB (PROVED: Cauchy-Schwarz, alternative to triangle inequality)
* `feb_implies_mc`       : FEB → MC (PROVED: composition)

### Dead End #93

While FEB → CCSB via a clean Cauchy-Schwarz argument (avoiding the triangle
inequality in `cme_implies_ccsb`), FEB is NOT strictly weaker than CME for
fixed q. The finite fiber count (q-1 positions) makes L² and L^∞ equivalent
via Markov's inequality: with CC_χ = o(N²) and T = ε·N, the number of fibers
where ‖F(a)‖ > T is #{a : ‖F(a)‖² > (εN)²} ≤ CC_χ/(εN)² = o(1), so eventually
all fibers satisfy the L^∞ bound.

Conclusion: No L^p interpolation between Dec and CCSB provides a strictly
weaker intermediate. The viable routes remain SieveTransfer, CME, or direct
CCSB approaches.
-/

section FiberEnergyBounds

open Classical

/-- **Fiber Energy Bound**: for every missing prime q, every nontrivial character χ,
    and ε > 0, eventually ∑_a ‖fiberMultCharSum q χ a N‖² ≤ ε · N².

    This is the L² fiber control condition: the fiber multiplier char sums are
    small in aggregate. CC_χ(N) = ∑_a |F(a)|² is the "conditional collision sum."

    Position in hierarchy:
    - CME → FiberEnergyBound (L^∞ → L²)
    - FiberEnergyBound → CCSB (Cauchy-Schwarz, proved below)
    - CCSB does NOT imply FiberEnergyBound (fibers can cancel by character weighting)
    - FiberEnergyBound ⟺ CME for fixed q (Markov on finitely many positions)

    In summary: FiberEnergyBound is equivalent to CME but implies CCSB
    by a different proof (Cauchy-Schwarz rather than triangle inequality).
    This is Dead End #93: the L² perspective does not provide a strictly
    weaker intermediate between CME and CCSB. -/
def FiberEnergyBound : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤ ε * (N : ℝ) ^ 2

/-- **CME implies FEB**: Conditional Multiplier Equidistribution implies
    Fiber Energy Bound. This is the L^∞ to L² implication.

    Proof: CME gives ‖F(a)‖ ≤ ε'·N for each fiber a. Then
    ∑_a ‖F(a)‖² ≤ ∑_a (ε'·N)² = C·(ε')²·N²
    where C = φ(q) is the number of fibers.
    To achieve ∑ ≤ ε·N², choose ε' = √(ε/C).

    Dead End #93: FEB ⟺ CME for fixed q, so this is an alternative
    route equivalent to the already-proved CME → CCSB path. -/
theorem cme_implies_feb (hcme : ConditionalMultiplierEquidist) : FiberEnergyBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- C = number of fibers = card (ZMod q)ˣ
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Choose ε' = √(ε/C) so that C · (ε')² = ε
  set ε' := Real.sqrt (ε / C) with hε'_def
  have hε'_pos : 0 < ε' := Real.sqrt_pos.mpr (div_pos hε hC_pos)
  -- Get N₀(a) from CME for each fiber a
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε' * N := by
    intro a; exact (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε' hε'_pos
  choose N₀_fn hN₀_fn using hcme_a
  refine ⟨Finset.univ.sup N₀_fn, fun N hN => ?_⟩
  -- For each a, ‖F(a)‖ ≤ ε' · N
  have hfa : ∀ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε' * N :=
    fun a => hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a)) hN)
  -- ‖F(a)‖² ≤ (ε' · N)²
  have hfa_sq : ∀ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤ (ε' * N) ^ 2 := by
    intro a
    apply sq_le_sq'
    · linarith [norm_nonneg (fiberMultCharSum q hq hne χ a N),
                mul_nonneg hε'_pos.le (Nat.cast_nonneg N)]
    · exact hfa a
  -- Sum: ∑_a ‖F(a)‖² ≤ C · (ε' · N)²
  calc ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2
      ≤ ∑ _a : (ZMod q)ˣ, (ε' * N) ^ 2 := Finset.sum_le_sum fun a _ => hfa_sq a
    _ = C * (ε' * N) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = C * (ε' ^ 2 * N ^ 2) := by ring
    _ = C * (ε / C * N ^ 2) := by
        congr 1
        rw [hε'_def, Real.sq_sqrt (le_of_lt (div_pos hε hC_pos))]
    _ = ε * (N : ℝ) ^ 2 := by
        field_simp

/-- **FEB implies CCSB**: Fiber Energy Bound implies Complex Character Sum Bound,
    via Cauchy-Schwarz instead of the triangle inequality.

    Proof:
    1. Walk char sum telescoping: ∑_n χ(w(n))·(χ(m(n))-1) = χ(w(N)) - χ(w(0))
    2. Fiber decomposition: ∑_n χ(w(n))·χ(m(n)) = ∑_a χ(a)·F(a)
    3. Cauchy-Schwarz: ‖∑_a χ(a)·F(a)‖² ≤ C·(∑‖F(a)‖²) = C·CC_χ(N)
    4. FEB gives CC_χ(N) ≤ ε'·N², so ‖S_N‖ ≤ √(C·ε')·N + 2 = o(N)

    Dead End #93: FEB ⟺ CME for fixed q, so this alternative route
    is equivalent to the already-proved CME → CCSB → MC path. -/
theorem feb_implies_ccsb (hfeb : FiberEnergyBound) : ComplexCharSumBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- C = number of fibers
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Choose ε' for FEB: we need √(C · ε') + 2/N ≤ ε
  -- Set ε' = (ε/2)² / C, so √(C·ε') = ε/2
  set ε' := (ε / 2) ^ 2 / C with hε'_def
  have hε'_pos : 0 < ε' := div_pos (sq_pos_of_pos (half_pos hε)) hC_pos
  -- Get N₀ from FEB
  obtain ⟨N₀_feb, hN₀_feb⟩ := hfeb q hq hne χ hχ ε' hε'_pos
  -- Also need N large enough for boundary absorption: 4/ε ≤ N
  set N₀ := max N₀_feb (Nat.ceil (4 / ε))
  refine ⟨N₀, fun N hN => ?_⟩
  -- FEB bound
  have hfeb_N : ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤
      ε' * (N : ℝ) ^ 2 :=
    hN₀_feb N (le_trans (le_max_left _ _) hN)
  -- Use telescoping identity
  have hSN_eq := walk_sum_eq_product_sub_boundary q hq hne χ N
  -- Fiber decomposition of the product sum
  have hfiber := walk_mult_product_fiber_decomp q hq hne χ N
  -- Cauchy-Schwarz: ‖∑_a χ(a) · F(a)‖² ≤ (∑ ‖χ(a)‖²) · (∑ ‖F(a)‖²) = C · ∑ ‖F(a)‖²
  have hcs : ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤
      C * ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := by
    calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖ ^ 2
        ≤ (∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ = (∑ a : (ZMod q)ˣ, ‖(χ a : ℂ)‖ * ‖fiberMultCharSum q hq hne χ a N‖) ^ 2 := by
          congr 1; congr 1; ext a; exact norm_mul _ _
      _ = (∑ a : (ZMod q)ˣ, 1 * ‖fiberMultCharSum q hq hne χ a N‖) ^ 2 := by
          congr 1; congr 1; ext a
          rw [walkTelescope_char_norm_one χ a]
      _ ≤ (∑ _a : (ZMod q)ˣ, (1 : ℝ) ^ 2) *
          (∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun _ => (1 : ℝ)) (fun a => ‖fiberMultCharSum q hq hne χ a N‖)
      _ = C * ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := by
          simp [Finset.card_univ, hC_def]
  -- Product sum norm bound via Cauchy-Schwarz + FEB
  have hprod_norm_sq : ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖ ^ 2 ≤
      C * ε' * (N : ℝ) ^ 2 := by
    rw [hfiber]
    calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖ ^ 2
        ≤ C * ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := hcs
      _ ≤ C * (ε' * (N : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hfeb_N (le_of_lt hC_pos)
      _ = C * ε' * (N : ℝ) ^ 2 := by ring
  -- Extract norm bound (not squared)
  have hprod_norm : ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖ ≤
      ε / 2 * N := by
    have hCε' : C * ε' = (ε / 2) ^ 2 := by
      rw [hε'_def]; field_simp
    have hCε'_nn : 0 ≤ C * ε' := le_of_lt (mul_pos hC_pos hε'_pos)
    rw [hCε'] at hprod_norm_sq
    have hN_nn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hεN_nn : 0 ≤ ε / 2 * N := mul_nonneg (le_of_lt (half_pos hε)) hN_nn
    nlinarith [sq_nonneg (‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖ - ε / 2 * N)]
  -- Boundary term bound
  have hboundary := walk_boundary_norm_le_two q hq hne χ N
  -- N ≥ 4/ε ensures boundary absorption
  have hN_ge : (4 / ε : ℝ) ≤ N := by
    calc (4 / ε : ℝ) ≤ ↑(Nat.ceil (4 / ε)) := Nat.le_ceil _
      _ ≤ ↑N := by exact_mod_cast le_trans (le_max_right N₀_feb _) hN
  have hε_half_N : 2 ≤ ε / 2 * (N : ℝ) := by
    have h4 : 4 ≤ ε * (N : ℝ) := by
      have := (div_le_iff₀ hε).mp hN_ge; linarith
    linarith
  -- Combine
  calc ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖
      = ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))
        - ((χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ))‖ := by
          rw [hSN_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))‖ +
        ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
    _ ≤ ε / 2 * N + 2 := by linarith [hprod_norm, hboundary]
    _ ≤ ε * N := by linarith [hε_half_N]

/-- **FEB implies MC**: Fiber Energy Bound implies Mullin's Conjecture,
    via the Cauchy-Schwarz route FEB → CCSB → MC.

    This is an alternative to the triangle inequality route CME → CCSB → MC.
    Both routes are equivalent since FEB ⟺ CME for fixed q (Dead End #93). -/
theorem feb_implies_mc (hfeb : FiberEnergyBound) : MullinConjecture :=
  complex_csb_mc' (feb_implies_ccsb hfeb)

/-! ### Dead End #93: FiberEnergyBound ⟺ CME for fixed q.

While FiberEnergyBound implies CCSB via Cauchy-Schwarz (a clean alternative
to the triangle inequality in `cme_implies_ccsb`), it is NOT a strictly
weaker condition than CME. For fixed q, there are only finitely many (q-1)
walk positions, so L² control (FEB) implies L∞ control (CME) by Markov's
inequality: #{a : ‖F(a)‖ > T} ≤ CC_χ/T². With CC_χ = o(N²) and T = ε·N,
the number of "bad" positions is o(1) → eventually 0 → all positions good → CME.

Similarly, Density-1 CME (allowing o(N) bad INDICES) is equivalent to CME
because each fiber has Θ(N/(q-1)) = Θ(N) elements for fixed q. The o(N)
bad-index budget cannot absorb a biased fiber of size Θ(N).

Conclusion: No L^p interpolation between Dec and CCSB provides a strictly
weaker intermediate. The only viable routes remain SieveTransfer, CME, or
direct CCSB approaches. -/

end FiberEnergyBounds

/-! ## Hierarchy Connectors

Small lemmas completing the hierarchy diagram. These connect the major open
Props and their proved implications.

### Results

* `ccsb_implies_mmcsb`  : CCSB → MMCSB with Q₀ = 0 (trivial unwrapping)
* `cme_implies_mmcsb`   : CME → MMCSB (composition through CCSB)
* `feb_implies_mmcsb`   : FEB → MMCSB (composition through CCSB)
* `ccsb_implies_sve`    : CCSB → SVE (character sum bounds → excess energy o(N²))

These complete the bidirectional picture: SVE ⟺ MMCSB ⟺ CCSB (modulo Q₀ threshold).
-/

section HierarchyConnectors

open Classical

/-- **CCSB → MMCSB**: ComplexCharSumBound implies MultiModularCSB with threshold
    Q₀ = 0 (i.e., for ALL primes). This is immediate since CCSB is the universal
    version of MMCSB without a threshold. -/
theorem ccsb_implies_mmcsb (hcsb : ComplexCharSumBound) : MultiModularCSB :=
  ⟨0, fun q _inst _ hq hne χ hχ ε hε => hcsb q hq hne χ hχ ε hε⟩

/-- **CME → MMCSB**: Conditional Multiplier Equidistribution implies MultiModularCSB.
    Composes CME → CCSB (telescoping + fiber decomposition) → MMCSB (trivial). -/
theorem cme_implies_mmcsb (hcme : ConditionalMultiplierEquidist) : MultiModularCSB :=
  ccsb_implies_mmcsb (cme_implies_ccsb hcme)

/-- **FEB → MMCSB**: Fiber Energy Bound implies MultiModularCSB.
    Composes FEB → CCSB (Cauchy-Schwarz) → MMCSB (trivial). -/
theorem feb_implies_mmcsb (hfeb : FiberEnergyBound) : MultiModularCSB :=
  ccsb_implies_mmcsb (feb_implies_ccsb hfeb)

/-- **CCSB → SVE**: ComplexCharSumBound implies SubquadraticVisitEnergy.

    Proof: CCSB gives ‖S_χ‖ ≤ ε'·N for each nontrivial χ. The excess energy
    equals ∑_{χ≠1} ‖S_χ‖², which is bounded by (p−2)·(ε'·N)². Choosing
    ε' = √(ε/(p−2)) gives excess ≤ ε·N².

    Combined with `sve_implies_mmcsb`, this shows CCSB ⟺ SVE ⟺ MMCSB
    (modulo the Q₀ threshold: CCSB has Q₀=0, SVE/MMCSB have Q₀≥0). -/
theorem ccsb_implies_sve (hcsb : ComplexCharSumBound) : SubquadraticVisitEnergy := by
  use 0
  intro q _inst _hge hq hne ε hε
  -- Step 1: Set up the Fin N walk wrapper
  -- We need to bound excessEnergy of the restricted walk
  haveI : Fact (Nat.Prime q) := _inst
  haveI : NeZero q := ⟨(Fact.out : Nat.Prime q).ne_zero⟩
  -- Number of nontrivial characters C = p - 2
  set C := (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card with hC_def
  -- Choose ε' so that C · (ε' · N)² ≤ ε · N²
  -- Set ε' = √(ε / max(C,1)) so that C · ε'² = ε · C / max(C,1) ≤ ε
  -- But simpler: use ε directly and get CCSB to deliver √ε bounds
  -- Since excess = ∑_{χ≠1} ‖S_χ‖² ≤ C * (ε' * N)² and we want ≤ ε * N²,
  -- choose ε' = √(ε / (C + 1)) (the +1 avoids division by zero when C=0)
  set ε' := Real.sqrt (ε / (C + 1)) with hε'_def
  have hC_pos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have hε'_pos : 0 < ε' := Real.sqrt_pos.mpr (div_pos hε hC_pos)
  -- For each nontrivial ψ, CCSB gives an N₀(ψ)
  -- Convert DirichletCharacter to unit hom via equivToUnitHom
  have hcsb_dc : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ‖∑ n ∈ Finset.range N, (ψ.toUnitHom (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε' * N := by
    intro ψ hψ
    have hχ : ψ.toUnitHom ≠ 1 := by
      intro h; apply hψ
      ext a
      have := congr_fun (congr_arg DFunLike.coe h) a
      simp only [MonoidHom.one_apply] at this
      rw [show ψ a = (ψ.toUnitHom a : ℂ) from (MulChar.coe_toUnitHom ψ a).symm, this]
      simp [MulChar.one_apply_coe]
    obtain ⟨N₀, hN₀⟩ := hcsb q hq hne ψ.toUnitHom hχ ε' hε'_pos
    exact ⟨N₀, hN₀⟩
  -- For each ψ, get an N₀ (use 0 for trivial character since it won't be used)
  have hcsb_dc' : ∀ ψ : DirichletCharacter ℂ q,
      ∃ N₀ : ℕ, ψ ≠ 1 → ∀ N ≥ N₀,
        ‖∑ n ∈ Finset.range N, (ψ.toUnitHom (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε' * N := by
    intro ψ
    by_cases hψ : ψ = 1
    · exact ⟨0, fun h => absurd hψ h⟩
    · obtain ⟨N₀, hN₀⟩ := hcsb_dc ψ hψ
      exact ⟨N₀, fun _ => hN₀⟩
  choose N₀_fn hN₀_fn using hcsb_dc'
  set N₀ := Finset.univ.sup N₀_fn
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 2: Bound excess energy using the nontrivial sum identity
  set w : Fin N → (ZMod q)ˣ := fun n => emWalkUnit q hq hne n.val
  rw [excess_energy_eq_nontrivial_sum w]
  -- Step 3: Bound each character sum term
  have hchar_bound : ∀ ψ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖∑ n : Fin N, ψ (↑(w n) : ZMod q)‖ ^ 2 ≤ (ε' * N) ^ 2 := by
    intro ψ hψ
    apply sq_le_sq'
    · linarith [norm_nonneg (∑ n : Fin N, ψ (↑(w n) : ZMod q)),
                mul_nonneg hε'_pos.le (Nat.cast_nonneg N)]
    · -- Convert Fin N sum to Finset.range N sum
      have hsum_convert : ∑ n : Fin N, ψ (↑(w n) : ZMod q) =
          ∑ n ∈ Finset.range N, (ψ.toUnitHom (emWalkUnit q hq hne n) : ℂ) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro n _; exact (MulChar.coe_toUnitHom ψ (w n)).symm
      rw [hsum_convert]
      exact hN₀_fn ψ (Finset.ne_of_mem_erase hψ) N
        (le_trans (Finset.le_sup (Finset.mem_univ ψ)) hN)
  -- Step 4: Sum the bounds
  calc (Finset.univ.erase (1 : DirichletCharacter ℂ q)).sum
          (fun χ => ‖∑ n : Fin N, χ (↑(w n) : ZMod q)‖ ^ 2)
      ≤ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).sum
          (fun _ => (ε' * ↑N) ^ 2) :=
        Finset.sum_le_sum hchar_bound
    _ = ↑C * (ε' * ↑N) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def]
    _ = ↑C * (ε' ^ 2 * ↑N ^ 2) := by ring
    _ = ↑C * (ε / (↑C + 1) * ↑N ^ 2) := by
        congr 1; rw [hε'_def, Real.sq_sqrt (le_of_lt (div_pos hε hC_pos))]
    _ ≤ (↑C + 1) * (ε / (↑C + 1) * ↑N ^ 2) := by
        gcongr; exact le_of_lt (lt_add_one (C : ℝ))
    _ = ε * (↑N : ℝ) ^ 2 := by field_simp

end HierarchyConnectors

