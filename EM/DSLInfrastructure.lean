import EM.MasterReduction

/-!
# DSL Infrastructure: Algebraic Backbone for DSL Proof Approaches

This file formalizes the **algebraic infrastructure** needed for proving the
Deterministic Stability Lemma (DSL) or its weaker variants.

## Key Identity: Character Sum Energy Evolution

For a character χ and multiplier sequence m(0), m(1), ..., the partial
character sum S(N) = ∑_{n<N} χ(m(n)) satisfies:

  ‖S(N+1)‖² = ‖S(N)‖² + 2·⟪S(N), χ(m(N))⟫ + 1

The **cross term** ⟪S(N), χ(m(N))⟫ = Re(S̄(N)·χ(m(N))) determines whether
the energy grows or shrinks. Position-blindness (`crt_multiplier_invariance`)
implies the cross term is structurally independent of the walk position.

## Main Results

### Proved Theorems
* `char_sum_energy_step`       — ‖S(N+1)‖² = ‖S(N)‖² + 2⟪S(N),z(N)⟫ + ‖z(N)‖²
* `char_sum_energy_telescoping` — ‖S(N)‖² = ∑‖z(k)‖² + 2∑⟪S(k),z(k)⟫
* `cross_term_bound_gives_energy_bound` — bounded cross terms ⟹ bounded energy
* `cross_term_controls_growth` — o(N) cross terms ⟹ o(N²) energy

### Fiber Energy Analysis (new)
* `feb_implies_cme`            — FEB => CME (closes the FEB-CME equivalence)
* `total_cross_term_eq_sum_fiber` — total cross term = sum of fiber cross terms
* `fiber_energy_lower_bound`   — Cauchy-Schwarz: ‖S(N)‖² ≤ C · ∑‖F(a)‖²
* `cross_term_implies_cme`     — CrossTermImpliesCME (assuming FEB)

### Definitions and Open Hypotheses
* `charSumCrossTerm`           — Re(S̄(N)·χ(m(N))) (the cross term)
* `CrossTermCancellation`      — cumulative cross terms = o(N)
* `CrossTermImpliesCME`        — cross term cancellation → CME
* `fiberCrossTerm`             — fiber-level cross term Re(F̄(a,k)·χ(m(k)))
* `fiberSelectiveCrossTerm`    — active-fiber cross term at w(k)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Character Sum Energy Evolution (General) -/

section EnergyEvolution

/-- The telescoping identity for squared norms: for a sequence z(0),...,z(N-1),
    the squared norm of the partial sum S(N) = ∑_{k<N} z(k) satisfies

    ‖S(N)‖² = ∑_{k<N} ‖z(k)‖² + 2·∑_{k<N} ⟪S(k), z(k)⟫

    where ⟪S(k), z(k)⟫ is the inner product of the accumulated sum with
    the next term. -/
theorem norm_sq_partial_sum_telescoping {F : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (z : Nat → F) (N : Nat) :
    ‖∑ k ∈ Finset.range N, z k‖ ^ 2 =
    ∑ k ∈ Finset.range N, ‖z k‖ ^ 2 +
    2 * ∑ k ∈ Finset.range N,
      @inner ℝ F _ (∑ j ∈ Finset.range k, z j) (z k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (f := z), norm_add_sq_real, ih,
      Finset.sum_range_succ (f := fun k => ‖z k‖ ^ 2),
      Finset.sum_range_succ (f := fun k =>
        @inner ℝ F _ (∑ j ∈ Finset.range k, z j) (z k))]
    ring

end EnergyEvolution

/-! ## Character Sum Cross Term -/

section CrossTerm

variable {q : Nat} [Fact (Nat.Prime q)]
  (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- The character sum partial sum at step N:
    S_χ(N) = ∑_{n<N} χ(m(n)).

    This is the total character sum over multipliers. Its growth is
    controlled by the cross terms. -/
def emCharPartialSum (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) : ℂ :=
  ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)

/-- The **cross term** at step N:
    Re(conj(S_χ(N)) · χ(m(N)))

    Equivalently: ⟪S_χ(N), χ(m(N))⟫ as an inner product in ℂ over ℝ.

    This is the quantity that determines whether the character sum
    energy grows (positive) or shrinks (negative) at step N. -/
def charSumCrossTerm (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) : ℝ :=
  @inner ℝ ℂ _ (emCharPartialSum hq hne χ N)
    (χ (emMultUnit q hq hne N) : ℂ)

/-- The character sum energy at step N+1 in terms of step N:
    ‖S(N+1)‖² = ‖S(N)‖² + 2·crossTerm(N) + ‖χ(m(N))‖².

    Since χ maps to ℂˣ and the group is finite, |χ(m)| = 1 always,
    so this simplifies to ‖S(N+1)‖² = ‖S(N)‖² + 2·crossTerm(N) + 1.
    We state the general form for clarity. -/
theorem char_sum_energy_step (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖emCharPartialSum hq hne χ (N + 1)‖ ^ 2 =
    ‖emCharPartialSum hq hne χ N‖ ^ 2 +
    2 * charSumCrossTerm hq hne χ N +
    ‖(χ (emMultUnit q hq hne N) : ℂ)‖ ^ 2 := by
  unfold emCharPartialSum
  rw [Finset.sum_range_succ]
  exact norm_add_sq_real _ _

/-- The character sum energy telescoping: ‖S(N)‖² equals the sum of
    squared norms plus twice the sum of cross terms. -/
theorem char_sum_energy_telescoping (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖emCharPartialSum hq hne χ N‖ ^ 2 =
    ∑ k ∈ Finset.range N, ‖(χ (emMultUnit q hq hne k) : ℂ)‖ ^ 2 +
    2 * ∑ k ∈ Finset.range N, charSumCrossTerm hq hne χ k := by
  unfold emCharPartialSum charSumCrossTerm
  exact norm_sq_partial_sum_telescoping _ N

end CrossTerm

/-! ## Cross Term Bounds -/

section CrossTermBounds

variable {q : Nat} [Fact (Nat.Prime q)]
  (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Character values on finite groups have norm 1.
    For χ : G →* ℂˣ with G finite, every g ∈ G has finite order d,
    so (χ g)^d = χ(g^d) = χ(1) = 1, meaning χ(g) is a d-th root of
    unity, hence ‖χ(g)‖ = 1. -/
theorem char_value_norm_one (χ : (ZMod q)ˣ →* ℂˣ) (u : (ZMod q)ˣ) :
    ‖(χ u : ℂ)‖ = 1 := by
  have hpow : (χ u : ℂ) ^ Fintype.card (ZMod q)ˣ = 1 := by
    have h : (χ u : ℂˣ) ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero

/-- When character values have norm 1, the energy telescoping simplifies:
    ‖S(N)‖² = N + 2·∑ crossTerms. -/
theorem char_sum_energy_eq_N_plus_cross (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖emCharPartialSum hq hne χ N‖ ^ 2 =
    N + 2 * ∑ k ∈ Finset.range N, charSumCrossTerm hq hne χ k := by
  rw [char_sum_energy_telescoping hq hne χ N]
  congr 1
  simp only [char_value_norm_one, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]

/-- **Cross term bound gives energy bound.**
    If the cumulative cross terms are bounded by B, then
    ‖S(N)‖² ≤ N + 2B. -/
theorem cross_term_bound_gives_energy_bound (χ : (ZMod q)ˣ →* ℂˣ)
    (N : Nat) (B : ℝ)
    (hB : |∑ k ∈ Finset.range N, charSumCrossTerm hq hne χ k| ≤ B) :
    ‖emCharPartialSum hq hne χ N‖ ^ 2 ≤ N + 2 * B := by
  rw [char_sum_energy_eq_N_plus_cross hq hne χ N]
  linarith [(abs_le.mp hB).2]

/-- **Cross term cancellation controls energy growth.**
    If the cross terms are o(N), then ‖S(N)‖² ≤ (1 + 2ε)·N for all ε > 0,
    eventually. This is the key algebraic step: o(N) cross terms imply
    the energy grows at most linearly (the norm-squared terms contribute
    exactly N, and the cross terms contribute o(N)). -/
theorem cross_term_controls_growth (χ : (ZMod q)ˣ →* ℂˣ)
    (hctc : ∀ (ε : ℝ), 0 < ε → ∃ N₀ : Nat, ∀ N ≥ N₀,
      |∑ k ∈ Finset.range N, charSumCrossTerm hq hne χ k| ≤ ε * N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₁ : Nat, ∀ N ≥ N₁,
      ‖emCharPartialSum hq hne χ N‖ ^ 2 ≤ (1 + 2 * ε) * N := by
  obtain ⟨N₀, hN₀⟩ := hctc ε hε
  exact ⟨N₀, fun N hN => by
    have h := cross_term_bound_gives_energy_bound hq hne χ N (ε * ↑N) (hN₀ N hN)
    linarith⟩

end CrossTermBounds

/-! ## Cross Term Cancellation Hypothesis -/

section CrossTermHypothesis

/-- **Cumulative Cross Term Cancellation**: the cumulative cross term grows
    sublinearly: |∑_{k<N} crossTerm(k)| = o(N).

    If this holds for all nontrivial characters χ mod q (for all primes q),
    then by `char_sum_energy_eq_N_plus_cross`:
    ‖S(N)‖² = N + o(N), so ‖S(N)‖ = O(√N) = o(N), giving CCSB.

    **Why this should hold:** position-blindness (`crt_multiplier_invariance`)
    implies the character value χ(m(N)) doesn't depend on the walk position.
    But S(N) = ∑χ(m(n)) is also position-independent (it's a function of the
    multiplier sequence alone). So the cross term Re(S̄(N)·χ(m(N))) depends
    only on the multiplier sequence {m(0),...,m(N)}.

    By PE, the multiplier values have positive density for each group element.
    For a nontrivial character χ, E[χ(m)] = 0 over the population. If the
    EM multipliers sample the population without systematic bias (the content
    of DSL), then the cross terms cancel on average. -/
def CrossTermCancellation : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ), χ ≠ 1 →
  ∀ (ε : ℝ), 0 < ε →
  ∃ N₀ : Nat, ∀ N ≥ N₀,
    |∑ k ∈ Finset.range N, charSumCrossTerm hq hne χ k| ≤ ε * N

/-- **Cross term cancellation → CME.**

    The bridge requires showing that fiber decomposition preserves the bound.
    Since S(N) = ∑_a F(a,N) (sum over walk positions), and the energy is
    ‖S(N)‖² = |∑_a F(a,N)|² ≤ (p-1)·∑_a |F(a,N)|² (Cauchy-Schwarz),
    the total energy bound ‖S(N)‖² ≤ N + o(N) implies the fiber energy
    ∑_a |F(a,N)|² ≤ N + o(N) as well (since the reverse inequality always
    holds by triangle inequality).

    **Status**: open hypothesis connecting total to fiber bounds. -/
def CrossTermImpliesCME : Prop :=
  CrossTermCancellation → ConditionalMultiplierEquidist

end CrossTermHypothesis

/-! ## Fiber Energy Analysis: From Cross Terms to CME

The key insight is that the **subquadratic fiber energy bound** (FEB, already
defined in LargeSieveSpectral.lean: `∑_a ‖F(a)‖² ≤ ε·N²`) is equivalent to
CME. The forward direction `cme_implies_feb` was already proved; here we prove
the reverse: **FEB implies CME**.

### Proved Results (new)

* `feb_implies_cme`         -- FEB => CME (closes the FEB-CME equivalence)
* `cross_term_implies_cme`  -- CrossTermImpliesCME assuming FEB

### Proof of FEB => CME

For each walk position a: `‖F(a)‖² ≤ ∑_a ‖F(a)‖² ≤ ε·N²`, so
`‖F(a)‖ ≤ √ε·N`. For any target δ > 0, choosing ε = δ² gives
`‖F(a)‖ ≤ δ·N` eventually, which is exactly CME.

### Fiber Cross Term Decomposition (PROVED)

* `total_cross_term_eq_sum_fiber` -- total cross term = sum of fiber cross terms
* `fiberCrossTerm`, `fiberSelectiveCrossTerm` -- fiber-level cross term definitions

### Cauchy-Schwarz Lower Bound (PROVED)

* `fiber_energy_lower_bound` -- `‖S(N)‖² ≤ C · ∑_a ‖F(a,N)‖²`

### Open Gap: CrossTermCancellation => FEB

The total cross term at step k is `∑_a fiberCrossTerm(a,k)` (sum over
ALL fibers), while the fiber energy evolves via `fiberCrossTerm(w(k),k)`
(ACTIVE fiber only). CTC controls the full sum; the gap is whether
the active-fiber selection also cancels.
-/

section FiberEnergyAnalysis

variable {q : Nat} [Fact (Nat.Prime q)]
  (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- The **fiber cross term** at step k for fiber a:
    Re(conj(F(a,k)) · χ(m(k))).

    This is the inner product of the accumulated fiber sum at position a
    with the character value of the multiplier at step k. The fiber energy
    ‖F(a)‖² increases by `2·fiberCrossTerm + 1` when the walk visits a,
    and stays constant otherwise. -/
def fiberCrossTerm (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (k : Nat) : ℝ :=
  @inner ℝ ℂ _ (fiberMultCharSum q hq hne χ a k)
    (χ (emMultUnit q hq hne k) : ℂ)

/-- The **fiber-selective cross term** at step k: the fiber cross term at
    the current walk position w(k).

    This is the quantity that drives the fiber energy sum evolution:
    `∑_a ‖F(a,N)‖² = N + 2·∑_{k<N} fiberSelectiveCrossTerm(k)`. -/
def fiberSelectiveCrossTerm (χ : (ZMod q)ˣ →* ℂˣ) (k : Nat) : ℝ :=
  fiberCrossTerm hq hne χ (emWalkUnit q hq hne k) k

/-- The total cross term at step k equals the sum of fiber cross terms
    over all walk positions.

    Proof: `S(k) = ∑_a F(a,k)`, so
    `Re(S̄(k)·χ(m(k))) = Re(∑_a F̄(a,k)·χ(m(k))) = ∑_a Re(F̄(a,k)·χ(m(k)))`.

    This decomposes the total cross term (which CTC controls) into fiber
    contributions. The fiber energy only uses the active fiber's
    contribution, not the full sum. -/
theorem total_cross_term_eq_sum_fiber (χ : (ZMod q)ˣ →* ℂˣ) (k : Nat) :
    charSumCrossTerm hq hne χ k =
    ∑ a : (ZMod q)ˣ, fiberCrossTerm hq hne χ a k := by
  simp only [charSumCrossTerm, emCharPartialSum, fiberCrossTerm]
  rw [mult_char_sum_eq_fiber_sum q hq hne χ k]
  -- inner(∑_a F(a), z) = ∑_a inner(F(a), z) by linearity of inner product
  exact sum_inner (𝕜 := ℝ) Finset.univ
    (fun a => fiberMultCharSum q hq hne χ a k) (χ (emMultUnit q hq hne k) : ℂ)

/-- **FEB implies CME**: the subquadratic fiber energy bound (defined in
    LargeSieveSpectral.lean) implies Conditional Multiplier Equidistribution.

    This closes the equivalence noted in Dead End #93: FEB and CME are
    equivalent for fixed q.

    **Proof**: for each walk position a,
    `‖F(a,N)‖² ≤ ∑_a' ‖F(a',N)‖² ≤ ε·N²`, so `‖F(a,N)‖ ≤ √ε·N`.
    For any target δ > 0, set ε = δ² to get `‖F(a,N)‖ ≤ δ·N` eventually. -/
theorem feb_implies_cme (hfeb : FiberEnergyBound) : ConditionalMultiplierEquidist := by
  intro q' inst hq' hne' χ hχ a ε hε
  haveI : Fact (Nat.Prime q') := inst
  -- Choose ε' = ε² so √ε' = ε
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨N₀, hN₀⟩ := hfeb q' hq' hne' χ hχ (ε ^ 2) hε2
  refine ⟨N₀, fun N hN => ?_⟩
  -- FEB gives: ∑_a' ‖F(a')‖² ≤ ε²·N²
  have h_total := hN₀ N hN
  -- Individual bound: ‖F(a)‖² ≤ ∑_a' ‖F(a')‖² ≤ ε²·N²
  have h_individual : ‖fiberMultCharSum q' hq' hne' χ a N‖ ^ 2 ≤ (ε * ↑N) ^ 2 :=
    calc ‖fiberMultCharSum q' hq' hne' χ a N‖ ^ 2
        ≤ ∑ a' : (ZMod q')ˣ, ‖fiberMultCharSum q' hq' hne' χ a' N‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun a' => ‖fiberMultCharSum q' hq' hne' χ a' N‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ a)
      _ ≤ ε ^ 2 * (N : ℝ) ^ 2 := h_total
      _ = (ε * ↑N) ^ 2 := by ring
  -- ‖F(a)‖² ≤ (ε·N)² ⟹ ‖F(a)‖ ≤ ε·N (since both are nonneg)
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h_individual

/-- **Cauchy-Schwarz lower bound on fiber energy**: the total character sum
    energy provides a lower bound on the fiber energy.

    `‖S(N)‖² ≤ C · ∑_a ‖F(a,N)‖²`

    where C = card (ZMod q)ˣ. Combined with CTC (which gives
    ‖S(N)‖² = N + o(N)), this shows the fiber energy is at least linear. -/
theorem fiber_energy_lower_bound (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖emCharPartialSum hq hne χ N‖ ^ 2 ≤
    Fintype.card (ZMod q)ˣ *
      ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := by
  -- S(N) = ∑_a F(a,N) by fiber decomposition
  have hdecomp : emCharPartialSum hq hne χ N =
      ∑ a : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a N := by
    simp only [emCharPartialSum, fiberMultCharSum]
    exact mult_char_sum_eq_fiber_sum q hq hne χ N
  rw [hdecomp]
  -- ‖∑x_a‖ ≤ ∑‖x_a‖ (triangle inequality)
  have h_triangle : ‖∑ a : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a N‖
      ≤ ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ := norm_sum_le _ _
  -- (∑1·‖x_a‖)² ≤ (∑1²)·(∑‖x_a‖²) by Cauchy-Schwarz for reals
  have h_cs : (∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖) ^ 2 ≤
      Fintype.card (ZMod q)ˣ *
        ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := by
    -- Use Finset.sum_mul_sq_le_sq_mul_sq: (∑ f·g)² ≤ (∑f²)·(∑g²)
    have hcsf := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ => (1 : ℝ)) (fun a => ‖fiberMultCharSum q hq hne χ a N‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ] at hcsf
    exact hcsf
  -- ‖∑x_a‖² ≤ (∑‖x_a‖)² ≤ C · ∑‖x_a‖²
  calc ‖∑ a : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a N‖ ^ 2
      ≤ (∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
          h_triangle
    _ ≤ Fintype.card (ZMod q)ˣ *
        ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := h_cs

/-- **Cross term cancellation implies CME, via the fiber energy bridge.**

    This is the main theorem connecting CTC to CME. The proof goes:

    1. CTC => total energy ‖S(N)‖^2 = N + o(N)   (proved: cross_term_controls_growth)
    2. S(N) = ∑_a F(a,N)                          (proved: mult_char_sum_eq_fiber_sum)
    3. FEB => CME                                  (proved: feb_implies_cme)

    The gap: step 1 gives |∑_a F(a)|^2 = N + o(N), but step 3 needs
    ∑_a |F(a)|^2 = ε·N^2 (subquadratic). These differ because cancellation
    between fibers can make the total small while individual fibers are large.

    The fiber energy sum evolves via the fiber-selective cross term (only the
    active fiber gains energy at each step). CTC controls the total of ALL
    fiber cross terms, but the gap is whether the active-fiber selection also
    leads to cancellation.

    **Status**: proved assuming FEB. Since FEB is equivalent to CME
    (`cme_implies_feb` + `feb_implies_cme`), the true open hypothesis
    is CTC => FEB, which requires showing that the active-fiber cross
    terms cancel when the total cross terms do. -/
theorem cross_term_implies_cme (hfeb : FiberEnergyBound) : CrossTermImpliesCME :=
  fun _hctc => feb_implies_cme hfeb

end FiberEnergyAnalysis

/-! ## Architecture Summary

### Cross Term Path
```
CrossTermCancellation  (OPEN: cross terms = o(N))
       ↓  (algebraic, via char_sum_energy_eq_N_plus_cross)
‖S(N)‖² = N + o(N), so ‖S(N)‖ = O(√N) = o(N)
       ↓  (PROVED: complex_csb_mc')
CCSB → MC
```

### Fiber Energy Path
```
FiberEnergyBound       (OPEN: ∑_a ‖F(a)‖² = o(N²))
       ↓  (PROVED: feb_implies_cme — new in this file)
CME → CCSB → MC
```

### Cross Term to CME Path
```
CrossTermCancellation  (OPEN)
       ↓  (OPEN GAP: CTC => FEB via active-fiber selection)
FiberEnergyBound
       ↓  (PROVED: feb_implies_cme)
CME → MC
```

### Key Structural Identity (PROVED)
```
total cross term(k) = ∑_a fiber cross term(a,k)
                      (total_cross_term_eq_sum_fiber)
```

CTC controls `∑_k ∑_a fiberCrossTerm(a,k)` (sum over ALL fibers).
Fiber energy depends on `∑_k fiberCrossTerm(w(k),k)` (ACTIVE fiber only).
The gap is: does active-fiber selection preserve cancellation?

### Cauchy-Schwarz (PROVED)
`‖S(N)‖² ≤ C · ∑_a ‖F(a,N)‖²` (fiber_energy_lower_bound)

This gives a LOWER bound on fiber energy from the total energy.
The UPPER bound (fiber energy = o(N²)) is the FEB hypothesis.

### The FEB-CME Equivalence
`FEB ⟺ CME` for fixed q (Dead End #93, now fully proved):
- `cme_implies_feb` (proved in LargeSieveSpectral.lean)
- `feb_implies_cme` (proved in this file)
-/

/-! ## The +1 Shift: Cofactor Walk and Shifted Walk Identity

The EM walk satisfies the fundamental relation `seq(n+1) | prod(n) + 1`.
This means there is a natural number cofactor `cof(n) = (prod(n) + 1) / seq(n+1)`
such that `prod(n) + 1 = seq(n+1) * cof(n)`.

In `ZMod q` (for any q), this gives the **shifted walk identity**:
  `walkZ(q,n) + 1 = multZ(q,n) * cofZ(q,n)`

where `cofZ(q,n) = (cof(n) : ZMod q)` is the cofactor cast to ZMod q.

This identity decomposes the "+1 shift" of the walk position into a product
of the multiplier and a cofactor. The cofactor captures "how much room"
there is between seq(n+1) and prod(n)+1.

When `walkZ(q,n) ≠ -1` (i.e., `walkZ(q,n) + 1 ≠ 0`), the shifted walk
is a nonzero element of ZMod q, and we can invert the identity to get
  `cofZ(q,n) = (walkZ(q,n) + 1) * (multZ(q,n))⁻¹`

For character sum analysis, this gives:
  `χ(walkZ(q,n) + 1) = χ(multZ(q,n)) * χ(cofZ(q,n))`
decomposing the "shifted walk character" into a product of the multiplier
character and the cofactor character.
-/

section ShiftedWalkIdentity

/-- The Euclid cofactor at step n: `cofactor(n) = (prod(n) + 1) / seq(n+1)`.
    This is a natural number since `seq(n+1) | prod(n) + 1`. -/
def euclidCofactor (n : ℕ) : ℕ := (prod n + 1) / seq (n + 1)

/-- **Cofactor factorization**: `prod(n) + 1 = seq(n+1) * cofactor(n)`.
    This is the defining property of the cofactor. -/
theorem euclid_cofactor_mul (n : ℕ) :
    prod n + 1 = seq (n + 1) * euclidCofactor n := by
  rw [euclidCofactor, Nat.mul_div_cancel' (seq_dvd_succ_prod n)]

/-- The cofactor is at least 1 (since `prod(n) + 1 ≥ 3` and `seq(n+1) ≤ prod(n) + 1`). -/
theorem euclidCofactor_pos (n : ℕ) : 0 < euclidCofactor n := by
  rw [euclidCofactor]
  exact Nat.div_pos (Nat.le_of_dvd (by have := prod_ge_two n; omega) (seq_dvd_succ_prod n))
    (by have := (seq_isPrime (n + 1)).1; omega)

/-- The cofactor cast to `ZMod q`. -/
def cofZ (q : ℕ) (n : ℕ) : ZMod q := (euclidCofactor n : ZMod q)

/-- **Shifted walk identity in ZMod**: `walkZ(q,n) + 1 = multZ(q,n) * cofZ(q,n)`.

    This is the fundamental "+1 shift" identity. It expresses the Euclid number
    `prod(n) + 1` in terms of its factorization `seq(n+1) * cofactor(n)`,
    all cast to `ZMod q`.

    This holds for ALL q, not just primes. No hypothesis needed. -/
theorem shifted_walk_eq_mult_mul_cof (q : ℕ) (n : ℕ) :
    walkZ q n + 1 = multZ q n * cofZ q n := by
  simp only [walkZ, multZ, cofZ]
  have h := euclid_cofactor_mul n
  calc (prod n : ZMod q) + 1
      = ((prod n + 1 : ℕ) : ZMod q) := by push_cast; ring
    _ = ((seq (n + 1) * euclidCofactor n : ℕ) : ZMod q) := by rw [h]
    _ = (seq (n + 1) : ZMod q) * (euclidCofactor n : ZMod q) := by push_cast; ring

/-- **Cofactor from shifted walk**: when the walk position is not -1 (i.e.,
    `walkZ(q,n) + 1 ≠ 0` in `ZMod q`), the cofactor equals the shifted walk
    divided by the multiplier:
      `cofZ(q,n) = (walkZ(q,n) + 1) * (multZ(q,n))⁻¹`

    This requires q prime and q not in the sequence (so multZ is nonzero). -/
theorem cofZ_eq_shifted_div_mult {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : ℕ) :
    cofZ q n = (walkZ q n + 1) * (multZ q n)⁻¹ := by
  have hm_ne := multZ_ne_zero hq hne n
  rw [shifted_walk_eq_mult_mul_cof, mul_comm (multZ q n), mul_assoc,
    mul_inv_cancel₀ hm_ne, mul_one]

/-- **Walk from cofactor and multiplier**: the walk position can be recovered
    from the multiplier and cofactor:
      `walkZ(q,n) = multZ(q,n) * cofZ(q,n) - 1` -/
theorem walkZ_eq_mult_mul_cof_sub_one (q : ℕ) (n : ℕ) :
    walkZ q n = multZ q n * cofZ q n - 1 :=
  eq_sub_of_add_eq (shifted_walk_eq_mult_mul_cof q n)

/-- **Death condition via cofactor**: the walk hits -1 at step n iff
    the cofactor `cofZ(q,n)` is zero in `ZMod q`.

    Since `walkZ(q,n) + 1 = multZ(q,n) * cofZ(q,n)`, and `multZ(q,n) ≠ 0`
    when q is prime and not in the sequence, we have
    `walkZ(q,n) + 1 = 0 ⟺ cofZ(q,n) = 0`. -/
theorem walkZ_eq_neg_one_iff_cofZ_zero {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : ℕ) :
    walkZ q n = -1 ↔ cofZ q n = 0 := by
  have hm_ne := multZ_ne_zero hq hne n
  rw [← add_eq_zero_iff_eq_neg, shifted_walk_eq_mult_mul_cof, mul_eq_zero,
    or_iff_right hm_ne]

/-- **Cofactor nonzero when alive**: when `walkZ(q,n) ≠ -1`, the cofactor
    is nonzero in `ZMod q`. -/
theorem cofZ_ne_zero_of_alive {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : ℕ)
    (halive : walkZ q n ≠ -1) :
    cofZ q n ≠ 0 :=
  fun h => halive ((walkZ_eq_neg_one_iff_cofZ_zero hq hne n).mpr h)

/-- **Shifted walk nonzero when alive**: when `walkZ(q,n) ≠ -1`,
    the quantity `walkZ(q,n) + 1` is nonzero in `ZMod q`. -/
theorem shifted_walk_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q) (n : ℕ)
    (halive : walkZ q n ≠ -1) :
    walkZ q n + 1 ≠ 0 :=
  fun h => halive (add_eq_zero_iff_eq_neg.mp h)

/-- **Walk successor via cofactor**: combining the walk recurrence
    `walkZ(q,n+1) = walkZ(q,n) * multZ(q,n)` with the shifted walk identity
    `walkZ(q,n) + 1 = multZ(q,n) * cofZ(q,n)`, we get:

      `walkZ(q,n+1) + 1 = multZ(q,n) * (multZ(q,n) * cofZ(q,n) - 1) + 1`
                        `= (multZ(q,n))² * cofZ(q,n) - multZ(q,n) + 1`

    which relates the shifted walk at step n+1 to the cofactor at step n.
    This is the "cofactor evolution" identity. -/
theorem shifted_walk_succ_eq (q : ℕ) (n : ℕ) :
    walkZ q (n + 1) + 1 = (multZ q n) ^ 2 * cofZ q n - multZ q n + 1 := by
  rw [walkZ_succ, walkZ_eq_mult_mul_cof_sub_one]; ring

/-- **Multiplier-cofactor product is the shifted walk**: at the unit level,
    when the walk is alive (not at -1), the product `multZ * cofZ` in ZMod q
    equals `walkZ + 1`, which is nonzero.

    This packages the shifted walk identity for unit-level reasoning. -/
theorem mult_cof_product_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : ℕ)
    (halive : walkZ q n ≠ -1) :
    multZ q n * cofZ q n ≠ 0 :=
  shifted_walk_eq_mult_mul_cof q n ▸ shifted_walk_ne_zero hq hne n halive

/-- **Character decomposition of shifted walk**: for any multiplicative
    character χ of `(ZMod q)ˣ`, when the walk is alive at step n, the
    character of the shifted walk decomposes as:

      `χ(walkZ(q,n) + 1) = χ(multZ(q,n)) * χ(cofZ(q,n))`

    where we view `walkZ(q,n) + 1`, `multZ(q,n)`, and `cofZ(q,n)` as units
    (they are all nonzero when the walk is alive).

    This is the key identity for Fourier analysis of the shifted walk:
    it separates the "multiplier contribution" from the "cofactor contribution"
    in the character sum. -/
theorem char_shifted_walk_eq_char_mult_mul_char_cof {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : ℕ)
    (halive : walkZ q n ≠ -1)
    (χ : (ZMod q)ˣ →* ℂˣ) :
    χ (Units.mk0 (walkZ q n + 1) (shifted_walk_ne_zero hq hne n halive)) =
    χ (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) *
    χ (Units.mk0 (cofZ q n) (cofZ_ne_zero_of_alive hq hne n halive)) := by
  rw [← map_mul]; congr 1; ext
  simp only [Units.val_mul, Units.val_mk0, shifted_walk_eq_mult_mul_cof]

/-- **Shifted walk vanishes mod any Euclid divisor**: if `q | prod(n) + 1`,
    then `walkZ(q,n) + 1 = 0` in `ZMod q`. Equivalently, `multZ(q,n) * cofZ(q,n) = 0`.

    This applies to ALL prime divisors of the Euclid number `prod(n) + 1`,
    not just the smallest one (`seq(n+1)`). At the auto-hit modulus `seq(n+1)`,
    this reduces to the well-known `walkZ_eq_neg_one_iff`. -/
theorem shifted_walk_zero_of_dvd (q n : ℕ) (hq : q ∣ (prod n + 1)) :
    walkZ q n + 1 = 0 := by
  simp only [walkZ]
  have h : ((prod n + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr hq
  calc (prod n : ZMod q) + 1 = ((prod n + 1 : ℕ) : ZMod q) := by push_cast; ring
    _ = 0 := h

/-- **Multiplier-cofactor product vanishes at auto-hit**: at the auto-hit
    modulus `seq(n+1)`, we have `multZ(seq(n+1), n) * cofZ(seq(n+1), n) = 0`.
    Since `multZ` is a self-cast (`seq(n+1) mod seq(n+1) = 0`), in fact
    `multZ(seq(n+1), n) = 0`, and the product is trivially zero. -/
theorem mult_cof_zero_at_auto_hit (n : ℕ) :
    multZ (seq (n + 1)) n * cofZ (seq (n + 1)) n = 0 :=
  shifted_walk_eq_mult_mul_cof _ n ▸ shifted_walk_zero_of_dvd _ n (seq_dvd_succ_prod n)

end ShiftedWalkIdentity

end
