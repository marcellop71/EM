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

### Definitions and Open Hypotheses
* `charSumCrossTerm`           — Re(S̄(N)·χ(m(N))) (the cross term)
* `CrossTermCancellation`      — cumulative cross terms = o(N)
* `CrossTermImpliesCME`        — cross term cancellation → CME
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Character Sum Energy Evolution (General) -/

section EnergyEvolution

/-- The squared norm expansion for inner product spaces over ℝ:
    ‖x + y‖² = ‖x‖² + 2·⟪x,y⟫ + ‖y‖². -/
theorem norm_sq_add_inner {F : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x y : F) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * @inner ℝ F _ x y + ‖y‖ ^ 2 :=
  norm_add_sq_real x y

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
    rw [Finset.sum_range_succ (f := z)]
    rw [norm_sq_add_inner]
    rw [ih]
    rw [Finset.sum_range_succ (f := fun k => ‖z k‖ ^ 2)]
    rw [Finset.sum_range_succ (f := fun k =>
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
  exact norm_sq_add_inner _ _

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
  -- Step 1: (χ u : ℂ) ^ (card G) = 1
  have hpow : (χ u : ℂ) ^ Fintype.card (ZMod q)ˣ = 1 := by
    have h := @pow_card_eq_one _ _ _ u
    have h2 : (χ u : ℂˣ) ^ Fintype.card (ZMod q)ˣ = 1 := by rw [← map_pow, h, map_one]
    have h3 : ((χ u : ℂˣ) : ℂ) ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    exact h3
  -- Step 2: ‖(χ u)‖ ^ (card G) = 1
  have h_norm_pow : ‖(χ u : ℂ)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← norm_pow, hpow, norm_one]
  -- Step 3: ‖(χ u)‖ = 1 (from x ≥ 0, x^n = 1, n > 0)
  have h_nonneg : 0 ≤ ‖(χ u : ℂ)‖ := norm_nonneg _
  have hcard_ne : Fintype.card (ZMod q)ˣ ≠ 0 := Fintype.card_ne_zero
  by_contra hne
  rcases ne_iff_lt_or_gt.mp hne with h | h
  · linarith [pow_lt_one₀ h_nonneg h hcard_ne]
  · have : 1 < ‖(χ u : ℂ)‖ ^ Fintype.card (ZMod q)ˣ :=
      one_lt_pow₀ h hcard_ne
    linarith

/-- When character values have norm 1, the energy telescoping simplifies:
    ‖S(N)‖² = N + 2·∑ crossTerms. -/
theorem char_sum_energy_eq_N_plus_cross (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖emCharPartialSum hq hne χ N‖ ^ 2 =
    N + 2 * ∑ k ∈ Finset.range N, charSumCrossTerm hq hne χ k := by
  rw [char_sum_energy_telescoping hq hne χ N]
  congr 1
  have : ∀ k ∈ Finset.range N,
      ‖(χ (emMultUnit q hq hne k) : ℂ)‖ ^ 2 = 1 := by
    intro k _
    rw [char_value_norm_one, one_pow]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- **Cross term bound gives energy bound.**
    If the cumulative cross terms are bounded by B, then
    ‖S(N)‖² ≤ N + 2B. -/
theorem cross_term_bound_gives_energy_bound (χ : (ZMod q)ˣ →* ℂˣ)
    (N : Nat) (B : ℝ)
    (hB : |∑ k ∈ Finset.range N, charSumCrossTerm hq hne χ k| ≤ B) :
    ‖emCharPartialSum hq hne χ N‖ ^ 2 ≤ N + 2 * B := by
  rw [char_sum_energy_eq_N_plus_cross hq hne χ N]
  have h := abs_le.mp hB
  linarith [h.2]

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

/-! ## Architecture Summary

The DSL proof approaches reduce to controlling the cross term:

```
Position-blindness (PROVED: crt_multiplier_invariance)
 + Population support  (PROVED: PE from pe_of_equidist)
 + Generation          (PROVED: SE from PRE)
       ↓
CrossTermCancellation  (OPEN: cross terms = o(N))
       ↓  (algebraic, via char_sum_energy_eq_N_plus_cross)
‖S(N)‖² = N + o(N)
       ↓
‖S(N)‖ = O(√N) = o(N)
       ↓
CCSB → MC  (PROVED: complex_csb_mc')
```

**The DSL gap in cross-term language:**

The cross term at step N is `Re(S̄(N) · χ(m(N)))`, where:
- S(N) = accumulated character sum (depends on m(0),...,m(N-1))
- χ(m(N)) = next character value

Both are functions of the multiplier sequence alone (not the walk
position). For random i.i.d. multipliers, E[χ(m)] = 0 gives cancellation.
For the deterministic EM sequence, the multipliers are not i.i.d., but:
1. They generate the full group (from SE)
2. Each value has positive population density (from PE)
3. Their q-coordinates are blind to the walk (from PBI)

Converting these three structural properties into the analytical conclusion
|∑ crossTerm| = o(N) is the content of the DSL.
-/

end
