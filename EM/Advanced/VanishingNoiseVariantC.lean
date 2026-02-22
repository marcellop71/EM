import EM.Advanced.VanishingNoiseVariantB

/-!
# Vanishing Noise Variant Part C: Stochastic Two-Point MC and Faithful Character Escape

## Overview

This file contains Parts 23-24 of the vanishing noise framework, split from
`VanishingNoiseVariant.lean` for modularity.

**Part 23**: Stochastic Two-Point MC. Connects non-self-consistent variant MC
with the self-consistent tree framework. Defines `fairCoin`, `TreeContractionAtHalf`,
and proves `StochasticTwoPointMC` from `UFDStrong`.

**Part 24**: Faithful Character Escape. Proves unconditional non-summability
of spectral gaps for faithful nontrivial characters. Closes `UFDStrong(3)`.
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter


/-! ## Part 23: Stochastic Two-Point MC

### Overview

This part connects the non-self-consistent variant MC machinery (Part 21) with the
self-consistent tree framework (Part 20), and provides a clean quantitative
statement about the "stochastic two-point MC" problem.

**Key definitions**:
* `fairCoin` -- constant epsilon schedule at 1/2
* `fairTreeCharSum` -- tree character sum at fair coin weights
* `TreeContractionAtHalf` -- tree contraction specialized to epsilon = 1/2
* `StochasticTwoPointMC` -- under UFDStrong, every element has positive count

**Key results**:
* `stochastic_two_point_mc_proved` -- StochasticTwoPointMC PROVED from UFDStrong
* `productMultiset_card_ge_two_pow` -- product multiset grows exponentially
* `fairTreeCharSum_norm_le_one` -- fair tree character sum bounded by 1
* `treeContraction_of_hypothesis` -- TreeContractionHypothesis implies TreeContractionAtHalf
* `treeCharSum_at_zero_step` -- deterministic degeneration at epsilon = 0
* `stochastic_two_point_mc_landscape` -- 7-part landscape theorem

### Conceptual significance

The stochastic two-point MC problem sits between two extremes:
1. **Deterministic MC** (standard Mullin conjecture): the ALL-minFac walk hits -1 mod q
2. **Full stochastic MC** (pathExistenceFromVanishing): SOME product of factor set elements
   reaches every target

Part 21 established (2) under UFDStrong via character orthogonality counting.
Part 20 established the self-consistent tree framework where branching follows
actual prime factorizations (not abstract factor sets).

Part 23 bridges these: under UFDStrong, the non-self-consistent counting already
gives positive multiset count for every target. The tree contraction machinery
(TreeContractionAtHalf) provides a route for the self-consistent version, but
requires the open TreeContractionHypothesis.

The key gap between Parts 21 and 23 on one hand and standard MC on the other
is the **selection coherence** problem: stochastic MC shows that for each prime q,
SOME selection path reaches -1 mod q, but different primes q may require different
selection sequences. Standard MC requires ONE fixed selection (all-minFac) to work
for ALL primes simultaneously.
-/

section StochasticTwoPointMC

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Definitions -/

/-- The fair coin epsilon schedule: constant 1/2 at every step. -/
def fairCoin : ℕ → ℝ := fun _ => 1 / 2

/-- The fair tree character sum: the branching tree character sum evaluated at
    accumulator 2 (= prod 0) with constant epsilon = 1/2. -/
def fairTreeCharSum (q : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) : ℂ :=
  treeCharSum q chi N 2 fairCoin

/-- **TreeContractionAtHalf**: the tree character sum at fair coin weights vanishes
    for all nontrivial characters. This is TreeContractionHypothesis specialized to
    the constant epsilon = 1/2 schedule.

    Strictly weaker than TreeContractionHypothesis (which quantifies over all
    epsilon schedules with 0 < epsilon_k < 1).

    Open Hypothesis. -/
def TreeContractionAtHalf (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    Filter.Tendsto (fun N => ‖fairTreeCharSum q chi N‖) Filter.atTop (nhds 0)

/-- **StochasticTwoPointMC**: Under UFDStrong with q >= 3, every element of (ZMod q)ˣ
    has positive count in the product multiset of padded unit sets at some depth N.
    This is the non-self-consistent version: the "random paths" are abstract products
    of factor set elements, not necessarily following the self-consistent tree. -/
def StochasticTwoPointMC (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → UFDStrong q →
    ∀ (a : (ZMod q)ˣ), ∃ N,
      0 < Multiset.count a (productMultiset (paddedUnitSet (q := q)) N)

/-! ### fairCoin validity -/

/-- fairCoin is strictly positive at every step. -/
theorem fairCoin_pos : ∀ k, 0 < fairCoin k :=
  fun _ => by norm_num [fairCoin]

/-- fairCoin is strictly less than 1 at every step. -/
theorem fairCoin_lt_one : ∀ k, fairCoin k < 1 :=
  fun _ => by norm_num [fairCoin]

/-- fairCoin is nonneg at every step. -/
theorem fairCoin_nonneg : ∀ k, 0 ≤ fairCoin k :=
  fun k => (fairCoin_pos k).le

/-- fairCoin is at most 1 at every step. -/
theorem fairCoin_le_one : ∀ k, fairCoin k ≤ 1 :=
  fun k => (fairCoin_lt_one k).le

/-! ### fairTreeCharSum properties -/

/-- The fair tree character sum is bounded by 1 in norm. This follows from
    `treeCharSum_norm_le_one` with the valid fairCoin weights. -/
theorem fairTreeCharSum_norm_le_one [NeZero q]
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    ‖fairTreeCharSum q chi N‖ ≤ 1 :=
  treeCharSum_norm_le_one q chi N 2 fairCoin fairCoin_nonneg fairCoin_le_one

/-- TreeContractionHypothesis (which quantifies over all valid epsilon schedules)
    implies TreeContractionAtHalf (the special case epsilon = 1/2). -/
theorem treeContraction_of_hypothesis [NeZero q]
    (h : TreeContractionHypothesis q) :
    TreeContractionAtHalf q :=
  fun chi hchi => h chi hchi fairCoin fairCoin_pos fairCoin_lt_one

/-! ### Exponential growth of product multiset -/

/-- For q >= 3, the product multiset over padded unit sets has cardinality at least
    2^N. This follows from `productMultiset_card` (cardinality = product of set sizes)
    combined with `paddedUnitSet_card_ge_two` (each set has size >= 2). -/
theorem productMultiset_card_ge_two_pow (hq3 : 2 < q) (N : ℕ) :
    2 ^ N ≤ Multiset.card (productMultiset (paddedUnitSet (q := q)) N) := by
  rw [productMultiset_card]
  calc (2 : ℕ) ^ N
      = ∏ _k ∈ Finset.range N, 2 := by simp [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range N, (paddedUnitSet (q := q) k).card :=
        Finset.prod_le_prod' (fun k _ => paddedUnitSet_card_ge_two hq3 k)

/-! ### StochasticTwoPointMC: proved from UFDStrong -/

/-- **StochasticTwoPointMC PROVED**: Under UFDStrong with q >= 3, every element of
    (ZMod q)ˣ has positive count in the product multiset of padded unit sets.

    Proof chain: UFDStrong => sparse spectral contraction => vanishing averaged
    character products => path existence (Fourier counting) => positive count.

    The key step is `ufdStrong_implies_path_existence`, which gives membership in
    `(productMultiset ...).toFinset`. Membership in toFinset is equivalent to
    positive count via `Multiset.count_pos` and `Multiset.mem_toFinset`. -/
theorem stochastic_two_point_mc_proved : StochasticTwoPointMC q := by
  intro hq3 hufd a
  obtain ⟨N, hN⟩ := ufdStrong_implies_path_existence hq3 hufd a
  exact ⟨N, Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hN)⟩

/-! ### Deterministic degeneration: treeCharSum at epsilon = 0

When all epsilon values are 0, the tree degenerates to a single path that always
picks minFac. This is the deterministic EM walk. The tree character sum at epsilon = 0
is then a product of character values along the deterministic path.

We prove the one-step reduction showing that at epsilon = 0, the tree character sum
factors as chiAt(minFac) times the recursive subtree at acc * minFac. -/

/-- At epsilon = 0, the tree character sum at depth 0 is 1 (base case). -/
theorem treeCharSum_at_zero_base (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
    (chi : (ZMod q')ˣ →* ℂˣ) (acc : ℕ) :
    treeCharSum q' chi 0 acc (fun _ => (0 : ℝ)) = 1 := rfl

/-- At epsilon = 0, the one-step tree character sum reduces to the deterministic
    (all-minFac) path: the secondMinFac branch has weight 0 and the minFac branch
    has weight 1, so only the minFac contribution survives. -/
theorem treeCharSum_at_zero_step (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
    (chi : (ZMod q')ˣ →* ℂˣ) (N : ℕ) (acc : ℕ) :
    treeCharSum q' chi (N + 1) acc (fun _ => (0 : ℝ)) =
    chiAt q' chi (acc + 1).minFac *
      treeCharSum q' chi N (acc * (acc + 1).minFac) (fun _ => (0 : ℝ)) := by
  simp only [treeCharSum]
  have h0 : (fun _ : ℕ => (0 : ℝ)) ∘ Nat.succ = fun _ => (0 : ℝ) := by ext; simp
  rw [h0]
  push_cast
  ring

/-! ### Relationship between self-consistent and non-self-consistent

The non-self-consistent approach (Part 21 + StochasticTwoPointMC above) and the
self-consistent tree approach (Part 20 + TreeContractionHypothesis) address different
questions:

1. **Non-self-consistent** (StochasticTwoPointMC): At each step n, the "factor set"
   is {minFac(prod(n)+1), secondMinFac(prod(n)+1)} mod q. The product multiset
   is formed by choosing one element from each factor set independently. The key
   insight is that these factor sets are determined by the ACTUAL EM walk (which
   always picks minFac), so the factor sets are FIXED regardless of which selection
   path we consider through the product multiset.

2. **Self-consistent** (TreeContractionHypothesis): The tree character sum tracks
   what happens when the accumulator CHANGES based on the selection. If we pick
   secondMinFac at step n, the accumulator at step n+1 is different, which changes
   the factor set at step n+1. The tree character sum accounts for this coupling.

The non-self-consistent version is PROVED (under UFDStrong) because the fixed
factor sets allow the product contraction machinery to apply directly. The
self-consistent version remains open because the path-dependent factor sets
prevent factorization into a product.

Despite this gap, the non-self-consistent result is still meaningful: it shows
that the COMBINATORIAL COUNTING of paths through the padded unit sets covers
every target. The issue is that the padded unit sets are computed from the
deterministic EM walk, not from the alternative walk that would be induced by
a different selection sequence. -/

/-- The non-self-consistent and self-consistent approaches are connected:
    if TreeContractionAtHalf holds AND the tree character sum controls the
    product multiset counting (which it does NOT in general -- this is the
    selection coherence gap), then a stronger variant MC would follow.

    We record the relationship between the two frameworks:
    - fairTreeCharSum at depth 0 is 1 (trivially)
    - fairTreeCharSum is bounded by 1 at all depths
    - TreeContractionHypothesis implies TreeContractionAtHalf
    - StochasticTwoPointMC is proved from UFDStrong alone -/
theorem self_consistent_vs_non_self_consistent [NeZero q] :
    -- 1. Fair tree char sum at depth 0 is 1
    (∀ (chi : (ZMod q)ˣ →* ℂˣ), fairTreeCharSum q chi 0 = 1)
    ∧
    -- 2. Fair tree char sum bounded by 1
    (∀ (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ), ‖fairTreeCharSum q chi N‖ ≤ 1)
    ∧
    -- 3. General tree contraction implies fair-coin contraction
    (TreeContractionHypothesis q → TreeContractionAtHalf q) :=
  ⟨fun _ => rfl, fairTreeCharSum_norm_le_one, treeContraction_of_hypothesis⟩

/-! ### Landscape theorem -/

/-- **Stochastic Two-Point MC Landscape**: summary of Part 23.

    PROVED theorems (no open hypotheses used in proofs):
    1. StochasticTwoPointMC: under UFDStrong, positive count for every target
    2. Product multiset grows exponentially (card >= 2^N for q >= 3)
    3. fairTreeCharSum bounded by 1
    4. TreeContractionHypothesis implies TreeContractionAtHalf
    5. Deterministic degeneration: treeCharSum at epsilon = 0 is the minFac path
    6. Standard EM walk = all-true epsilon-walk (Part 20 bridge)

    OPEN hypotheses documented:
    A. TreeContractionAtHalf: tree char sum at fair coin vanishes
       (strictly weaker than TreeContractionHypothesis)
    B. UFDStrong: per-chi spectral gap non-summability (see Part 22 for routes) -/
theorem stochastic_two_point_mc_landscape :
    -- 1. StochasticTwoPointMC PROVED from UFDStrong
    StochasticTwoPointMC q
    ∧
    -- 2. TreeContractionHypothesis implies TreeContractionAtHalf
    (∀ [NeZero q], TreeContractionHypothesis q → TreeContractionAtHalf q)
    ∧
    -- 3. fairTreeCharSum norm bounded by 1
    (∀ [NeZero q] (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ),
      ‖fairTreeCharSum q chi N‖ ≤ 1)
    ∧
    -- 4. Product multiset card >= 2^N for q >= 3
    (2 < q → ∀ N, 2 ^ N ≤
      Multiset.card (productMultiset (paddedUnitSet (q := q)) N))
    ∧
    -- 5. treeCharSum at epsilon = 0 is 1 at depth 0 (deterministic degeneration)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] [NeZero q']
       (chi : (ZMod q')ˣ →* ℂˣ) (acc : ℕ),
       treeCharSum q' chi 0 acc (fun _ => (0 : ℝ)) = 1)
    ∧
    -- 6. Standard EM walk is one leaf of the tree (Part 20 bridge)
    (∀ n, epsWalkProd emDecision n = prod n) :=
  ⟨stochastic_two_point_mc_proved,
   treeContraction_of_hypothesis,
   fun chi N => fairTreeCharSum_norm_le_one chi N,
   productMultiset_card_ge_two_pow,
   fun _ _ _ _ _ => rfl,
   epsWalkProd_emDecision⟩

end StochasticTwoPointMC

/-! ## Part 24: Faithful Character Escape and Unconditional Variant MC for q = 3

### Overview

A character `chi : (ZMod q)ˣ →* ℂˣ` is **faithful** if it is injective. For groups of
prime order, every nontrivial character is faithful (by Lagrange's theorem: the kernel
is a subgroup of prime-order group, so either trivial or the whole group; nontriviality
excludes the whole group).

The key insight is that for faithful characters, whenever the raw two-point unit set
has card at least 2 (i.e., minFac and secondMinFac give distinct units mod q), the
character values at these two units are automatically distinct. This gives a positive
spectral gap at every non-fallback step, without any number-theoretic hypothesis.

Combined with the `ufd_fallback_not_summable` result (which handles the case of
infinitely many fallback steps), we get **unconditional** non-summability of spectral
gaps for faithful nontrivial characters.

For q = 3, the unit group `(ZMod 3)ˣ` has order 2 (prime!), so every nontrivial
character is faithful. Therefore `UFDStrong 3` holds unconditionally, and the full
`StochasticTwoPointMC 3` follows with zero open hypotheses.

### Main results

* `IsFaithfulChar` -- definition: chi is injective
* `faithful_iff_trivial_ker` -- equivalence: injective ↔ trivial kernel
* `faithful_distinct_values` -- a ≠ b → chi(a) ≠ chi(b) (as complex numbers)
* `faithful_character_escape` -- unconditional non-summability for faithful nontrivial chi
* `prime_order_nontrivial_is_faithful` -- nontrivial char of prime-order group is faithful
* `ufdStrong_three` -- UFDStrong 3 unconditional
* `variant_mc_three_unconditional` -- every element of (ZMod 3)ˣ reachable, zero hypotheses
* `NonFaithfulCharacterEscape` -- open Prop for non-faithful characters (q > 3)
* `faithful_escape_landscape` -- 4-clause summary theorem
-/

section FaithfulCharacterEscape

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### IsFaithfulChar: definition and basic properties -/

/-- A character `chi : (ZMod q)ˣ →* ℂˣ` is **faithful** if it is injective.
    Equivalently, its kernel is trivial. For groups of prime order, every
    nontrivial character is faithful. -/
def IsFaithfulChar (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  Function.Injective chi

/-- A character is faithful iff its kernel is trivial: every element mapping to 1
    must be the identity. -/
theorem faithful_iff_trivial_ker (chi : (ZMod q)ˣ →* ℂˣ) :
    IsFaithfulChar q chi ↔ ∀ u : (ZMod q)ˣ, chi u = 1 → u = 1 := by
  constructor
  · intro hinj u hu
    have h1 : chi u = chi 1 := by rw [hu, map_one]
    exact hinj h1
  · intro hker a b hab
    have : chi (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hab1 := hker _ this
    have := mul_eq_one_iff_eq_inv.mp hab1
    rw [this, inv_inv]

/-- A faithful character separates points: distinct units have distinct character values
    (viewed as complex numbers). -/
theorem faithful_distinct_values (chi : (ZMod q)ˣ →* ℂˣ) (hfaith : IsFaithfulChar q chi)
    {a b : (ZMod q)ˣ} (hab : a ≠ b) :
    (chi a : ℂ) ≠ (chi b : ℂ) :=
  Units.val_injective.ne (hfaith.ne hab)

/-- When rawTwoPointUnitSet has card at least 2, the two lifted units are distinct. -/
theorem raw_card_two_implies_ne (n : ℕ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) ≠
    liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q) := by
  intro heq
  have : rawTwoPointUnitSet (q := q) n =
      {liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)} := by
    simp [rawTwoPointUnitSet, heq]
  rw [this] at hcard
  simp at hcard

/-- At a non-fallback step, a faithful character has a positive spectral gap.
    Key: card ≥ 2 means the two lifted units are distinct; faithfulness means
    their character values are distinct; this gives strict contraction. -/
theorem faithful_gap_pos_at_nonfallback (chi : (ZMod q)ˣ →* ℂˣ)
    (hfaith : IsFaithfulChar q chi) (n : ℕ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  have hne := raw_card_two_implies_ne n hcard
  have hdiff := faithful_distinct_values chi hfaith hne
  exact gap_pos_at_escape n chi hcard hdiff

/-- For a faithful nontrivial character, there exists a uniform positive spectral gap
    bound at all non-fallback steps. Proof: the gap function has finite range
    (paddedUnitSet maps into a finite type), and faithfulness gives positive gap at
    every non-fallback step. The minimum of the positive values in this finite range
    is a uniform lower bound. -/
theorem faithful_uniform_gap (chi : (ZMod q)ˣ →* ℂˣ)
    (hfaith : IsFaithfulChar q chi) :
    ∃ δ > 0, ∀ n, 2 ≤ (rawTwoPointUnitSet (q := q) n).card →
      δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  -- The gap function has finite range
  have hfin := gap_function_finite_range (q := q) chi
  -- At non-fallback steps, gaps are positive
  have hpos : ∀ n, 2 ≤ (rawTwoPointUnitSet (q := q) n).card →
      0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ :=
    fun n hcard => faithful_gap_pos_at_nonfallback chi hfaith n hcard
  -- We need at least one non-fallback step to get a nonempty positive range
  -- If no such step exists, any delta works vacuously
  by_cases hexists : ∃ n, 2 ≤ (rawTwoPointUnitSet (q := q) n).card
  · obtain ⟨n₀, hn₀⟩ := hexists
    -- Extract positive values in the range
    set posRange := {x ∈ hfin.toFinset | (0 : ℝ) < x}
    have hne : posRange.Nonempty := by
      exact ⟨_, by rw [Finset.mem_filter]; exact
        ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n₀, rfl⟩, hpos n₀ hn₀⟩⟩
    set δ := posRange.min' hne
    have hδ_pos : 0 < δ := by
      have hmem := Finset.min'_mem posRange hne
      rw [Finset.mem_filter] at hmem
      exact hmem.2
    have hδ_le : ∀ n, 0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ →
        δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
      intro n hfn
      apply Finset.min'_le
      rw [Finset.mem_filter]
      exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩
    exact ⟨δ, hδ_pos, fun n hcard => hδ_le n (hpos n hcard)⟩
  · push_neg at hexists
    exact ⟨1, one_pos, fun n hcard => absurd hcard (not_le.mpr (hexists n))⟩

/-! ### Faithful Character Escape: unconditional non-summability -/

/-- **Faithful Character Escape**: For every prime q at least 3 and every faithful
    nontrivial character, the spectral gaps of padded unit sets are non-summable.
    UNCONDITIONAL -- no open hypotheses.

    Proof by case split on whether infinitely many fallback steps exist:
    - If infinitely many fallback steps: gaps include infinitely many 1's (by
      `ufd_fallback_not_summable`), hence non-summable.
    - If cofinitely many non-fallback steps: faithfulness gives a uniform positive
      lower bound on the gap (by `faithful_uniform_gap`), and infinitely many
      such steps give non-summability (by `not_summable_of_frequently_ge`). -/
theorem faithful_character_escape (hq3 : 2 < q)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1)
    (hfaithful : IsFaithfulChar q chi) :
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) := by
  -- Case split: infinitely many fallback steps, or cofinitely many non-fallback
  by_cases h : ∀ N, ∃ n, N ≤ n ∧ ¬(2 ≤ (rawTwoPointUnitSet (q := q) n).card)
  · -- Case A: infinitely many fallback steps
    exact ufd_fallback_not_summable hq3 chi hchi h
  · -- Case B: cofinitely many non-fallback steps
    push_neg at h
    obtain ⟨N₀, hN₀⟩ := h
    -- Get uniform gap bound from faithfulness
    obtain ⟨δ, hδ_pos, hδ_le⟩ := faithful_uniform_gap chi hfaithful
    -- Infinitely many steps have gap >= delta
    apply not_summable_of_frequently_ge _ (fun n => paddedUnitSet_gap_nonneg chi n) hδ_pos
    intro N
    -- Take n = max N N₀; then n >= N₀ so non-fallback, and n >= N
    use max N N₀
    constructor
    · exact le_max_left N N₀
    · exact hδ_le _ (hN₀ _ (le_max_right N N₀))

/-! ### Prime-order groups: every nontrivial character is faithful -/

/-- In a finite group of prime order, every nontrivial character is faithful (injective).

    Proof: The kernel of chi is a subgroup of G. By Lagrange's theorem, its order
    divides |G|. Since |G| is prime, |ker| is 1 or |G|. Since chi is nontrivial,
    ker ≠ G (i.e., ker ≠ top). So ker = bot, which means chi is injective. -/
theorem prime_order_nontrivial_is_faithful {G : Type*} [CommGroup G] [Fintype G]
    (hprime : (Nat.card G).Prime)
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    Function.Injective chi := by
  -- The kernel is a subgroup of a prime-order group, so bot or top
  haveI : Fact (Nat.card G).Prime := Fact.mk hprime
  have h_or := chi.ker.eq_bot_or_eq_top_of_prime_card
  -- chi ≠ 1 means ker ≠ top
  have h_ne_top : chi.ker ≠ ⊤ := by
    rwa [Ne, MonoidHom.ker_eq_top_iff]
  -- So ker = bot
  have h_bot : chi.ker = ⊥ := h_or.resolve_right h_ne_top
  -- bot kernel means injective
  rwa [MonoidHom.ker_eq_bot_iff] at h_bot

/-- Fintype.card (ZMod q)ˣ = q - 1 for prime q. -/
theorem card_units_zmod_eq (hq : Nat.Prime q) : Fintype.card (ZMod q)ˣ = q - 1 := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]

/-- Nat.card (ZMod q)ˣ = q - 1 for prime q. -/
theorem natCard_units_zmod_eq (hq : Nat.Prime q) : Nat.card (ZMod q)ˣ = q - 1 := by
  rw [Nat.card_eq_fintype_card, card_units_zmod_eq hq]

/-! ### UFDStrong for q = 3: unconditional -/

/-- For q = 3, the unit group has prime order 2, so every nontrivial character is faithful.
    Combined with `faithful_character_escape`, this gives UFDStrong 3 unconditionally. -/
theorem ufdStrong_three : letI := Fact.mk (by decide : Nat.Prime 3); UFDStrong 3 := by
  letI : Fact (Nat.Prime 3) := Fact.mk (by decide)
  intro chi hchi
  have hprime : (Nat.card (ZMod 3)ˣ).Prime := by
    rw [natCard_units_zmod_eq (by decide : Nat.Prime 3)]
    decide
  have hfaithful : IsFaithfulChar 3 chi :=
    prime_order_nontrivial_is_faithful hprime chi hchi
  exact faithful_character_escape (by norm_num : (2 : ℕ) < 3) chi hchi hfaithful

/-- **Unconditional Variant MC for q = 3**: Every element of `(ZMod 3)ˣ` is reachable
    with ZERO open hypotheses. This is the first unconditional result in the stochastic
    MC framework.

    Proof: `ufdStrong_three` (unconditional) feeds into `stochastic_two_point_mc_proved`. -/
theorem variant_mc_three_unconditional :
    letI := Fact.mk (by decide : Nat.Prime 3)
    ∀ (a : (ZMod 3)ˣ), ∃ N,
      0 < Multiset.count a
        (productMultiset (paddedUnitSet (q := 3) ·) N) := by
  letI : Fact (Nat.Prime 3) := Fact.mk (by decide)
  intro a
  exact stochastic_two_point_mc_proved (q := 3)
    (by norm_num : (2 : ℕ) < 3) ufdStrong_three a

/-! ### NonFaithfulCharacterEscape: the remaining gap for q > 3 -/

/-- **FaithfulCharacterEscape**: All faithful nontrivial characters have non-summable
    spectral gaps. This holds UNCONDITIONALLY for all primes q >= 3. -/
def FaithfulCharacterEscape (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → IsFaithfulChar q chi →
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)

/-- **NonFaithfulCharacterEscape**: All non-faithful nontrivial characters have
    non-summable spectral gaps. This is the SOLE remaining open hypothesis for
    UFDStrong at primes q where `(ZMod q)ˣ` has composite order (i.e., q >= 5).

    For q = 3, (ZMod 3)ˣ has prime order 2, so there are NO non-faithful nontrivial
    characters, and this Prop is vacuously true. -/
def NonFaithfulCharacterEscape (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar q chi →
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)

/-- FaithfulCharacterEscape holds unconditionally for all primes q >= 3. -/
theorem faithful_escape_unconditional (hq3 : 2 < q) : FaithfulCharacterEscape q :=
  fun chi hchi hfaith => faithful_character_escape hq3 chi hchi hfaith

/-- FaithfulCharacterEscape + NonFaithfulCharacterEscape implies UFDStrong.
    Every nontrivial character is either faithful or not, so the two cases cover all. -/
theorem nfce_and_fce_implies_ufdStrong
    (_hq3 : 2 < q)
    (hfce : FaithfulCharacterEscape q)
    (hnfce : NonFaithfulCharacterEscape q) :
    UFDStrong q := by
  intro chi hchi
  by_cases hfaith : IsFaithfulChar q chi
  · exact hfce chi hchi hfaith
  · exact hnfce chi hchi hfaith

/-- For primes where the unit group has prime order, NonFaithfulCharacterEscape is
    vacuously true (there are no non-faithful nontrivial characters). -/
theorem nfce_vacuous_of_prime_order
    (hprime : (Nat.card (ZMod q)ˣ).Prime) :
    NonFaithfulCharacterEscape q := by
  intro chi hchi hnfaith
  exact absurd (prime_order_nontrivial_is_faithful hprime chi hchi) hnfaith

/-- NonFaithfulCharacterEscape is the sole remaining open hypothesis for UFDStrong
    at primes q >= 3. Combined with `faithful_escape_unconditional`, it suffices. -/
theorem nfce_implies_ufdStrong (hq3 : 2 < q)
    (hnfce : NonFaithfulCharacterEscape q) :
    UFDStrong q :=
  nfce_and_fce_implies_ufdStrong hq3 (faithful_escape_unconditional hq3) hnfce

/-! ### Landscape theorem -/

/-- **Faithful Character Escape Landscape**: summary of Part 24.

    PROVED UNCONDITIONALLY:
    1. Faithful character escape for all q >= 3 (no open hypotheses)
    2. UFDStrong(3) (no open hypotheses, since (ZMod 3)ˣ has prime order 2)
    3. StochasticTwoPointMC(3): every element of (ZMod 3)ˣ reachable (zero hypotheses)
    4. For q > 3: NonFaithfulCharacterEscape is the SOLE remaining open hypothesis

    The mathematical content is clean: faithfulness = injectivity of characters.
    For cyclic groups of prime order, every nontrivial character is faithful (Lagrange).
    For (ZMod 3)ˣ of order 2, this closes UFDStrong entirely. -/
theorem faithful_escape_landscape :
    -- 1. Faithful character escape unconditional for all q >= 3
    (∀ (q : ℕ) [Fact (Nat.Prime q)], 2 < q →
      ∀ chi : (ZMod q)ˣ →* ℂˣ, chi ≠ 1 → IsFaithfulChar q chi →
      ¬Summable (fun n => 1 - ‖meanCharValue chi (@paddedUnitSet q _ n)‖))
    ∧
    -- 2. UFDStrong(3) unconditional
    (letI := Fact.mk (by decide : Nat.Prime 3); UFDStrong 3)
    ∧
    -- 3. StochasticTwoPointMC(3) unconditional: every element reachable
    (letI := Fact.mk (by decide : Nat.Prime 3);
     ∀ (a : (ZMod 3)ˣ), ∃ N,
      0 < Multiset.count a
        (productMultiset (paddedUnitSet (q := 3) ·) N))
    ∧
    -- 4. NFCE is the sole remaining open hypothesis for q > 3
    (∀ (q : ℕ) [Fact (Nat.Prime q)], 2 < q →
      NonFaithfulCharacterEscape q → UFDStrong q) :=
  ⟨fun _ _ => faithful_character_escape,
   ufdStrong_three,
   variant_mc_three_unconditional,
   fun _ _ => nfce_implies_ufdStrong⟩

end FaithfulCharacterEscape
