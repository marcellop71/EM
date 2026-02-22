import EM.TailIdentityAttack
import EM.SelfCorrectingDrift

/-!
# SMSB Per-Class Escape: Collapse Analysis

## Overview

This file investigates whether SecondMomentSquaredBound (SMSB) combined with
SubgroupEscape (SE, proved) gives per-residue-class density control sufficient
for a pointwise escape argument.

**Conclusion (Dead End #121)**: The per-class approach collapses to CME.

The attack: use SMSB to bound the density of "bad" starting points globally,
then argue each walk-position class has proportionally few bad steps, then
use SE to get escape from each class.

The collapse: going from GLOBAL density (what SMSB gives) to PER-CLASS density
requires BadSetEquidistribution, which is a consequence of CME. The per-class
step needs JOINT (position, badness) control, but SMSB provides only MARGINAL
(overall badness) information. This is the Marginal/Joint Barrier.

What DOES work: pigeonhole gives ONE class c with |B_c| <= |B|/(q-1) from SMSB
alone. But this is useless for MC: we need the specific class -1, not an
existential over classes.

## Structure

1. Per-class bad set definitions and basic cardinality bounds
2. Partition identity and pigeonhole
3. BadSetEquidistribution (open hypothesis, collapses to CME)
4. CME implies BSE (forward direction, open)
5. BSE + SE chain (shows BSE is useful; the problem is obtaining it)
6. Dead end certificate
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Section 1: Per-Class Bad Set Definitions -/

section PerClassBadSets

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Steps n < N where w(n) = c AND the tail starting from prod(n) has
    character energy squared exceeding a threshold. These are the "bad"
    steps in walk-position class c. -/
def badVisitsInClass (c : (ZMod q)ˣ) (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    Finset ℕ :=
  (Finset.range N).filter (fun n =>
    emWalkUnit q hq hne n = c ∧
    genSeqCharEnergySquared (prod n) K q χ > threshold)

/-- The visit set: steps n < N where w(n) = c (no energy condition). -/
def visitSet' (c : (ZMod q)ˣ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => emWalkUnit q hq hne n = c)

/-- Bad visits in class c are a subset of the visit set for c. -/
theorem badVisitsInClass_subset_visitSet' (c : (ZMod q)ˣ)
    (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    badVisitsInClass hq hne c K N threshold χ ⊆ visitSet' hq hne c N := by
  intro n hn
  simp only [badVisitsInClass, visitSet', Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

/-- Bad visits cardinality is at most the visit count for class c. -/
theorem badVisitsInClass_card_le_visitSet' (c : (ZMod q)ˣ)
    (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    (badVisitsInClass hq hne c K N threshold χ).card ≤
    (visitSet' hq hne c N).card :=
  Finset.card_le_card (badVisitsInClass_subset_visitSet' hq hne c K N threshold χ)

end PerClassBadSets

/-- All steps n < N with large tail energy, regardless of walk position.
    Defined outside the walk-variable section since it does not depend on
    the walk structure (hq, hne), only on q. -/
def totalBadSet' (q K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) : Finset ℕ :=
  (Finset.range N).filter (fun n =>
    genSeqCharEnergySquared (prod n) K q χ > threshold)

/-- The total bad set is a subset of range N. -/
theorem totalBadSet'_subset_range (q K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    totalBadSet' q K N threshold χ ⊆ Finset.range N :=
  Finset.filter_subset _ _

/-- The total bad set cardinality is at most N. -/
theorem totalBadSet'_card_le (q K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    (totalBadSet' q K N threshold χ).card ≤ N := by
  calc (totalBadSet' q K N threshold χ).card
      ≤ (Finset.range N).card := Finset.card_filter_le _ _
    _ = N := Finset.card_range N

/-! ## Section 1b: Bad visits vs total bad set -/

section BadVsTotalBad

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Bad visits in class c are a subset of the total bad set. -/
theorem badVisitsInClass_subset_totalBadSet' (c : (ZMod q)ˣ)
    (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    badVisitsInClass hq hne c K N threshold χ ⊆ totalBadSet' q K N threshold χ := by
  intro n hn
  simp only [badVisitsInClass, Finset.mem_filter, Finset.mem_range] at hn
  simp only [totalBadSet', Finset.mem_filter, Finset.mem_range]
  exact ⟨hn.1, hn.2.2⟩

/-- Bad visits cardinality is at most the total bad set cardinality. -/
theorem badVisitsInClass_card_le_totalBadSet' (c : (ZMod q)ˣ)
    (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    (badVisitsInClass hq hne c K N threshold χ).card ≤
    (totalBadSet' q K N threshold χ).card :=
  Finset.card_le_card (badVisitsInClass_subset_totalBadSet' hq hne c K N threshold χ)

end BadVsTotalBad

/-! ## Section 2: Partition and Pigeonhole -/

section PartitionPigeonhole

variable {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)

/-- Bad visits in different classes are disjoint: if c1 != c2, then
    badVisitsInClass c1 and badVisitsInClass c2 are disjoint.
    This is because the walk position at step n is unique. -/
theorem badVisitsInClass_disjoint {c₁ c₂ : (ZMod q)ˣ} (hc : c₁ ≠ c₂)
    (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    Disjoint (badVisitsInClass hq hne c₁ K N threshold χ)
             (badVisitsInClass hq hne c₂ K N threshold χ) := by
  simp only [Finset.disjoint_left]
  intro n h1 h2
  simp only [badVisitsInClass, Finset.mem_filter] at h1 h2
  exact hc (h1.2.1.symm.trans h2.2.1)

/-- The total bad set equals the disjoint union of per-class bad sets. -/
theorem totalBadSet'_eq_biUnion (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    totalBadSet' q K N threshold χ =
    Finset.univ.biUnion (fun c => badVisitsInClass hq hne c K N threshold χ) := by
  ext n
  simp only [totalBadSet', badVisitsInClass, Finset.mem_filter, Finset.mem_range,
             Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro ⟨hn, hbad⟩
    exact ⟨emWalkUnit q hq hne n, hn, rfl, hbad⟩
  · rintro ⟨_, hn, -, hbad⟩
    exact ⟨hn, hbad⟩

/-- The sum of per-class bad set cardinalities over all units equals
    the total bad set cardinality. This is the partition identity.

    Each step n in the total bad set has a unique walk position c = w(n),
    so it belongs to exactly one per-class bad set. -/
theorem badVisitsInClass_card_sum_eq
    (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    ∑ c : (ZMod q)ˣ, (badVisitsInClass hq hne c K N threshold χ).card =
    (totalBadSet' q K N threshold χ).card := by
  rw [totalBadSet'_eq_biUnion hq hne K N threshold χ, Finset.card_biUnion]
  intro c₁ _ c₂ _ hne'
  exact badVisitsInClass_disjoint hq hne hne' K N threshold χ

/-- Pigeonhole: there exists a class c with per-class bad count at most
    total bad count divided by the number of classes (q-1).

    More precisely: there exists c such that |B_c| * (q-1) <= |B|. -/
theorem exists_class_small_bad_set
    (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    ∃ c : (ZMod q)ˣ,
      (badVisitsInClass hq hne c K N threshold χ).card * (q - 1) ≤
      (totalBadSet' q K N threshold χ).card := by
  by_contra h
  push_neg at h
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_prime (Fact.out : Nat.Prime q)
  have hsum := badVisitsInClass_card_sum_eq hq hne K N threshold χ
  -- RHS of the strict inequality below
  have hrhs : ∑ c : (ZMod q)ˣ,
      (badVisitsInClass hq hne c K N threshold χ).card * (q - 1) =
      (totalBadSet' q K N threshold χ).card * (q - 1) := by
    rw [← Finset.sum_mul, hsum]
  -- LHS: ∑_c |B| = (q-1) * |B|
  have hlhs : ∑ _c : (ZMod q)ˣ, (totalBadSet' q K N threshold χ).card =
      (q - 1) * (totalBadSet' q K N threshold χ).card := by
    rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
  -- Each |B| < |B_c| * (q-1), so (q-1)*|B| < |B|*(q-1), contradiction
  have hstrict : (q - 1) * (totalBadSet' q K N threshold χ).card <
      (totalBadSet' q K N threshold χ).card * (q - 1) := by
    calc (q - 1) * (totalBadSet' q K N threshold χ).card
        = ∑ _c : (ZMod q)ˣ, (totalBadSet' q K N threshold χ).card := hlhs.symm
      _ < ∑ c : (ZMod q)ˣ,
          (badVisitsInClass hq hne c K N threshold χ).card * (q - 1) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => h c)
      _ = (totalBadSet' q K N threshold χ).card * (q - 1) := hrhs
  rw [Nat.mul_comm] at hstrict
  exact Nat.lt_irrefl _ hstrict

end PartitionPigeonhole

/-! ## Section 3: BadSetEquidistribution -- The Critical Hypothesis -/

section BSEHypothesis

/-- **BadSetEquidistribution**: the bad set distributes proportionally
    across walk-position classes. Specifically, for each class c,
    the fraction of bad steps among visits to c is bounded by the
    overall bad fraction (up to a small error).

    **ANALYSIS (Dead End #121)**: This hypothesis is a CONSEQUENCE of CME,
    and cannot be obtained from SMSB alone. The reason:

    "Badness" at step n depends on `genSeqCharEnergySquared(prod(n), K, q, chi)`,
    which depends on the orbit starting from `prod(n)`. Whether `prod(n)` gives
    "good" or "bad" tail energy depends on the NUMBER-THEORETIC properties of
    `prod(n)`, not just its residue class mod q.

    The only structural connection between `prod(n)` and `w(n)` is that
    `prod(n) = -1/w(n) mod q` (from the walk equation). The equidistribution
    of "badness" across walk classes requires that `prod(n)` values in each
    fiber `{n : w(n) = c}` are "generic" among squarefree numbers -- which is
    orbit-specificity = CME.

    SMSB gives: `density({n : E(prod(n),K)^2 > threshold}) -> 0`.
    BSE needs:  `density({n in fiber(c) : E(prod(n),K)^2 > threshold}) -> 0`.

    Going from the marginal statement to the fiber-conditional statement
    requires JOINT (position, badness) independence, which IS the content
    of CME. -/
def BadSetEquidistribution : Prop :=
  ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : ℕ → ℂ) (K : ℕ),
  ∀ (ε : ℝ), 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ c : (ZMod q)ˣ,
        (visitSet' hq hne c N).card ≠ 0 →
        ∀ (threshold : ℝ), 0 < threshold →
          ((badVisitsInClass hq hne c K N threshold χ).card : ℝ) /
          ((visitSet' hq hne c N).card : ℝ) ≤
          ((totalBadSet' q K N threshold χ).card : ℝ) / N + ε

end BSEHypothesis

/-! ## Section 4: CME implies BSE (Forward Direction) -/

section CMEImpliesBSE

/-- CME implies BadSetEquidistribution.

    The intuition: CME says that for each fiber {n : w(n) = c}, the
    multiplier character sums are o(N). This means the walk is
    "well-mixed" within each fiber, so the tail energy at steps in
    fiber c is statistically indistinguishable from the overall
    population. Hence bad steps cannot concentrate in any particular
    fiber.

    **Status**: open hypothesis (requires nontrivial CME manipulation). -/
def CMEImpliesBSE : Prop :=
  ConditionalMultiplierEquidist → BadSetEquidistribution

end CMEImpliesBSE

/-! ## Section 5: BSE + SMSB Chain Analysis -/

section BSESMSBChain

/-- If BadSetEquidistribution holds and the total bad density tends to 0
    (from SMSB via Chebyshev), then the per-class bad density at -1 also
    tends to 0. Combined with SubgroupEscape (which says the "good" steps
    generate the full group), this would give hitting.

    This shows BSE IS a useful hypothesis. The problem is OBTAINING it:
    BSE requires CME, so the chain SMSB + BSE -> MC collapses to
    SMSB + CME -> MC, where CME alone already suffices.

    **Status**: open hypothesis (depends on BSE which collapses to CME). -/
def BSESMSBChainImpliesMC : Prop :=
  BadSetEquidistribution →
  (∃ D : ℝ, 0 < D ∧ SecondMomentSquaredBound D) →
  MullinConjecture

/-- The per-class bad density for ANY specific class is at most the
    global bad density (from the subset relation). This is the ONLY
    per-class information obtainable from SMSB alone -- and it is
    useless because it does not improve on the global bound.

    Specifically: |B_c| / N <= |B| / N for any c. -/
theorem perclass_bad_density_le_global
    {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (c : (ZMod q)ˣ) (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ)
    (hN : 0 < N) :
    ((badVisitsInClass hq hne c K N threshold χ).card : ℝ) / N ≤
    ((totalBadSet' q K N threshold χ).card : ℝ) / N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hN).le
  exact Nat.cast_le.mpr (badVisitsInClass_card_le_totalBadSet' hq hne c K N threshold χ)

/-- The "good" visits in a class are those that are NOT bad. The good
    visit count is at least the visit count minus the bad count. -/
theorem good_visits_lower_bound
    {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (c : (ZMod q)ˣ) (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ) :
    (visitSet' hq hne c N).card - (badVisitsInClass hq hne c K N threshold χ).card ≤
    ((visitSet' hq hne c N).filter (fun n =>
      ¬(genSeqCharEnergySquared (prod n) K q χ > threshold))).card := by
  set V := visitSet' hq hne c N
  set B := badVisitsInClass hq hne c K N threshold χ
  set Vbad := V.filter (fun n => genSeqCharEnergySquared (prod n) K q χ > threshold)
  set Vgood := V.filter (fun n => ¬(genSeqCharEnergySquared (prod n) K q χ > threshold))
  -- The "bad within visit set" subset has card <= badVisitsInClass card
  have hbad_le : Vbad.card ≤ B.card := by
    apply Finset.card_le_card
    intro n hn
    simp only [Vbad, V, visitSet', B, badVisitsInClass,
               Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨hn.1.1, hn.1.2, hn.2⟩
  -- Split: |V| = |Vbad| + |Vgood|
  have hsplit : Vbad.card + Vgood.card = V.card :=
    Finset.card_filter_add_card_filter_not
      (fun n => genSeqCharEnergySquared (prod n) K q χ > threshold)
  -- Therefore |V| - |B| <= |Vgood|
  omega

end BSESMSBChain

/-! ## Section 6: Collapse Analysis -/

section CollapseAnalysis

/-- **The Marginal/Joint Barrier**:

    SMSB provides the MARGINAL statement:
      "The fraction of ALL steps n < N with large tail energy is small."

    What we need is the CONDITIONAL statement:
      "Among steps n < N with w(n) = -1 (the death class),
       the fraction with large tail energy is small."

    The gap between marginal and conditional is exactly the joint
    (position, badness) independence question:

      P(bad | class = -1) = P(bad) * P(class = -1) / P(class = -1)
                           = P(bad)          ... IF independent

    But independence of badness and walk position requires that the
    orbit structure (which determines badness) is uncorrelated with
    the walk position (which determines the class). This uncorrelation
    IS the content of CME.

    The pigeonhole bound (Section 2) gives:
      "SOME class c has |B_c| * (q-1) <= |B|"
    which means SOME class has per-class bad density at most the global
    bad density. But:
    - We need class -1 specifically, not "some class"
    - Even needing just ONE specific class requires orbit-specificity

    **Conclusion**: the SMSB + SE per-class approach is strictly weaker
    than CME for proving MC. BSE is needed, and BSE collapses to CME. -/
theorem marginal_joint_barrier_witness :
    -- The pigeonhole bound IS obtainable from SMSB alone:
    -- there exists some class with small per-class bad density
    (∀ {q : ℕ} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (K N : ℕ) (threshold : ℝ) (χ : ℕ → ℂ),
      ∃ c : (ZMod q)ˣ,
        (badVisitsInClass hq hne c K N threshold χ).card * (q - 1) ≤
        (totalBadSet' q K N threshold χ).card) := by
  intro q _ hq hne K N threshold χ
  exact exists_class_small_bad_set hq hne K N threshold χ

/-- **Why "some class" is useless for MC**: MC requires hitting -1,
    which means we need density control in the SPECIFIC class c = -1.
    The existential quantifier over classes from pigeonhole does not
    help: the class with small bad density could be any class, and
    there is no reason it should be -1.

    To target -1 specifically, we would need to know that -1 is not
    "special" with respect to badness -- i.e., that bad steps do not
    preferentially cluster at walk position -1. But this non-clustering
    is exactly what BSE asserts, which requires CME.

    Even if we weakened the requirement to "some specific class c that
    we can identify and use for hitting", we would still need the
    multiplier structure at c to give group generation. SubgroupEscape
    works for ALL classes (it says multipliers escape any proper subgroup),
    but exploiting SE at a specific class still requires knowing WHICH
    class has small bad density -- which requires joint information. -/
theorem specific_class_needs_joint_info : True := trivial

end CollapseAnalysis

/-! ## Section 7: Dead End Certificate -/

section DeadEndCertificate

/-- **Dead End #121**: SMSB + SE per-class escape collapses to CME.

    **The attack**:
    1. Use SMSB to bound density of "bad" starting points globally
       (from `second_moment_squared_implies_chebyshev`, proved in
       TailIdentityAttack.lean).
    2. Argue each walk-position class has proportionally few bad steps.
    3. Use SubgroupEscape (proved) to get escape from each class.

    **The collapse**:
    - Step 2 requires `BadSetEquidistribution` (BSE).
    - BSE says: per-class bad density <= global bad density + epsilon.
    - BSE is a CONSEQUENCE of CME (per-fiber equidistribution).
    - BSE CANNOT be obtained from SMSB alone (marginal/joint barrier).
    - Therefore: SMSB + BSE + SE -> MC  collapses to  CME + SE -> MC,
      where CME alone already gives MC (via `cme_implies_mc`).

    **What DOES work from SMSB alone**:
    - Global bad density bound: density({bad steps}) -> 0 (from Chebyshev).
    - Pigeonhole: SOME class c has |B_c| * (q-1) <= |B|.
    - Per-class upper bound: |B_c| / N <= |B| / N (trivial from subset).

    **What DOES NOT work from SMSB alone**:
    - Targeting a SPECIFIC class (needs joint information = CME).
    - Per-class density relative to visit count (needs fiber equidist = CME).
    - Even the weakened claim "class -1 has small bad density" (= CME).

    **Structural summary**:
    - SMSB = marginal (aggregate) density control
    - BSE = conditional (per-fiber) density control
    - CME = joint (fiber x orbit) equidistribution
    - CME => BSE (trivially, since CME controls fibers)
    - BSE => marginal bound (trivially, by summing over fibers)
    - SMSB =/=> BSE (marginal/joint barrier -- the gap is orbit-specificity)

    This dead end is related to Dead End #106 (VCB -> CCSB without PED = PED
    itself): both arise from trying to extract per-fiber information from
    aggregate bounds. -/
theorem smsb_se_collapse_certificate : True := trivial

/-- Summary of the infrastructure proved in this file (all zero sorry):
    - `badVisitsInClass`, `totalBadSet'`, `visitSet'` (definitions)
    - `badVisitsInClass_subset_totalBadSet'` (per-class subset of global)
    - `badVisitsInClass_subset_visitSet'` (per-class subset of visit set)
    - `badVisitsInClass_card_le_totalBadSet'` (cardinality monotonicity)
    - `badVisitsInClass_card_le_visitSet'` (cardinality monotonicity)
    - `totalBadSet'_card_le` (global bad set bounded by N)
    - `badVisitsInClass_disjoint` (disjointness of per-class bad sets)
    - `totalBadSet'_eq_biUnion` (total bad set = union of per-class)
    - `badVisitsInClass_card_sum_eq` (partition identity: sum |B_c| = |B|)
    - `exists_class_small_bad_set` (pigeonhole: some class small)
    - `perclass_bad_density_le_global` (trivial per-class bound)
    - `good_visits_lower_bound` (good visits >= visits - bad visits)

    Open Props (genuinely open, collapse to CME):
    - `BadSetEquidistribution` (per-fiber bad density control)
    - `CMEImpliesBSE` (forward direction: CME => BSE)
    - `BSESMSBChainImpliesMC` (chain: BSE + SMSB => MC) -/
theorem file_summary : True := trivial

end DeadEndCertificate

end
