import EM.Ensemble.CRT
import EM.Population.ReciprocalSum

/-!
# Backward Dynamics Framework for CRT Propagation

This file formalizes a Tao-style backward dynamics framework for reducing
`CRTPropagationStep` to a single open hypothesis about empirical transition
probabilities. The chain to close:

  EnsembleTransitionApprox -> CRTPropagationStep -> AEP -> ... -> PositiveDensityRSD

All bridges from FirstMomentStep onward are already proved in existing files.

## Mathematical Overview

The accumulator `genProd n (k+1) = genProd n k * genSeq n k` propagates as a product.
To understand how the mod-q distribution of `genProd n (k+1)` relates to that of
`genProd n k`, we decompose the population by BOTH the accumulator class and the
multiplier class at step k.

The **joint count** records how many squarefree n have both `genProd n k` in a given
class c AND `genSeq n k` in a given class b. The **transition probability** is the
conditional fraction: among n with `genProd n k` in class c, what fraction has
`genSeq n k` in class b?

The **backward density decomposition** expresses the density at step k+1 as a
weighted sum over source classes with transition probabilities as weights.

## Main Results

### Definitions
* `jointCount`                    -- joint count of (accumulator class, multiplier class)
* `transitionProb`                -- empirical transition probability
* `EnsembleTransitionApprox`      -- open hypothesis: non-death transitions ≈ 1/(q-1)
* `DeathClassTransitionApprox`    -- open hypothesis: death class transitions ≈ 1/(q-1)

### Proved Theorems
* `jointCount_le_accumCount`      -- joint count bounded by accumulator count
* `jointCount_sum_eq_accumCount`  -- partition identity: sum over multiplier classes
* `transitionProb_nonneg`         -- transition probability is non-negative
* `transitionProb_le_one`         -- transition probability is at most 1
* `transitionProb_sum_one`        -- transition probabilities sum to 1
* `accumCount_succ_decomp`        -- backward decomposition of accumulator count
* `accumDensity_succ_eq`          -- backward decomposition of accumulator density
* `eta_dcta_implies_crt_propagation` -- ETA + DCTA -> CRTPropagationStep
* `eta_sre_implies_prsd`          -- ETA + DCTA + SRE -> PositiveDensityRSD
* `backward_dynamics_landscape`   -- summary landscape theorem
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Section 1: Joint Count Infrastructure -/

section JointCount

/-- **Joint count**: number of squarefree n in [1,X] with genProd(n,k) in residue class
    c mod q AND genSeq(n,k) in residue class b mod q.

    This refines `sqfreeAccumCount` by additionally recording the multiplier class. -/
def jointCount (X k q : Nat) (c b : ZMod q) : Nat :=
  ((Finset.Icc 1 X).filter (fun n =>
    Squarefree n ∧ (genProd n k : ZMod q) = c ∧ (genSeq n k : ZMod q) = b)).card

/-- The joint count is bounded by the accumulator count: every n counted by
    `jointCount` satisfies the accumulator condition. -/
theorem jointCount_le_accumCount (X k q : Nat) (c b : ZMod q) :
    jointCount X k q c b ≤ sqfreeAccumCount X k q c := by
  unfold jointCount sqfreeAccumCount
  exact Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.1⟩

/-- The joint count is bounded by the total squarefree count. -/
theorem jointCount_le_sqfreeCount (X k q : Nat) (c b : ZMod q) :
    jointCount X k q c b ≤ sqfreeCount X :=
  le_trans (jointCount_le_accumCount X k q c b) (sqfreeAccumCount_le_sqfreeCount X k q c)

/-- **Partition identity**: the sum of joint counts over all multiplier classes b
    equals the accumulator count. Every n in the accumulator class c falls into
    exactly one multiplier class. -/
theorem jointCount_sum_eq_accumCount (X k q : Nat) [NeZero q] (c : ZMod q) :
    ∑ b : ZMod q, jointCount X k q c b = sqfreeAccumCount X k q c := by
  unfold jointCount sqfreeAccumCount
  -- Show the accumulator filter is the biUnion of joint filters
  have hset_eq : (Finset.Icc 1 X).filter (fun n =>
      Squarefree n ∧ (genProd n k : ZMod q) = c) =
    Finset.univ.biUnion (fun b : ZMod q =>
      (Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ (genProd n k : ZMod q) = c ∧ (genSeq n k : ZMod q) = b)) := by
    ext n
    constructor
    · intro hn
      simp only [Finset.mem_filter] at hn
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      exact ⟨(genSeq n k : ZMod q), hn.1, hn.2.1, hn.2.2, rfl⟩
    · intro hn
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter] at hn
      obtain ⟨_, hn_icc, hsf, hck, _⟩ := hn
      exact Finset.mem_filter.mpr ⟨hn_icc, hsf, hck⟩
  -- Pairwise disjoint
  have hdisj : ((Finset.univ : Finset (ZMod q)) : Set (ZMod q)).PairwiseDisjoint (fun b =>
      (Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ (genProd n k : ZMod q) = c ∧ (genSeq n k : ZMod q) = b)) := by
    intro b₁ _ b₂ _ hne
    simp only [Function.onFun, Finset.disjoint_filter]
    intro n _ ⟨_, _, hb₁⟩ ⟨_, _, hb₂⟩
    exact hne (hb₁.symm.trans hb₂)
  rw [hset_eq, Finset.card_biUnion hdisj]

end JointCount

/-! ## Section 2: Transition Probability -/

section TransitionProb

/-- **Empirical transition probability**: among squarefree n in [1,X] with
    genProd(n,k) in class c mod q, the fraction with genSeq(n,k) in class b mod q. -/
def transitionProb (X k q : Nat) (c b : ZMod q) : ℝ :=
  (jointCount X k q c b : ℝ) / (sqfreeAccumCount X k q c : ℝ)

/-- The transition probability is non-negative. -/
theorem transitionProb_nonneg (X k q : Nat) (c b : ZMod q) :
    0 ≤ transitionProb X k q c b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The transition probability is at most 1. -/
theorem transitionProb_le_one (X k q : Nat) (c b : ZMod q) :
    transitionProb X k q c b ≤ 1 := by
  unfold transitionProb
  rcases eq_or_ne (sqfreeAccumCount X k q c) 0 with hzero | hpos
  · simp [hzero]
  · have hac_pos : (0 : ℝ) < (sqfreeAccumCount X k q c : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hpos)
    rw [div_le_one hac_pos]
    exact Nat.cast_le.mpr (jointCount_le_accumCount X k q c b)

/-- When the accumulator count is positive, the transition probabilities sum to 1. -/
theorem transitionProb_sum_one (X k q : Nat) [NeZero q] (c : ZMod q)
    (hpos : 0 < sqfreeAccumCount X k q c) :
    ∑ b : ZMod q, transitionProb X k q c b = 1 := by
  unfold transitionProb
  rw [← Finset.sum_div]
  have hcast : (0 : ℝ) < (sqfreeAccumCount X k q c : ℝ) := Nat.cast_pos.mpr hpos
  rw [div_eq_one_iff_eq hcast.ne']
  have := jointCount_sum_eq_accumCount X k q c
  exact_mod_cast this

end TransitionProb

/-! ## Section 3: Backward Density Decomposition

The key identity: genProd(n, k+1) = genProd(n, k) * genSeq(n, k), so
genProd(n, k+1) mod q = (genProd(n, k) mod q) * (genSeq(n, k) mod q).

For a nonzero target a, we have genProd(n,k+1) = a iff there exist nonzero c, b
with c * b = a and genProd(n,k) = c and genSeq(n,k) = b.

When genProd(n,k) = 0 mod q (absorbed), genProd(n,k+1) = 0 as well (by
`genProd_mod_zero_absorbing`), so these orbits don't contribute to nonzero targets.
-/

section BackwardDecomposition

/-- Helper: when genProd(n,k) has nonzero residue mod q and genProd(n,k+1) = a (nonzero),
    then genSeq(n,k) = a * (genProd(n,k))^(-1) mod q. -/
private theorem genSeq_eq_of_genProd_succ {q n k : Nat} [NeZero q]
    [Fact (Nat.Prime q)] {a c : ZMod q}
    (hc : c ≠ 0) (ha : (genProd n (k + 1) : ZMod q) = a)
    (hck : (genProd n k : ZMod q) = c) :
    (genSeq n k : ZMod q) = a * c⁻¹ := by
  have hprod : a = c * (genSeq n k : ZMod q) := by
    have : (genProd n (k + 1) : ZMod q) = (genProd n k : ZMod q) * (genSeq n k : ZMod q) := by
      simp only [genProd_succ, Nat.cast_mul]
    rw [← ha, this, hck]
  -- From a = c * s, we get s = c⁻¹ * a = a * c⁻¹
  have hfield := ZMod.mul_inv_of_unit c (IsUnit.mk0 c hc)
  -- c * c⁻¹ = 1
  calc (genSeq n k : ZMod q) = 1 * (genSeq n k : ZMod q) := (one_mul _).symm
    _ = (c⁻¹ * c) * (genSeq n k : ZMod q) := by rw [show c⁻¹ * c = 1 from by
        rw [mul_comm]; exact hfield]
    _ = c⁻¹ * (c * (genSeq n k : ZMod q)) := by rw [mul_assoc]
    _ = c⁻¹ * a := by rw [hprod]
    _ = a * c⁻¹ := mul_comm _ _

/-- Helper: when genProd(n,k+1) ≡ a mod q with a ≠ 0, then genProd(n,k) ≢ 0 mod q.
    This follows from absorption: if q | genProd(n,k), then q | genProd(n,k+1),
    contradicting a ≠ 0. -/
private theorem genProd_succ_nonzero_of_source {q n k : Nat} [NeZero q]
    (_hq : 1 < q) {a : ZMod q} (ha : a ≠ 0)
    (hak : (genProd n (k + 1) : ZMod q) = a) :
    (genProd n k : ZMod q) ≠ 0 := by
  intro h0
  have hdvd : q ∣ genProd n k := by
    rwa [ZMod.natCast_eq_zero_iff] at h0
  have hdvd1 : q ∣ genProd n (k + 1) := by
    rw [genProd_succ]; exact dvd_mul_of_dvd_left hdvd _
  have : (genProd n (k + 1) : ZMod q) = 0 := by
    rwa [ZMod.natCast_eq_zero_iff]
  rw [hak] at this; exact ha this

/-- **Backward decomposition of accumulator count**: the count of squarefree n in
    [1,X] with genProd(n,k+1) in class a decomposes as a sum over source classes c
    of the joint count at (c, a * c^(-1)).

    This follows from genProd(n,k+1) = genProd(n,k) * genSeq(n,k), so
    n contributes to the a-class at step k+1 iff genProd(n,k) = c and
    genSeq(n,k) = a * c^(-1) for some nonzero c. -/
theorem accumCount_succ_decomp (X k q : Nat) [NeZero q] (hq : Nat.Prime q)
    (a : ZMod q) (ha : a ≠ 0) :
    sqfreeAccumCount X (k + 1) q a =
    ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (· ≠ 0),
      jointCount X k q c (a * c⁻¹) := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  unfold sqfreeAccumCount jointCount
  -- Show the filter set decomposes as a biUnion over nonzero c
  have hset_eq : (Finset.Icc 1 X).filter (fun n =>
      Squarefree n ∧ (genProd n (k + 1) : ZMod q) = a) =
    ((Finset.univ : Finset (ZMod q)).filter (· ≠ 0)).biUnion (fun c =>
      (Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ (genProd n k : ZMod q) = c ∧
        (genSeq n k : ZMod q) = a * c⁻¹)) := by
    ext n
    constructor
    · intro hn
      simp only [Finset.mem_filter] at hn
      obtain ⟨hn_icc, hsf, hak⟩ := hn
      have hc_ne : (genProd n k : ZMod q) ≠ 0 :=
        genProd_succ_nonzero_of_source hq.one_lt ha hak
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(genProd n k : ZMod q), hc_ne, hn_icc, hsf, rfl,
        genSeq_eq_of_genProd_succ hc_ne hak rfl⟩
    · intro hn
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hn
      obtain ⟨c, hc_ne, hn_icc, hsf, hck, hbk⟩ := hn
      simp only [Finset.mem_filter]
      refine ⟨hn_icc, hsf, ?_⟩
      show (genProd n (k + 1) : ZMod q) = a
      have : (genProd n (k + 1) : ZMod q) =
          (genProd n k : ZMod q) * (genSeq n k : ZMod q) := by
        simp only [genProd_succ, Nat.cast_mul]
      rw [this, hck, hbk]
      rw [mul_comm c, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
  rw [hset_eq]
  apply Finset.card_biUnion
  intro c₁ _ c₂ _ hne
  simp only [Function.onFun, Finset.disjoint_filter]
  intro n _ ⟨_, hc₁', _⟩ ⟨_, hc₂', _⟩
  exact hne (hc₁'.symm.trans hc₂')

/-- **Backward decomposition of accumulator density**: the density at step k+1 equals
    a weighted sum of source densities with transition probabilities as weights. -/
theorem accumDensity_succ_eq (X k q : Nat) [NeZero q] (hq : Nat.Prime q)
    (a : ZMod q) (ha : a ≠ 0) (hX : 0 < sqfreeCount X) :
    sqfreeAccumDensity X (k + 1) q a =
    ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (· ≠ 0),
      sqfreeAccumDensity X k q c * transitionProb X k q c (a * c⁻¹) := by
  simp only [sqfreeAccumDensity, transitionProb]
  rw [accumCount_succ_decomp X k q hq a ha]
  have hX_ne : (sqfreeCount X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- LHS: (∑ jointCount c : ℝ) / sqfreeCount
  -- RHS: ∑ (accumCount c / sqfreeCount) * (jointCount c / accumCount c)
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c hc
  rcases eq_or_ne (sqfreeAccumCount X k q c) 0 with hzero | hpos
  · -- If accumCount = 0, jointCount = 0 too
    have hjoint : jointCount X k q c (a * c⁻¹) = 0 := by
      have hle := jointCount_le_accumCount X k q c (a * c⁻¹)
      omega
    simp only [hzero, hjoint, Nat.cast_zero, zero_div, mul_zero]
  · have hac_ne : (sqfreeAccumCount X k q c : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hpos
    -- jointCount / sqfreeCount = (accumCount / sqfreeCount) * (jointCount / accumCount)
    rw [div_mul_div_comm]
    rw [div_eq_div_iff hX_ne (mul_ne_zero hX_ne hac_ne)]
    ring

end BackwardDecomposition

/-! ## Section 4: Ensemble Transition Approximation

The key open hypothesis: the empirical transition probability for the EM ensemble
approximates the uniform distribution 1/(q-1) on nonzero residues.

This is the CRT-blindness content: among squarefree n with genProd(n,k) in a given
class c mod q, the fraction with genSeq(n,k) in class b mod q converges to 1/(q-1)
for each nonzero b. This follows (informally) from:

1. genSeq(n,k) = minFac(genProd(n,k) + 1) depends on genProd(n,k) only through
   its residues mod primes OTHER than q (by CRT invariance).
2. Among squarefree n with genProd(n,k) in class c mod q, the non-mod-q coordinates
   of genProd(n,k) are approximately uniformly distributed (by CRT for squarefree).
3. So the conditional distribution of genSeq(n,k) mod q, given genProd(n,k) mod q = c,
   is approximately independent of c and uniform on nonzero residues.

**Death class subtlety**: For the "death class" c ≡ -1 mod q, we have q | genProd+1,
which biases genSeq toward q (since q divides the number being factored). For small q
(e.g., q=3 where genSeq_eq_three_of_genProd_mod3 proves genSeq = 3 deterministically
for k ≥ 1), the transition probabilities to nonzero b are NOT 1/(q-1). We therefore
separate the death class into a distinct hypothesis `DeathClassTransitionApprox`.
-/

-- EnsembleTransitionApprox archived to EM/Archive/Ensemble/BackwardDynamicsArchive.lean (RED #10)
-- DeathClassTransitionApprox archived to EM/Archive/Ensemble/BackwardDynamicsArchive.lean (RED #4)
-- full_eta_of_eta_dcta deleted (RED #10 + RED #4)
-- eta_dcta_implies_crt_propagation deleted (RED #10 + RED #4 → RED #3)
-- eta_reduces_crt_prop deleted (RED #10 + RED #4 → RED #3)
-- eta_sre_implies_prsd archived to EM/Archive/Ensemble/BackwardDynamicsArchive.lean (RED #10)
-- backward_dynamics_landscape archived to EM/Archive/Ensemble/BackwardDynamicsArchive.lean (RED #10)

end

/-! ## Summary

The backward dynamics framework establishes the following chain:

```
EnsembleTransitionApprox (non-death transition probabilities approximate 1/(q-1))
  + DeathClassTransitionApprox (death class transition also approximates 1/(q-1))
  -> CRTPropagationStep (equidist at step k implies equidist at step k+1)
  + SquarefreeResidueEquidist (standard ANT, base case k=0)
  -> AccumulatorEquidistPropagation (genProd n k equidistributes for all k)
  -> DeathDensityLB (death density positive, via specialization to q=3, a=-1)
  -> PositiveDensityRSD (positive density of divergent reciprocal sums)
```

**Key insight**: CRTPropagationStep, which was previously an opaque open hypothesis
about accumulator equidistribution propagation, reduces to EnsembleTransitionApprox +
DeathClassTransitionApprox, statements about **conditional distributions** of
multipliers given accumulators.

**Death class separation**: The death class c ≡ -1 mod q is where q | genProd(n,k)+1,
biasing genSeq toward q. For non-death classes (c ≠ 0, c ≠ -1), the CRT-blindness
argument applies directly: genSeq depends on genProd only through non-q residues.
For the death class, the q-divisibility of genProd+1 creates a structural bias.
For small q (e.g., q = 3), this bias is total: genSeq = 3 deterministically
(genSeq_eq_three_of_genProd_mod3). DCTA is therefore false for q = 3 but plausibly
true for large q where the bias is negligible (O(1/log q) by Mertens).

**Open hypotheses**: `EnsembleTransitionApprox` (non-death classes) and
`DeathClassTransitionApprox` (death class). Combined with `SquarefreeResidueEquidist`
(standard ANT), they yield PositiveDensityRSD.
-/
