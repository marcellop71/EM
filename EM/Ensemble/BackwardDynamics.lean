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
* `EnsembleTransitionApprox`      -- open hypothesis: transitions approximate 1/(q-1)

### Proved Theorems
* `jointCount_le_accumCount`      -- joint count bounded by accumulator count
* `jointCount_sum_eq_accumCount`  -- partition identity: sum over multiplier classes
* `transitionProb_nonneg`         -- transition probability is non-negative
* `transitionProb_le_one`         -- transition probability is at most 1
* `transitionProb_sum_one`        -- transition probabilities sum to 1
* `accumCount_succ_decomp`        -- backward decomposition of accumulator count
* `accumDensity_succ_eq`          -- backward decomposition of accumulator density
* `eta_implies_crt_propagation`   -- ETA -> CRTPropagationStep
* `eta_sre_implies_prsd`          -- ETA + SRE -> PositiveDensityRSD
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
-/

section EnsembleTransition

/-- **EnsembleTransitionApprox**: the empirical transition probability for the EM ensemble
    approximates the uniform distribution 1/(q-1) on nonzero residues.

    This says: for each prime q, step k, nonzero accumulator class c, and nonzero
    multiplier class b, the fraction of squarefree n with genProd(n,k) = c that have
    genSeq(n,k) = b converges to 1/(q-1) as X -> infinity.

    **Status**: open hypothesis (the key content of backward dynamics). -/
def EnsembleTransitionApprox : Prop :=
  ∀ (q : Nat), Nat.Prime q → ∀ (k : Nat),
    ∀ (c : ZMod q), c ≠ 0 →
    ∀ (b : ZMod q), b ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => transitionProb X k q c b)
        Filter.atTop
        (nhds (1 / ((q : ℝ) - 1)))

/-- **EnsembleTransitionApprox implies CRTPropagationStep**.

    If the transition probabilities all converge to 1/(q-1), and the density at step k
    converges to 1/(q-1) for all nonzero classes (IH), then the density at step k+1
    also converges to 1/(q-1).

    The argument: by the backward decomposition,
      F_{k+1}(a) = sum_c F_k(c) * T(c, a*c^(-1))
    where F_k(c) -> 1/(q-1) (IH) and T(c, b) -> 1/(q-1) (ETA). The product converges
    to (1/(q-1))^2, and summing over q-1 nonzero terms c gives
    (q-1) * (1/(q-1))^2 = 1/(q-1). -/
theorem eta_implies_crt_propagation :
    EnsembleTransitionApprox → CRTPropagationStep := by
  intro heta r hr k hih a ha
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  -- We need: sqfreeAccumDensity X (k+1) r a -> 1/(r-1)
  -- Strategy: decompose via accumDensity_succ_eq, then use limit arithmetic
  -- The target limit is 1/(r-1)
  set L := (1 : ℝ) / ((r : ℝ) - 1) with hL_def
  have hr_pos : (0 : ℝ) < (r : ℝ) - 1 := by
    have h2 := hr.two_le
    have : (2 : ℝ) ≤ (r : ℝ) := Nat.ofNat_le_cast.mpr h2
    linarith
  -- Step 1: for each nonzero c, F_k(c) * T(c, a*c^{-1}) -> L * L = L^2
  have hterm : ∀ c : ZMod r, c ≠ 0 →
      Filter.Tendsto
        (fun X => sqfreeAccumDensity X k r c * transitionProb X k r c (a * c⁻¹))
        Filter.atTop (nhds (L * L)) := by
    intro c hc
    have hacne : a * c⁻¹ ≠ 0 := by
      -- In ZMod r with r prime (hence a field), products of nonzero elements are nonzero
      exact mul_ne_zero ha (by rwa [ne_eq, inv_eq_zero])
    exact Filter.Tendsto.mul (hih c hc) (heta r hr k c hc (a * c⁻¹) hacne)
  -- Step 2: the total sum -> sum of L^2 over nonzero c = (r-1) * L^2 = L
  have hsum_limit :
      Filter.Tendsto
        (fun X => ∑ c ∈ (Finset.univ : Finset (ZMod r)).filter (· ≠ 0),
          sqfreeAccumDensity X k r c * transitionProb X k r c (a * c⁻¹))
        Filter.atTop (nhds (∑ _ ∈ (Finset.univ : Finset (ZMod r)).filter (· ≠ 0), L * L)) := by
    apply tendsto_finset_sum
    intro c hc
    simp only [Finset.mem_filter] at hc
    exact hterm c hc.2
  -- Step 3: compute the constant sum
  have hcard : ((Finset.univ : Finset (ZMod r)).filter (· ≠ 0)).card = r - 1 := by
    rw [Finset.filter_ne' Finset.univ 0, Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  have hconst_sum :
      ∑ _ ∈ (Finset.univ : Finset (ZMod r)).filter (· ≠ 0), L * L = L := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    simp only [hL_def]
    have hr1 : (r : ℝ) - 1 ≠ 0 := ne_of_gt hr_pos
    have hr_cast : (↑(r - 1) : ℝ) = (r : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hr.ne_zero)
    rw [hr_cast]
    field_simp
  rw [hconst_sum] at hsum_limit
  -- Step 4: connect the actual function to the decomposed sum for large X
  rw [show L = 1 / ((r : ℝ) - 1) from rfl]
  apply Filter.Tendsto.congr' _ hsum_limit
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.Ici 1, Filter.Ici_mem_atTop 1, ?_⟩
  intro X hX
  simp only [Set.mem_Ici] at hX
  have hsfpos : 0 < sqfreeCount X := by
    unfold sqfreeCount
    exact Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_refl _, hX⟩, squarefree_one⟩⟩
  exact (accumDensity_succ_eq X k r hr a ha hsfpos).symm

end EnsembleTransition

/-! ## Section 5: Master Chain

Combining the backward dynamics reduction with existing infrastructure to
reach PositiveDensityRSD from ETA + SRE.
-/

section MasterChain

/-- **Master chain**: ETA + SRE -> PositiveDensityRSD.

    Combines:
    1. eta_implies_crt_propagation (this file): ETA -> CRTPropagationStep
    2. sre_crt_implies_accum_equidist (CRT.lean): SRE + CRTPropStep -> AEP
    3. AEP specialized to q=3, a=-1 gives DeathDensityLB(3, 1/4)
    4. death_density_implies_prsd (CRT.lean): DeathDensityLB -> PRSD -/
theorem eta_sre_implies_prsd :
    EnsembleTransitionApprox → SquarefreeResidueEquidist → PositiveDensityRSD := by
  intro heta hsre
  have hcrt := eta_implies_crt_propagation heta
  have haep := sre_crt_implies_accum_equidist hsre hcrt
  -- AEP gives: for all primes q, all k, all a != 0: density -> 1/(q-1)
  -- In particular, for q = 3, a = -1 (= 2 mod 3), density -> 1/2
  -- So DeathDensityLB(3, 1/4) holds (eventually >= 1/4 < 1/2)
  have hp3 : Nat.Prime 3 := by decide
  have hdd : DeathDensityLB 3 (1/4) := by
    intro k
    have h := haep 3 hp3 k (-1 : ZMod 3) (by decide)
    -- h : Tendsto (fun X => sqfreeAccumDensity X k 3 (-1)) atTop (nhds (1/((3:R)-1)))
    have h12 : (1 : ℝ) / ((↑(3 : ℕ) : ℝ) - 1) = 1 / 2 := by norm_num
    rw [h12] at h
    -- Use that nhds(1/2) contains the interval (1/4, 3/4), so eventually density > 1/4
    have hev : ∀ᶠ X in Filter.atTop, (1 : ℝ) / 4 < sqfreeAccumDensity X k 3 (-1) := by
      exact h.eventually (Ioi_mem_nhds (by norm_num : (1:ℝ)/4 < 1/2))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨X₀, hX₀⟩ := hev
    exact ⟨X₀, fun X hX => le_of_lt (hX₀ X hX)⟩
  exact death_density_implies_prsd hp3 (by norm_num) (by norm_num) hdd

/-- **ETA alone implies CRTPropagationStep**: this is the key new reduction.
    CRTPropagationStep was previously an opaque open hypothesis; now it is
    reducible to EnsembleTransitionApprox, which is a more natural and
    potentially more tractable statement about conditional distributions. -/
theorem eta_reduces_crt_prop :
    EnsembleTransitionApprox → CRTPropagationStep :=
  eta_implies_crt_propagation

end MasterChain

/-! ## Section 6: Landscape Theorem -/

section Landscape

/-- **Backward dynamics landscape**: summary of all routes and their dependencies.

    This captures the main contributions of the backward dynamics framework:
    1. ETA + SRE -> PositiveDensityRSD (new master chain)
    2. ETA -> CRTPropagationStep (key new reduction)
    3. LMG alone -> PositiveDensityRSD (existing, for comparison)
    4. The transition probabilities satisfy basic probability axioms -/
theorem backward_dynamics_landscape :
    -- Route 1: ETA + SRE -> PositiveDensityRSD
    (EnsembleTransitionApprox → SquarefreeResidueEquidist → PositiveDensityRSD) ∧
    -- Route 2: ETA -> CRTPropagationStep (proved reduction)
    (EnsembleTransitionApprox → CRTPropagationStep) ∧
    -- Route 3: LMG alone -> PositiveDensityRSD (proved in ReciprocalSum.lean)
    (LinearMeanGrowth → PositiveDensityRSD) ∧
    -- Route 4: joint count bounds accumulator count
    (∀ (X k q : Nat) (c b : ZMod q),
      jointCount X k q c b ≤ sqfreeAccumCount X k q c) :=
  ⟨eta_sre_implies_prsd,
   eta_implies_crt_propagation,
   lmg_implies_positive_density_rsd,
   fun X k q c b => jointCount_le_accumCount X k q c b⟩

end Landscape

end

/-! ## Summary

The backward dynamics framework establishes the following chain:

```
EnsembleTransitionApprox (transition probabilities approximate 1/(q-1))
  -> CRTPropagationStep (equidist at step k implies equidist at step k+1)
  + SquarefreeResidueEquidist (standard ANT, base case k=0)
  -> AccumulatorEquidistPropagation (genProd n k equidistributes for all k)
  -> DeathDensityLB (death density positive, via specialization to q=3, a=-1)
  -> PositiveDensityRSD (positive density of divergent reciprocal sums)
```

**Key insight**: CRTPropagationStep, which was previously an opaque open hypothesis
about accumulator equidistribution propagation, reduces to EnsembleTransitionApprox,
a statement about **conditional distributions** of multipliers given accumulators.
This is a more natural formulation of the "CRT blindness" principle: the multiplier
genSeq(n,k) = minFac(genProd(n,k)+1) depends on genProd(n,k) only through its
residues mod primes OTHER than q, so conditioning on genProd(n,k) mod q should not
affect the distribution of genSeq(n,k) mod q.

**Open hypotheses**: `EnsembleTransitionApprox` is the sole new open hypothesis.
Combined with `SquarefreeResidueEquidist` (standard ANT), it yields PositiveDensityRSD.
-/
