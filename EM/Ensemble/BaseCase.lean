import EM.Ensemble.PT
import EM.Ensemble.CRTFreedom

/-!
# JSE Base Case: Joint Equidistribution at Steps (0, 1)

This file proves the JSE base case -- that `genSeq n 0` and `genSeq n 1` are
jointly equidistributed mod q among nonzero residue classes -- under standard
analytic number theory axioms.

## Key Structural Observations

At step j = 0:
- genProd n 0 = n (the starting point)
- genSeq n 0 = minFac(n + 1)

At step k = 1:
- genProd n 1 = n * minFac(n + 1)
- genSeq n 1 = minFac(n * minFac(n + 1) + 1)

The joint density P(genSeq 0 = a, genSeq 1 = b | sqfree) decomposes as
P(genSeq 1 = b | genSeq 0 = a) * P(genSeq 0 = a) via the tower property.

The marginal P(genSeq 0 = a) -> 1/(q-1) is standard (squarefree equidistribution).

The conditional P(genSeq 1 = b | genSeq 0 = a mod q) -> 1/(q-1) is the key
independence statement: knowing genSeq n 0 mod q does not bias genSeq n 1 mod q.

## Main Results

### Proved Theorems
* `genSeq_zero_eq_minFac`              -- genSeq n 0 = minFac(n + 1)
* `genProd_zero_eq`                    -- genProd n 0 = n
* `genProd_one_eq`                     -- genProd n 1 = n * minFac(n + 1)
* `genSeq_one_eq`                      -- genSeq n 1 = minFac(n * minFac(n+1) + 1)
* `minFacConditionCount_le`            -- condition count <= sqfreeCount
* `conditionalSeqCount_le`             -- conditional count <= condition count
* `conditionalSeqCount_le_sqfreeCount` -- conditional count <= sqfreeCount
* `sqfreeJointSeqCount_le_seqCount_first` -- joint <= marginal at step 0
* `joint_seq_density_eq_conditional_mul_marginal` -- P(A,B) = P(A|B) * P(B)
* `jse_base_case`                      -- JSE(0,1) from conditional + marginal (PROVED)
* `jse_base_case_via_per_prime`        -- JSE(0,1) via per-prime route (PROVED)
* `jse_base_case_instance`             -- JSE(0,1) instance form (PROVED)
* `conditionalSeqCount_sum_eq`         -- partition identity for conditional counts
* `conditionalSeqDensity_nonneg`       -- conditional density >= 0
* `conditionalSeqDensity_le_one`       -- conditional density <= 1

### Open Hypotheses (4)
* `JSEConditionalEquidist`      -- P(genSeq 1 = b | genSeq 0 = a mod q) -> 1/(q-1)
* `JSEMarginalEquidist`         -- P(genSeq 0 = a mod q) -> 1/(q-1)
* `PerPrimeConditionalEquidist` -- P(genSeq 1 = b | minFac(n+1) = p) -> 1/(q-1)
* `PerPrimeImpliesMixture`      -- per-prime convergence => mixture convergence
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Structural Lemmas for genProd and genSeq at Small Steps -/

section SmallSteps

/-- genProd n 0 = n (trivial unfolding of the definition). -/
@[simp] theorem genProd_zero_eq (n : Nat) : genProd n 0 = n := rfl

/-- genSeq n 0 = Nat.minFac (n + 1). This is the trivial unfolding
    of the genSeq definition at step 0. -/
@[simp] theorem genSeq_zero_eq_minFac (n : Nat) : genSeq n 0 = Nat.minFac (n + 1) := rfl

/-- genProd n 1 = n * Nat.minFac (n + 1). -/
@[simp] theorem genProd_one_eq (n : Nat) :
    genProd n 1 = n * Nat.minFac (n + 1) := rfl

/-- genSeq n 1 = Nat.minFac (n * Nat.minFac (n + 1) + 1). -/
@[simp] theorem genSeq_one_eq (n : Nat) :
    genSeq n 1 = Nat.minFac (n * Nat.minFac (n + 1) + 1) := rfl

end SmallSteps

/-! ## Conditional Counting Functions -/

section ConditionalCounting

/-- Count of squarefree n in [1,X] with minFac(n+1) = p.
    This is the set of starting points whose first generalized EM prime
    is exactly p. -/
def MinFacConditionCount (X p : Nat) : Nat :=
  ((Finset.Icc 1 X).filter (fun n =>
    Squarefree n ∧ Nat.minFac (n + 1) = p)).card

/-- Count of squarefree n in [1,X] with minFac(n+1) = p AND
    genSeq n 1 in residue class b mod q. -/
def ConditionalSeqCount (X p q : Nat) (b : ZMod q) : Nat :=
  ((Finset.Icc 1 X).filter (fun n =>
    Squarefree n ∧ Nat.minFac (n + 1) = p ∧ (genSeq n 1 : ZMod q) = b)).card

/-- The condition count is bounded by the total squarefree count. -/
theorem minFacConditionCount_le (X p : Nat) :
    MinFacConditionCount X p ≤ sqfreeCount X := by
  apply Finset.card_le_card
    (Finset.monotone_filter_right _ fun _ _ h => h.1)

/-- The conditional count is bounded by the condition count. -/
theorem conditionalSeqCount_le (X p q : Nat) (b : ZMod q) :
    ConditionalSeqCount X p q b ≤ MinFacConditionCount X p := by
  apply Finset.card_le_card
    (Finset.monotone_filter_right _ fun _ _ h => ⟨h.1, h.2.1⟩)

/-- The conditional count is bounded by the sqfreeCount. -/
theorem conditionalSeqCount_le_sqfreeCount (X p q : Nat) (b : ZMod q) :
    ConditionalSeqCount X p q b ≤ sqfreeCount X :=
  le_trans (conditionalSeqCount_le X p q b) (minFacConditionCount_le X p)

end ConditionalCounting

/-! ## Bound: Joint Count at Most Marginal -/

section JointBound

/-- The joint count at (0,1) is bounded by the marginal at step 0. -/
theorem sqfreeJointSeqCount_le_seqCount_first (X q : Nat) (a b : ZMod q) :
    sqfreeJointSeqCount X 0 1 q a b ≤ sqfreeSeqCount X 0 q a := by
  apply Finset.card_le_card
    (Finset.monotone_filter_right _ fun _ _ h => ⟨h.1, h.2.1⟩)

end JointBound

/-! ## Algebraic Factorization of Densities -/

section DensityFactorization

/-- **Algebraic identity**: the joint density equals the conditional density
    times the marginal density.

    sqfreeJointSeqDensity X 0 1 q a b =
    (sqfreeJointSeqCount / sqfreeSeqCount) * sqfreeSeqDensity X 0 q a

    This is the tower rule P(A,B) = P(A|B) * P(B) at the finite level. -/
theorem joint_seq_density_eq_conditional_mul_marginal (X q : Nat) [NeZero q]
    (a b : ZMod q) :
    sqfreeJointSeqDensity X 0 1 q a b =
    ((sqfreeJointSeqCount X 0 1 q a b : ℝ) /
      (sqfreeSeqCount X 0 q a : ℝ)) *
    sqfreeSeqDensity X 0 q a := by
  unfold sqfreeJointSeqDensity sqfreeSeqDensity
  by_cases h : (sqfreeSeqCount X 0 q a : ℝ) = 0
  · -- If marginal count = 0, joint count = 0 too
    have hseq_zero : sqfreeSeqCount X 0 q a = 0 := by exact_mod_cast h
    have hjoint_zero : sqfreeJointSeqCount X 0 1 q a b = 0 := by
      have := sqfreeJointSeqCount_le_seqCount_first X q a b; omega
    simp [hjoint_zero, hseq_zero]
  · -- joint/total = (joint * seq) / (seq * total) = (joint/seq) * (seq/total)
    rw [div_mul_div_comm, mul_comm (sqfreeJointSeqCount X 0 1 q a b : ℝ),
        mul_div_mul_left _ _ h]

end DensityFactorization

/-! ## Open Hypotheses (Standard ANT Axioms) -/

section ANTAxioms

/-- **JSE conditional equidistribution**: the conditional density of
    genSeq n 1 = b mod q given genSeq n 0 = a mod q among squarefree n
    tends to 1/(q-1).

    This is the key independence statement: knowing genSeq n 0 mod q does
    not bias genSeq n 1 mod q.

    **Status**: open hypothesis (standard ANT: CRT + population equidist). -/
def JSEConditionalEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a b : ZMod q), a ≠ 0 → b ≠ 0 →
    Filter.Tendsto
      (fun X : Nat =>
        (sqfreeJointSeqCount X 0 1 q a b : ℝ) /
        (sqfreeSeqCount X 0 q a : ℝ))
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1)))

/-- **Marginal equidistribution of genSeq n 0 mod q**: the density of
    squarefree n with genSeq n 0 = a mod q (nonzero) tends to 1/(q-1).

    **Status**: open hypothesis (follows from SquarefreeResidueEquidist + PE). -/
def JSEMarginalEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a : ZMod q), a ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeSeqDensity X 0 q a)
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1)))

end ANTAxioms

/-! ## JSE Base Case Assembly -/

section JSEBaseCase

/-- **JSE at (j=0, k=1)** from conditional + marginal equidistribution.

    The joint density decomposes as (conditional density) * (marginal density)
    by the tower rule. Under JSEConditionalEquidist, the conditional density
    -> 1/(q-1). Under JSEMarginalEquidist, the marginal density -> 1/(q-1).
    Their product -> 1/(q-1)^2, which is the JSE target.

    **Status**: PROVED (from JSEConditionalEquidist + JSEMarginalEquidist). -/
theorem jse_base_case
    (hcond : JSEConditionalEquidist)
    (hmarg : JSEMarginalEquidist)
    (q : Nat) (hq : Nat.Prime q)
    (a b : ZMod q) (ha : a ≠ 0) (hb : b ≠ 0) :
    Filter.Tendsto
      (fun X : Nat => sqfreeJointSeqDensity X 0 1 q a b)
      Filter.atTop
      (nhds (1 / (((q : ℝ) - 1) ^ 2))) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- Step 1: Rewrite the target as a product 1/(q-1) * 1/(q-1)
  rw [show (1 : ℝ) / ((q : ℝ) - 1) ^ 2 = 1 / ((q : ℝ) - 1) * (1 / ((q : ℝ) - 1))
    from by rw [sq, one_div_mul_one_div_rev]]
  -- Step 2: Rewrite joint density as conditional * marginal, then apply Tendsto.mul
  exact (Filter.Tendsto.congr
    (fun X => (joint_seq_density_eq_conditional_mul_marginal X q a b).symm)
    (Filter.Tendsto.mul (hcond q hq a b ha hb) (hmarg q hq a ha)))

/-- **Per-prime conditional equidistribution.**

    For each fixed prime p (distinct from q), the conditional density of
    genSeq n 1 = b mod q given minFac(n+1) = p tends to 1/(q-1).

    **Status**: open hypothesis (standard ANT). -/
def PerPrimeConditionalEquidist : Prop :=
  ∀ (p q : Nat), Nat.Prime p → Nat.Prime q → p ≠ q →
  ∀ (b : ZMod q), b ≠ 0 →
    Filter.Tendsto
      (fun X : Nat =>
        (ConditionalSeqCount X p q b : ℝ) /
        (MinFacConditionCount X p : ℝ))
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1)))

/-- **JSEConditionalEquidist follows from PerPrimeConditionalEquidist.**

    If the conditional density converges for each conditioning prime p
    separately, then the mixture (conditioning on genSeq 0 = a mod q)
    also converges.

    **Status**: open hypothesis (requires mixture convergence / tail bounds). -/
def PerPrimeImpliesMixture : Prop :=
  PerPrimeConditionalEquidist → JSEConditionalEquidist

/-- **JSE(0,1) via the per-prime route**: composes per-prime convergence with
    mixture bridge and marginal equidistribution.

    **Status**: PROVED (from the three open hypotheses). -/
theorem jse_base_case_via_per_prime
    (hpp : PerPrimeConditionalEquidist)
    (hmix : PerPrimeImpliesMixture)
    (hmarg : JSEMarginalEquidist)
    (q : Nat) (hq : Nat.Prime q)
    (a b : ZMod q) (ha : a ≠ 0) (hb : b ≠ 0) :
    Filter.Tendsto
      (fun X : Nat => sqfreeJointSeqDensity X 0 1 q a b)
      Filter.atTop
      (nhds (1 / (((q : ℝ) - 1) ^ 2))) :=
  jse_base_case (hmix hpp) hmarg q hq a b ha hb

/-- **Partial JSE**: the JSE base case gives JSE at (0, 1) specifically.

    **Status**: PROVED. -/
theorem jse_base_case_instance
    (hcond : JSEConditionalEquidist)
    (hmarg : JSEMarginalEquidist) :
    ∀ (q : Nat), Nat.Prime q →
    ∀ (a b : ZMod q), a ≠ 0 → b ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => sqfreeJointSeqDensity X 0 1 q a b)
        Filter.atTop
        (nhds (1 / (((q : ℝ) - 1) ^ 2))) :=
  jse_base_case hcond hmarg

end JSEBaseCase

/-! ## Additional Structural Results -/

section StructuralResults

/-- **Partition identity for the conditional count**: summing ConditionalSeqCount
    over all residue classes b mod q gives MinFacConditionCount. -/
theorem conditionalSeqCount_sum_eq (X p q : Nat) [NeZero q] :
    ∑ b : ZMod q, ConditionalSeqCount X p q b = MinFacConditionCount X p := by
  unfold ConditionalSeqCount MinFacConditionCount
  -- Rewrite the 3-way conjunction filter as a nested filter
  have hterm : ∀ b : ZMod q,
      ((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ Nat.minFac (n + 1) = p ∧ (genSeq n 1 : ZMod q) = b)).card =
      (((Finset.Icc 1 X).filter (fun n =>
        Squarefree n ∧ Nat.minFac (n + 1) = p)).filter
        (fun n => (genSeq n 1 : ZMod q) = b)).card := by
    intro b; congr 1; ext n; simp only [Finset.mem_filter, and_assoc]
  simp_rw [hterm]
  -- Apply the fiber decomposition: #S = ∑ b, #{n ∈ S | f(n) = b}
  exact (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm

/-- **Conditional density nonneg**: ConditionalSeqCount / MinFacConditionCount >= 0. -/
theorem conditionalSeqDensity_nonneg (X p q : Nat) (b : ZMod q) :
    (0 : ℝ) ≤ (ConditionalSeqCount X p q b : ℝ) / (MinFacConditionCount X p : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Conditional density at most 1**: ConditionalSeqCount / MinFacConditionCount <= 1. -/
theorem conditionalSeqDensity_le_one (X p q : Nat) (b : ZMod q) :
    (ConditionalSeqCount X p q b : ℝ) / (MinFacConditionCount X p : ℝ) ≤ 1 := by
  by_cases h : MinFacConditionCount X p = 0
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (conditionalSeqCount_le X p q b))

/-- The joint density at step (0, 1) is nonneg. -/
theorem jse_base_density_nonneg (X q : Nat) (a b : ZMod q) :
    0 ≤ sqfreeJointSeqDensity X 0 1 q a b :=
  sqfreeJointSeqDensity_nonneg X 0 1 q a b

/-- The joint density at step (0, 1) is at most 1. -/
theorem jse_base_density_le_one (X q : Nat) (a b : ZMod q) :
    sqfreeJointSeqDensity X 0 1 q a b ≤ 1 :=
  sqfreeJointSeqDensity_le_one X 0 1 q a b

end StructuralResults

/-! ## Summary

### Definitions (6)
* `MinFacConditionCount`         -- count of sqfree n with minFac(n+1) = p
* `ConditionalSeqCount`         -- count with minFac(n+1) = p AND genSeq n 1 = b mod q
* `JSEConditionalEquidist`      -- conditional equidist of genSeq 1 given genSeq 0 (open)
* `JSEMarginalEquidist`         -- marginal equidist of genSeq 0 mod q (open)
* `PerPrimeConditionalEquidist` -- per-prime conditional equidist (open)
* `PerPrimeImpliesMixture`      -- mixture convergence bridge (open)

### Proved Theorems (17)
* `genProd_zero_eq`                                  -- genProd n 0 = n
* `genSeq_zero_eq_minFac`                            -- genSeq n 0 = minFac(n+1)
* `genProd_one_eq`                                   -- genProd n 1 = n * minFac(n+1)
* `genSeq_one_eq`                                    -- genSeq n 1 = minFac(n*minFac(n+1)+1)
* `minFacConditionCount_le`                          -- condition count <= sqfreeCount
* `conditionalSeqCount_le`                           -- conditional count <= condition count
* `conditionalSeqCount_le_sqfreeCount`               -- conditional count <= sqfreeCount
* `sqfreeJointSeqCount_le_seqCount_first`            -- joint <= marginal at step 0
* `joint_seq_density_eq_conditional_mul_marginal`    -- P(A,B) = P(A|B) * P(B)
* `jse_base_case`                                    -- JSE(0,1) from conditional + marginal (PROVED)
* `jse_base_case_via_per_prime`                      -- JSE(0,1) via per-prime route (PROVED)
* `jse_base_case_instance`                           -- JSE(0,1) instance form (PROVED)
* `conditionalSeqCount_sum_eq`                       -- partition identity for conditional counts
* `conditionalSeqDensity_nonneg`                     -- conditional density >= 0
* `conditionalSeqDensity_le_one`                     -- conditional density <= 1
* `jse_base_density_nonneg`                          -- joint density >= 0
* `jse_base_density_le_one`                          -- joint density <= 1

### Open Hypotheses (4)
* `JSEConditionalEquidist`      -- P(genSeq 1 = b | genSeq 0 = a mod q) -> 1/(q-1)
* `JSEMarginalEquidist`         -- P(genSeq 0 = a mod q) -> 1/(q-1)
* `PerPrimeConditionalEquidist` -- P(genSeq 1 = b | minFac(n+1) = p) -> 1/(q-1) for p != q
* `PerPrimeImpliesMixture`      -- per-prime convergence => mixture convergence

### Proof Architecture
```
Route 1 (direct):
  JSEConditionalEquidist + JSEMarginalEquidist -> JSE(0,1)
  [jse_base_case, PROVED: tower rule P(A,B) = P(A|B)*P(B) + Tendsto.mul]

Route 2 (via per-prime):
  PerPrimeConditionalEquidist + PerPrimeImpliesMixture -> JSEConditionalEquidist
  JSEConditionalEquidist + JSEMarginalEquidist -> JSE(0,1)
  [jse_base_case_via_per_prime, PROVED: composition of Route 1 with mixture bridge]
```
-/

end
