import EM.Ensemble.PT
import EM.Ensemble.CRTFreedom

/-!
# JSE Base Case: Joint Equidistribution at Steps (0, 1)

This file sets up the JSE base case -- the joint law of `genSeq n 0` and `genSeq n 1`
mod q among squarefree seeds -- via the tower rule.

**Status (2026-11-11).**  The assembly theorems `jse_base_case`,
`jse_base_case_via_per_prime`, `jse_base_case_instance` took as hypothesis the uniform
marginal `JSEMarginalEquidist` (P(genSeq 0 ≡ a mod q) → 1/(q-1)), which is FALSE: it is the
step-`0` instance of `EnsembleMultiplierEquidist` (small-prime domination, Dead End #157;
`HypothesisAudit.not_jseMarginalEquidist`).  They are archived (RED #23,
`EM/Archive/Ensemble/BaseCaseArchive.lean`).  The counting lemmas and the tower-rule
identity below are unconditional and stay live.

## Key Structural Observations

At step j = 0:
- genProd n 0 = n (the starting point)
- genSeq n 0 = minFac(n + 1)

At step k = 1:
- genProd n 1 = n * minFac(n + 1)
- genSeq n 1 = minFac(n * minFac(n + 1) + 1)

The joint density P(genSeq 0 = a, genSeq 1 = b | sqfree) decomposes as
P(genSeq 1 = b | genSeq 0 = a) * P(genSeq 0 = a) via the tower property.

The marginal P(genSeq 0 = a) does NOT tend to 1/(q-1): genSeq n 0 = 2 for every odd seed.

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
* `conditionalSeqCount_sum_eq`         -- partition identity for conditional counts
* `conditionalSeqDensity_nonneg`       -- conditional density >= 0
* `conditionalSeqDensity_le_one`       -- conditional density <= 1

### Open Hypotheses (3)
* `JSEConditionalEquidist`      -- P(genSeq 1 = b | genSeq 0 = a mod q) -> 1/(q-1)
* `PerPrimeConditionalEquidist` -- P(genSeq 1 = b | minFac(n+1) = p) -> 1/(q-1)
* `PerPrimeImpliesMixture`      -- per-prime convergence => mixture convergence

**Warning (2026-11-11).**  The first two are false as stated (argued in their docstrings, not
machine-checked): asking the limit `1/(q-1)` for every `b ≠ 0` forces the class `b = 0`
(`genSeq n 1 = q`) to have conditional density `0`, and it has positive density.  They are
kept, flagged, because a short Lean refutation is not available.
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

    **Status**: open hypothesis (standard ANT: CRT + population equidist).

    **WARNING (2026-11-11, review close-out): false as stated; not machine-checked.**
    The limit is asked for every `b ≠ 0`, and the `q - 1` limits `1/(q-1)` add up to `1`.
    Since the joint counts over *all* `b : ZMod q` add up to the marginal count, the
    hypothesis forces the class `b = 0` — the seeds with `genSeq n 1 = q` — to have conditional
    density `0`.  It does not: `q ∣ n · genSeq n 0 + 1` on a positive proportion of seeds.
    Concretely at `q = 3`, `a = 2`: every odd squarefree `n` has `genSeq n 0 = 2`, and those
    with `n ≡ 1 (mod 3)` have `2n + 1` odd and divisible by `3`, so `genSeq n 1 = 3`.
    Squarefree `n ≡ 1 (mod 6)` have natural density `3/(2π²) ≈ 0.152`, and the denominator is
    at most the squarefree count, of density `6/π² ≈ 0.608`; so the class `b = 0` keeps
    conditional mass at least `1/4`, and the classes `b = 1, 2` cannot both tend to `1/2`.
    (This is the head-domination phenomenon at step `1`; independently of the `b = 0` mass,
    there is no reason for the nonzero classes to be balanced, e.g. at `q = 5`, `a = 2` the
    class `b = 3` contains all odd squarefree `n ≡ 1 (mod 3)`, and the even squarefree
    `n ≡ 2 (mod 3)` have `genSeq n 0 = 3` and are outside the conditioning class, which gives
    conditional density at least `(1/4)/(7/8) = 2/7 > 1/4`.)
    A Lean refutation needs a positive lower density for squarefree numbers in a residue class
    (`n ≡ 1 mod 6`), which is not in the repository (`odd_sf_card_ge_half` handles only the
    class of odd numbers); it was judged not short and is left for a later pass, so the
    hypothesis is *not* archived.  Its only live consumer is the bridge
    `PerPrimeImpliesMixture`; `jse_base_case*` are already archived (RED #23).  Do not build
    on it. -/
def JSEConditionalEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a b : ZMod q), a ≠ 0 → b ≠ 0 →
    Filter.Tendsto
      (fun X : Nat =>
        (sqfreeJointSeqCount X 0 1 q a b : ℝ) /
        (sqfreeSeqCount X 0 q a : ℝ))
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1)))

-- JSEMarginalEquidist: this is the step-`0` instance of `EnsembleMultiplierEquidist`, false by
-- small-prime domination (odd squarefree seeds, at least half of all, have `genSeq n 0 = 2`):
-- `HypothesisAudit.not_jseMarginalEquidist` (review 2026-11-10 row H12, RED #23).  Its
-- definition now lives next to that refutation in EM/Meta/HypothesisAudit.lean.

end ANTAxioms

/-! ## JSE Base Case Assembly -/

section JSEBaseCase

-- jse_base_case archived to EM/Archive/Ensemble/BaseCaseArchive.lean (RED #23)

/-- **Per-prime conditional equidistribution.**

    For each fixed prime p (distinct from q), the conditional density of
    genSeq n 1 = b mod q given minFac(n+1) = p tends to 1/(q-1).

    **Status**: open hypothesis (standard ANT).

    **WARNING (2026-11-11): false as stated, for the same reason as
    `JSEConditionalEquidist`; not machine-checked.**  By `conditionalSeqCount_sum_eq` the
    conditional densities over all `b : ZMod q` add up to `1`, so asking for `1/(q-1)` at every
    `b ≠ 0` forces the class `b = 0` (`genSeq n 1 = q`) to have conditional density `0`; at
    `p = 2`, `q = 3` that class contains every odd squarefree `n ≡ 1 (mod 3)`, conditional
    density `3/8`.  A correct statement would exclude the seeds with `q ∣ n p + 1` and would
    still have to account for head domination among the remaining classes. -/
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

    **Status**: open hypothesis (requires mixture convergence / tail bounds).

    Note (2026-11-11): both sides are false as stated (see the warnings on
    `PerPrimeConditionalEquidist` and `JSEConditionalEquidist`), so this bridge is expected to
    be vacuously true; neither falsity is machine-checked. -/
def PerPrimeImpliesMixture : Prop :=
  PerPrimeConditionalEquidist → JSEConditionalEquidist

-- jse_base_case_via_per_prime archived to EM/Archive/Ensemble/BaseCaseArchive.lean (RED #23)
-- jse_base_case_instance archived to EM/Archive/Ensemble/BaseCaseArchive.lean (RED #23)

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

### Definitions (5)
* `MinFacConditionCount`         -- count of sqfree n with minFac(n+1) = p
* `ConditionalSeqCount`         -- count with minFac(n+1) = p AND genSeq n 1 = b mod q
* `JSEConditionalEquidist`      -- conditional equidist of genSeq 1 given genSeq 0 (open)
* `PerPrimeConditionalEquidist` -- per-prime conditional equidist (open)
* `PerPrimeImpliesMixture`      -- mixture convergence bridge (open)

### Proved Theorems (14)
* `genProd_zero_eq`                                  -- genProd n 0 = n
* `genSeq_zero_eq_minFac`                            -- genSeq n 0 = minFac(n+1)
* `genProd_one_eq`                                   -- genProd n 1 = n * minFac(n+1)
* `genSeq_one_eq`                                    -- genSeq n 1 = minFac(n*minFac(n+1)+1)
* `minFacConditionCount_le`                          -- condition count <= sqfreeCount
* `conditionalSeqCount_le`                           -- conditional count <= condition count
* `conditionalSeqCount_le_sqfreeCount`               -- conditional count <= sqfreeCount
* `sqfreeJointSeqCount_le_seqCount_first`            -- joint <= marginal at step 0
* `joint_seq_density_eq_conditional_mul_marginal`    -- P(A,B) = P(A|B) * P(B)
* `conditionalSeqCount_sum_eq`                       -- partition identity for conditional counts
* `conditionalSeqDensity_nonneg`                     -- conditional density >= 0
* `conditionalSeqDensity_le_one`                     -- conditional density <= 1
* `jse_base_density_nonneg`                          -- joint density >= 0
* `jse_base_density_le_one`                          -- joint density <= 1

### Open Hypotheses (3) — all flagged 2026-11-11, see the warnings in their docstrings
* `JSEConditionalEquidist`      -- P(genSeq 1 = b | genSeq 0 = a mod q) -> 1/(q-1); FALSE as
                                   stated (the class `b = 0` has positive conditional density);
                                   argued, not machine-checked
* `PerPrimeConditionalEquidist` -- P(genSeq 1 = b | minFac(n+1) = p) -> 1/(q-1) for p != q;
                                   FALSE as stated, same reason
* `PerPrimeImpliesMixture`      -- per-prime convergence => mixture convergence (then vacuous)

### Archived (RED #23, 2026-11-11)
`JSEMarginalEquidist` (false; definition and refutation in `EM/Meta/HypothesisAudit.lean`) and
its consumers `jse_base_case`, `jse_base_case_via_per_prime`, `jse_base_case_instance`
(`EM/Archive/Ensemble/BaseCaseArchive.lean`).
-/

end
