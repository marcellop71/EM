import EM.ShiftedSquarefreeDensity
import EM.PopulationEquidistProof
import EM.AbelChain
import EM.MasterReduction
import EM.EnsembleStructure

/-!
# Alladi Density: From WeightedPNTinAP to MinFacResidueEquidist

This file defines intermediate hypotheses and proves reductions connecting
`PrimesEquidistributedInAP` (output of the proved ANT chain in AbelChain.lean)
to `MinFacResidueEquidist` (input to `pe_of_equidist` in PopulationEquidistProof.lean).

## The Chain

```
WeightedPNTinAP                      (external hypothesis = Wiener-Ikehara)
  | [PROVED: wpnt_implies_primes_equidist_proved]
  v
PrimesEquidistributedInAP            (proved output of ANT chain)
  | [OPEN: PrimesEquidistImpliesRoughLPF]
  v
RoughLPFEquidist                   (minFac equidist mod q among q-rough integers)
  | [OPEN: RoughLPFImpliesMFRE]
  v
MinFacResidueEquidist                (minFac equidist mod q among q-rough shifted squarefree)
  | [PROVED: pe_of_equidist]
  v
PopulationEquidist                   (PE)
  | [OPEN: DeterministicStabilityLemma or DSLHitting]
  v
MullinConjecture
```

## Mathematical Content of the Open Hypotheses

**PrimesEquidistImpliesRoughLPF**: Alladi's density formula + weight-independence.
Among q-rough integers, the density of {m : minFac(m) = p} is
  (1/p) * prod_{q < r < p} (1 - 1/r)
This weight depends on p only through |p|, not through p mod q. By
PrimesEquidistInAP (which gives primes weighted by any size-dependent function
are equidist mod q), minFac is equidist mod q among q-rough integers.
Estimated proof: ~600-800 lines of sieve theory.

**RoughLPFImpliesMFRE**: CRT sieve transfer from generic q-rough to shifted squarefree.
The shifted squarefree condition mu^2(m-1)=1 involves moduli for m-1, while
the minFac condition involves moduli for m. By CRT (m-1 and m are coprime),
these constraints are asymptotically independent. Therefore minFac equidist
among generic q-rough integers implies minFac equidist among q-rough shifted
squarefree integers. Estimated proof: ~400-600 lines of analytic number theory.

## Main Results

### Definitions
* `roughCount`                        -- count of m in [2,X] with minFac(m) > z
* `roughLPFCount`                     -- count of m in [2,X] with minFac(m) = p
* `RoughLPFEquidist`                -- minFac equidist mod q among q-rough integers
* `AlladiDensityFormula`              -- Alladi's formula for LPF density (open hypothesis)
* `PrimesEquidistImpliesRoughLPF`   -- PrimesEquidistInAP -> RoughLPFEquidist (open)
* `RoughLPFImpliesMFRE`             -- RoughLPFEquidist -> MinFacResidueEquidist (open)

### Proved Theorems
* `roughCount_le_card`                -- roughCount z X <= X - 1
* `roughLPFCount_le_roughCount`       -- roughLPFCount z p X <= roughCount z X (when p > z)
* `ant_to_mfre`                       -- PrimesEquidistImpliesRoughLPF + RoughLPFImpliesMFRE
                                         -> (PrimesEquidistInAP -> forall q, MFRE q) (PROVED)
* `wpnt_to_mfre`                      -- WeightedPNTinAP -> (forall q, MFRE q) (PROVED)
* `wpnt_dsl_implies_mc`               -- WeightedPNTinAP + DSL -> MC (PROVED)
* `wpnt_dsl_hitting_implies_mc`       -- WeightedPNTinAP + DSLHitting -> MC (PROVED)
* `alladi_chain_status`               -- summary conjunction (PROVED)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Counting Functions for q-rough Integers -/

section RoughCounting

/-- Count of integers m in [2,X] with minFac(m) > z.
    These are the z-rough integers in the interval. -/
noncomputable def roughCount (z X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter (fun m => z < Nat.minFac m)).card

/-- Count of integers m in [2,X] with minFac(m) = p.
    When p > z, these contribute to the z-rough population. -/
noncomputable def roughLPFCount (z p X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter (fun m => z < Nat.minFac m ∧ Nat.minFac m = p)).card

/-- The rough count is at most |[2,X]| = X - 1. -/
theorem roughCount_le_card (z X : Nat) (hX : 2 ≤ X) :
    roughCount z X ≤ X - 1 := by
  unfold roughCount
  have h1 : ((Finset.Icc 2 X).filter (fun m => z < Nat.minFac m)).card
      ≤ (Finset.Icc 2 X).card := Finset.card_filter_le _ _
  have h2 : (Finset.Icc 2 X).card = X + 1 - 2 := by simp [Nat.card_Icc]
  omega

/-- The LPF count for any specific prime is at most the rough count. -/
theorem roughLPFCount_le_roughCount (z p X : Nat) :
    roughLPFCount z p X ≤ roughCount z X := by
  apply Finset.card_le_card
  intro m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact fun ⟨hm, hmin, _⟩ => ⟨hm, hmin⟩

end RoughCounting

/-! ## Intermediate Hypotheses -/

section Hypotheses

/-- **Equidistribution of minFac mod q among q-rough integers.**

    For each coprime residue class a mod q, the density of
    {m in [2,X] : minFac(m) > q, minFac(m) = a mod q} among
    {m in [2,X] : minFac(m) > q} converges to 1/(q-1).

    This is the "generic" version of `MinFacResidueEquidist`, without
    the shifted squarefree condition. The step from this to MFRE
    requires showing that the squarefree condition on m-1 is
    asymptotically independent of the minFac condition on m. -/
def RoughLPFEquidist (q : Nat) : Prop :=
  ∀ (a : Nat), 0 < a → a < q → Nat.Coprime a q →
    ∃ (c : ℝ), 0 < c ∧
      Filter.Tendsto (fun X : Nat => (roughCount q X : ℝ) / (X : ℝ))
        Filter.atTop (nhds c) ∧
      Filter.Tendsto (fun X : Nat =>
        (((Finset.Icc 2 X).filter
          (fun m => q < Nat.minFac m ∧ Nat.minFac m % q = a)).card : ℝ) / (X : ℝ))
        Filter.atTop (nhds (c / (q - 1 : ℝ)))

/-- **Alladi's density formula for the least prime factor.**

    Among z-rough integers, the density of {m : minFac(m) = p} is
      (1/p) * prod_{z < r < p, r prime} (1 - 1/r)
    This follows from inclusion-exclusion / Buchstab identity. The key
    observation is that this weight depends on p only through its SIZE
    (the product over primes between z and p), not through p mod q.

    This is a classical result in analytic number theory; see
    Alladi (1982), "Asymptotic estimates of sums involving the Moebius
    function II", or Tenenbaum, "Introduction to Analytic and Probabilistic
    Number Theory", Ch. III.6. -/
def AlladiDensityFormula : Prop :=
  ∀ (z : Nat), 2 ≤ z →
    ∀ (p : Nat), Nat.Prime p → z < p →
      ∃ (w : ℝ), 0 < w ∧
        Filter.Tendsto
          (fun X : Nat =>
            (roughLPFCount z p X : ℝ) / (roughCount z X : ℝ))
          Filter.atTop (nhds (w / p))

/-- **PrimesEquidistInAP implies RoughLPFEquidist.**

    This is the main analytic step: Dirichlet equidistribution of primes
    in arithmetic progressions, combined with Alladi's density formula
    (where the weight depends only on prime size, not residue class),
    implies that minFac is equidistributed mod q among q-rough integers.

    The proof would proceed:
    1. Alladi's formula gives density of {minFac = p} among q-rough as w(p)/p
    2. The weight w(p) = prod_{q<r<p}(1-1/r) depends only on |p|
    3. The density of class a is sum_{p = a mod q} w(p)/p
    4. By PrimesEquidistInAP with size-dependent weights, this is
       (1/(q-1)) * sum_{gcd(p,q)=1} w(p)/p = (total density)/(q-1) -/
def PrimesEquidistImpliesRoughLPF : Prop :=
  IK.PrimesEquidistributedInAP → ∀ (q : Nat), Nat.Prime q → RoughLPFEquidist q

/-- **RoughLPFEquidist implies MinFacResidueEquidist.**

    The CRT sieve transfer: the shifted squarefree condition mu^2(m-1)=1
    involves moduli for m-1, while minFac involves m itself. Since m-1
    and m are coprime, by CRT these conditions are asymptotically
    independent for large moduli. Therefore equidistribution among
    generic q-rough integers transfers to equidistribution among q-rough
    shifted squarefree integers.

    The proof would use:
    1. CRT independence: for prime r != q, r | m and r^2 | m-1 are on
       coprime moduli (m vs m-1), so asymptotically independent
    2. The squarefree sieve: density of mu^2(m-1)=1 among q-rough
       integers is a positive constant (product formula from sieveDensity)
    3. The minFac distribution in the squarefree subpopulation equals
       the generic distribution up to sieve corrections that are
       class-independent -/
def RoughLPFImpliesMFRE : Prop :=
  (∀ (q : Nat), Nat.Prime q → RoughLPFEquidist q) →
  (∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q)

end Hypotheses

/-! ## Proved Reductions -/

section Reductions

/-- **PrimesEquidistInAP implies MinFacResidueEquidist via the Alladi chain.**

    Composing the two open hypotheses:
    PrimesEquidistInAP --[PrimesEquidistImpliesRoughLPF]--> RoughLPFEquidist
    RoughLPFEquidist --[RoughLPFImpliesMFRE]--> MinFacResidueEquidist -/
theorem ant_to_mfre
    (h1 : PrimesEquidistImpliesRoughLPF)
    (h2 : RoughLPFImpliesMFRE) :
    IK.PrimesEquidistributedInAP →
    ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q :=
  fun hant q hq => h2 (h1 hant) q hq

/-- **WeightedPNTinAP implies MinFacResidueEquidist via the full chain.**

    Composing the proved ANT chain with the Alladi hypotheses:
    WeightedPNTinAP --[proved]--> PrimesEquidistInAP
    PrimesEquidistInAP --[open hypotheses]--> MinFacResidueEquidist -/
theorem wpnt_to_mfre
    (h1 : PrimesEquidistImpliesRoughLPF)
    (h2 : RoughLPFImpliesMFRE) :
    IK.WeightedPNTinAP →
    ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q :=
  fun hwpnt => ant_to_mfre h1 h2 (IK.wpnt_implies_primes_equidist_proved hwpnt)

/-- **WeightedPNTinAP + DSL implies Mullin's Conjecture.**

    The master reduction combining:
    1. WPNT --[proved]--> PrimesEquidistInAP
    2. PrimesEquidistInAP --[h1]--> RoughLPFEquidist (for all primes q)
    3. RoughLPFEquidist --[h2]--> MinFacResidueEquidist (for all primes q)
    4. MinFacResidueEquidist --[proved: pe_of_equidist]--> PE
    5. PE + DSL --[proved: pe_dsl_implies_mc]--> MC

    This shows that MC follows from three hypotheses:
    - WeightedPNTinAP (standard ANT, external = Wiener-Ikehara)
    - PrimesEquidistImpliesRoughLPF (Alladi density, sieve theory)
    - RoughLPFImpliesMFRE (CRT independence)
    - DeterministicStabilityLemma (the hard open problem) -/
theorem wpnt_dsl_implies_mc
    (h1 : PrimesEquidistImpliesRoughLPF)
    (h2 : RoughLPFImpliesMFRE)
    (hwpnt : IK.WeightedPNTinAP)
    (hdsl : DeterministicStabilityLemma) :
    MullinConjecture :=
  full_chain_dsl (wpnt_to_mfre h1 h2 hwpnt) hdsl

/-- **WeightedPNTinAP + DSLHitting implies Mullin's Conjecture.**

    The weaker variant using DSLHitting (existential hitting) instead of
    the full DSL (quantitative equidistribution):
    WPNT --[proved + open]--> MFRE --[proved]--> PE --[DSLHitting]--> DH --[proved]--> MC -/
theorem wpnt_dsl_hitting_implies_mc
    (h1 : PrimesEquidistImpliesRoughLPF)
    (h2 : RoughLPFImpliesMFRE)
    (hwpnt : IK.WeightedPNTinAP)
    (hdsl : DSLHitting) :
    MullinConjecture :=
  full_chain_dsl_hitting (wpnt_to_mfre h1 h2 hwpnt) hdsl

/-- **Summary of the Alladi density chain.**

    Part 1: The three open hypotheses compose to give
    WeightedPNTinAP -> (forall q prime, MinFacResidueEquidist q).

    Part 2: Adding DSL closes the full chain to MC. -/
theorem alladi_chain_status :
    (PrimesEquidistImpliesRoughLPF → RoughLPFImpliesMFRE →
      IK.WeightedPNTinAP → ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q) ∧
    (PrimesEquidistImpliesRoughLPF → RoughLPFImpliesMFRE →
      IK.WeightedPNTinAP → DeterministicStabilityLemma → MullinConjecture) :=
  ⟨fun h1 h2 hwpnt => wpnt_to_mfre h1 h2 hwpnt,
   fun h1 h2 hwpnt hdsl => wpnt_dsl_implies_mc h1 h2 hwpnt hdsl⟩

end Reductions

end
