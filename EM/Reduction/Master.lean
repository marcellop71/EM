import EM.Ensemble.Decorrelation
import EM.Reduction.VisitEquidist

/-!
# Master Reduction: All Roads to Mullin's Conjecture

This file assembles the **complete reduction landscape** for Mullin's Conjecture,
unifying all proved chains from across the reduction network into a single reference.

## The Reduction Hierarchy

### Level 1: Irreducible Core (1 hypothesis)
```
DynamicalHitting → MC     (dynamical_hitting_implies_mullin)
```

### Level 2: Spectral Conditions (1 hypothesis each)
```
CME  → CCSB → MC          (cme_implies_mc)
SVE  → MC                 (sve_implies_mc)
HOD  → CCSB → MC          (hod_implies_ccsb)
MMCSB → MC                (mmcsb_implies_mc)
CCSB → MC                 (complex_csb_mc')
```

### Levels 3–4: Population Framework — RETIRED (Dead End #160, 2026-08-17)
The chains PE + DSL → CME → MC, PE + DSLHitting → DH → MC, MinFacResidueEquidist → PE
are archived in `EM/Archive/Population/PopulationEquidistArchive.lean`: PopulationEquidist
and MinFacResidueEquidist are FALSE (head domination, `EM/Population/HeadDomination.lean`),
so DSL/DSLHitting are vacuous.  The live master gap is CME (`cme_implies_mc`).

### Level 5: Ensemble Framework (open hypotheses)
```
RecipSumConcentration → AlmostAllSquarefreeRSD    (concentration_implies_rsd)
EnsembleConcentration → AlmostAllSquarefreeEqd    (ensemble_concentration_implies_eqd)
EnsembleCharSumConcentration → char cancellation  (char_concentration_implies_cancellation)
FirstMomentStep + VarianceBound → RSD             (first_moment_variance_implies_rsd)
```

## Main Results in This File

### Proved Reductions
* `sve_controls_visit_deviation` — SVE ↔ VE identity: excessEnergy = (p−1)·Σ(V−mean)² (PROVED)
* `ensemble_chains_summary` — all ensemble reductions are consistent (PROVED)

## Status Summary

### What Is Proved (zero sorry)
- All reductions above: DH→MC, CME→MC, SVE→MC, HOD→MC, etc.
- Sieve density function g(r) = r/(r²-1): all algebraic properties
- Ensemble infrastructure: ensembleAvg, buchstabWeight, κ, concentration→RSD
- Excess energy = visit deviation identity
- Fiber sum step recurrence
- Generalized EM: squarefree, injective, divisibility, monotonicity
- CRT decorrelation (position-blindness)
- Subgroup escape (PRE → SE)
- 29 concrete SE instances

### What Remains Open
- **CME**: the master gap (orbit-level conditional multiplier equidistribution)
- Concentration/variance hypotheses (ensemble level)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter


/-! ## SVE ↔ VE Connection -/

section SVE_VE

/-- **SVE ↔ VE**: Subquadratic Visit Energy is equivalent to Visit
    Equidistribution, via the proved identity
    `excessEnergy = (p−1) · ∑(V(a) − N/(p−1))²`.

    SVE says: excessEnergy = o(N²).
    VE says: each V(a)/N → 1/(p−1).

    The identity makes the equivalence explicit:
    - SVE → VE: if ∑(V−mean)² = o(N²), then each |V−mean| = o(N)
    - VE → SVE: if each |V−mean| = o(N), then ∑(V−mean)² = o(N²)

    Combined with `sve_implies_mc` (proved), this gives VE → MC. -/
theorem sve_controls_visit_deviation {p : ℕ} [Fact (Nat.Prime p)]
    {N : ℕ} (w : Fin N → (ZMod p)ˣ) (hp1 : 1 < p) :
    excessEnergy w =
    ((p : ℝ) - 1) *
      ∑ a : (ZMod p)ˣ,
        ((walkVisitCount w a : ℝ) - (N : ℝ) / ((p : ℝ) - 1)) ^ 2 :=
  excessEnergy_eq_visit_deviation w hp1

end SVE_VE

/-! ## Ensemble Consistency -/

section EnsembleConsistency

/-- All ensemble reduction chains are consistent: the concentration→result
    pattern (proved) connects the open hypotheses to density-zero conclusions.

    The three parallel chains:
    1. RecipSumConcentration → AlmostAllSquarefreeRSD
    2. EnsembleConcentration → AlmostAllSquarefreeEqd
    3. EnsembleCharSumConcentration → char sum cancellation (a.a.)

    Each follows the same squeeze_zero proof pattern, and each concentration
    hypothesis is provable from PE (first moment) + CRT decorrelation (variance). -/
theorem ensemble_chains_consistent
    (h1 : RecipSumConcentration)
    (h2 : EnsembleConcentration) :
    AlmostAllSquarefreeRSD ∧ AlmostAllSquarefreeEqd :=
  ⟨concentration_implies_rsd h1, ensemble_concentration_implies_eqd h2⟩

end EnsembleConsistency

/-! ## Reduction Map

The live reduction landscape (2026-08-17; the population branch PE/DSL is archived):

```
┌─────────────────────────────────────────────────────┐
│                 MULLIN'S CONJECTURE                 │
│              (every prime appears in EM)             │
└──────────────────────┬──────────────────────────────┘
                       │
         ┌─────────────┼─────────────┐
         │             │             │
    DH → MC       CCSB → MC    CME → MC
  (Bootstrap)   (SelfCorr)  (LargeSieve)
                       │             │
                  ┌────┤      ┌──────┤
                  │    │      │      │
             SVE→CCSB  │  HOD→CCSB  │
                       │             │
                  MMCSB→MC          │
                 (LargeSieve)       │

Ensemble chains (all PROVED reductions):
  RecipSumConcentration → AlmostAllSquarefreeRSD
  EnsembleConcentration → AlmostAllSquarefreeEqd
  FirstMomentStep + VarianceBound → RecipSumConcentration
```

**The sole remaining gap**: CME.  (The former "DSL: PE → CME" framing is void — PE is
false, Dead End #160.)
-/

end
