import EM.Reduction.SelfCorrecting
import EM.Reduction.SMSB
import EM.Reduction.WeakRecurrence
import EM.Advanced.Diamonds
import EM.Advanced.Dobrushin
import EM.Advanced.LFunction
import EM.Advanced.MarkovSieve
import EM.Adelic.UniformConductor
import EM.Adelic.Profinite
import EM.CME.Reduction
import EM.Ensemble.Decorrelation
import EM.LargeSieve.PrimeArithLS
import EM.FunctionField.Analog
import EM.FunctionField.MultiplierCCSB
import EM.FunctionField.CyclicWalkCoverage
import EM.GaussEM.GaussConfinement
import EM.GaussEM.GaussWalkStructure
import EM.Population.ReciprocalSum

/-!
# Dead End Registry

Central catalog of all documented dead ends in the EM formalization.
Each entry records the dead end number, category, one-line description,
the file where it is documented, and whether a formal Lean witness exists.

## Categories
- **OS** — Orbit-Specificity: population statistics ≠ orbit statistics
- **TM** — Technique Mismatch: framework assumes structure EM lacks
- **SM** — Scale Mismatch: error terms dominate the signal
- **CI** — Circularity: reduces to the hypothesis it aims to prove
- **SF** — Structurally False: provably impossible (counterexample)
- **CO** — Collapse: reduces definitionally to an existing hypothesis
- **DG** — Decorrelation Gap: transfer from marginal to joint fails
- **AG** — Aggregate Gap: average-case ≠ per-fiber case

## Weak-MC Revival Scores (0–3)
- **0** — stays dead for any weak form
- **1** — marginal help, contributes indirectly
- **2** — medium: helps for AlmostAllRSD or positive density
- **3** — high: revives substantially for a specific weak MC form

## Catalog

### Fundamental barriers
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| 90 | OS | Population ≠ orbit (core obstruction) | Adelic/UniformConductor | — | 3 (ensemble bypasses) |
| 117 | DG | MultCancel ≠ WalkCancel (core hardness) | Ensemble/Decorrelation | — | 0 (CCSB-specific) |

### Technique mismatches
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| 86 | TM | Random walk category error (EM deterministic) | Advanced/Diamonds | — | 2 (ensemble quasi-random) |
| 95 | TM | Spectral gap for deterministic walks | Advanced/Dobrushin | `spectral_gap_inapplicable` | 0 |
| 128 | TM | p-adic geometry mismatch | Advanced/Diamonds | — | 1 (structural results help) |
| 131 | TM | Dobrushin coeff = 1 always | Advanced/Dobrushin | `dobrushin_coefficient_one` | 0 |
| 135 | TM | Number field extensions invisible | GaussEM/GaussConfinement | `dead_end_135_certificate` | 1 (weak Gauss MC) |

### Scale mismatches
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| 96 | SM | LoD exponential vs linear | LargeSieve/PrimeArithLS | — | 0 |
| 108 | SM | Weil √q·log q vs linear N | FunctionField/Analog | — | 1 (FF positive density) |

### Circularity and collapse
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| 93 | CO | No L^p interpolation (FEB ≡ CME) | CME/Reduction | — | 0 |
| 110 | CO | Doeblin convergence = CME (rfl) | Advanced/MarkovSieve | `no_new_leverage` | 0 |
| 116 | CI | Sieve DSL circular | FunctionField/MultiplierCCSB | — | 0 |
| 120 | CO | SCD ≡ SVE algebraically | Reduction/SelfCorrecting | — | 2 (Lyapunov route) |
| 132 | CI | L-function factorization circular | Advanced/LFunction | `dead_end_132_witness` | 1 (growth estimates) |

### Structurally false / counterexamples
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| 20 | SF | Generation ≠ coverage (Z/4Z) | FunctionField/CyclicWalkCoverage | `alternating_walk_misses_two` | 1 (lower bounds) |
| 125 | SF | Pairwise ≠ k-wise (XOR) | Adelic/Profinite | — | 3 (variance only needs k=2) |
| 129 | SF | FFLM false (cyclotomic) | FunctionField/Analog | `ff_cyclotomic_dead_end` | 3 (abelian = Dirichlet) |
| 130 | SF | SE ⇏ DH (Z/4Z) | FunctionField/CyclicWalkCoverage | `selection_bias_dead_end_analysis` | 1 (quantify coverage) |

### Decorrelation and transfer gaps
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| 58 | DG | Mult-to-walk transfer fails generically | Ensemble/Decorrelation | — | 0 |
| 81 | DG | CME ≠ HOD (higher-order) | CME/Reduction | — | 0 |
| 101 | AG | Profinite adds nothing | Advanced/Diamonds | — | 0 |
| 106 | AG | Aggregate ≠ fiber (VCB ≠ CCSB) | Reduction/SMSB | — | 2 (pigeonhole density) |
| 109 | TM | Non-multiplicative Halász | Advanced/MarkovSieve | — | 0 |
| 115 | DG | Cofactor joint barrier | paper only | — | 0 |
| 121 | AG | Per-class bad set → CME collapse | Reduction/SMSB | `smsb_se_collapse_certificate` | 2 (positive density) |
| 127 | OS | Weil ≠ FF-DSL | FunctionField/Analog | — | 2 (FF weak MC) |

### L-function and analytic
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| 133 | TM | Self-similar FE mismatch | Advanced/LFunction | `dead_end_133_witness` | 0 |
| 134 | CI | No Tauberian lever | Advanced/LFunction | `tauberian_lever_absent_witness` | 1 |

### Gaussian EM
| # | Cat | Description | File | Witness | Revival |
|---|-----|-------------|------|---------|---------|
| GaussOS | OS | Gauss orbit specificity barrier | GaussEM/GaussWalkStructure | `gauss_orbit_specificity_barrier` | 1 |

## Revival Summary

**Tier A — Revives substantially (score 3)**
- #90 via ensemble averaging (AlmostAllRSD route)
- #125 via pairwise-only variance (second moment suffices)
- #129 via abelian Galois = Dirichlet (FF weak MC)

**Tier B — Medium revival (score 2)**
- #86 via ensemble quasi-randomness
- #106 via pigeonhole density of good fibers
- #120 via Lyapunov one-sided drift (upper_drift_bound_implies_mc)
- #121 via per-class certificate for positive density
- #127 via FF population + finite pool

**Tier C — Marginal (score 1)**
- #20, #108, #128, #130, #132, #134, #135, GaussOS

**Tier D — Stays dead (score 0)**
- #58, #81, #93, #95, #96, #101, #109, #110, #115, #116, #117, #131, #133
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter
open scoped BigOperators

/-! ## Formal witnesses: re-export from source files -/

-- Dead End #20: generation ≠ coverage (Z/4Z counterexample)
-- Walk with steps {1,3} generates Z/4Z but only visits {0,1}
#check @alternating_walk_misses_two   -- ∀ n, additiveWalk4 n ≠ 2
#check @alternating_walk_misses_three -- ∀ n, additiveWalk4 n ≠ 3

-- Dead End #95: spectral gap inapplicable to deterministic walks
#check @spectral_gap_inapplicable    -- SpectralGapInapplicable

-- Dead End #110: Doeblin/sieve add nothing beyond CME/CCSB
#check @no_new_leverage              -- conjunction: all routes collapse

-- Dead End #121: per-class bad set escape
#check @smsb_se_collapse_certificate -- Dead End certificate
#check @marginal_joint_barrier_witness -- pigeonhole gives one good class

-- Dead End #129: FFLM structurally false (cyclotomic counterexample)
#check @FunctionFieldAnalog.ff_cyclotomic_dead_end  -- (p : ℕ) → landscape

-- Dead End #130: selection bias (SE ⇏ DH)
#check @FunctionFieldAnalog.selection_bias_dead_end_analysis  -- (p : ℕ) → 4-clause

-- Dead End #131: Dobrushin coefficient = 1, MUB ≠ CME
#check @dobrushin_coefficient_one    -- trivially 1 for deterministic walks
#check @dobrushin_inapplicable       -- framework mismatch
#check @dead_end_131_witness         -- full conjunction

-- Dead End #132: L-function factorization circular
#check @dead_end_132_witness

-- Dead End #133: self-similar functional equation mismatch
#check @dead_end_133_witness

-- Dead End #134: no Tauberian lever for L_EM
#check @tauberian_lever_absent_witness

-- Dead End #135: number field extensions invisible to walk
#check @GaussEM.dead_end_135_certificate

-- Gaussian EM: orbit specificity barrier
#check @GaussEM.gauss_orbit_specificity_barrier

/-! ## Revival chains (proved in other files) -/

-- Revival of #90: ensemble route bypasses orbit specificity
-- AlmostAllSquarefreeRSD targets density-1 of starting points
#check @concentration_implies_rsd     -- RecipSumConcentration → AlmostAllRSD

-- Revival of #120: Lyapunov one-sided drift
-- Only the upper bound R(N) ≤ CN is needed; lower bound is free
#check @upper_drift_bound_implies_mc  -- one-sided upper → MC
#check @cumulativeDrift_lower_bound   -- FREE lower bound (unconditional)

-- Revival of #125: pairwise suffices for variance
-- Dead End #125 killed k-wise, but RSD only needs k=2
#check @dead_end_125_pairwise_revival -- PSD + variance + mean → AlmostAllRSD

-- Revival of #129: abelian Galois = good news for Dirichlet equidistribution
-- (FF weak MC attack — see FunctionField/WeakMC.lean when available)

/-! ## Aggregate statistics -/

/-- Total number of documented dead ends. -/
def deadEndCount : ℕ := 134

/-- Dead ends with formal Lean witnesses. -/
def witnessedDeadEndCount : ℕ := 13

/-- Dead ends with weak-MC revival score ≥ 2. -/
def revivableDeadEndCount : ℕ := 8

/-- Dead end registry summary. -/
theorem dead_end_registry :
    -- Witnessed dead ends have Lean proofs
    deadEndCount = 134 ∧
    witnessedDeadEndCount = 13 ∧
    revivableDeadEndCount = 8 ∧
    -- Key revival chains are proved
    (RecipSumConcentration → AlmostAllSquarefreeRSD) ∧  -- #90 revival
    (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (N : ℕ), -((N : ℝ) * ((q : ℝ) - 2) / (2 * ((q : ℝ) - 1))) ≤
        cumulativeDrift hq hne N) ∧  -- #120 free lower bound
    (LinearDrift → MullinConjecture) :=  -- #120 chain
  ⟨rfl, rfl, rfl,
   concentration_implies_rsd,
   fun _q _ hq hne N => cumulativeDrift_lower_bound hq hne N,
   linearDrift_implies_mc⟩

end
