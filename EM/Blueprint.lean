import Architect
import EM.MullinConjectures
import EM.MullinGroupCore
import EM.MasterReduction
import EM.EquidistBootstrap
import EM.EquidistSelfCorrecting
import EM.LargeSieveSpectral
import EM.EnsemblePT
import EM.EnsembleWeylChain
import EM.PopulationTransferStrategy
import EM.WeakErgodicity
import EM.EnsembleStructure
import EM.VisitEquidistribution
import EM.TailWindowDecorrelation

/-!
# Blueprint Annotations for Paper Cross-Check

This file adds `@[blueprint]` annotations to the key theorems referenced
in the paper. Building `:blueprint` will generate JSON with both the
formal Lean type signature and the informal LaTeX statement, enabling
automated consistency checking between the paper and the formalization.

This file does NOT modify any existing code — it only attaches metadata
to existing declarations via retroactive `attribute` application.
-/

open Mullin Euclid MullinGroup

-- ============================================================================
-- Core definitions
-- ============================================================================

attribute [blueprint "def:mc"
  (statement := /--
    **Mullin's Conjecture** (1963, open).
    Every prime number eventually appears in the Euclid–Mullin sequence:
    $\forall\, p$ prime, $\exists\, n$, $a(n) = p$.
  -/)
  (latexEnv := "conjecture")]
  Mullin.MullinConjecture

-- ============================================================================
-- Walk–divisibility bridge
-- ============================================================================

attribute [blueprint "thm:walk-div-bridge"
  (statement := /--
    $\operatorname{walkZ}(q, n) = -1 \iff q \mid (\operatorname{prod}(n) + 1)$.
  -/)]
  MullinGroup.walkZ_eq_neg_one_iff

-- ============================================================================
-- Master reduction chain
-- ============================================================================

attribute [blueprint "thm:full-chain-dsl"
  (statement := /--
    $\mathrm{DSL} \;\Longrightarrow\; \mathrm{CME}
    \;\Longrightarrow\; \mathrm{CCSB} \;\Longrightarrow\; \mathrm{MC}$.
    DSL is the sole remaining hypothesis for MC, assuming standard
    analytic number theory.
  -/)]
  full_chain_dsl

-- ============================================================================
-- Single Hit Theorem
-- ============================================================================

attribute [blueprint "thm:single-hit"
  (statement := /--
    $\mathrm{SingleHitHypothesis} \;\Longrightarrow\; \mathrm{MC}$.
  -/)]
  single_hit_implies_mc

-- ============================================================================
-- Dynamical Hitting → MC
-- ============================================================================

attribute [blueprint "thm:dh-mc"
  (statement := /--
    $\mathrm{DynamicalHitting} \;\Longrightarrow\; \mathrm{MC}$.
    If the walk hits $-1$ cofinally for every missing prime,
    then every prime appears.
  -/)]
  dynamical_hitting_implies_mullin

-- ============================================================================
-- CCSB → MC
-- ============================================================================

attribute [blueprint "thm:ccsb-mc"
  (statement := /--
    $\mathrm{ComplexCharSumBound} \;\Longrightarrow\; \mathrm{MC}$.
    Character sums of the walk being $o(N)$ implies MC.
  -/)]
  complex_csb_mc'

-- ============================================================================
-- CME → CCSB and CME → MC
-- ============================================================================

attribute [blueprint "thm:cme-ccsb"
  (statement := /--
    $\mathrm{CME} \;\Longrightarrow\; \mathrm{CCSB}$.
    Conditional multiplier equidistribution implies complex character
    sum bound, for all character orders.
  -/)]
  cme_implies_ccsb

attribute [blueprint "thm:cme-mc"
  (statement := /--
    $\mathrm{CME} \;\Longrightarrow\; \mathrm{MC}$ (sharpest sufficient condition).
  -/)]
  cme_implies_mc

-- ============================================================================
-- SVE → MC
-- ============================================================================

attribute [blueprint "thm:sve-mc"
  (statement := /--
    $\mathrm{SVE} \;\Longrightarrow\; \mathrm{MMCSB} \;\Longrightarrow\; \mathrm{MC}$.
    Subquadratic visit energy implies MC.
  -/)]
  sve_implies_mc

-- ============================================================================
-- HOD → CCSB
-- ============================================================================

attribute [blueprint "thm:hod-ccsb"
  (statement := /--
    $\mathrm{HOD} \;\Longrightarrow\; \mathrm{CCSB} \;\Longrightarrow\; \mathrm{MC}$.
    Higher-order decorrelation implies MC.
  -/)]
  hod_implies_ccsb

-- ============================================================================
-- PRE (proved elementarily)
-- ============================================================================

attribute [blueprint "thm:pre"
  (statement := /--
    PrimeResidueEscape holds: for every prime $q$ with $q \nmid 2$,
    the set of primes coprime to $q$ generates $(\mathbb{Z}/q\mathbb{Z})^\times$.
  -/)]
  prime_residue_escape

-- ============================================================================
-- prod_squarefree
-- ============================================================================

attribute [blueprint "thm:prod-sqfree"
  (statement := /--
    $\operatorname{prod}(n)$ is squarefree for all $n$.
  -/)]
  prod_squarefree

-- ============================================================================
-- Ensemble and character-analytic reductions
-- ============================================================================

attribute [blueprint "thm:cancel-weyl-mc"
  (statement := /--
    Walk character cancellation for $n = 2$ (strong Weyl form)
    $\;\Longrightarrow\; \mathrm{MC}$.
  -/)]
  cancel_weyl_implies_mc

attribute [blueprint "thm:sd-cancel"
  (statement := /--
    $\mathrm{StepDecorrelation}$ alone $\;\Longrightarrow\;$
    character sum cancellation for almost all squarefree starting points.
  -/)]
  sd_implies_cancellation

attribute [blueprint "thm:pe-dsl-mc"
  (statement := /--
    $\mathrm{PE} + \mathrm{DSL} \;\Longrightarrow\; \mathrm{MC}$.
  -/)]
  pe_dsl_implies_mc

attribute [blueprint "thm:pe-dslh-mc"
  (statement := /--
    $\mathrm{PE} + \mathrm{DSLHitting} \;\Longrightarrow\; \mathrm{MC}$.
  -/)]
  pe_dsl_hitting_implies_mc

attribute [blueprint "thm:dsl-closes-all"
  (statement := /--
    Under standard ANT (MinFacResidueEquidist) plus DSL:
    $\mathrm{MC} \;\wedge\; \mathrm{CCSB}$.
  -/)]
  dsl_closes_all

-- ============================================================================
-- Generalized MC
-- ============================================================================

attribute [blueprint "thm:gen-hitting-mc"
  (statement := /--
    If the generalized walk hits $-1$ cofinally for every prime $q$,
    then $\mathrm{GenMullinConjecture}(n)$ holds.
  -/)]
  gen_hitting_implies_gen_mc_proved

-- ============================================================================
-- Visit equidistribution identity
-- ============================================================================

attribute [blueprint "thm:excess-energy"
  (statement := /--
    The excess energy $E_\chi(N) - N$ equals $(q{-}1)$ times the
    squared deviation of visit counts from the uniform distribution:
    $\sum_{\chi \neq \chi_0} \|S_\chi(N)\|^2
    = (q{-}1) \sum_a (V_N(a) - N/(q{-}1))^2$.
  -/)]
  excessEnergy_eq_visit_deviation

-- ============================================================================
-- Tail window decorrelation
-- ============================================================================

attribute [blueprint "thm:twd-mc"
  (statement := /--
    $\mathrm{TWDImpliesCCSB} + \mathrm{TWD} \;\Longrightarrow\; \mathrm{MC}$.
  -/)]
  twd_implies_mc_from_bridge
