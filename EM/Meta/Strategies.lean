import DeclbuildMeta

-- Modules that own the declarations referenced below.
-- Each `import` here exists only so that the `` `Foo `` literals resolve at
-- elaboration time; this file does not modify any existing EM code.
import EM.Core.Conjectures           -- Mullin.MullinConjecture
import EM.CME.Reduction              -- ConditionalMultiplierEquidist
import EM.Equidist.FourierB          -- ComplexCharSumBound
import EM.Equidist.Bootstrap         -- SingleHitHypothesis
import EM.Reduction.TailWindow       -- TailWindowDecorrelation, TWDImpliesCCSB
import EM.Adelic.UniformConductor    -- UniformConductorEquidist, UCEImpliesCME

/-!
# EM Meta: Theories and Strategies for Mullin's Conjecture

This file declares **theories** and **strategies** as content-addressed
structural units using `DeclbuildMeta`, sitting one level above the per-
declaration `@[publish]` / `@[open_point]` annotations in
`EM/Meta/Registry.lean`.

It is the dogfood for `DeclbuildMeta` on a real ~78k-LoC formalization.

**This file does not modify any existing EM code.** It only declares new
`def`s of type `DeclbuildMeta.Theory` / `DeclbuildMeta.Strategy` and tags
them with the `@[publish_theory]` / `@[publish_strategy]` attributes. The
trailing `#publish_meta` command writes
`registry/theories.json` and `registry/strategies.json` alongside the
existing `registry/declarations.json` produced by CA.

## What's modeled here

Five reduction theories — coherent groupings of related hypotheses and
proved bridge results:

| Theory | Open hypothesis | Bridge into MC |
|---|---|---|
| `CMETheory`         | `ConditionalMultiplierEquidist` | via CCSB |
| `CCSBTheory`        | `ComplexCharSumBound`           | direct |
| `TailWindowTheory`  | `TailWindowDecorrelation`       | via CCSB |
| `UCETheory`         | `UniformConductorEquidist`      | via CME (RETIRED: UCE false, #160) |
| `SingleHitTheory`   | `SingleHitHypothesis`           | direct |

Five strategies — distinct paths from open hypotheses to MC:

1. **`CMERouteToMC`**       — CME ⇒ CCSB ⇒ MC
2. **`SingleHitRouteToMC`** — single-hit ⇒ MC (the shortest known path)
3. **`TailWindowRoute`**    — TWD ⇒ CCSB ⇒ MC (an alternative to CME for closing CCSB)
4. **`UCEViaCME`**          — UCE ⇒ CME ⇒ CCSB ⇒ MC (a fork of `CMERouteToMC`
                              that pushes the open point one layer further upstream)

Each strategy lists its `frontier` — the *open declarations* whose proof
would close the route. This is the actionable AI-facing field; the
distance-to-goal value function reads it as the reward shaping signal.
-/

namespace EM.Meta.Strategies

open DeclbuildMeta

-- ============================================================================
-- Theories
-- ============================================================================

@[publish_theory]
def CMETheory : Theory := {
  display_name := "Conditional Multiplier Equidistribution"
  description  :=
    "The CME hypothesis: a uniform multiplicative equidistribution \
     statement for residues of the Euclid–Mullin product. CME implies \
     CCSB, which together with the master reduction implies MC."
  members      := #[``ConditionalMultiplierEquidist]
  -- The hypothesis itself is the public face of this theory.
  interface    := #[``ConditionalMultiplierEquidist]
  paper_anchor := some "the_character_sum_reduction.tex#sec:cme"
}

@[publish_theory]
def CCSBTheory : Theory := {
  display_name := "Complex Character Sum Bound"
  description  :=
    "The CCSB hypothesis: a Weil-style cancellation bound on \
     character sums over the Euclid–Mullin walk. CCSB implies MC \
     directly via the master reduction chain."
  members      := #[``ComplexCharSumBound]
  interface    := #[``ComplexCharSumBound]
  paper_anchor := some "the_character_sum_reduction.tex#sec:ccsb"
}

@[publish_theory]
def TailWindowTheory : Theory := {
  display_name := "Tail-Window Decorrelation"
  description  :=
    "The TWD hypothesis and its consequences: decorrelation of the \
     Euclid–Mullin walk on tail windows. TWD implies CCSB (via \
     `TWDImpliesCCSB`) and so reaches MC by the same route as CME, \
     trading one open point for another."
  members      := #[``TailWindowDecorrelation, ``TWDImpliesCCSB]
  interface    := #[``TailWindowDecorrelation]
  paper_anchor := some "the_residue_walk.tex#sec:twd"
}

@[publish_theory]
def UCETheory : Theory := {
  display_name := "Uniform Conductor Equidistribution"
  description  :=
    "RETIRED (2026-08-17, Dead End #160): UCE at conductor M = 1 is \
     RoughLPFEquidist, which is FALSE by head domination \
     (`uce_implies_roughLPFEquidist`, `HeadDomination.roughLPFEquidist_iff`); \
     hence UCE is false and `UCEImpliesCME` is vacuous. Kept as a record."
  members      := #[``UniformConductorEquidist, ``UCEImpliesCME]
  interface    := #[``UniformConductorEquidist]
  paper_anchor := some "the_residue_walk.tex#sec:uce"
}

@[publish_theory]
def SingleHitTheory : Theory := {
  display_name := "Single-Hit Hypothesis"
  description  :=
    "The single-hit hypothesis: a single guaranteed hit of the \
     Euclid–Mullin walk on a primitive prime suffices to imply MC. \
     This is the shortest known reduction path; the open point is \
     the simplest to state and the hardest to prove unconditionally."
  members      := #[``SingleHitHypothesis]
  interface    := #[``SingleHitHypothesis]
  paper_anchor := some "the_ensemble_reduction.tex#sec:single-hit"
}

-- ============================================================================
-- Strategies
-- ============================================================================

@[publish_strategy]
def CMERouteToMC : Strategy := {
  display_name := "CME ⇒ CCSB ⇒ MC"
  description  :=
    "The classical reduction: prove CME, derive CCSB, conclude MC. \
     The frontier is the two open hypotheses that would close this \
     route unconditionally. This is currently the most-developed \
     route in EM."
  goal         := ``Mullin.MullinConjecture
  path         := #[``CMETheory, ``CCSBTheory]
  frontier     := #[``ConditionalMultiplierEquidist, ``ComplexCharSumBound]
  paper_anchor := some "the_character_sum_reduction.tex"
}

@[publish_strategy]
def SingleHitRouteToMC : Strategy := {
  display_name := "Single-Hit ⇒ MC"
  description  :=
    "The shortest reduction: a single guaranteed hit suffices. \
     One open point in the frontier, but the open point is intrinsically \
     the most difficult of the available formulations."
  goal         := ``Mullin.MullinConjecture
  path         := #[``SingleHitTheory]
  frontier     := #[``SingleHitHypothesis]
  paper_anchor := some "the_ensemble_reduction.tex#sec:single-hit"
}

@[publish_strategy]
def TailWindowRouteToMC : Strategy := {
  display_name := "TWD ⇒ CCSB ⇒ MC"
  description  :=
    "An alternative to the CME route for closing CCSB. Trades \
     `ConditionalMultiplierEquidist` for `TailWindowDecorrelation`, \
     which has different harmonic-analytic structure and may be \
     easier to attack."
  goal         := ``Mullin.MullinConjecture
  path         := #[``TailWindowTheory, ``CCSBTheory]
  frontier     := #[``TailWindowDecorrelation, ``ComplexCharSumBound]
  paper_anchor := some "the_residue_walk.tex"
}

/-- A fork of `CMERouteToMC` that pushes the upstream open point one
    layer further: instead of asking for CME directly, ask for the
    Uniform Conductor Equidistribution (UCE) which implies CME.

    This is the canonical example of a *derived strategy*: the
    `derived_from` field carries fork lineage. Lineage forms a DAG and
    the same DAG carries value attribution if the strategy closes. -/
@[publish_strategy]
def UCEViaCMERoute : Strategy := {
  display_name := "UCE ⇒ CME ⇒ CCSB ⇒ MC"
  description  :=
    "RETIRED (2026-08-17, Dead End #160): the UCE open point is false \
     (its M = 1 clause is the head-dominated RoughLPFEquidist), so this \
     fork of `CMERouteToMC` has a false frontier. Kept as a record."
  goal         := ``Mullin.MullinConjecture
  path         := #[``UCETheory, ``CMETheory, ``CCSBTheory]
  frontier     := #[``UniformConductorEquidist, ``ComplexCharSumBound]
  derived_from := some ``CMERouteToMC
  paper_anchor := some "the_residue_walk.tex#sec:uce"
}

-- ============================================================================
-- Emit registry/theories.json + registry/strategies.json
--
-- Place this command at the very end of the file so it runs as a side
-- effect of `lake build`. The output sits next to the existing
-- `registry/declarations.json` produced by CA's `#ca_registry`.
-- ============================================================================

#publish_meta "registry/"

end EM.Meta.Strategies
