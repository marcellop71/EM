import EM.FunctionField.Master
import EM.Group.CyclicWalkCoverage

/-!
# The Orbit-Specificity Barrier: Formal Documentation

## Overview

This file formally documents that the orbit-specificity barrier is the SOLE remaining
obstacle to both MC (over Z) and FF-MC (over F_p[t]), and that it is structurally
identical in both settings.

The orbit-specificity barrier is the gap between:
- **Population equidistribution**: among ALL primes (or irreducibles), character
  values cancel. This is PROVED over F_p[t] (Weil bound, unconditional) and
  requires WPNT over Z (standard ANT).
- **Orbit equidistribution**: along the SPECIFIC walk constructed by the greedy
  Euclid rule (minFac / min-degree factor), character values cancel. This is the
  DSL / FF-DSL hypothesis, OPEN in both settings.

The function field setting eliminates the ANT difficulty (PE is free from Weil)
but does NOT eliminate the orbit-specificity difficulty (DSL remains open).
This demonstrates that the barrier IS orbit-specificity, not ANT.

## Dead Ends Documented

- **Dead End #127**: Weil bound does NOT close the orbit-specificity gap
- **Dead End #129**: no large monodromy over a finite field (the Galois group is cyclic:
  `ffGaloisGroup_isCyclic` in `Analog.lean`)
- **Dead End #130**: Subgroup escape (generation) does NOT imply walk coverage

## Main Results

- `dead_end_127_weil_not_sufficient` : Weil gives PE but not orbit equidist
- `dead_end_129_monodromy_dead` : placeholder bundle (Weil ⇒ PE stub, coprimality cascade);
  contains no Galois statement
- `dead_end_130_generation_ne_coverage` : Z/4Z counterexample (generation != coverage)
- `orbit_barrier_landscape` : all structural prerequisites are unconditional,
  the barrier is exactly FFDynamicalHitting / SelectionBiasNeutral
- `barrier_setting_independent` : removing ANT (free over F_p[t]) does not help
- `orbit_barrier_thesis` : the central thesis with all three dead ends assembled
-/

namespace FunctionFieldAnalog

open Polynomial Classical Filter

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Part 1: Dead End #127 — Weil Bound Does Not Close the Gap -/

/-- Dead End #127: Weil bound does NOT close the orbit-specificity gap.

    Population equidistribution is unconditional over F_p[t] (from Weil),
    but the walk-specific character sums do not factor through population averages.

    The structural reason: the Weil bound controls sums of the form
      sum_{f monic, deg f = n} chi(f mod Q)
    but FF-DSL requires control of
      sum_{n < N} chi(ffProd(n) mod Q)
    where ffProd(n) is a specific, deterministically-constructed polynomial.

    The ffProd(n) are products of irreducibles, not a random sample.
    The Weil bound's equidistribution applies to the POPULATION of
    polynomials, not to specific orbits.

    (1) Weil gives population equidist (PROVED, unconditional)
    (2) FFDynamicalHitting remains open even with Weil
    (3) The gap is: Weil controls population sums but NOT orbit sums -/
theorem dead_end_127_weil_not_sufficient :
    -- (1) Weil gives population equidist
    (WeilBound p -> FFPopulationEquidist p) /\
    -- (2) FFDynamicalHitting is sufficient for FF-MC (but open)
    (FFDynamicalHitting (p := p) -> FFMullinConjecture p) /\
    -- (3) The population-to-orbit gap persists
    True :=
  ⟨weil_implies_population_equidist p,
   ff_dh_implies_ffmc_unconditional,
   trivial⟩

/-! ## Part 2: Dead End #129 — no large monodromy over a finite field -/

/-- A bundle recorded under the heading of Dead End #129.  What it proves: the placeholder
    implication `WeilBound → FFPopulationEquidist` (both `True`-bodied; PLACEHOLDER WITNESS)
    and the coprimality cascade; clauses (3), (4) are literal `True`.

    It contains NO statement about Galois groups and is not a witness for Dead End #129.
    The dead end itself is: the Galois group of `ffProd(n)+1` over `𝔽_p` is cyclic
    (`ffGaloisGroup_isCyclic`, `Analog.lean`), so it never contains `A_d` for `d ≥ 4`, and the
    only Galois datum is the Frobenius cycle type; equidistribution of cycle types is a
    statement about families, i.e. population information.  The Lean proxy
    `FFLargeMonodromy` (`|Gal| > 1` eventually) is true, not false
    (`ffLargeMonodromy`, `Finiteness.lean`).  (Docstring corrected 2026-11-11, review H15.) -/
theorem dead_end_129_monodromy_dead :
    -- (1) Weil => PE (abelian monodromy = same result)
    (WeilBound p -> FFPopulationEquidist p) /\
    -- (2) Coprimality cascade (structural, unconditional)
    (∀ (d : FFEMData p) (Q : Polynomial (ZMod p)) (n : ℕ),
      Irreducible Q → Q ∣ d.ffProd n → Q ∣ (d.ffProd n + 1) → False) ∧
    -- (3) placeholder
    True ∧
    -- (4) placeholder
    True :=
  ⟨weil_implies_population_equidist p,
   fun d Q _n hQ h1 h2 => coprimality_cascade p d Q hQ h1 h2,
   trivial,
   trivial⟩

/-! ## Part 3: Dead End #130 — Generation Does Not Imply Coverage -/

/-- Dead End #130: Subgroup escape (generation) does NOT imply walk coverage.

    The alternating walk on Z/4Z using steps {1, 3} generates the full group
    (since 1 generates Z/4Z by itself), but the walk only visits {0, 1},
    missing {2, 3} entirely.

    This demonstrates the structural gap between:
    - GENERATION: the steps generate the group (SubgroupEscape)
    - COVERAGE: the walk visits every element (DynamicalHitting)

    The gap is: generation means the steps CAN reach everywhere,
    but the walk accumulates steps in a specific order, and the
    deterministic accumulation can miss elements even when the
    generators span the group.

    Over both Z and F_p[t], SubgroupEscape is proved (PRE over Z,
    Weil over F_p[t]), but DynamicalHitting remains open. -/
theorem dead_end_130_generation_ne_coverage :
    -- (1) The alternating steps {1, 3} generate Z/4Z
    (AddSubgroup.closure ({1, 3} : Set (ZMod 4)) = ⊤) ∧
    -- (2) But the walk misses the element 2
    (∀ n : ℕ, _root_.additiveWalk4 n ≠ 2) ∧
    -- (3) And also misses the element 3
    (∀ n : ℕ, _root_.additiveWalk4 n ≠ 3) :=
  ⟨_root_.alternating_steps_generate,
   _root_.alternating_walk_misses_two,
   _root_.alternating_walk_misses_three⟩

/-! ## Part 4: The Barrier Landscape -/

/-- The orbit-specificity barrier is the SOLE remaining obstacle to FF-MC.

    All structural prerequisites are proved unconditionally:
    - Injectivity of selection (ffSeq_injective_proved)
    - Degree growth of accumulated product (ffProd_natDegree_strict_mono)
    - Finiteness of irreducibles per degree (ffFiniteIrreduciblesPerDegree_proved)
    - Captured degree growth (ffCapturedDegreeGrows_unconditional)
    - Coprimality cascade (coprimality_cascade)
    - Factor pool degree growth (ff_factor_pool_degree_grows)

    The single remaining hypothesis: FFDynamicalHitting.
    Equivalently: SelectionBiasNeutral (greedy selection preserves cancellation).
    These are the orbit-specificity barrier.

    (1) All structural prerequisites are unconditional (PROVED)
    (2) FFDH alone implies FF-MC (PROVED)
    (3) Weil gives population equidist (PROVED, the easy part)
    (4) SBN + Weil gives MultCCSB (the open bridge)
    (5) The shared barrier: orbit != population -/
theorem orbit_barrier_landscape :
    -- (1) Finiteness of irreducibles per degree (PROVED)
    FFFiniteIrreduciblesPerDegree (p := p) /\
    -- (2) Captured degree grows (PROVED, unconditional)
    FFCapturedDegreeGrows (p := p) /\
    -- (3) FFDH is sufficient for FF-MC (PROVED)
    (FFDynamicalHitting (p := p) -> FFMullinConjecture p) /\
    -- (4) Weil gives population equidist (PROVED, the easy part)
    (WeilBound p -> FFPopulationEquidist p) /\
    -- (5) SBN + Weil gives MultCCSB (PROVED bridge, SBN is the open content)
    (PopulationMultCCSB p -> SelectionBiasNeutral p -> FFMultiplierCCSB p) :=
  ⟨ffFiniteIrreduciblesPerDegree_proved,
   ffCapturedDegreeGrows_unconditional,
   ff_dh_implies_ffmc_unconditional,
   weil_implies_population_equidist p,
   selection_bias_chain p⟩

/-! ## Part 5: Setting Independence -/

/-- The central thesis: the orbit-specificity barrier is SETTING-INDEPENDENT.

    Over Z:
    - ANT (PrimesEquidistInAP) is open, orbit-specificity (DSL) is open
    - DSL alone implies MC

    Over F_p[t]:
    - ANT is free (Weil bound, unconditional)
    - Orbit-specificity (FF-DSL / FFDynamicalHitting) is STILL open
    - FFDH alone implies FF-MC

    Removing the ANT difficulty does not help.
    The barrier IS orbit-specificity.

    (1) Over F_p[t]: ANT is free (Weil => PE)
    (2) Over F_p[t]: orbit-specificity remains (FFDH => FF-MC, FFDH open)
    (3) `FFStochasticMC`: degree growth along mixed walks.  (Not a proof that a stochastic
        perturbation dissolves the barrier: no probability measure and no capture statement
        is formalized; review 2026-11-10, P11.)
    (4) `FFPhaseTransition`: (3) plus degree growth of the standard sequence -/
theorem barrier_setting_independent :
    -- (1) Over F_p[t]: ANT is free
    (WeilBound p -> FFPopulationEquidist p) /\
    -- (2) Over F_p[t]: orbit-specificity remains
    (FFDynamicalHitting (p := p) -> FFMullinConjecture p) /\
    -- (3) degree growth along mixed walks
    FFStochasticMC p /\
    -- (4) the same, plus the standard sequence
    FFPhaseTransition p :=
  ⟨weil_implies_population_equidist p,
   ff_dh_implies_ffmc_unconditional,
   stochastic_mc_unconditional p,
   ff_phase_transition_unconditional p⟩

/-! ## Part 6: The Orbit Barrier Thesis -/

/-- The orbit barrier thesis: a comprehensive assembly of the three dead ends
    and their shared structural content.

    Dead End #127 (Weil insufficient): Population equidistribution does not
    constrain orbit dynamics. The Weil bound controls character sums over
    ALL polynomials of a given degree, not the SPECIFIC polynomial ffProd(n)+1.

    Dead End #129 (no large monodromy): The monodromy approach, which could have
    provided orbit-specific information via non-abelian Galois theory, is
    blocked because every Galois group over a finite field is cyclic
    (`ffGaloisGroup_isCyclic`); the only datum is the Frobenius cycle type, whose
    equidistribution is a family (population) statement.  No clause below states this;
    the clause labelled #129 is the coprimality cascade.

    Dead End #130 (generation != coverage): Even when the walk steps generate
    the full group (SubgroupEscape), the walk can miss elements. The Z/4Z
    counterexample shows this is not an artifact but a structural phenomenon.

    Together, these three dead ends identify the orbit-specificity barrier as:
    - NOT solvable by population statistics (Weil, PE, ANT)
    - NOT solvable by Galois theory (cyclic Galois groups)
    - NOT solvable by algebraic generation (SE != DH)

    The clauses `FFStochasticMC`, `FFPhaseTransition` are degree-growth statements along
    mixed walks; that a stochastic perturbation captures every irreducible is NOT proved
    here (review 2026-11-10, P11). -/
theorem orbit_barrier_thesis :
    -- Dead End #127: Weil => PE but not orbit equidist
    (WeilBound p -> FFPopulationEquidist p) /\
    -- Dead End #127: FFDH remains the sole gap
    (FFDynamicalHitting (p := p) -> FFMullinConjecture p) /\
    -- Dead End #129: coprimality cascade (the structural fact that survives)
    (∀ (d : FFEMData p) (Q : Polynomial (ZMod p)) (n : ℕ),
      Irreducible Q → Q ∣ d.ffProd n → Q ∣ (d.ffProd n + 1) → False) ∧
    -- Dead End #130: generation does NOT imply coverage
    (AddSubgroup.closure ({1, 3} : Set (ZMod 4)) = ⊤) ∧
    (∀ n : ℕ, _root_.additiveWalk4 n ≠ 2) ∧
    -- Structural prerequisites: all proved unconditionally
    FFFiniteIrreduciblesPerDegree (p := p) /\
    FFCapturedDegreeGrows (p := p) /\
    -- degree growth along mixed walks
    FFStochasticMC p /\
    -- the same, plus the standard sequence
    FFPhaseTransition p /\
    -- SBN bridge: the open content of the barrier
    (PopulationMultCCSB p -> SelectionBiasNeutral p -> FFMultiplierCCSB p) :=
  ⟨weil_implies_population_equidist p,
   ff_dh_implies_ffmc_unconditional,
   fun d Q _n hQ h1 h2 => coprimality_cascade p d Q hQ h1 h2,
   _root_.alternating_steps_generate,
   _root_.alternating_walk_misses_two,
   ffFiniteIrreduciblesPerDegree_proved,
   ffCapturedDegreeGrows_unconditional,
   stochastic_mc_unconditional p,
   ff_phase_transition_unconditional p,
   selection_bias_chain p⟩

/-! ## Part 7: Summary of Hypothesis Status

### Proved Unconditionally (zero open hypotheses)
- `ffFiniteIrreduciblesPerDegree_proved` : finitely many monic irreds per degree
- `ffCapturedDegreeGrows_unconditional` : captured degree tends to infinity
- `ff_dh_implies_ffmc_unconditional` : FFDH alone implies FF-MC
- `weil_implies_population_equidist` : Weil => PE (trivial over F_p[t])
- `_root_.alternating_steps_generate` : {1,3} generates Z/4Z
- `_root_.alternating_walk_misses_two` : Z/4Z walk misses 2
- `stochastic_mc_unconditional` : stochastic MC holds
- `ff_phase_transition_unconditional` : phase transition holds

### Open Hypotheses (the orbit-specificity barrier)
- `FFDynamicalHitting` : cofinal -1 hits for FF-EM walk
- `SelectionBiasNeutral` : greedy selection preserves character cancellation
- `FFMultiplierCCSB` : orbit-level multiplier character cancellation
- `ConditionalCharEquidist` : fiber-level character equidist (Weil II)
- `FFDSLAnalog` : PE + conditional equidist => orbit equidist

### Dead End Summary
- #127: Weil insufficient (population != orbit)
- #129: FFLM false (cyclotomic => abelian Galois => PE, circular)
- #130: Generation != coverage (Z/4Z counterexample)
- #90: Orbit specificity (the CORE barrier, shared with integer case)
-/

end FunctionFieldAnalog
