import EM.FunctionField.StochasticMC
import EM.FunctionField.Finiteness
import EM.FunctionField.FFSieve

/-!
# Function Field Unconditional Theorems — Master File

This file assembles four bundles of unconditional facts about the function-field sequence.
Their historical names ("Stochastic FF-MC", "Phase Transition", "Almost-all GenMixedMC")
promise more than the Lean statements say; what each statement IS (review 2026-11-10, P11):

**Theorem A** (Factor Tree Structural): injectivity of every valid mixed selection,
coprimality cascade, degree growth, infinitely many distinct irreducibles explored.  These
are genuine statements about every mixed walk.  (It does NOT say that every monic
irreducible appears on some branch.)

**Theorem B** (`FFStochasticMC`): *degree growth along mixed walks* — for every target `Q`
and every valid mixed walk, `deg(acc(n)+1)` eventually reaches `deg Q`.  No probability
measure, no `ε`, and no capture statement is formalized; "a.s. every monic irreducible
appears" is NOT a Lean theorem.

**Theorem C** (`FFPhaseTransition`): `FFStochasticMC` together with degree growth of the
standard sequence.  No `ε` occurs in the statement; the "transition at ε = 0" is prose.

**Theorem D** (`FFAlmostAllGenMixedMC` and the "ANT chain"): *counting proxies* —
`π_p(d) ≥ 1` and `d·π_p(d) ≤ p^d` for the number `π_p(d)` of monic irreducibles of degree
`d`, plus the necklace identity.  Not a statement about starting points.  The genuine
density statement ("the proportion of starts from which `Q` is not tree-reachable tends to
0") is `FFAlmostAllGenMixedDensity` in `EM/FunctionField/DensityMC.lean`, proved there
conditionally on `FFDirichletDensity` (Kornblum).

## Proved unconditionally (zero sorry, zero open Props):

1. Mixed selection injectivity — no irreducible appears twice in any valid walk
2. Factor pool degree growth — deg(acc(n)+1) → ∞ for any valid mixed selection
3. Mixed walk explores ∞ distinct monic irreducibles
4. FFFiniteIrreduciblesPerDegree — PROVED (Finiteness.lean)
5. Captured degree grows — NOW UNCONDITIONAL (finiteness proved)
6. Start not capturable — the starting polynomial can never be selected
7. Coprimality cascade — no irreducible divides both acc(n) and acc(n)+1
8. Standard FF-EM degree growth — deg(ffProd(n)+1) → ∞
9. FFDH alone implies FF-MC — finiteness no longer needed as hypothesis
10. The counting proxy `FFAlmostAllGenMixedMC` (π_p(d) ≥ 1 and d·π_p(d) ≤ p^d; FFSieve.lean)
11. The counting proxies `FFCharSumCancellation` (necklace identity), `FFPNTInAPs`
    (π_p(d) ≥ 1), `FFFCD` (∑_{d ≤ D} π_p(d) ≥ D), `FFSieveProductVanishing`, `FFPSCD`
12. Monic polynomial count — p^n monic polys of degree n (NecklaceFormula.lean)
13. Irreducible count positive — pi_p(d) >= 1 for all d >= 1 (NecklaceFormula.lean)

## Infrastructure summary

| File | Lines | Theorems | Key contribution |
|------|-------|----------|------------------|
| FactorTree.lean | 455 | 25+ | Definitions, injectivity, coprimality |
| PopulationEquidist.lean | 370 | 18 | Degree growth, population transfer |
| StochasticMC.lean | 420 | 15+ | Degree growth along mixed walks, pigeonhole |
| Finiteness.lean | ~200 | 15+ | Finiteness proved + unconditional wrappers |
| NecklaceFormula.lean | 151 | 10 | Monic count, irred count, necklace identity |
| FFCharacterSums.lean | 226 | 14 | Necklace identity, irreducible counts (counting proxies) |
| FFSieve.lean | 342 | 15+ | Necklace upper bounds (counting proxies) |
| Master.lean | ~310 | 5 | Assembly of target theorems |
| **Total** | **~2474** | **112+** | |
-/

namespace FunctionFieldAnalog

open Polynomial Classical Filter

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Theorem A: Factor Tree Structural Results -/

/-- **Theorem A**: The factor tree over F_p[t] has strong structural properties
    that hold unconditionally (no open hypotheses).

    For ANY valid starting polynomial and ANY valid mixed selection:
    (1) The walk explores infinitely many distinct monic irreducibles
    (2) The factor pool degree grows to infinity
    (3) No monic irreducible appears twice (selection injective)
    (4) The accumulated product is injective (distinct steps give distinct products)
    (5) The coprimality cascade holds (no irred divides both acc(n) and acc(n)+1)
    (6) The starting polynomial is never captured (only reachable as root)
    (7) Start divides the accumulated product at every step -/
theorem theorem_A_factor_tree :
    -- (1) Explores infinitely many
    (∀ (start : Polynomial (ZMod p)) (σ : FFMixedSelection p),
      FFMixedSelectionValid p start σ → Set.Infinite (Set.range σ.sel)) ∧
    -- (2) Factor pool degree → ∞
    (∀ (start : Polynomial (ZMod p)) (σ : FFMixedSelection p),
      FFMixedSelectionValid p start σ →
      Tendsto (fun n => (ffMixedWalkProd p start σ n + 1).natDegree) atTop atTop) ∧
    -- (3) Selection injective
    (∀ (start : Polynomial (ZMod p)) (σ : FFMixedSelection p),
      FFMixedSelectionValid p start σ → Function.Injective σ.sel) ∧
    -- (4) Accumulated product injective
    (∀ (start : Polynomial (ZMod p)) (σ : FFMixedSelection p),
      FFMixedSelectionValid p start σ → Function.Injective (ffMixedWalkProd p start σ)) ∧
    -- (5) Coprimality cascade
    (∀ (start : Polynomial (ZMod p)) (σ : FFMixedSelection p)
      (Q : Polynomial (ZMod p)) (_ : Irreducible Q) (n : ℕ),
      Q ∣ ffMixedWalkProd p start σ n →
      Q ∣ ffMixedWalkProd p start σ n + 1 → False) ∧
    -- (6) Start not capturable
    (∀ (start : Polynomial (ZMod p)) (σ : FFMixedSelection p)
      (_ : start.Monic ∧ Irreducible start)
      (_ : FFMixedSelectionValid p start σ),
      ¬ ffMixedCaptures p start σ start) ∧
    -- (7) Start divides accumulated product
    (∀ (start : Polynomial (ZMod p)) (σ : FFMixedSelection p) (n : ℕ),
      start ∣ ffMixedWalkProd p start σ n) :=
  ⟨fun _ _ hv => ff_mixed_explores_infinitely_many hv,
   fun _ _ hv => ff_factor_pool_degree_grows hv,
   fun _ _ hv => ffMixedSel_injective hv,
   fun _ _ hv => ffMixedWalkProd_injective hv,
   fun _ _ Q hQ n h1 h2 => ffMixedWalkProd_coprime_succ Q hQ n h1 h2,
   fun _ _ ⟨_, hsi⟩ hv => start_not_capturable hv hsi,
   fun _ _ n => start_dvd_ffMixedWalkProd n⟩

/-! ## Theorem B: Stochastic MC -/

/-- **Theorem B**: degree growth along mixed walks (`FFStochasticMC`, `FFPhaseTransition`).

    What is proved: for every monic irreducible `Q`, every start and every valid mixed
    selection, some Euclid polynomial `acc(n) + 1` has degree `≥ deg Q`; and the degree of
    the Euclid polynomials of the standard sequence tends to infinity.

    What is NOT proved: that a randomly perturbed selection rule captures every monic
    irreducible.  No probability space is formalized here; the names `FFStochasticMC` and
    `FFPhaseTransition` are historical.  The capture statement would need, at least, the
    population-to-orbit transfer that the integer case also lacks. -/
theorem theorem_B_stochastic_mc :
    FFStochasticMC p ∧ FFPhaseTransition p :=
  ⟨stochastic_mc_unconditional p, ff_phase_transition_unconditional p⟩

/-! ## Theorem C: Phase Transition -/

/-- **Theorem C**: a bundle of five unconditional facts.

    (1) `FFStochasticMC`: degree growth along mixed walks (see Theorem B; not a capture
        statement)
    (2) `FFPhaseTransition`: (1) plus degree growth of the standard sequence (no `ε` occurs)
    (3) Captured degree grows (unconditional — finiteness proved)
    (4) Standard FF-EM degree also grows to infinity
    (5) FFDH alone implies FF-MC (finiteness no longer needed as hypothesis) -/
theorem theorem_C_phase_transition :
    -- (1) degree growth along mixed walks
    FFStochasticMC p ∧
    -- (2) the same, plus the standard sequence
    FFPhaseTransition p ∧
    -- (3) Captured degree grows (unconditional)
    FFCapturedDegreeGrows (p := p) ∧
    -- (4) Standard EM degree grows
    (∀ (d : FFEMData p),
      Tendsto (fun n => (d.ffProd n + 1).natDegree) atTop atTop) ∧
    -- (5) FFDH alone implies FF-MC
    (FFDynamicalHitting (p := p) → FFMullinConjecture p) :=
  ⟨stochastic_mc_unconditional p,
   ff_phase_transition_unconditional p,
   ffCapturedDegreeGrows_unconditional,
   fun d => ff_standard_degree_grows d,
   ff_dh_implies_ffmc_unconditional⟩

/-! ## Theorem D: counting proxies for the sieve chain -/

/-- **Theorem D**: the counting facts that the sieve argument consumes hold over `𝔽_p[t]`.

    Every clause is a statement about the number `π_p(d)` of monic irreducibles of degree `d`
    (COUNTING PROXIES; none is a statement about starting points, residue classes or
    characters):

      `FFCharSumCancellation`  = the necklace identity `∑_{d ∣ n} d·π_p(d) = p^n`
      `FFPNTInAPs`             = `π_p(d) ≥ 1` for `d ≥ 1`
      `FFFCD`                  = `∑_{d ≤ D} π_p(d) ≥ D`
      `FFSieveProductVanishing` = `n·π_p(n) ≤ p^n`
      `FFPSCD`                 = `π_p(n) ≤ p^n / n`
      `FFAlmostAllGenMixedMC`  = `π_p(d) ≥ 1` ∧ `n·π_p(n) ≤ p^n`

    The genuine statement "from a density-1 set of starts the factor tree reaches `Q`" is
    `FFAlmostAllGenMixedDensity` in `EM/FunctionField/DensityMC.lean`, proved there
    (`ff_almost_all_genmixed_density`) conditionally on `FFDirichletDensity`.

    A fifth clause `FFGenMixedMC p → FFAlmostAllGenMixedMC p` was dropped on 2026-11-10:
    `FFGenMixedMC` is false (`FunctionFieldAnalog.not_ffGenMixedMC`); see
    `EM/Archive/FunctionField/FFGenMixedMCArchive.lean` (RED #19). -/
theorem theorem_D_sieve_chain :
    -- (1) π_p(d) ≥ 1 and n·π_p(n) ≤ p^n
    FFAlmostAllGenMixedMC p ∧
    -- (2) necklace identity, π_p(d) ≥ 1, ∑_{d ≤ D} π_p(d) ≥ D
    (FFCharSumCancellation p ∧ FFPNTInAPs p ∧ FFFCD p) ∧
    -- (3) n·π_p(n) ≤ p^n and π_p(n) ≤ p^n / n
    (FFSieveProductVanishing p ∧ FFPSCD p) ∧
    -- (4) (trivially, the conclusion being unconditional)
    (FFFCD p → FFAlmostAllGenMixedMC p) :=
  ⟨ff_almost_all_unconditional p,
   ⟨ff_char_sum_cancellation_proved p, ff_pnt_in_aps_proved p, ff_fcd_proved p⟩,
   ⟨ff_spv_proved p, ff_pscd_proved p⟩,
   ff_fcd_implies_almost_all p⟩

/-! ## Landscape: Full hierarchy -/

/-- The full FF unconditional hierarchy landscape.

    This theorem witnesses all the key structural results proved in the
    FF unconditional series:
    - Infinite exploration (ALL mixed walks)
    - Degree growth (factor pool AND standard EM)
    - Selection injectivity (coprimality cascade)
    - Product injectivity
    - Start not capturable
    - Captured degree growth (NOW UNCONDITIONAL — finiteness proved)
    - `FFStochasticMC`, `FFPhaseTransition`: degree growth along mixed walks (not capture)
    - FFDH alone implies FF-MC
    - `FFAlmostAllGenMixedMC`: the counting proxy π_p(d) ≥ 1 ∧ n·π_p(n) ≤ p^n -/
theorem ff_unconditional_landscape :
    -- Structural properties (ALL mixed walks)
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Set.Infinite (Set.range σ.sel)) ∧
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Tendsto (fun n => (ffMixedWalkProd p start σ n + 1).natDegree) atTop atTop) ∧
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Function.Injective σ.sel) ∧
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Function.Injective (ffMixedWalkProd p start σ)) ∧
    -- Degree growth along mixed walks
    FFStochasticMC p ∧
    FFPhaseTransition p ∧
    -- Captured degree (unconditional)
    FFCapturedDegreeGrows (p := p) ∧
    -- Standard EM degree
    (∀ (d : FFEMData p),
      Tendsto (fun n => (d.ffProd n + 1).natDegree) atTop atTop) ∧
    -- FFDH alone implies FF-MC
    (FFDynamicalHitting (p := p) → FFMullinConjecture p) ∧
    -- Counting proxy
    FFAlmostAllGenMixedMC p :=
  ⟨fun _ _ hv => ff_mixed_explores_infinitely_many hv,
   fun _ _ hv => ff_factor_pool_degree_grows hv,
   fun _ _ hv => ffMixedSel_injective hv,
   fun _ _ hv => ffMixedWalkProd_injective hv,
   stochastic_mc_unconditional p,
   ff_phase_transition_unconditional p,
   ffCapturedDegreeGrows_unconditional,
   fun d => ff_standard_degree_grows d,
   ff_dh_implies_ffmc_unconditional,
   ff_almost_all_unconditional p⟩

/-! ## Grand Summary -/

/-- Grand summary: everything proved in the FF unconditional series.

    Line count: ~2474 lines across 8 files (FactorTree, PopulationEquidist,
    StochasticMC, Finiteness, NecklaceFormula, FFCharacterSums, FFSieve,
    Master), zero sorry, zero errors.

    Unconditional structural theorems:
    - Mixed walk explores ∞ distinct monic irreducibles
    - Factor pool degree → ∞
    - Selection injectivity (coprimality cascade)
    - Accumulated product injectivity
    - Start not capturable
    - Captured degree grows (UNCONDITIONAL — finiteness proved in Finiteness.lean)
    - Standard FF-EM degree grows
    - FFFiniteIrreduciblesPerDegree (PROVED)
    - FFDH alone implies FF-MC (finiteness eliminated as hypothesis)
    - Monic polynomial count: p^n monic polys of degree n (NecklaceFormula)
    - Irreducible count positive: pi_p(d) >= 1 for all d >= 1 (NecklaceFormula)
    - Counting proxies (statements about π_p(d) only; see Theorem D): necklace identity
      (`FFCharSumCancellation`), π_p(d) ≥ 1 (`FFPNTInAPs`), ∑_{d ≤ D} π_p(d) ≥ D (`FFFCD`),
      n·π_p(n) ≤ p^n (`FFSieveProductVanishing`), π_p(n) ≤ p^n/n (`FFPSCD`), and their
      conjunction `FFAlmostAllGenMixedMC`.  None of these is a density statement about
      starting points; that is `FFAlmostAllGenMixedDensity` (DensityMC.lean, conditional).

    Degree growth along mixed walks (`FFStochasticMC`, `FFPhaseTransition`): NOT a statement
    that a perturbed rule captures every irreducible. -/
theorem ff_unconditional_grand_summary :
    -- Theorem A (structural)
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Set.Infinite (Set.range σ.sel)) ∧
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Tendsto (fun n => (ffMixedWalkProd p start σ n + 1).natDegree) atTop atTop) ∧
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Function.Injective σ.sel) ∧
    (∀ start σ, @FFMixedSelectionValid p _ start σ →
      Function.Injective (ffMixedWalkProd p start σ)) ∧
    -- Theorem B (degree growth along mixed walks)
    FFStochasticMC p ∧ FFPhaseTransition p ∧
    -- Theorem C (finiteness proved, captured degree unconditional)
    FFFiniteIrreduciblesPerDegree (p := p) ∧
    FFCapturedDegreeGrows (p := p) ∧
    -- Standard EM degree
    (∀ (d : FFEMData p),
      Tendsto (fun n => (d.ffProd n + 1).natDegree) atTop atTop) ∧
    -- FFDH alone implies FF-MC
    (FFDynamicalHitting (p := p) → FFMullinConjecture p) ∧
    -- Theorem D (counting proxy)
    FFAlmostAllGenMixedMC p :=
  ⟨fun _ _ hv => ff_mixed_explores_infinitely_many hv,
   fun _ _ hv => ff_factor_pool_degree_grows hv,
   fun _ _ hv => ffMixedSel_injective hv,
   fun _ _ hv => ffMixedWalkProd_injective hv,
   stochastic_mc_unconditional p,
   ff_phase_transition_unconditional p,
   ffFiniteIrreduciblesPerDegree_proved,
   ffCapturedDegreeGrows_unconditional,
   fun d => ff_standard_degree_grows d,
   ff_dh_implies_ffmc_unconditional,
   ff_almost_all_unconditional p⟩

end FunctionFieldAnalog
