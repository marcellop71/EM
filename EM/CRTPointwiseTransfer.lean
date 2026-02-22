import EM.CMEDecomposition
import EM.PopulationTransferStrategy

/-!
# CRT Pointwise Transfer: Orbit-Conditional Equidistribution

This file introduces **OrbitConditionalEquidist (OCE)** and proves it is
*definitionally equal* to **ConditionalMultiplierEquidist (CME)** from
`LargeSieveSpectral.lean`. This is an important finding: what appears
conceptually as a new hypothesis (conditioning on walk position within
the EM orbit) is in fact exactly CME.

## Main Results

### Key Finding
* `oce_eq_cme`                    : OCE = CME (definitional, `rfl`)

### Definitions
* `OrbitConditionalEquidist`      : character sums conditioned on walk position are o(N)
* `returnVisitCharSum`            : helper — character sum restricted to a walk fiber
* `PopulationConditionalEquidist` : population-level conditional equidistribution (open Prop)
* `CRTPointwiseTransferBridge`    : PCE implies OCE (open Prop)

### Proved Reductions
* `oce_implies_cme`               : OCE -> CME (trivial from definitional equality)
* `cme_implies_oce`               : CME -> OCE (trivial from definitional equality)
* `returnVisitCharSum_eq_fiberMultCharSum` : returnVisitCharSum = fiberMultCharSum (rfl)
* `oce_implies_mc`                : OCE -> MC via CME -> CCSB -> MC
* `oce_implies_ccsb`              : OCE -> CCSB via CME -> CCSB
* `pce_bridge_implies_mc`         : PCE + CRTPointwiseTransferBridge -> MC
* `pce_bridge_dsl_comparison`     : DSL = (PE -> CME), CRTPointwiseTransferBridge = (PCE -> CME)
                                    — both are "X implies CME" for different X

## Mathematical Context

The CRT Pointwise Transfer idea is: for each integer M = P(n) in the
EM orbit, the CRT decomposition `M mod q1, M mod q2, ...` determines
`minFac(M+1)` independently of `M mod q` (by `crt_multiplier_invariance`).
If the population of integers in each residue class mod q has equidistributed
minFac residues, and if the EM orbit samples this population representatively,
then CME follows.

The key discovery formalized here is that OCE (orbit-conditional equidist)
is *literally the same statement* as CME. The conceptual difference — "orbit
conditioning" vs "fiber conditioning" — collapses because the EM walk
position *is* the orbit residue class. This means any route to OCE
automatically gives CME.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Orbit-Conditional Equidistribution -/

section OCE

/-- **Orbit-Conditional Equidistribution (OCE)**: for the standard EM orbit,
    the multiplier character sum at each walk position is o(N).

    OCE says: for every prime q not in the sequence, every nontrivial character
    chi of (Z/qZ)*, and every walk position a, the sum of chi(m(n)) over
    indices n < N where w(n) = a satisfies ||sum|| <= eps * N eventually.

    **Key finding**: this is definitionally equal to `ConditionalMultiplierEquidist`
    from `LargeSieveSpectral.lean`. The conceptual names differ (orbit-conditional
    vs fiber-restricted) but the mathematical content is identical. -/
def OrbitConditionalEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- OCE is definitionally equal to CME. Both say: for every prime q not in
    the sequence, every nontrivial character, and every walk position, the
    fiber-restricted multiplier character sum is o(N).

    This is an important structural observation: the "orbit-conditional"
    perspective does not add any new content beyond what CME already captures.
    Any proof of OCE is automatically a proof of CME, and vice versa. -/
theorem oce_eq_cme : OrbitConditionalEquidist = ConditionalMultiplierEquidist :=
  rfl

/-- OCE implies CME (forward direction of the definitional equality). -/
theorem oce_implies_cme (h : OrbitConditionalEquidist) : ConditionalMultiplierEquidist :=
  oce_eq_cme ▸ h

/-- CME implies OCE (backward direction of the definitional equality). -/
theorem cme_implies_oce (h : ConditionalMultiplierEquidist) : OrbitConditionalEquidist :=
  oce_eq_cme ▸ h

end OCE

/-! ## Return Visit Character Sum -/

section ReturnVisit

/-- The character sum of multipliers restricted to steps where the walk
    returns to position a. This is a conceptual wrapper around the sum
    that appears in both OCE and CME.

    Definitionally equal to `fiberMultCharSum` from `LargeSieveSpectral.lean`. -/
noncomputable def returnVisitCharSum (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
    (χ (emMultUnit q hq hne n) : ℂ)

/-- returnVisitCharSum equals fiberMultCharSum — they are the same sum,
    just with different names reflecting different conceptual perspectives.
    returnVisitCharSum emphasizes "steps where the walk returns to a",
    fiberMultCharSum emphasizes "the fiber of walk positions over a". -/
theorem returnVisitCharSum_eq_fiberMultCharSum (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : ℕ) :
    returnVisitCharSum q hq hne χ a N = fiberMultCharSum q hq hne χ a N :=
  rfl

end ReturnVisit

/-! ## Full Chain: OCE -> MC -/

section OCEChain

/-- **OCE implies MC** via the chain OCE = CME -> CCSB -> MC.
    Since OCE is definitionally CME, this is just `cme_implies_mc`. -/
theorem oce_implies_mc (h : OrbitConditionalEquidist) : MullinConjecture :=
  cme_implies_mc (oce_implies_cme h)

/-- **OCE implies CCSB** via the chain OCE = CME -> CCSB.
    An intermediate stop in the reduction. -/
theorem oce_implies_ccsb (h : OrbitConditionalEquidist) : ComplexCharSumBound :=
  cme_implies_ccsb (oce_implies_cme h)

end OCEChain

/-! ## Population-Conditional Equidistribution -/

section PopulationConditional

/-- **Population-Conditional Equidistribution (PCE)**: among integers M in a
    given residue class c (mod q) that are q-rough (not divisible by any prime
    <= q) and shifted-squarefree, the value minFac(M+1) mod q is equidistributed
    among the nonzero residue classes.

    In character sum form: for each walk position c and nontrivial character chi,
    the population-level character sum over M <= X with M equiv c (mod q) and
    M q-rough is o(#{such M <= X}).

    This is a number-theoretic hypothesis about the *population* of integers,
    not about the specific EM orbit. It would follow from PE (PopulationEquidist)
    plus a CRT argument showing that conditioning on M mod q does not bias
    the minFac distribution (which is the content of `crt_multiplier_invariance`).

    The gap between PCE and OCE is the *orbit specificity barrier*: even if
    the population has conditional equidistribution, the EM orbit is a specific
    deterministic sequence within that population. Transferring population
    statistics to orbit statistics is exactly the content of DSL. -/
def PopulationConditionalEquidist : Prop :=
  ∀ (q : Nat) (_hq : Nat.Prime q) (c a : Nat) (_hc : c % q ≠ 0) (_ha : a % q ≠ 0),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ X₀ : ℕ, ∀ X ≥ X₀,
    -- Among M <= X with M equiv c (mod q) and M q-rough and Squarefree(M):
    -- |#{M : minFac(M+1) mod q = a} / #{such M} - 1/(q-1)| < epsilon
    -- Placeholder: the precise counting function requires infrastructure
    -- for q-rough integer counts that does not yet exist in the codebase.
    True

end PopulationConditional

/-! ## CRT Pointwise Transfer Bridge -/

section CRTBridge

/-- **CRT Pointwise Transfer Bridge**: PopulationConditionalEquidist gives OCE
    for the standard EM orbit.

    This bridges population-level equidistribution (about all integers in a
    residue class) to orbit-specific equidistribution (about the specific
    values P(n) visited by the EM walk).

    The structural basis is `crt_multiplier_invariance`: the minFac mechanism
    is q-blind, meaning minFac(M+1) mod q depends on M only through its
    residues mod primes r != q. So if we know that for *any* collection of
    integers in residue class c mod q, the minFac residues are equidistributed
    (which is PCE), then in particular the EM orbit's values in class c should
    have equidistributed minFac residues.

    The subtlety is that the EM orbit is not a random sample from the population:
    it is a deterministic sequence where each term depends on all previous terms.
    The CRT pointwise observation says that at each step, the choice of minFac
    is q-blind (depends on other primes, not on q-residue), but the *selection*
    of which integers appear in the orbit may introduce correlations.

    Compare with DSL (DeterministicStabilityLemma): DSL says PE -> CME,
    while CRTPointwiseTransferBridge says PCE -> OCE. Since OCE = CME
    and PCE is (in principle) a consequence of PE, the bridge is a
    refinement of DSL that makes the CRT structure explicit. -/
def CRTPointwiseTransferBridge : Prop :=
  PopulationConditionalEquidist → OrbitConditionalEquidist

/-- CRTPointwiseTransferBridge gives MC when combined with PCE.
    Chain: PCE -> (via bridge) -> OCE = CME -> CCSB -> MC. -/
theorem pce_bridge_implies_mc
    (hpce : PopulationConditionalEquidist)
    (hbridge : CRTPointwiseTransferBridge) :
    MullinConjecture :=
  oce_implies_mc (hbridge hpce)

/-- CRTPointwiseTransferBridge gives CCSB when combined with PCE. -/
theorem pce_bridge_implies_ccsb
    (hpce : PopulationConditionalEquidist)
    (hbridge : CRTPointwiseTransferBridge) :
    ComplexCharSumBound :=
  oce_implies_ccsb (hbridge hpce)

end CRTBridge

/-! ## Comparison: CRT Bridge vs DSL -/

section Comparison

/-- **DSL subsumes CRT bridge**: if DSL holds (PE -> CME), then in particular
    PCE -> OCE holds (since OCE = CME and PE gives CME via DSL, making the
    PCE hypothesis unnecessary).

    In other words, DSL is strictly stronger: it does not need the intermediate
    PCE hypothesis at all. The CRT bridge factors DSL's content into
    "population conditional equidist" + "transfer to orbit", while DSL
    bypasses the factorization entirely. -/
theorem dsl_implies_crt_bridge
    (hdsl : DeterministicStabilityLemma)
    (hpe : PopulationEquidist) :
    CRTPointwiseTransferBridge :=
  fun _ => cme_implies_oce (hdsl hpe)

/-- **Structural comparison**: the landscape of "X implies CME" hypotheses.

    - DSL:                   PE -> CME
    - CRTPointwiseTransfer:  PCE -> CME (= OCE)
    - EMDImpliesCME:         EMD -> CME

    All three are open. DSL is the broadest (PE is provable from ANT).
    CRTPointwiseTransfer refines DSL by making the CRT mechanism explicit.
    EMDImpliesCME is the narrowest (EMD = DecorrelationHypothesis, which
    is strictly weaker than CME by `cme_implies_emd`).

    This theorem witnesses that all three routes end at MC. -/
theorem all_routes_to_mc :
    (DeterministicStabilityLemma → PopulationEquidist → MullinConjecture) ∧
    (CRTPointwiseTransferBridge → PopulationConditionalEquidist → MullinConjecture) ∧
    (EMDImpliesCME → EMDirichlet → MullinConjecture) :=
  ⟨fun hdsl hpe => pe_dsl_implies_mc hpe hdsl,
   fun hbridge hpce => pce_bridge_implies_mc hpce hbridge,
   fun hcme hemd => emd_cme_implies_mc hcme hemd⟩

end Comparison

end

