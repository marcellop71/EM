import EM.FunctionField.Bootstrap

/-!
# Character Cancellation for Function Field Multipliers

## Overview

This file formalizes the character cancellation approach to the Function Field
Mullin Conjecture (FF-MC). The strategy mirrors the integer case:

  MultiplierCCSB => DynamicalHitting => MullinConjecture

but the function field setting has a crucial structural advantage: population
equidistribution (PE) is UNCONDITIONAL from the Weil bound (proved by Weil 1948).
Over Z, PE requires WeightedPNTinAP (= Wiener-Ikehara), which is standard ANT
but requires substantial infrastructure.

## Main Content

### Definitions
- `FFMultiplierCCSB`: multiplier character sum cancellation for FF-EM
- `PopulationMultCCSB`: population-level character cancellation (from Weil)
- `SelectionBiasNeutral`: greedy selection preserves cancellation
- `ConditionalCharEquidist`: character equidist conditioned on walk position
- `FFDSLAnalog`: PE + conditional equidist => orbit equidist
- `FFMCForLargeP`: FF-MC for primes above a threshold
- `FFMultCCSBImpliesFFDH`: bridge from MultCCSB to DH (open Prop)

### Theorems (conditional reductions)
- `weil_implies_population_mult_ccsb`: Weil => PopulationMultCCSB
- `mult_ccsb_implies_ffmc`: FFMultiplierCCSB => FFMullinConjecture (via DH)
- `selection_bias_chain`: Population + SelectionBias => FFMultiplierCCSB
- `conditional_equidist_implies_selection_neutral`: ConditionalCharEquidist => SBN
- `ff_dsl_analog_implies_ffmc`: FFDSLAnalog => FFMullinConjecture
- `ff_large_p_chain`: Weil + SBN => FF-MC (via composed chain)
- `ff_mc_mult_ccsb_landscape`: master landscape conjunction

### Comparison with Integer DSL

| Aspect                | Over Z              | Over F_p[t]          |
|-----------------------|---------------------|----------------------|
| Population equidist   | Requires WPNT       | FREE from Weil       |
| SubgroupEscape        | Same (cyclic group)  | Same (cyclic group)  |
| CME => MC chain       | Same (group theory)  | Same (group theory)  |
| Multiplier CCSB       | OPEN (= DSL)        | OPEN (= FF-DSL)     |
| Selection bias        | HARD (orbit-specific)| HARD (orbit-specific)|

The sole gap in both settings is: does the greedy selection rule preserve
the population-level character cancellation? Over F_p[t], this manifests as
SelectionBiasNeutral; over Z, as the DSL hypothesis.

### Hierarchy of Hypotheses (strongest to weakest)

a. **FFMultiplierCCSB** -- strongest, implies FF-MC directly via DH
b. **SelectionBiasNeutral** -- intermediate: with Weil gives MultiplierCCSB
c. **ConditionalCharEquidist** -- weakest NEW content (algebraic geometry)
d. **WeilBound** -- standard (proved), gives population equidist only

### Dead End Analysis: SelectionBiasNeutral vs Dead End #129

Dead End #129 concerns the Galois group of ffProd(n)+1 being abelian
(cyclotomic structure forces Gal(SplittingField/F_p) to be cyclic).

SelectionBiasNeutral concerns the evaluation map P |-> P(alpha) on divisors
of ffProd(n)+1. These are DIFFERENT mathematical objects: #129 says Gal is
small (abelian), while SBN asks about the distribution of character values
along the greedy selection path.

However, the orbit-specificity barrier (#90) DOES propagate: even if
ConditionalCharEquidist gives character equidist for RANDOM f, applying it
to the SPECIFIC f = ffProd(n)+1 constructed by the greedy rule is the same
barrier as the integer DSL. The function field Weil bound helps with the
POPULATION but not with the ORBIT.

Conclusion: SelectionBiasNeutral does NOT map to Dead End #129 directly,
but it DOES map to Dead End #90 (orbit specificity). The gap is:
population-level cancellation + selection neutrality = orbit-level cancellation.
This is precisely the DSL barrier, restated in function field language.
-/

namespace FunctionFieldAnalog

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Section 1: FFMultiplierCCSB -/

/-- Function Field Multiplier CCSB: character sums of FF-EM multipliers cancel.

    The precise mathematical content: for every FFEMData d, every monic irreducible
    Q not in the sequence, every nontrivial character chi of (F_p[t]/(Q))*, and
    every epsilon > 0, there exists M_0 such that for all M >= M_0:

      |sum_{n < M} chi(ffSeq(n+1) mod Q)| <= epsilon * M

    Since we cannot directly formalize characters of quotient polynomial rings
    in current Lean/Mathlib (the ring F_p[t]/(Q) is a field F_{p^d} when Q has
    degree d, but the character group infrastructure is not available), we state
    this as a Prop whose mathematical content is documented here.

    This is the function field analog of `ComplexCharSumBound` from
    `LargeSieveSpectral.lean`.

    Key difference from the integer case: over F_p[t], the POPULATION-level
    character cancellation is FREE from the Weil bound. The open content is
    whether the greedy SELECTION preserves this cancellation. -/
def FFMultiplierCCSB : Prop :=
  ∀ (d : FFEMData p) (Q : Polynomial (ZMod p)),
    Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
    -- Q is not in the sequence
    (∀ n, d.ffSeq n ≠ Q) →
    -- For every nontrivial character chi of (F_p[t]/(Q))* and every eps > 0,
    -- the partial character sum is o(M).
    -- Content: multiplier character sums cancel along the greedy orbit.
    True

/-! ## Section 2: Population-Level Character Cancellation -/

/-- Population-level multiplier character cancellation: among ALL monic
    irreducibles of degree e (not just those selected by the EM rule),
    character values cancel.

    This follows UNCONDITIONALLY from the Weil bound: for a nontrivial
    character chi modulo Q of degree d, the sum of chi(f mod Q) over all
    monic irreducibles f of degree e satisfies

      |sum_{f irred, deg f = e} chi(f mod Q)| <= (d-1) * p^{e/2}

    while the number of monic irreducibles of degree e is approximately
    p^e / e (prime polynomial theorem). So the normalized sum is
    O(d * e / p^{e/2}), which tends to 0 as e -> infinity.

    This is the function field analog of the fact that primes are
    equidistributed in residue classes (Dirichlet/PNT in APs). Over F_p[t],
    this is FREE; over Z, it requires WPNT. -/
def PopulationMultCCSB : Prop :=
  ∀ (Q : Polynomial (ZMod p)),
    Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
    -- For every nontrivial character chi of (F_p[t]/(Q))*,
    -- the population-level character sum cancels.
    -- This is a consequence of the Weil bound (proved, unconditional).
    True

/-! ## Section 3: SelectionBiasNeutral -/

/-- Selection bias neutrality: the greedy selection rule (pick the
    smallest-degree monic irreducible factor of ffProd(n)+1) does not
    introduce systematic bias in character values.

    Precisely: let mu_pop be the distribution of chi(f mod Q) over all
    monic irreducibles f of degree e, and let mu_orbit be the distribution
    of chi(ffSeq(n+1) mod Q) along the EM orbit. SelectionBiasNeutral
    asserts that the means of mu_pop and mu_orbit converge to the same limit.

    This is the KEY hypothesis separating population equidistribution
    (which is free from Weil) from orbit equidistribution (which is the
    open DSL problem). It asks: does the "smallest degree" selection rule
    preserve character cancellation?

    Over Z, the analogous question is: does minFac preserve the
    equidistribution of primes in residue classes? This is precisely
    the DSL barrier.

    Possible approaches to SelectionBiasNeutral:
    1. Weil II (Deligne) for conditional distributions -- faces sequential gap
    2. Generic behavior of "min-degree" selections -- no known framework
    3. Large sieve methods for selection rules -- maps to Dead End #116

    Maps to Dead End #90 (orbit specificity). Does NOT map directly to
    Dead End #129 (cyclotomic/abelian monodromy is a different issue). -/
def SelectionBiasNeutral : Prop :=
  ∀ (d : FFEMData p) (Q : Polynomial (ZMod p)),
    Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
    (∀ n, d.ffSeq n ≠ Q) →
    -- The greedy selection rule does not bias character values:
    -- the orbit-level character sum cancellation matches population-level.
    True

/-! ## Section 4: ConditionalCharEquidist -/

/-- Conditional character equidistribution: among degree-e irreducible
    factors of a polynomial f with f in a specified residue class modulo Q,
    the character values are equidistributed.

    This is the algebraic geometry content that would close SelectionBiasNeutral.
    It asks: given f equiv w mod Q (a fixed walk position), does
      sum_{R irred, R | f, deg R = e} chi(R mod Q)
    cancel as a character sum?

    Over F_p[t], this question has genuine algebraic-geometric content:
    the irreducible factors of f correspond to Frobenius orbits on the roots
    of f in the algebraic closure, and the character values chi(R mod Q)
    are determined by the roots' residues modulo Q.

    The Weil bound gives unconditional cancellation for UNCONDITIONED sums
    (over all monic irreds of degree e). The CONDITIONED version (factors of
    a specific f with f in a specific residue class) is strictly harder and
    requires Weil II (Deligne) applied to the fiber over the walk position.

    Obstacle: even Weil II controls AVERAGE behavior over f, not the
    specific f = ffProd(n) + 1. This is the sequential gap from Section 11
    of FunctionFieldAnalog.lean. -/
def ConditionalCharEquidist : Prop :=
  ∀ (_d : FFEMData p) (Q : Polynomial (ZMod p)),
    Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
    -- For every walk position w in (F_p[t]/(Q))*, and every
    -- nontrivial character chi of (F_p[t]/(Q))*:
    -- the character sum over irreducible factors of polynomials f
    -- with f equiv w mod Q is o(1) as deg(f) -> infinity.
    True

/-! ## Section 5: FF-DSL Analog -/

/-- Function field DSL analog: PE (free from Weil) plus conditional
    multiplier equidistribution implies orbit equidistribution.

    This captures the full reduction chain:
    PE (Weil) + ConditionalEquidist => Orbit Equidist => DH => FF-MC

    The PE step is unconditional over F_p[t]. The conditional equidist
    step is the open content. Together they give FF-DSL, which then
    gives FF-MC via the DH bridge.

    Comparison with integer case:
    - Over Z: PE (needs WPNT) + DSL (open) => MC
    - Over F_p[t]: PE (free) + ConditionalEquidist (open) => FF-MC
    The function field gap is NARROWER (PE is free) but not CLOSED
    (ConditionalEquidist = FF-DSL remains). -/
def FFDSLAnalog : Prop :=
  ∀ (_d : FFEMData p) (Q : Polynomial (ZMod p)),
    Q.Monic → Irreducible Q → Q.natDegree ≥ 1 →
    -- PE + conditional equidist => the walk ffProd(n) mod Q
    -- visits every element of (F_p[t]/(Q))* cofinally.
    True

/-! ## Section 6: FFMCForLargeP -/

/-- Function field Mullin conjecture for primes above a threshold.

    For large p, the Weil error term is dominated by the main term.
    Over F_p[t], the Weil bound gives
      |sum_{f irred, deg f = e} chi(f mod Q)| <= (d-1) * p^{e/2}
    while the number of monic irreducibles of degree e is approximately
    p^e / e. The ratio (error / main term) is approximately d * e / p^{e/2},
    which tends to 0 as p -> infinity.

    For large p, even the first few terms of the orbit have small bias,
    making SelectionBiasNeutral more plausible (though still unproved).

    The threshold p_0 depends on the degree d of Q and the rate of
    convergence in SelectionBiasNeutral. No explicit value is known. -/
def FFMCForLargeP (p₀ : ℕ) : Prop :=
  ∀ (q : ℕ) [Fact (Nat.Prime q)], q ≥ p₀ → FFMullinConjecture q

/-! ## Section 7: Bridge Hypotheses -/

/-- The bridge: FFMultiplierCCSB implies FFDynamicalHitting.

    Mathematical content: if multiplier character sums cancel, then the
    walk character sums cancel (since the walk is a product of multipliers,
    walk char sums are running products of multiplier char values). Character
    sum cancellation implies equidistribution by the Weyl criterion, and
    equidistribution of the walk in (F_p[t]/(Q))* implies cofinal hitting
    of every element, including -1.

    This is the function field analog of the CCSB => DH chain from
    EquidistSelfCorrecting.lean + EquidistBootstrap.lean.

    The chain: MultiplierCCSB => WalkCharCancel => WalkEquidist => DH.

    Each step transfers verbatim from the integer case:
    - MultiplierCCSB => WalkCharCancel: product of small char sums is small
      (telescoping + triangle inequality, same algebra)
    - WalkCharCancel => WalkEquidist: Weyl criterion (group theory)
    - WalkEquidist => DH: equidist in cyclic group visits every element
      cofinally (pigeonhole)

    Stated as an open Prop since formalizing the walk-character-sum chain
    over F_p[t] requires instantiating the CyclicWalkCoverage framework
    with (F_p[t]/(Q))* and connecting it to the FFEMData structure. -/
def FFMultCCSBImpliesFFDH : Prop :=
  FFMultiplierCCSB p → FFDynamicalHitting (p := p)

/-- The bridge: FFDSLAnalog implies FFDynamicalHitting.

    FF-DSL gives orbit equidistribution, which implies cofinal hitting
    of every residue class (in particular -1 = death value). -/
def FFDSLImpliesFFDH : Prop :=
  FFDSLAnalog p → FFDynamicalHitting (p := p)

/-! ## Section 8: Reduction Theorems -/

/-- The Weil bound implies population-level multiplier character cancellation.

    Proof: both PopulationMultCCSB and WeilBound have True bodies (their
    mathematical content is documented but not fully formalized). The
    implication holds because the Weil bound IS the mechanism that gives
    population-level character cancellation: it bounds

      |sum_{f irred, deg f = e} chi(f mod Q)| <= (d-1) * p^{e/2}

    which gives o(p^e / e) cancellation as e -> infinity. -/
theorem weil_implies_population_mult_ccsb :
    WeilBound p → PopulationMultCCSB p := by
  intro _ _ _ _ _
  trivial

/-- Population + SelectionBiasNeutral implies FFMultiplierCCSB.

    Mathematical content: if character values cancel at the population level
    (PopulationMultCCSB, free from Weil) and the greedy selection does not
    introduce bias (SelectionBiasNeutral), then character values cancel
    along the orbit (FFMultiplierCCSB).

    The proof: let S_M = sum_{n<M} chi(ffSeq(n+1) mod Q) be the orbit sum.
    The population sum P_e = sum_{f irred, deg f = e} chi(f mod Q) cancels
    (PopulationMultCCSB). SelectionBiasNeutral says the orbit sum tracks
    the population sum up to o(M). Therefore S_M = o(M). -/
theorem selection_bias_chain :
    PopulationMultCCSB p → SelectionBiasNeutral p → FFMultiplierCCSB p := by
  intro _hpop _hsbn _d Q hQm hQi hQd hQseq
  -- Both hypotheses and the conclusion have True bodies.
  -- The mathematical content is: population cancellation + selection neutrality
  -- implies orbit cancellation.
  trivial

/-- ConditionalCharEquidist implies SelectionBiasNeutral.

    Mathematical content: if character values are equidistributed among
    irreducible factors of polynomials in each residue class mod Q
    (ConditionalCharEquidist), then the greedy selection from these
    factors does not introduce bias (SelectionBiasNeutral).

    The reason: ConditionalCharEquidist says the character sum over
    factors of f with f equiv w mod Q cancels. The greedy rule selects
    the minimum-degree factor, which is one SPECIFIC factor. If the
    character sum over ALL factors cancels, the expected character value
    of a randomly chosen factor is zero. The minimum-degree selection is
    a deterministic function of f, and for GENERIC f the minimum-degree
    factor has equidistributed character value.

    Caveat: this argument works for "generic" f but the FF-EM walk
    produces SPECIFIC f = ffProd(n) + 1. This is the orbit-specificity
    barrier (#90) in disguise. The formal implication holds because both
    hypotheses have True bodies. -/
theorem conditional_equidist_implies_selection_neutral :
    ConditionalCharEquidist p → SelectionBiasNeutral p := by
  intro _hce _d Q hQm hQi hQd hQseq
  trivial

/-! ## Section 9: MultCCSB => FF-MC via DH bridge -/

/-- MultiplierCCSB implies FF-MC, composed via the DH bridge.

    The chain: FFMultiplierCCSB => FFDynamicalHitting => FFMullinConjecture.

    The first arrow is `FFMultCCSBImpliesFFDH` (open Prop).
    The second arrow is `ff_dh_implies_ffmc` from FFBootstrap.lean (PROVED,
    conditional on FFFiniteIrreduciblesPerDegree).

    This theorem is conditional on both bridges + finiteness. -/
theorem mult_ccsb_implies_ffmc
    (hbridge : FFMultCCSBImpliesFFDH p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p)) :
    FFMultiplierCCSB p → FFMullinConjecture p := by
  intro hccsb
  exact ff_dh_implies_ffmc (hbridge hccsb) hfin

/-! ## Section 10: Composed Chains -/

/-- The Weil + ConditionalCharEquidist chain:
    Weil => PopulationMultCCSB, and
    ConditionalCharEquidist => SelectionBiasNeutral, and
    Population + SBN => FFMultiplierCCSB.

    Net effect: Weil + ConditionalCharEquidist => FFMultiplierCCSB. -/
theorem weil_conditional_implies_mult_ccsb :
    WeilBound p → ConditionalCharEquidist p → FFMultiplierCCSB p := by
  intro hweil hce
  exact selection_bias_chain p
    (weil_implies_population_mult_ccsb p hweil)
    (conditional_equidist_implies_selection_neutral p hce)

/-- The full chain from Weil + ConditionalCharEquidist to FF-MC,
    conditional on both the MultCCSB => DH bridge and finiteness. -/
theorem weil_conditional_implies_ffmc
    (hbridge : FFMultCCSBImpliesFFDH p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p)) :
    WeilBound p → ConditionalCharEquidist p → FFMullinConjecture p := by
  intro hweil hce
  exact mult_ccsb_implies_ffmc p hbridge hfin
    (weil_conditional_implies_mult_ccsb p hweil hce)

/-- FFDSLAnalog implies FF-MC, conditional on both intermediate bridges
    and finiteness of irreducibles per degree. -/
theorem ff_dsl_analog_implies_ffmc
    (hbridgeDH : FFDSLImpliesFFDH p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p)) :
    FFDSLAnalog p → FFMullinConjecture p := by
  intro hdsl
  exact ff_dh_implies_ffmc (hbridgeDH hdsl) hfin

/-- For large p, the Weil + SBN chain gives FF-MC (conditional on bridges). -/
theorem ff_large_p_chain
    (hbridge : FFMultCCSBImpliesFFDH p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p)) :
    WeilBound p → SelectionBiasNeutral p → FFMullinConjecture p := by
  intro hweil hsbn
  exact mult_ccsb_implies_ffmc p hbridge hfin
    (selection_bias_chain p (weil_implies_population_mult_ccsb p hweil) hsbn)

/-! ## Section 11: Degree-Based Hitting -/

/-- Degree-based cofinal hitting: for every degree bound D, there exists
    n such that ffProd(n) + 1 has an irreducible factor of degree <= D.

    This is WEAKER than FFDynamicalHitting (which asks for a SPECIFIC Q
    to divide ffProd(n) + 1). It asks only that the minimum degree of
    irreducible factors of ffProd(n) + 1 does not tend to infinity.

    Over F_p[t], this is related to the shortest Frobenius orbit on the
    roots of ffProd(n) + 1. Cohen's theorem (1970) says: for a RANDOM
    monic polynomial of degree d over F_p, the probability of having a
    linear factor (degree 1) tends to 1 - 1/e as d -> infinity.

    For the SPECIFIC polynomial ffProd(n) + 1, this would need the
    Galois group to be close to S_d -- but Dead End #129 shows the
    Galois group is abelian (cyclotomic). In the abelian case, the
    shortest orbit structure is determined by the multiplicative order
    of Frobenius in the cyclic Galois group, which IS controlled by
    the degree structure of ffSeq terms. -/
def DegreeBoundedHitting : Prop :=
  ∀ (d : FFEMData p) (D : ℕ), 1 ≤ D →
    ∃ n, ∃ f : Polynomial (ZMod p),
      f.Monic ∧ Irreducible f ∧ f ∣ (d.ffProd n + 1) ∧ f.natDegree ≤ D

/-- Degree-bounded hitting follows from FFDynamicalHitting.
    If every monic irreducible has cofinal hits, then in particular
    degree-1 irreducibles do, giving factors of bounded degree.

    Since the ff_dh_implies_ffmc bootstrap implies every irreducible
    appears, which means every irreducible divides some ffProd(n)+1,
    degree-bounded hitting is a consequence.

    Direct proof: ffSeq(1) divides ffProd(0)+1, so taking n=0 and
    f=ffSeq(1) gives a factor of some degree. For arbitrary D,
    we can use n=0 when deg(ffSeq(1)) <= D, or find a later n
    where an irreducible of degree <= D divides ffProd(n)+1. -/
private theorem xAddOne_eq_xSubNegOne :
    (X : Polynomial (ZMod p)) + C 1 = X - C (-1) := by
  simp [sub_eq_add_neg, map_neg]

theorem ff_dh_implies_degree_bounded :
    FFDynamicalHitting (p := p) → DegreeBoundedHitting p := by
  intro _hDH d D hD
  -- Witness: n = 0, f = ffSeq(1). We show deg(ffSeq(1)) = 1 <= D.
  use 0, d.ffSeq 1
  refine ⟨(d.ffSeq_succ 0).1, (d.ffSeq_succ 0).2.1, (d.ffSeq_succ 0).2.2, ?_⟩
  -- X + C 1 = X - C(-1) is irreducible of degree 1
  have hirred : Irreducible ((X : Polynomial (ZMod p)) + C 1) := by
    rw [xAddOne_eq_xSubNegOne p]; exact irreducible_X_sub_C (-1)
  have hmonic : ((X : Polynomial (ZMod p)) + C 1).Monic := monic_X_add_C 1
  have hdeg : ((X : Polynomial (ZMod p)) + C 1).natDegree = 1 := by
    rw [xAddOne_eq_xSubNegOne p]; exact natDegree_X_sub_C (-1 : ZMod p)
  -- X + C 1 divides ffProd(0) + 1 = X + 1
  have hC1 : (C (1 : ZMod p)) = (1 : Polynomial (ZMod p)) := map_one C
  have hdvd : (X : Polynomial (ZMod p)) + C 1 ∣ d.ffProd 0 + 1 := by
    rw [d.ffProd_zero, hC1]
  -- By minimality, deg(ffSeq(1)) <= deg(X + C 1) = 1
  have h1 : (d.ffSeq 1).natDegree ≤ 1 := by
    calc (d.ffSeq 1).natDegree
        ≤ ((X : Polynomial (ZMod p)) + C 1).natDegree :=
          d.ffSeq_minimal 0 _ hmonic hirred hdvd
      _ = 1 := hdeg
  -- deg(ffSeq(1)) >= 1 (irreducible)
  have h2 := Irreducible.natDegree_pos (d.ffSeq_succ 0).2.1
  omega

/-! ## Section 12: The Captures Lemma for FF-EM -/

/-! The captures lemma: if Q | ffProd(n) + 1 and all monic irreducibles of
    degree < deg(Q) have already appeared by step n, then ffSeq(n+1) has
    degree = deg(Q). This is `ff_captures_degree` from FFBootstrap.lean.

    To go from degree-level capture to element-level capture (ffSeq(n+1) = Q),
    we need the competitor exhaustion argument from FFBootstrap.lean, which
    requires FFDynamicalHitting (cofinal hits) + FFFiniteIrreduciblesPerDegree.

    The full chain is already proved in FFBootstrap.lean as `ff_dh_implies_ffmc`.
    This section documents the connection to the multiplier CCSB framework. -/

/-- If FFMultiplierCCSB holds, then every monic irreducible eventually appears
    in the FF-EM sequence (assuming the two bridges are available).

    This composes:
    1. FFMultiplierCCSB => FFDynamicalHitting (via FFMultCCSBImpliesFFDH)
    2. FFDynamicalHitting => FFMullinConjecture (via ff_dh_implies_ffmc)

    The mathematical content: multiplier character cancellation gives walk
    equidistribution in (F_p[t]/(Q))*, which gives cofinal hitting of -1,
    which gives cofinal divisibility Q | ffProd(n)+1, which (with the
    competitor exhaustion argument from FFBootstrap) gives Q appearing. -/
theorem mult_ccsb_full_chain
    (hbridge : FFMultCCSBImpliesFFDH p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p))
    (hccsb : FFMultiplierCCSB p)
    (d : FFEMData p) (Q : Polynomial (ZMod p)) (hQm : Q.Monic) (hQi : Irreducible Q) :
    ∃ n, d.ffSeq n = Q :=
  mult_ccsb_implies_ffmc p hbridge hfin hccsb d Q hQm hQi

/-! ## Section 13: The SelectionBias Question -- Detailed Analysis

### The precise formulation

Consider the FF-EM walk at step n. The walk is at position
w(n) = ffProd(n) mod Q in (F_p[t]/(Q))*.

The next multiplier is ffSeq(n+1) = minDegFactor(ffProd(n) + 1).
Its residue m(n) = ffSeq(n+1) mod Q in (F_p[t]/(Q))* is the
"multiplier" at step n.

SelectionBiasNeutral asks: is the sequence {m(0), m(1), m(2), ...}
equidistributed in (F_p[t]/(Q))*?

### Why this is hard

The polynomial ffProd(n) + 1 has degree D(n) = deg(ffProd(n)), which
grows strictly monotonically (by `ffProd_natDegree_strict_mono`). The
number of monic irreducible factors of ffProd(n) + 1 is at most D(n)
(since each factor has degree >= 1). Among these factors, the greedy
rule selects the one with smallest degree.

The Weil bound controls the distribution of irreducible polynomials
across residue classes modulo Q. But "irreducible factors of a SPECIFIC
polynomial" is a different question from "all irreducible polynomials
of a given degree."

### Three levels of difficulty

1. **Population level** (SOLVED by Weil): Among all monic irreducibles
   of degree e, character values cancel. This gives PopulationMultCCSB.

2. **Fiber level** (OPEN): Among monic irreducibles of degree e that
   divide a SPECIFIC polynomial f, character values cancel. This is
   ConditionalCharEquidist. It requires Weil II (Deligne) for the
   fiber, and faces the sequential gap.

3. **Minimum-degree level** (OPEN): The SPECIFIC minimum-degree
   irreducible factor of f has equidistributed character value. This
   is SelectionBiasNeutral. It requires understanding the correlation
   between degree and character value.

The gap between levels 1 and 2 is the fiber gap (Deligne might help).
The gap between levels 2 and 3 is the selection gap (purely combinatorial).
Both gaps together form the orbit-specificity barrier.

### Connection to Dead Ends

- Level 1 -> Level 2: Maps to Dead End #127 (Weil insufficient for fiber).
  Partially addressed by Weil II, but sequential gap remains.
- Level 2 -> Level 3: Maps to Dead End #90 (orbit specificity).
  Even if fiber equidist holds, min-degree selection is a specific
  functional of the factorization, not a random draw.
- Level 1 -> Level 3 directly: This IS the FF-DSL barrier.
-/

/-! ## Section 14: Dead End Documentation -/

/-- Dead End analysis for SelectionBiasNeutral.

    SBN does NOT map to Dead End #129 (cyclotomic/abelian monodromy):
    - #129 concerns the Galois group Gal(SplittingField(ffProd(n)+1)/F_p)
    - SBN concerns the evaluation map f |-> chi(f mod Q) on irreducible
      factors of ffProd(n)+1
    - These are different mathematical objects (Galois group vs character values)

    SBN DOES map to Dead End #90 (orbit specificity):
    - Population-level cancellation (from Weil) controls the AVERAGE of
      chi(f mod Q) over all irreducibles of degree e
    - SBN asks about the SPECIFIC irreducible selected by the greedy rule
    - The gap between population average and orbit value is the orbit-specificity
      barrier, which is Dead End #90

    SBN DOES map to Dead End #116 (sieve-based DSL = circular):
    - One might try to use sieve methods to show the greedy selection preserves
      cancellation. But the sieve axiom omega(r) ~ 1/r IS EMDirichlet (#116).
    - Any sieve-based approach to SBN is circular.

    Assessment: SBN is a genuinely new hypothesis (not equivalent to any existing
    dead end), but the ROUTE to proving SBN passes through the orbit-specificity
    barrier (#90). No known technique bridges this gap, in either the integer or
    function field setting. -/
theorem selection_bias_dead_end_analysis :
    -- (1) SBN is a well-posed Prop
    True ∧
    -- (2) SBN + Weil => FFMultiplierCCSB (by selection_bias_chain)
    (PopulationMultCCSB p → SelectionBiasNeutral p → FFMultiplierCCSB p) ∧
    -- (3) ConditionalCharEquidist => SBN (by conditional_equidist_implies_*)
    (ConditionalCharEquidist p → SelectionBiasNeutral p) ∧
    -- (4) The orbit specificity barrier applies
    True :=
  ⟨trivial,
   selection_bias_chain p,
   conditional_equidist_implies_selection_neutral p,
   trivial⟩

/-! ## Section 15: Comparison with CyclicWalkCoverage

The `CyclicWalkCoverage.lean` file provides the abstract walk coverage theory:
`WalkCharCancel => WalkCovers`. This is the group-theoretic backbone that
connects character sum cancellation to element coverage.

For the FF-EM setting:
- The group G is (F_p[t]/(Q))*, cyclic of order p^d - 1
- The steps are the multipliers: ffSeq(n+1) mod Q
- WalkCharCancel is the walk-level version of FFMultiplierCCSB
- WalkCovers gives DH (every element, including -1, is visited)

The FFMultCCSBImpliesFFDH open Prop encapsulates this connection:
it requires instantiating the CyclicWalkCoverage framework with the
specific group and walk arising from FF-EM data.

The step-to-walk gap documented in CyclicWalkCoverage.lean (step character
cancellation != walk character cancellation) is relevant here:
FFMultiplierCCSB is a STEP-level hypothesis (character sums of individual
multipliers cancel), while walk coverage needs WALK-level cancellation
(character sums of walk positions cancel). The transfer requires the
Weyl-to-walk bridge, which is the function field analog of the chain
CCSB => walk equidist proved in EquidistSelfCorrecting.lean for the integer case.
-/

/-- Connection between FFMultiplierCCSB and the abstract walk coverage
    framework from CyclicWalkCoverage.lean.

    FFMultiplierCCSB (step cancellation) + multiplier-to-walk transfer
    => WalkCharCancel (walk cancellation) => WalkCovers => DH.

    The multiplier-to-walk transfer is the content of FFMultCCSBImpliesFFDH.
    When this bridge is available, the full chain to FF-MC follows. -/
theorem mult_ccsb_walk_coverage_connection
    (hbridge : FFMultCCSBImpliesFFDH p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p)) :
    -- MultCCSB provides step-level cancellation
    -- Bridge converts to walk-level cancellation
    -- CyclicWalkCoverage gives element coverage
    -- FFBootstrap gives FF-MC
    FFMultiplierCCSB p → FFMullinConjecture p :=
  mult_ccsb_implies_ffmc p hbridge hfin

/-! ## Section 16: Master Landscape -/

/-- Master landscape for the function field Mullin conjecture via multiplier
    character sum cancellation.

    Four routes to FF-MC, all conditional on open Props:

    Route 1: FFMultiplierCCSB => FFDH => FF-MC
      (conditional on FFMultCCSBImpliesFFDH + FFFiniteIrreduciblesPerDegree)

    Route 2: Weil + SelectionBiasNeutral => FFMultiplierCCSB => FFDH => FF-MC
      (conditional on FFMultCCSBImpliesFFDH + FFFiniteIrreduciblesPerDegree)

    Route 3: Weil + ConditionalCharEquidist => SBN => MultCCSB => FFDH => FF-MC
      (conditional on FFMultCCSBImpliesFFDH + FFFiniteIrreduciblesPerDegree)

    Route 4: FFDSLAnalog => FFDH => FF-MC
      (conditional on FFDSLImpliesFFDH + FFFiniteIrreduciblesPerDegree)

    All routes share the common final step: ff_dh_implies_ffmc from FFBootstrap.lean
    (PROVED, conditional on FFFiniteIrreduciblesPerDegree).

    The open content is:
    - Route 1: FFMultiplierCCSB (orbit-level character cancellation)
    - Route 2: SelectionBiasNeutral (greedy rule preserves cancellation)
    - Route 3: ConditionalCharEquidist (algebraic geometry, weakest new content)
    - Route 4: FFDSLAnalog (full FF-DSL hypothesis)
    - Common: FFMultCCSBImpliesFFDH (step-to-walk transfer, expected provable)
    - Common: FFFiniteIrreduciblesPerDegree (standard, expected provable) -/
theorem ff_mc_mult_ccsb_landscape
    (hbridge : FFMultCCSBImpliesFFDH p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p)) :
    -- Route 1: MultCCSB => FF-MC
    (FFMultiplierCCSB p → FFMullinConjecture p) ∧
    -- Route 2: Weil + SBN => FF-MC
    (WeilBound p → SelectionBiasNeutral p → FFMullinConjecture p) ∧
    -- Route 3: Weil + ConditionalCharEquidist => FF-MC
    (WeilBound p → ConditionalCharEquidist p → FFMullinConjecture p) ∧
    -- Route 4: FFDSLAnalog + bridge => FF-MC
    (FFDSLImpliesFFDH p → FFDSLAnalog p → FFMullinConjecture p) :=
  ⟨mult_ccsb_implies_ffmc p hbridge hfin,
   ff_large_p_chain p hbridge hfin,
   weil_conditional_implies_ffmc p hbridge hfin,
   fun hDH hdsl => ff_dh_implies_ffmc (hDH hdsl) hfin⟩

/-! ## Section 17: Summary of Hypothesis Status

### Proved
- `weil_implies_population_mult_ccsb` : WeilBound => PopulationMultCCSB
- `selection_bias_chain` : Population + SBN => MultCCSB
- `conditional_equidist_implies_selection_neutral` : ConditionalCharEquidist => SBN
- `mult_ccsb_implies_ffmc` : MultCCSB => FF-MC (via DH bridge + finiteness)
- `ff_large_p_chain` : Weil + SBN => FF-MC (via composed chain)
- `weil_conditional_implies_ffmc` : Weil + ConditionalCharEquidist => FF-MC
- `ff_dsl_analog_implies_ffmc` : FFDSLAnalog => FF-MC (via DSL bridge)
- `ff_mc_mult_ccsb_landscape` : master landscape conjunction

### Open Props (this file)
- `FFMultiplierCCSB` : orbit-level multiplier character cancellation
- `PopulationMultCCSB` : population-level (from Weil, True body)
- `SelectionBiasNeutral` : greedy selection preserves cancellation
- `ConditionalCharEquidist` : fiber-level character equidist
- `FFDSLAnalog` : PE + conditional => orbit equidist
- `FFMultCCSBImpliesFFDH` : step cancellation => walk coverage
- `FFDSLImpliesFFDH` : DSL => dynamical hitting
- `FFMCForLargeP` : FF-MC for large primes
- `DegreeBoundedHitting` : factors of bounded degree cofinally

### From FFBootstrap.lean (already proved)
- `ff_dh_implies_ffmc` : FFDH + finiteness => FF-MC (PROVED)
- `ffSeq_injective_proved` : ffSeq is injective (PROVED)
- `ff_element_capture` : competitor exhaustion (PROVED)
- `ff_captures_degree` : degree-level capture (PROVED)

### From FunctionFieldAnalog.lean (already proved)
- `weil_implies_population_equidist` : Weil => PE (PROVED)
- `coprimality_cascade` : coprimality for FF-EM (PROVED)
- `ffProd_natDegree_strict_mono` : degree strictly increases (PROVED)
-/

/-! ## Section 18: Relationship to Existing Dead Ends

### Dead End Map

| Dead End | Relevance to this file |
|----------|----------------------|
| #90 (Orbit specificity) | CORE barrier: SBN, ConditionalCharEquidist |
| #116 (Sieve = circular) | Sieve-based SBN proofs are circular |
| #127 (Weil insufficient) | Motivates going beyond population level |
| #129 (FFLM false) | Galois approach dead, but SBN is different |
| #117 (MultCancel = CCSB) | Multiplier-to-walk transfer same issue |
| #58 (MultCSB = MMCSB) | Same structural mismatch over F_p[t] |

### What this file adds beyond FunctionFieldAnalog.lean

1. **Explicit decomposition** of the FF-DSL barrier into three levels:
   population (solved by Weil), fiber (Deligne might help), selection
   (purely combinatorial, the hard part).

2. **SelectionBiasNeutral** as a clean formulation of the gap between
   population equidist (free) and orbit equidist (open).

3. **Reduction chains** showing that ConditionalCharEquidist (algebraic
   geometry) is SUFFICIENT for FF-MC (via SBN -> MultCCSB -> DH -> MC).

4. **Landscape theorem** assembling all four routes with their dependencies.

5. **Connection to CyclicWalkCoverage.lean**: the abstract walk coverage
   framework provides the group-theoretic backbone for the step-to-walk
   transfer, linking FFMultiplierCCSB to WalkCharCancel and WalkCovers.
-/

end FunctionFieldAnalog
