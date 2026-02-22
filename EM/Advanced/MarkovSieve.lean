import EM.Reduction.Master
import EM.Adelic.Equidist
import EM.Reduction.SelfCorrecting

/-!
# Markov Chain and Sieve Synthesis: Definitive Dead End Assessment

## Overview

This file synthesizes two natural-seeming approaches to the Deterministic Stability
Lemma (DSL) and proves they collapse to existing barriers:

1. **Non-homogeneous Markov chain (Doeblin-Dobrushin)**: Model the EM walk as a
   non-homogeneous Markov chain on (Z/qZ)* and apply ergodic theory. The Doeblin
   coefficient of ergodicity delta(P_n) measures how close the n-th transition
   kernel is to being "mixing." Dobrushin's theorem says: if sum(1 - delta(P_n))
   converges, the chain converges to uniform.

   **Why this fails**: The EM walk is deterministic (delta = 0 or 1 at each step).
   Asking delta(P_n) -> 1 for the empirical transition matrix is equivalent to asking
   the conditional distribution of mult given walk position to be uniform -- which IS
   ConditionalMultiplierEquidist (CME). The Markov chain language adds no content.

   **Dead end mapping**: #95 (spectral gap for deterministic walks),
   #110 (transition matrix convergence = CME).

2. **Multiplicative large sieve as sieve**: Use the large sieve inequality to bound
   the number of integers in an interval whose least prime factor avoids certain
   residue classes. Since minFac(P(n)+1) = seq(n+1) is the EM multiplier, perhaps
   sieve bounds on minFac equidistribution give DSL.

   **Why this fails**: The large sieve controls AVERAGES over moduli q (sum over q
   of character sums). DSL needs control at EACH FIXED q. Moreover, minFac is not
   a multiplicative function, so multiplicative large sieve technology does not
   apply directly. The gap between average-over-q and pointwise-in-q control is
   exactly the orbit-specificity barrier, which is the same obstruction that makes
   Artin's primitive root conjecture hard.

   **Dead end mapping**: #20 (Linnik/Burgess), #90 (orbit-specificity),
   #108 (Harper BDH inapplicable), #109 (non-multiplicative Halasz).

## The Artin's Conjecture Analogy

Artin's primitive root conjecture (1927) asks: for a fixed integer a != -1, 0, 1
that is not a perfect square, is a a primitive root mod p for infinitely many primes p?

The analogy to our problem is precise:
- Artin needs: for a SPECIFIC a, the multiplicative order of a mod p equals p-1
  for infinitely many p.
- We need: for a SPECIFIC orbit (n=2), the walk visits -1 mod q cofinally,
  for all primes q.

Both require pointwise control over a specific arithmetic object (a fixed integer,
a fixed orbit) where only average-case tools (Chebotarev, large sieve) are available.
Hooley (1967) proved Artin's conjecture conditionally on GRH. Our DSL would require
an analogous conditional result for the EM orbit.

## Dead End Summary

All roads through Markov chains and sieves lead to CME:
- Doeblin coefficient -> 1 IS CME (by definition, for empirical transitions)
- Quantitative DSL is STRONGER than qualitative DSL (harder to prove, not easier)
- Sieve orbit control IS the orbit-specificity gap (#90)
- Spectral gap for non-homogeneous chains requires mixing (#95)
- Transition matrix convergence = CME (#110)

No mathematical content is added beyond the existing infrastructure.

## Sections

1. DoeblinDobrushinFramework: Hypotheses and their collapse to CME
2. QuantitativeDSL: Rate-enhanced DSL and its relationship to DSL
3. SieveOrbitControl: Sieve-based approach and its collapse to orbit specificity
4. Landscape: Definitive synthesis of all routes
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Section 1: Doeblin-Dobrushin Framework

The Doeblin-Dobrushin theory of non-homogeneous Markov chains provides
convergence criteria via the "coefficient of ergodicity." For a transition
matrix P on a finite state space, the Doeblin coefficient is

    delta(P) = min_{a,b} sum_c min(P(a,c), P(b,c))

If delta(P_n) -> 1 fast enough (sum of 1 - delta converges), the chain
converges to the unique stationary distribution.

For the EM walk, the transition at step n is deterministic: the walk goes
from w(n) to w(n) * m(n) where m(n) = seq(n+1) mod q. So P_n is a
permutation matrix (delta = 0 or 1 depending on whether all rows map to
the same column -- which only happens if m(n) = 1, i.e., q | seq(n+1)).

The "empirical" Doeblin coefficient for the first N steps measures whether
the AVERAGE transition over the first N steps is mixing. But this average
mixing IS the conditional multiplier equidistribution (CME): the conditional
distribution of m(n) given w(n) = a should be approximately uniform.

This section formalizes this equivalence. -/

section DoeblinDobrushinFramework

/-- **Doeblin convergence for the EM walk**: the empirical conditional
    distribution of the multiplier given the walk position converges to uniform.

    This is stated as: for every walk position a and every nontrivial character chi,
    the fiber-restricted character sum is o(N). This is EXACTLY
    ConditionalMultiplierEquidist.

    Dead End #110: Transition matrix convergence = CME. -/
def DoeblinConvergenceForEM : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **DoeblinConvergenceForEM is definitionally ConditionalMultiplierEquidist.**
    The Markov chain language adds no mathematical content; the Doeblin coefficient
    approaching 1 for the empirical transition matrix is precisely the statement
    that conditional character sums vanish, which is CME.

    Dead End #110: Transition matrix convergence = CME. -/
theorem doeblin_eq_cme : DoeblinConvergenceForEM = ConditionalMultiplierEquidist := rfl

/-- **Doeblin convergence implies MC**, via the proved CME -> CCSB -> MC chain. -/
theorem doeblin_implies_mc (h : DoeblinConvergenceForEM) : MullinConjecture :=
  cme_implies_mc (doeblin_eq_cme ▸ h)

/-- **Spectral gap for deterministic walks is a category error.**
    The EM walk is a deterministic dynamical system on (Z/qZ)*: given w(n),
    the next position w(n+1) = w(n) * m(n) is determined by the sequence,
    not by a stochastic transition. Spectral gap techniques require a
    fixed lazy random walk operator with a gap; the EM walk has no such
    operator because the multiplier changes at every step.

    This hypothesis asks for a spectral gap in the time-averaged transition
    operator. It is STRONGER than CME (it gives explicit convergence rates),
    and therefore harder to prove, not easier.

    Dead End #95: Spectral gap for deterministic walks. -/
def SpectralGapForEMAverage : Prop :=
  ∃ (γ : ℝ), 0 < γ ∧ γ < 1 ∧
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ),
    ∃ C > (0 : ℝ), ∀ N : ℕ, N ≥ 1 →
      ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ C * γ ^ N

/-- **Spectral gap implies Doeblin convergence (= CME).**
    Exponential decay of character sums implies sublinear decay, so SpectralGap
    is strictly stronger than Doeblin/CME. The proof is elementary: for N large
    enough, C * gamma^N <= C * 1 = C <= epsilon * N. -/
theorem spectral_gap_implies_doeblin (h : SpectralGapForEMAverage) :
    DoeblinConvergenceForEM := by
  obtain ⟨γ, hγ_pos, hγ_lt, hspec⟩ := h
  intro q inst hq hne χ hχ a ε hε
  obtain ⟨C, hC_pos, hbound⟩ := hspec q hq hne χ hχ a
  have hγ_nn : 0 ≤ γ := le_of_lt hγ_pos
  -- For N >= max(1, ceil(C/ε) + 1), we have C * γ^N ≤ C ≤ ε * N
  refine ⟨max 1 (Nat.ceil (C / ε) + 1), fun N hN => ?_⟩
  have hN1 : N ≥ 1 := le_of_max_le_left hN
  calc ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖
      ≤ C * γ ^ N := hbound N hN1
    _ ≤ C * 1 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
        exact pow_le_one₀ hγ_nn (le_of_lt hγ_lt)
    _ = C := mul_one C
    _ ≤ ε * (Nat.ceil (C / ε) + 1 : ℕ) := by
        rw [Nat.cast_add, Nat.cast_one]
        calc C = ε * (C / ε) := by field_simp
          _ ≤ ε * (↑⌈C / ε⌉₊ + 1) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hε)
              have : C / ε ≤ ↑⌈C / ε⌉₊ := Nat.le_ceil (C / ε)
              linarith
    _ ≤ ε * N := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hε)
        exact_mod_cast le_of_max_le_right hN

/-- **Spectral gap implies MC.** Composition of the two reductions above. -/
theorem spectral_gap_implies_mc (h : SpectralGapForEMAverage) : MullinConjecture :=
  doeblin_implies_mc (spectral_gap_implies_doeblin h)

end DoeblinDobrushinFramework

/-! ## Section 2: Quantitative DSL

The qualitative DSL says: PE -> CME (population equidistribution implies
conditional multiplier equidistribution, i.e., fiber character sums are o(N)).

A natural attempt to prove DSL is to seek a QUANTITATIVE version: the fiber
character sums are uniformly O(1) -- bounded by a constant independent of N.
This is STRICTLY STRONGER than qualitative DSL, since a bounded sequence is
trivially o(N), but not vice versa.

Therefore QuantitativeDSL is HARDER to prove than DSL. Any approach that
"reduces DSL to QuantitativeDSL" is going in the wrong direction: it requires
proving a strictly stronger statement. The quantitative version would follow
from spectral gap estimates, but those are themselves equivalent to CME with
rates -- which is what we are trying to prove in the first place. -/

section QuantitativeDSL

/-- **Quantitative DSL with uniform bound**: the fiber character sums
    are uniformly bounded (O(1)). This is STRICTLY STRONGER than qualitative
    DSL, which only asks for o(N) decay.

    QuantitativeDSL says: PE implies that for each q, chi, a, there exists
    a constant C such that the fiber character sum is at most C for all N.
    This implies o(N) trivially (C/N -> 0) but is much harder to prove. -/
def QuantitativeDSL : Prop :=
  PopulationEquidist →
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ),
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ C

/-- **QuantitativeDSL implies qualitative DSL.**
    A uniformly bounded character sum is trivially o(N): for any epsilon > 0,
    the bound C <= epsilon * N holds once N > C / epsilon. -/
theorem qdsl_implies_dsl (hqdsl : QuantitativeDSL) :
    DeterministicStabilityLemma := by
  intro hpe
  have hbody := hqdsl hpe
  intro q inst hq hne χ hχ a ε hε
  obtain ⟨C, hbd⟩ := @hbody q inst hq hne χ hχ a
  refine ⟨⌈C / ε⌉₊ + 1, fun N hN => ?_⟩
  calc ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖
      ≤ C := hbd N
    _ ≤ ε * (↑⌈C / ε⌉₊ + 1) := by
        calc C = ε * (C / ε) := by field_simp
          _ ≤ ε * (↑⌈C / ε⌉₊ + 1) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hε)
              have : C / ε ≤ ↑⌈C / ε⌉₊ := Nat.le_ceil (C / ε)
              linarith
    _ ≤ ε * N := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hε)
        have : (↑⌈C / ε⌉₊ + 1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith

/-- **QuantitativeDSL implies MC**, via the qualitative DSL chain. -/
theorem qdsl_implies_mc
    (h_equidist : ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q)
    (hqdsl : QuantitativeDSL) : MullinConjecture :=
  full_chain_dsl h_equidist (qdsl_implies_dsl hqdsl)

end QuantitativeDSL

/-! ## Section 3: Sieve Orbit Control

The multiplicative large sieve bounds character sums AVERAGED over moduli q:

    sum_{q <= Q} sum_{chi mod q} |S(chi)|^2 ≤ (N + Q^2) * sum |a_n|^2

This controls the TOTAL energy across all characters and all moduli. But for
DSL, we need control at EACH FIXED modulus q: for a specific q, the specific
character sums sum_n chi(m(n)) * 1_{w(n)=a} should be o(N).

The gap between "average over q" and "pointwise in q" is the orbit-specificity
barrier. It is the same obstruction that prevents proving Artin's conjecture
unconditionally: we can show that most integers a are primitive roots mod most
primes p (Chebotarev), but we cannot pin this to a specific a for all p.

Additionally, the EM multiplier seq(n+1) = minFac(prod(n)+1) is NOT a
multiplicative function of n. The large sieve is designed for sums of
multiplicative functions (Dirichlet characters, Mobius function). The minFac
function has no multiplicative structure, so the harmonic analysis that powers
the large sieve does not apply.

Dead End #90: orbit-specificity gap.
Dead End #108: Harper Brownian Dirichlet model inapplicable.
Dead End #109: Non-multiplicative Halasz methods fail. -/

section SieveOrbitControl

/-- **Sieve orbit control**: the hypothesis that large sieve bounds can be
    specialized to the specific EM orbit to control walk character sums at
    each fixed prime q. This is the Artin gap: it asks for pointwise-in-q
    control where only average-over-q tools are available.

    If true, it would give MC directly. But it cannot be proved from
    existing sieve technology because the EM orbit is a specific deterministic
    sequence, and sieves only control generic/average behavior.

    The statement is identical to ComplexCharSumBound (CCSB): walk character
    sums at each prime q are o(N).

    Dead End #90: orbit-specificity gap. -/
def SieveOrbitControl : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **SieveOrbitControl is definitionally ComplexCharSumBound** (CCSB).
    The sieve orbit control hypothesis, when formalized as pointwise walk
    character sum bounds, is exactly what CCSB asserts.

    This shows the sieve approach adds no new content: SieveOrbitControl IS
    the existing open hypothesis, just restated in sieve language.

    Dead End #90: orbit-specificity gap. -/
theorem sieve_orbit_control_eq_ccsb : SieveOrbitControl = ComplexCharSumBound := rfl

/-- **Sieve orbit control implies MC**, via the proved CCSB -> MC chain. -/
theorem sieve_orbit_control_implies_mc (h : SieveOrbitControl) :
    MullinConjecture :=
  complex_csb_mc' (sieve_orbit_control_eq_ccsb ▸ h)

/-- **MinFac is a MIN, not a product.**
    For n, m > 1: minFac(n * m) = min(minFac(n), minFac(m)).
    No coprimality hypothesis needed.

    Proof: (≤) minFac(n) | n | n*m, so minFac(n*m) ≤ minFac(n); same for m.
    (≥) minFac(n*m) is prime and divides n*m, so by Euclid's lemma it
    divides n or m, hence minFac of that factor ≤ minFac(n*m).

    This identity is why minFac cannot be analyzed with multiplicative
    number theory tools (Dirichlet series, Halász, pretentious distance):
    minFac is a lattice operation (min), not an algebraic one (product).

    Dead End #109: Non-multiplicative Halász methods fail. -/
theorem minFac_mul_eq_min {n m : ℕ} (hn : 1 < n) (hm : 1 < m) :
    Nat.minFac (n * m) = min (Nat.minFac n) (Nat.minFac m) := by
  apply le_antisymm
  · -- (≤) minFac(n*m) ≤ min(minFac n, minFac m)
    apply le_min
    · exact Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le
        ((Nat.minFac_dvd n).mul_right m)
    · exact Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le
        ((Nat.minFac_dvd m).mul_left n)
  · -- (≥) min(minFac n, minFac m) ≤ minFac(n*m)
    have hnm : 1 < n * m := one_lt_mul_of_lt_of_le hn (by omega)
    have hp := Nat.minFac_prime (by omega : n * m ≠ 1)
    have hdvd := Nat.minFac_dvd (n * m)
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact le_trans (min_le_left _ _)
        (Nat.minFac_le_of_dvd hp.two_le h)
    · exact le_trans (min_le_right _ _)
        (Nat.minFac_le_of_dvd hp.two_le h)

/-- **Corollary: minFac is NOT multiplicative.** -/
theorem minFac_not_multiplicative :
    ¬ ∀ (a b : ℕ), 1 < a → 1 < b → Nat.Coprime a b →
      Nat.minFac (a * b) = Nat.minFac a * Nat.minFac b := by
  push_neg
  exact ⟨6, 35, by omega, by omega, by native_decide, by native_decide⟩

end SieveOrbitControl

/-! ## Section 4: Collapse Certificates

This section provides formal certificates that the Markov chain and sieve
approaches collapse to existing infrastructure. Each certificate is a
definitional equality or a simple reduction showing the "new" hypothesis
is definitionally identical to an existing one. -/

section CollapseCertificates

/-- **Collapse certificate 1: Doeblin = CME.**
    The non-homogeneous Markov chain approach, when formalized, yields exactly
    ConditionalMultiplierEquidist. No new mathematical content is introduced. -/
theorem collapse_doeblin : DoeblinConvergenceForEM = ConditionalMultiplierEquidist :=
  doeblin_eq_cme

/-- **Collapse certificate 2: Sieve orbit control = CCSB.**
    The sieve approach, when specialized to the EM orbit for walk character
    sum bounds, yields exactly ComplexCharSumBound. No new mathematical content. -/
theorem collapse_sieve : SieveOrbitControl = ComplexCharSumBound :=
  sieve_orbit_control_eq_ccsb

/-- **Collapse certificate 3: Both approaches give MC via proved chains.**
    Neither approach introduces a genuinely new route to MC; both pass through
    existing proved reductions (CME -> CCSB -> MC or Dec -> CCSB -> MC). -/
theorem collapse_both_give_mc :
    (DoeblinConvergenceForEM → MullinConjecture) ∧
    (SieveOrbitControl → MullinConjecture) :=
  ⟨doeblin_implies_mc, sieve_orbit_control_implies_mc⟩

end CollapseCertificates

/-! ## Section 5: Definitive Landscape

The landscape theorem below witnesses ALL known routes to MC, including the
Markov chain and sieve approaches assessed here, and certifies that none of
them introduce new mathematical content beyond the existing infrastructure.

The routes are organized by their essential open hypothesis:

**Level 1** (irreducible): DH -> MC
**Level 2** (spectral): CME/CCSB/SVE -> MC
**Level 3** (population): PE + DSL -> MC
**Level 4** (Markov chain): DoeblinConvergenceForEM = CME -> MC (collapse)
**Level 5** (sieve): SieveOrbitControl = CCSB -> MC (collapse)
**Level 6** (quantitative): QuantitativeDSL -> DSL -> MC (strictly harder)
**Level 7** (spectral gap): SpectralGapForEMAverage -> CME -> MC (strictly harder) -/

section Landscape

/-- **Definitive landscape of Markov chain and sieve routes to MC.**

    All seven routes are witnessed. The key facts are:
    1. DSL alone implies MC (the master reduction, proved)
    2. CME implies MC (proved: CME -> CCSB -> MC)
    3. QuantitativeDSL implies DSL (quantitative is strictly stronger)
    4. SieveOrbitControl = ComplexCharSumBound (definitional collapse)
    5. DoeblinConvergenceForEM = CME (definitional collapse)
    6. SpectralGap implies Doeblin = CME (exponential implies sublinear)
    7. Adelic decomposition: CME decomposes as MWI + MME

    No new route to MC is opened by the Markov chain or sieve approaches.
    The sole remaining gap is DSL: PopulationEquidist -> CME. -/
theorem markov_sieve_landscape :
    -- Route 1: DSL alone implies MC (master reduction)
    (DeterministicStabilityLemma →
      (∀ q, Nat.Prime q → MinFacResidueEquidist q) →
      MullinConjecture) ∧
    -- Route 2: CME directly implies MC
    (ConditionalMultiplierEquidist → MullinConjecture) ∧
    -- Route 3: QuantitativeDSL implies DSL (stronger, not easier)
    (QuantitativeDSL → DeterministicStabilityLemma) ∧
    -- Route 4: SieveOrbitControl = ComplexCharSumBound (collapse)
    (SieveOrbitControl = ComplexCharSumBound) ∧
    -- Route 5: DoeblinConvergenceForEM = CME (collapse)
    (DoeblinConvergenceForEM = ConditionalMultiplierEquidist) ∧
    -- Route 6: SpectralGap -> CME (strictly stronger)
    (SpectralGapForEMAverage → ConditionalMultiplierEquidist) ∧
    -- Route 7: SieveOrbitControl -> MC (via CCSB -> MC)
    (SieveOrbitControl → MullinConjecture) :=
  ⟨fun hdsl heq => full_chain_dsl heq hdsl,
   cme_implies_mc,
   qdsl_implies_dsl,
   sieve_orbit_control_eq_ccsb,
   doeblin_eq_cme,
   fun h => doeblin_eq_cme ▸ spectral_gap_implies_doeblin h,
   sieve_orbit_control_implies_mc⟩

end Landscape

/-! ## Section 6: Dead End Documentation

### Dead End #90 (orbit-specificity gap)
The large sieve controls character sum energy AVERAGED over moduli q ≤ Q.
DSL needs control at each FIXED q. The gap between average and pointwise
is the orbit-specificity barrier, analogous to the gap between Chebotarev
density theorem (average) and Artin's conjecture (pointwise).

### Dead End #95 (spectral gap for deterministic walks)
The EM walk at each step is a deterministic multiplication by m(n) on (Z/qZ)*.
A spectral gap requires a FIXED random walk operator with a gap between its
first and second eigenvalues. The EM walk has no such operator -- the transition
changes at every step. Time-averaged spectral gap IS CME.

### Dead End #108 (Harper BDH inapplicable)
The Harper-style Brownian Dirichlet model gives distributional results about
RANDOM L-functions. The EM sequence is deterministic; distributional results
about random models do not constrain specific deterministic sequences.

### Dead End #109 (non-multiplicative Halasz)
Halasz's theorem bounds mean values of multiplicative functions. The function
n -> minFac(n) is not multiplicative (it takes the MIN of prime factors, not
the product). No multiplicative number theory tool applies directly.

### Dead End #110 (transition matrix convergence = CME)
Asking the empirical transition matrix of the EM walk to converge to the
uniform matrix is exactly asking for CME. The Markov chain language is a
cosmetic relabeling with no mathematical content.

### Assessment
Both the Markov chain and sieve approaches were assessed at 0/10 feasibility
for providing new mathematical content. All formulations collapse to existing
open hypotheses (CME or DecorrelationHypothesis). The sole remaining gap
remains DSL: PopulationEquidist -> ConditionalMultiplierEquidist. -/

/-! ## Section 7: Relationship to Adelic Framework

The adelic framework (AdelicEquidist.lean) decomposes CME as MWI + MME:
- MWI (MultWalkIndependence): multiplier independent of walk position (structural)
- MME (MultiplierMarginalEquidist): unconditional multiplier char sums vanish (analytic)

The Doeblin approach attempts to prove CME directly (= MWI + MME combined).
The sieve approach attempts to prove MME (= DecorrelationHypothesis) directly.
Neither provides leverage on MWI (the structural independence component). -/

section AdelicRelationship

/-- **Sieve orbit control is exactly CCSB** (ComplexCharSumBound).
    The sieve approach, when formalized as walk character sum bounds, targets
    the walk-level cancellation. CCSB is strictly stronger than MME
    (multiplier marginal equidist) since walk sums involve walk position
    modulation. The sieve approach bypasses the MWI/MME decomposition entirely
    by targeting the combined walk character sum. -/
theorem sieve_orbit_is_ccsb :
    SieveOrbitControl = ComplexCharSumBound :=
  sieve_orbit_control_eq_ccsb

/-- **Doeblin targets the full CME** (MWI + MME combined).
    The Markov chain approach, when formalized, is equivalent to asserting both
    MWI and MME simultaneously. It is therefore at least as hard as the hardest
    component. -/
theorem doeblin_is_full_cme :
    DoeblinConvergenceForEM = ConditionalMultiplierEquidist :=
  doeblin_eq_cme

/-- **Neither approach provides new leverage.**
    - Sieve approach: targets CCSB (walk character sums). This is exactly
      the existing open hypothesis, restated in sieve language.
    - Markov chain approach: targets CME (conditional multiplier equidist).
      Equivalent to the existing open problem, with no decomposition advantage.
    - Adelic approach: at least DECOMPOSES CME into MWI + MME, allowing
      independent attacks. The adelic framework is therefore preferable
      to the monolithic Markov chain formulation.

    We witness this by showing both approaches imply MC via proved chains,
    and the adelic decomposition provides strictly more structure. -/
theorem no_new_leverage :
    -- Both approaches give MC (via existing chains)
    (DoeblinConvergenceForEM → MullinConjecture) ∧
    (SieveOrbitControl → MullinConjecture) ∧
    -- The adelic decomposition is strictly more informative
    (ConditionalMultiplierEquidist ↔ AdelicEquidist) :=
  ⟨doeblin_implies_mc, sieve_orbit_control_implies_mc, cme_iff_adelic⟩

end AdelicRelationship

end -- noncomputable section
