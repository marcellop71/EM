import EM.CRTPointwiseTransfer
import EM.EnsembleStructure

/-!
# Substitution Principle: Fiber Return Visit Infrastructure

This file formalizes the **Substitution Principle (SP)** and proves that it
equals CME and implies MC. The key structural observation:

At each return visit to a fiber (steps where walkZ q n = a), the multiplier
seq(n+1) is a *distinct prime* (by `seq_injective`) and the multiplier primes
at distinct return visits are *pairwise coprime* (by `seq_coprime_of_distinct`).

SP is definitionally equal to CME (`sp_eq_cme`). **Caveat**: the coprime
cascade structure alone does NOT force character cancellation—explicit
counterexamples exist for general coprime sequences. The cancellation in
SP/CME, if true, relies on the specific EM feedback dynamics.

## Main Results

### Fiber Return Infrastructure (Proved)
* `fiberReturnSteps`                   : indices where walkZ q n = a
* `fiberReturnSteps_card_le`           : card ≤ N
* `mem_fiberReturnSteps_iff`           : membership characterization
* `return_visit_seq_distinct`          : seq(j+1) ≠ seq(k+1) at distinct visits
* `fiberReturnSteps_eq_filter`         : definitional equality with fiberMultCharSum filter

### Substitution Principle (Open Prop)
* `SubstitutionPrinciple`              : character sums over coprime fiber primes cancel

### Reductions (Proved)
* `substitution_principle_implies_cme` : SP → CME
* `substitution_principle_implies_mc`  : SP → MC (via CME → CCSB → MC)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

open scoped BigOperators

/-! ## Section 1: Fiber Return Visit Infrastructure -/

section FiberReturn

/-- The set of indices n < N where the walk position equals a given unit.
    These are the "return visit" steps to the fiber at position a. -/
def fiberReturnSteps (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N : Nat) : Finset Nat :=
  (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)

/-- The cardinality of fiberReturnSteps is at most N (it is a subset of range N). -/
theorem fiberReturnSteps_card_le (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N : Nat) :
    (fiberReturnSteps q hq hne a N).card ≤ N := by
  calc (fiberReturnSteps q hq hne a N).card
      ≤ (Finset.range N).card := Finset.card_filter_le _ _
    _ = N := Finset.card_range N

/-- Membership characterization for fiberReturnSteps. -/
theorem mem_fiberReturnSteps_iff {q : Nat} [Fact (Nat.Prime q)] {hq : IsPrime q}
    {hne : ∀ k, seq k ≠ q} {a : (ZMod q)ˣ} {N k : Nat} :
    k ∈ fiberReturnSteps q hq hne a N ↔ k < N ∧ emWalkUnit q hq hne k = a := by
  simp [fiberReturnSteps, Finset.mem_filter, Finset.mem_range]

/-- At distinct return visits, the sequence terms (multiplier primes) are distinct.
    This is immediate from `seq_injective`: the EM sequence never repeats a prime,
    so distinct indices give distinct values. -/
theorem return_visit_seq_distinct {j k : Nat} (hjk : j ≠ k) :
    seq (j + 1) ≠ seq (k + 1) :=
  distinct_primes_at_returns hjk

/-- The fiberReturnSteps filter is exactly the filter used in fiberMultCharSum.
    This connects our infrastructure to the central CME quantity. -/
theorem fiberReturnSteps_eq_filter (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N : Nat) :
    fiberReturnSteps q hq hne a N =
    (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a) :=
  rfl

/-- The fiber character sum equals the sum over return visit steps.
    This is definitionally true — the sum in fiberMultCharSum ranges
    over exactly the same filtered set as fiberReturnSteps. -/
theorem fiberMultCharSum_eq_sum_over_returns (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : Nat) :
    fiberMultCharSum q hq hne χ a N =
    ∑ n ∈ fiberReturnSteps q hq hne a N, (χ (emMultUnit q hq hne n) : ℂ) :=
  rfl

end FiberReturn

/-! ## Section 2: Coprime Cascade at Return Visits -/

section CoprimeCascade

/-- At return visits, the multiplier primes are pairwise distinct.
    The function n ↦ seq(n+1) is injective on fiberReturnSteps
    (indeed on all of ℕ, by seq_injective). -/
theorem return_visit_mult_injective (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N : Nat) :
    Set.InjOn (fun n => seq (n + 1)) ↑(fiberReturnSteps q hq hne a N) := by
  intro j _hj k _hk hjk
  exact Nat.succ_injective (seq_injective _ _ hjk)

/-- At return visits, distinct multiplier primes are coprime.
    Since all seq values are pairwise coprime (seq_coprime_of_distinct),
    the multiplier primes at distinct return visits are also coprime. -/
theorem return_visit_mult_coprime {j k : Nat} (hjk : j ≠ k) :
    Nat.Coprime (seq (j + 1)) (seq (k + 1)) :=
  seq_coprime_of_distinct (fun h => hjk (Nat.succ_injective h))

end CoprimeCascade

/-! ## Section 3: Fiber Structure at Return Visits -/

section FiberStructure

/-- At a return visit n ∈ fiberReturnSteps, the walk position walkZ q n
    equals ↑a (the coercion of the unit a to ZMod q).
    This means prod(n) ≡ a (mod q). -/
theorem walkZ_at_return {q : Nat} [Fact (Nat.Prime q)] {hq : IsPrime q}
    {hne : ∀ k, seq k ≠ q} {a : (ZMod q)ˣ} {N n : Nat}
    (hn : n ∈ fiberReturnSteps q hq hne a N) :
    walkZ q n = ↑a := by
  rw [mem_fiberReturnSteps_iff] at hn
  have heq := hn.2
  -- emWalkUnit q hq hne n = Units.mk0 (walkZ q n) ... = a
  -- So walkZ q n = ↑a as ZMod q elements
  have : (emWalkUnit q hq hne n : ZMod q) = ↑a := congrArg Units.val heq
  simp only [emWalkUnit, Units.val_mk0] at this
  exact this

/-- At a return visit, the Euclid number prod(n)+1 is in a fixed residue
    class mod q: namely, it is ≡ a + 1 (mod q).
    This follows from walkZ q n = (prod n : ZMod q) = ↑a. -/
theorem euclid_residue_at_return {q : Nat} [Fact (Nat.Prime q)] {hq : IsPrime q}
    {hne : ∀ k, seq k ≠ q} {a : (ZMod q)ˣ} {N n : Nat}
    (hn : n ∈ fiberReturnSteps q hq hne a N) :
    (prod n + 1 : ZMod q) = ↑a + 1 := by
  have hw := walkZ_at_return hn
  simp only [walkZ] at hw
  -- hw : (prod n : ZMod q) = ↑a
  exact congrArg (· + 1) hw

/-- The multiplier at a return visit is seq(n+1), which divides prod(n)+1.
    Combined with the coprime cascade, the multiplier primes at distinct
    return visits are pairwise coprime factors of Euclid numbers in a
    fixed residue class mod q. -/
theorem mult_dvd_euclid_at_return (n : Nat) :
    seq (n + 1) ∣ prod n + 1 :=
  seq_dvd_succ_prod n

end FiberStructure

/-! ## Section 4: Substitution Principle — Open Prop -/

section SP

/-- **Substitution Principle**: Character sums over multiplier residues at
    fiber return visits cancel.

    Concretely: for any prime q not in the EM sequence, any nontrivial
    character chi of (Z/qZ)*, any walk position a, and any epsilon > 0,
    eventually (for N large enough) the fiber character sum satisfies
    ||sum_{n in fiber(a,N)} chi(m(n))|| <= epsilon * N.

    This is equivalent to CME (ConditionalMultiplierEquidist) by definition
    (see `sp_eq_cme`). The structural properties at return visits are:
    1. The primes are distinct (by seq_injective)
    2. They are coprime to each other (by seq_coprime_of_distinct)
    3. The underlying integers (Euclid numbers) are in a fixed class mod q
    4. minFac is "q-blind" (by crt_multiplier_invariance)

    **Caveat**: These structural properties alone do NOT force cancellation.
    For any q ≥ 3, one can construct pairwise coprime integers in a fixed
    residue class whose minFac values all lie in the same class mod q
    (e.g. N_i = p_i·r_i with p_i ≡ 2, r_i ≡ 3 mod 5 gives Θ(I) character
    sums). The cancellation in SP/CME, if true, must rely on the specific
    feedback dynamics of the EM sequence, not merely on coprimality. -/
def SubstitutionPrinciple : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ fiberReturnSteps q hq hne a N,
      (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

end SP

/-! ## Section 5: SP ⟹ CME ⟹ MC -/

section SPChain

/-- **SP is equivalent to CME**: the Substitution Principle is definitionally
    the same as ConditionalMultiplierEquidist, since fiberReturnSteps
    is the same filter as in CME and the sums are identical.

    The SP name emphasizes the *mechanism* (coprime cascade + q-blindness),
    while CME emphasizes the *conclusion* (conditional equidistribution).
    But the mathematical statements are identical. -/
theorem sp_eq_cme : SubstitutionPrinciple = ConditionalMultiplierEquidist := by
  simp only [SubstitutionPrinciple, ConditionalMultiplierEquidist,
    fiberReturnSteps_eq_filter]

/-- **SP implies CME**: the Substitution Principle gives Conditional
    Multiplier Equidistribution. -/
theorem substitution_principle_implies_cme (hsp : SubstitutionPrinciple) :
    ConditionalMultiplierEquidist :=
  sp_eq_cme ▸ hsp

/-- **SP implies MC**: the Substitution Principle gives Mullin's Conjecture
    via the chain SP = CME → CCSB → MC. -/
theorem substitution_principle_implies_mc (hsp : SubstitutionPrinciple) :
    MullinConjecture :=
  cme_implies_mc (substitution_principle_implies_cme hsp)

/-- **SP implies CCSB**: the Substitution Principle gives the Complex
    Character Sum Bound, an intermediate step toward MC. -/
theorem substitution_principle_implies_ccsb (hsp : SubstitutionPrinciple) :
    ComplexCharSumBound :=
  cme_implies_ccsb (substitution_principle_implies_cme hsp)

/-- **All routes to MC — augmented**: adding the SP route to the existing
    landscape of CME-based reductions.

    - DSL:  PE → CME → MC
    - CRT:  PCE + Bridge → OCE = CME → MC
    - EMD:  EMD + EMDImpliesCME → CME → MC
    - SP:   SubstitutionPrinciple = CME → MC  (new) -/
theorem all_routes_to_mc_with_sp :
    (SubstitutionPrinciple → MullinConjecture) ∧
    (DeterministicStabilityLemma → PopulationEquidist → MullinConjecture) ∧
    (CRTPointwiseTransferBridge → PopulationConditionalEquidist → MullinConjecture) ∧
    (EMDImpliesCME → EMDirichlet → MullinConjecture) :=
  ⟨substitution_principle_implies_mc,
   fun hdsl hpe => pe_dsl_implies_mc hpe hdsl,
   fun hbridge hpce => pce_bridge_implies_mc hpce hbridge,
   fun hcme hemd => emd_cme_implies_mc hcme hemd⟩

end SPChain

/-! ## Section 6: Structural Lemmas — Why SP is Plausible -/

section SPStructure

/-- The number of distinct multiplier primes at return visits equals
    the number of return visits. This follows from injectivity of
    n ↦ seq(n+1) on the return visit set. -/
theorem return_visit_distinct_primes_count (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N : Nat) :
    ((fiberReturnSteps q hq hne a N).image (fun n => seq (n + 1))).card =
    (fiberReturnSteps q hq hne a N).card := by
  apply Finset.card_image_of_injective
  intro j k hjk
  exact Nat.succ_injective (seq_injective _ _ hjk)

/-- All multiplier primes at return visits are pairwise coprime.
    This is the coprime cascade specialized to the fiber: the function
    n ↦ seq(n+1) produces pairwise coprime values on fiberReturnSteps. -/
theorem return_visit_pairwise_coprime (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N : Nat) :
    ∀ j ∈ fiberReturnSteps q hq hne a N,
    ∀ k ∈ fiberReturnSteps q hq hne a N,
    j ≠ k → Nat.Coprime (seq (j + 1)) (seq (k + 1)) :=
  fun _ _ _ _ hjk => return_visit_mult_coprime hjk

/-- All multiplier primes at return visits are genuinely prime.
    This is just `seq_isPrime` applied at the appropriate index. -/
theorem return_visit_mult_prime (n : Nat) :
    IsPrime (seq (n + 1)) :=
  seq_isPrime (n + 1)

/-- The SP mechanism in summary: the fiber character sum
    ∑_{n ∈ fiber(a,N)} chi(m(n)) is a sum of chi-values at distinct,
    pairwise coprime primes, all dividing Euclid numbers in a fixed
    residue class mod q. The SP asserts this sum cancels. -/
theorem sp_structural_summary (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (a : (ZMod q)ˣ) (N : Nat) :
    -- (1) Distinct primes:
    (Set.InjOn (fun n => seq (n + 1)) ↑(fiberReturnSteps q hq hne a N)) ∧
    -- (2) Pairwise coprime:
    (∀ j ∈ fiberReturnSteps q hq hne a N,
     ∀ k ∈ fiberReturnSteps q hq hne a N,
     j ≠ k → Nat.Coprime (seq (j + 1)) (seq (k + 1))) ∧
    -- (3) All prime:
    (∀ n ∈ fiberReturnSteps q hq hne a N, IsPrime (seq (n + 1))) ∧
    -- (4) All divide Euclid numbers:
    (∀ n ∈ fiberReturnSteps q hq hne a N, seq (n + 1) ∣ prod n + 1) :=
  ⟨return_visit_mult_injective q hq hne a N,
   return_visit_pairwise_coprime q hq hne a N,
   fun n _ => return_visit_mult_prime n,
   fun n _ => mult_dvd_euclid_at_return n⟩

end SPStructure

end -- noncomputable section
