import EM.Population.HittingSetStructure
import EM.Population.SpectralConspiracy

/-!
# Rigidity Master Theorems

Assembles the rigidity results from the Population module into tiered
master theorems that characterize the structural consequences of missing
primes in the Euclid-Mullin sequence.

## Main Results

### Tier A: Unconditional from |M| = infinity
* `rigidity_tier_A` : consequences of infinitely many missing primes
  (dichotomy, guardian structure, active/inactive classification,
  hitting multiplicity bounds, large finite subsets, spectral conspiracy)

### Tier B: Under not WeakMullin
* `rigidity_tier_B` : everything in Tier A plus tube collapse,
  joint excess energy divergence, guardian demand exceeds capacity

### Master Assembly
* `rigidity_master` : not MC gives nonempty MissingPrimes and either
  WM or full Tier B structural rigidity
* `rigidity_landscape` : five-clause conjunction summarizing all routes
-/

open Mullin Euclid MullinGroup RotorRouter
open Classical

/-! ## Tier A: Unconditional Rigidity from |M| = infinity -/

section TierA

/-- **Tier A rigidity**: unconditional consequences of infinitely many
    missing primes. No assumption on WeakMullin is needed.

    (1) Every missing prime has the shielded/avoidance dichotomy
    (2) Hitting step guardians: at hitting steps, seq(n+1) < q
    (3) Active/inactive classification of steps is exhaustive
    (4) Hitting multiplicity bounded by |F|
    (5) Arbitrarily many missing primes exist (each at least 3)
    (6) Spectral conspiracy: perpetual avoidance gives rogue characters -/
theorem rigidity_tier_A (hInf : Set.Infinite MissingPrimes) :
    -- (1) SH/EPA dichotomy for each missing prime
    (∀ q, q ∈ MissingPrimes → ShieldedHitting q ∨ EventualPerpetualAvoidance q) ∧
    -- (2) Guardian at hitting steps
    (∀ q, q ∈ MissingPrimes → ∀ n, n ∈ HittingSet q → seq (n + 1) < q) ∧
    -- (3) Active/inactive classification
    (∀ n, GuardianActive n ∨ GuardianInactive n) ∧
    -- (4) Hitting multiplicity bounded
    (∀ n F, hittingMultiplicity n F ≤ F.card) ∧
    -- (5) Arbitrarily many missing primes (each at least 3)
    (∀ k : Nat, ∃ F : Finset Nat, k ≤ F.card ∧
      (∀ q ∈ F, q ∈ MissingPrimes) ∧ (∀ q ∈ F, 3 ≤ q)) ∧
    -- (6) Spectral conspiracy under perpetual avoidance
    ((∀ q ∈ MissingPrimes, PerpetualAvoidance q) →
      ∀ k : Nat, ∃ Q : Finset Nat,
        Q.card = k ∧ (↑Q : Set Nat) ⊆ MissingPrimes ∧
        ∀ q ∈ Q, ∃ (_hq_prime : Nat.Prime q),
          ∃ χ : DirichletCharacter ℂ q, χ ≠ 1) := by
  refine ⟨fun q hq => perpetual_avoidance_dichotomy hq,
    fun q hq n hn => hitting_step_guardian hq hn,
    guardian_active_or_inactive,
    hittingMultiplicity_le,
    ?_, ?_⟩
  -- (5) Arbitrarily many missing primes
  · intro k
    obtain ⟨T, hTsub, hTcard⟩ := hInf.exists_subset_card_eq k
    refine ⟨T, le_of_eq hTcard.symm, fun q hq => hTsub (Finset.mem_coe.mpr hq),
      fun q hq => missing_prime_ge_three (hTsub (Finset.mem_coe.mpr hq))⟩
  -- (6) Spectral conspiracy
  · intro hPA
    exact (infiniteSpectralConspiracy hInf hPA)

end TierA

/-! ## Tier B: Under not WeakMullin -/

section TierB

/-- **Tier B rigidity**: under the negation of WeakMullin, all of Tier A
    holds plus additional quantitative consequences.

    (1) MissingPrimes is infinite
    (2) Tube ratio collapses to 0
    (3) Joint excess energy diverges
    (4) Guardian demand exceeds any finite capacity
    (5) SH/EPA dichotomy for each missing prime
    (6) Hitting step guardians -/
theorem rigidity_tier_B (hnwm : ¬ WeakMullin) :
    -- (1) MissingPrimes is infinite
    Set.Infinite MissingPrimes ∧
    -- (2) Tube ratio collapses
    (∀ ε : ℝ, 0 < ε → ∃ F : Finset Nat,
      (∀ q ∈ F, q ∈ MissingPrimes) ∧ tubeRatio F < ε) ∧
    -- (3) Joint excess energy diverges
    (∀ C : ℝ, ∃ F : Finset Nat, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      C < ∑ q ∈ F, Real.log (((q : ℝ) - 1) / ((q : ℝ) - 2))) ∧
    -- (4) Guardian demand exceeds capacity
    (∀ B : ℝ, ∃ F : Finset Nat, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      B < ∑ q ∈ F, (1 : ℝ) / ((q : ℝ) - 1)) ∧
    -- (5) SH/EPA dichotomy
    (∀ q, q ∈ MissingPrimes → ShieldedHitting q ∨ EventualPerpetualAvoidance q) ∧
    -- (6) Hitting step guardians
    (∀ q, q ∈ MissingPrimes → ∀ n, n ∈ HittingSet q → seq (n + 1) < q) := by
  have hInf := not_wm_implies_missing_infinite hnwm
  have hA := rigidity_tier_A hInf
  exact ⟨hInf,
    fun ε hε => tube_squeeze hnwm ε hε,
    joint_excess_energy_diverges hnwm,
    guardian_demand_exceeds_capacity hnwm,
    hA.1,
    hA.2.1⟩

/-- Tier B implies Tier A. -/
theorem tier_B_implies_tier_A (hnwm : ¬ WeakMullin) :
    Set.Infinite MissingPrimes := (rigidity_tier_B hnwm).1

end TierB

/-! ## Master Assembly -/

section Master

/-- **Rigidity master theorem**: if MC fails, then MissingPrimes is
    nonempty. Moreover, either WeakMullin holds (finitely many missing
    primes with convergent reciprocal sum), or the full Tier B rigidity
    obtains (infinitely many missing primes with tube collapse, energy
    divergence, and guardian exhaustion).

    This gives a complete structural dichotomy for the negation of MC. -/
theorem rigidity_master (hnmc : ¬ MullinConjecture) :
    -- Missing primes exist
    Set.Nonempty MissingPrimes ∧
    -- Either WM or full Tier B
    (WeakMullin ∨
      (¬ WeakMullin ∧ Set.Infinite MissingPrimes ∧
        (∀ q, q ∈ MissingPrimes → ShieldedHitting q ∨ EventualPerpetualAvoidance q) ∧
        (∀ ε : ℝ, 0 < ε → ∃ F : Finset Nat,
          (∀ q ∈ F, q ∈ MissingPrimes) ∧ tubeRatio F < ε))) := by
  refine ⟨not_mc_nonempty_missing hnmc, ?_⟩
  by_cases hwm : WeakMullin
  · left; exact hwm
  · right
    have hB := rigidity_tier_B hwm
    exact ⟨hwm, hB.1, hB.2.2.2.2.1, hB.2.1⟩

/-- **Tier B closure**: if MC fails and WeakMullin also fails,
    then the spectral conspiracy landscape holds in full
    (from SpectralConspiracy.lean). -/
theorem tier_B_spectral_closure (_hnmc : ¬ MullinConjecture) (hnwm : ¬ WeakMullin) :
    -- Spectral conspiracy landscape
    Set.Infinite MissingPrimes ∧
    (∀ C : ℝ, ∃ F : Finset ℕ, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      C < ∑ q ∈ F, Real.log (((q : ℝ) - 1) / ((q : ℝ) - 2))) ∧
    (∀ B : ℝ, ∃ F : Finset ℕ, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      B < ∑ q ∈ F, (1 : ℝ) / ((q : ℝ) - 1)) ∧
    (∀ k : ℕ, ∃ F : Finset ℕ, k ≤ F.card ∧
      (∀ q ∈ F, q ∈ MissingPrimes) ∧ (∀ q ∈ F, 3 ≤ q)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ,
      (∀ q ∈ F, q ∈ MissingPrimes) ∧ tubeRatio F < ε) ∧
    (∀ C : ℝ, ∃ F : Finset ℕ, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      C ≤ ∏ q ∈ F, (((q : ℝ) - 1) / ((q : ℝ) - 2))) :=
  spectral_conspiracy_landscape hnwm

end Master

/-! ## Landscape -/

section Landscape

/-- **Rigidity landscape**: five-clause conjunction summarizing the
    key structural results across all tiers.

    (1) not MC implies MissingPrimes nonempty
    (2) MissingFinite implies WeakMullin
    (3) not WeakMullin implies MissingPrimes infinite
    (4) Every missing prime has the SH/EPA dichotomy
    (5) Shielding lemma: seq(n+1) is never a missing prime -/
theorem rigidity_landscape :
    -- (1) not MC implies nonempty
    (¬ MullinConjecture → Set.Nonempty MissingPrimes) ∧
    -- (2) MissingFinite implies WM
    (MissingFinite → WeakMullin) ∧
    -- (3) not WM implies infinite
    (¬ WeakMullin → Set.Infinite MissingPrimes) ∧
    -- (4) Every missing prime has dichotomy
    (∀ q, q ∈ MissingPrimes → ShieldedHitting q ∨ EventualPerpetualAvoidance q) ∧
    -- (5) Shielding lemma
    (∀ n, seq (n + 1) ∉ MissingPrimes) :=
  ⟨not_mc_nonempty_missing,
   missing_finite_implies_wm,
   not_wm_implies_missing_infinite,
   fun _ hq => perpetual_avoidance_dichotomy hq,
   shielding_lemma⟩

end Landscape
