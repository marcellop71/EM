import EM.Equidist.OneHorizon
import EM.Population.HittingSetStructure
import EM.Stochastic.ReachableSets
import EM.Stochastic.RandomFactorMC

/-!
# The Weakest Orbit Target: Every Prime Divides Some Euclid Number

Mullin's conjecture asks that every prime be *selected*.  Selection is two conditions at
once: the prime must divide a Euclid number, and it must be the least factor when it does.
This file isolates the first condition on its own.

> **(V)** For every odd prime `q`, some Euclid number is divisible by `q`:
> `HittingSet q ≠ ∅`.

Equivalently: keep the standard `minFac` accumulator, but count a prime as captured as
soon as it divides `Pₙ + 1`, whether or not it is the factor selected.  The dynamics is
untouched; only the notion of success is widened.

## Why this is the right weakening

Two properties are in tension across the selection rules.  A rule that grows the
accumulator slowly gives each prime many trials; a rule that captures generously removes
the selection barrier.  `minFac` has the first and not the second; taking *all* factors has
the second and destroys the first, since the accumulator then satisfies
`Pₙ₊₁ = Pₙ(Pₙ+1)`, closes into the autonomous map `w ↦ w² + w`, and provably misses every
prime `q ≡ 2 (mod 3)` (the mechanism of Dead End~#146).

(V) takes both: the accumulator is the standard one, and capture is generous.

## The ladder

`HittingHypothesis ⟹ MullinConjecture ⟹ (V) ⟹ (−1 reachable in the factor tree)`.

The first arrow is `Mullin.hh_implies_mullin`, the second `mullin_implies_everyPrimeDividesEuclid`
below, the third `everyPrimeDividesEuclid_implies_reachable`.  (V) is the missing rung: the
repository already carried the outer three.

`HittingHypothesis` asks for *cofinally many* hits, `MullinConjecture` for a hit at a step
where `q` is minimal, and (V) for **one hit, ever**.  That makes (V) the weakest orbit
statement in the project.

## What it does not buy

(V) changes what counts as success, not the object: the accumulator is the same single
deterministic orbit, so the orbit-specificity barrier (Dead End~#90) applies verbatim, and
`SubgroupEscape` still does not suffice because generation is not coverage (Dead
Ends~#20, #130).  Empirically the gain is real but concentrated on the easy primes: after
seven steps the generous rule has captured `139`, `443` and `248867` ahead of the min
rule, while `19, 23, 29, 31, 37, 41` divide none of the first thirteen Euclid numbers.

Its payoff is as a *target*: (V) follows from a single Fourier window per prime
(`OneWindowGain`), with no cofinality and no first-missing-prime bootstrap — strictly less
than `OneHorizon.WindowFourierGain` demands.
-/

noncomputable section

open Mullin Euclid MullinGroup
open scoped Classical

namespace WeakHitting

/-- **(V)**: every odd prime divides some Euclid number.  The parity restriction is
forced — `Pₙ` is always even, so `Pₙ + 1` is always odd and `2` divides no Euclid number;
`2` is the seed, not a capture. -/
def EveryPrimeDividesEuclid : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ≠ 2 → ∃ n, q ∣ prod n + 1

/-- (V) restated with the repository's `HittingSet`. -/
theorem everyPrimeDividesEuclid_iff_hittingSet :
    EveryPrimeDividesEuclid ↔
      ∀ q : ℕ, Nat.Prime q → q ≠ 2 → (HittingSet q).Nonempty := by
  constructor
  · intro h q hq h2
    obtain ⟨n, hn⟩ := h q hq h2
    exact ⟨n, hn⟩
  · intro h q hq h2
    obtain ⟨n, hn⟩ := h q hq h2
    exact ⟨n, hn⟩

/-! ## Upper rung: Mullin's conjecture implies (V) -/

/-- **MC ⟹ (V)**: a selected prime divides the Euclid number it was selected from. -/
theorem mullin_implies_everyPrimeDividesEuclid (hmc : MullinConjecture) :
    EveryPrimeDividesEuclid := by
  intro q hq h2
  obtain ⟨k, hk⟩ := hmc q ((isPrime_iff_natPrime q).mpr hq)
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := by
    cases k with
    | zero => exact absurd (by rw [seq_zero] at hk; exact hk.symm) h2
    | succ n => exact ⟨n, rfl⟩
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  refine ⟨n, ?_⟩
  rw [← hk, seq_succ, euclid_minFac_eq_nat_minFac _ hge]
  exact Nat.minFac_dvd _

/-! ## Lower rung: (V) implies reachability in the factor tree

The standard orbit is one branch of the mixed walk, so a hit on the standard orbit is in
particular a position reachable in the factor tree from the root. -/

/-- **(V) ⟹ the death class is reachable in the factor tree from `2`.** -/
theorem everyPrimeDividesEuclid_implies_reachable (h : EveryPrimeDividesEuclid)
    {q : ℕ} [NeZero q] (hq : Nat.Prime q) (h2 : q ≠ 2) :
    (-1 : ZMod q) ∈ reachableEver q 2 := by
  obtain ⟨n, hn⟩ := h q hq h2
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  refine ⟨minFacMixed, minFacMixed_valid 2, ?_⟩
  rw [mixedWalkProd_two_minFac_eq_prod]
  have : ((prod n + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hn
  push_cast at this
  linear_combination this

/-! ## The weakest Fourier criterion

`OneHorizon.WindowFourierGain` demands a good window past *every* stage, because Mullin's
conjecture needs the first-missing-prime bootstrap.  For (V) one window suffices, anywhere,
once per prime. -/

/-- **OneWindowGain**: for each prime never selected, *some* window on which the
nontrivial character sums total less than its length. -/
def OneWindowGain : Prop :=
  ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∃ N₀ N : ℕ, 0 < N ∧
      ∑ f ∈ Finset.univ.erase (1 : (ZMod q)ˣ →* ℂˣ),
        ‖∑ j ∈ Finset.range N, (f (emWalkUnit q hq hne (N₀ + j)) : ℂ)‖ < (N : ℝ)

/-- The window criterion of `OneHorizon` is strictly stronger: it supplies a window past
every stage, whereas `OneWindowGain` asks for one. -/
theorem windowFourierGain_implies_oneWindowGain
    (h : OneHorizon.WindowFourierGain) : OneWindowGain := by
  intro q _ hq hne
  obtain ⟨N, hNpos, hN⟩ := h q hq hne 0
  exact ⟨0, N, hNpos, hN⟩

/-- **One window per prime suffices for (V).**  A prime that is selected divides its own
Euclid number; a prime that is never selected has a unit walk, and one good window forces
that walk to cover every unit, in particular the death class. -/
theorem oneWindowGain_implies_V (h : OneWindowGain) : EveryPrimeDividesEuclid := by
  intro q hq h2
  have : Fact (Nat.Prime q) := ⟨hq⟩
  by_cases hex : ∃ k, seq k = q
  · -- selected: the standard argument
    obtain ⟨k, hk⟩ := hex
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := by
      cases k with
      | zero => exact absurd (by rw [seq_zero] at hk; exact hk.symm) h2
      | succ n => exact ⟨n, rfl⟩
    have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
    exact ⟨n, by rw [← hk, seq_succ, euclid_minFac_eq_nat_minFac _ hge]; exact Nat.minFac_dvd _⟩
  · -- never selected: the walk is a unit walk, and one window covers everything
    have hne : ∀ k, seq k ≠ q := fun k hk => hex ⟨k, hk⟩
    have hqp : IsPrime q := (isPrime_iff_natPrime q).mpr hq
    obtain ⟨N₀, N, hNpos, hN⟩ := h q hqp hne
    have hunit : IsUnit (-1 : ZMod q) := (isUnit_one).neg
    obtain ⟨n, _, hval⟩ :=
      OneHorizon.covers_of_charSum_lt
        (fun j => emWalkUnit q hqp hne (N₀ + j)) N hN hunit.unit
    refine ⟨N₀ + n, ?_⟩
    have hw : walkZ q (N₀ + n) = -1 := by
      have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hval
      simpa [emWalkUnit] using this
    exact (walkZ_eq_neg_one_iff (N₀ + n)).mp hw

/-- **The ladder, as one statement.**  Four rungs, of which (V) was the missing one. -/
theorem weak_hitting_ladder :
    (Mullin.HittingHypothesis → MullinConjecture) ∧
    (MullinConjecture → EveryPrimeDividesEuclid) ∧
    (∀ (q : ℕ) [NeZero q], Nat.Prime q → q ≠ 2 →
      EveryPrimeDividesEuclid → (-1 : ZMod q) ∈ reachableEver q 2) ∧
    (OneHorizon.WindowFourierGain → OneWindowGain) ∧
    (OneWindowGain → EveryPrimeDividesEuclid) :=
  ⟨Mullin.hh_implies_mullin,
    mullin_implies_everyPrimeDividesEuclid,
    fun _ _ hq h2 h => everyPrimeDividesEuclid_implies_reachable h hq h2,
    windowFourierGain_implies_oneWindowGain,
    oneWindowGain_implies_V⟩

end WeakHitting

end
