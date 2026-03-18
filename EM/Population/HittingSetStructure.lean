import EM.Population.InfiniteM

/-!
# Hitting Set Structure for Missing Primes

Formalizes the hitting set structure of the Euclid-Mullin sequence.
For a prime q, the **hitting set** `HittingSet q` is the set of steps n
where q divides prod(n)+1. For missing primes, every hitting step is
"shielded": seq(n+1) = minFac(prod(n)+1) < q, so a smaller prime
captures the slot.

## Main Results

### Part 1: Hitting Set + Dichotomy
* `HittingSet` : {n | q divides prod(n)+1}
* `ShieldedHitting` : missing + HittingSet infinite
* `EventualPerpetualAvoidance` : missing + HittingSet finite
* `perpetual_avoidance_dichotomy` : every missing prime is one or the other
* `sh_epa_exclusive` : the dichotomy is exclusive

### Part 2: Hitting Set Containment
* `hitting_step_guardian` : at shielded hitting steps, seq(n+1) < q
* `hitting_event_has_guardian` : guardian prime exists with full properties
* `guardian_is_appeared` : the guardian is always an appeared prime

### Part 3: Guardian-Active/Inactive Classification
* `GuardianActive` / `GuardianInactive` : classification of steps
* `guardian_active_or_inactive` : exhaustive
* `guardian_active_inactive_exclusive` : exclusive
* `active_step_shielded` : at active steps, all missing divisors are shielded
* `shielded_hitting_implies_infinitely_many_active` : ShieldedHitting gives i.o. active

### Part 4: Hitting Correlation
* `hittingMultiplicity` : count of missing primes dividing prod(n)+1
* `hittingMultiplicity_le` : bounded by |F|
* `hittingMultiplicity_inactive` : zero at inactive steps
* `hitting_set_landscape` : 5-clause summary
-/

open Mullin Euclid MullinGroup RotorRouter
open Classical

/-! ## Part 1: Hitting Set + Dichotomy -/

section HittingSetDichotomy

/-- HittingSet q = {n | q divides prod(n) + 1} -- the set of steps where
    walkZ q n = -1. For missing primes, these are the "shielded hitting" steps. -/
def HittingSet (q : Nat) : Set Nat := {n | q ∣ prod n + 1}

/-- ShieldedHitting q means q is missing AND HittingSet q is infinite:
    q divides prod(n)+1 infinitely often, but is always shielded by
    a smaller factor (since seq(n+1) = minFac(prod(n)+1) < q). -/
def ShieldedHitting (q : Nat) : Prop :=
  q ∈ MissingPrimes ∧ Set.Infinite (HittingSet q)

/-- EventualPerpetualAvoidance: q is missing AND HittingSet q is finite.
    After finitely many steps, q never divides prod(n)+1 again. -/
def EventualPerpetualAvoidance (q : Nat) : Prop :=
  q ∈ MissingPrimes ∧ Set.Finite (HittingSet q)

/-- Hitting set membership = q divides prod(n) + 1. -/
theorem mem_hittingSet_iff (q n : Nat) : n ∈ HittingSet q ↔ q ∣ prod n + 1 :=
  Iff.rfl

/-- Hitting set membership = walkZ = -1. -/
theorem hittingSet_eq_walkZ_neg_one (q : Nat) :
    HittingSet q = {n | walkZ q n = -1} := by
  ext n
  simp only [HittingSet, Set.mem_setOf_eq]
  exact (walkZ_eq_neg_one_iff n).symm

/-- **Perpetual avoidance dichotomy**: every missing prime q either has
    ShieldedHitting (HittingSet infinite) or EventualPerpetualAvoidance
    (HittingSet finite). This is an exhaustive, exclusive dichotomy. -/
theorem perpetual_avoidance_dichotomy {q : Nat} (hq : q ∈ MissingPrimes) :
    ShieldedHitting q ∨ EventualPerpetualAvoidance q := by
  rcases Set.finite_or_infinite (HittingSet q) with h | h
  · right; exact ⟨hq, h⟩
  · left; exact ⟨hq, h⟩

/-- The dichotomy is exclusive: ShieldedHitting and EPA are incompatible. -/
theorem sh_epa_exclusive (q : Nat) : ¬(ShieldedHitting q ∧ EventualPerpetualAvoidance q) := by
  intro ⟨⟨_, hinf⟩, ⟨_, hfin⟩⟩
  exact hinf.not_finite hfin

end HittingSetDichotomy

/-! ## Part 2: Hitting Set Containment -/

section HittingSetContainment

/-- At a shielded hitting step, seq(n+1) < q. -/
theorem hitting_step_guardian {q : Nat} (hq : q ∈ MissingPrimes) {n : Nat}
    (hn : n ∈ HittingSet q) : seq (n + 1) < q :=
  (factor_dichotomy_strong hq n hn).1

/-- At a shielded hitting step, seq(n+1) is a prime < q that divides prod(n)+1.
    This "guardian" prime shields q from capture. -/
theorem hitting_event_has_guardian {q : Nat} (hq : q ∈ MissingPrimes) {n : Nat}
    (hn : n ∈ HittingSet q) :
    ∃ g, g = seq (n + 1) ∧ Nat.Prime g ∧ g < q ∧ g ∣ prod n + 1 := by
  refine ⟨seq (n + 1), rfl, ?_, hitting_step_guardian hq hn, ?_⟩
  · exact (isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))
  · rw [seq_succ]
    exact minFac_dvd (prod n + 1) (by have := prod_ge_two n; omega)

/-- The guardian at any step is always an appeared prime (trivially). -/
theorem guardian_is_appeared {q : Nat} (_hq : q ∈ MissingPrimes) {n : Nat}
    (_hn : n ∈ HittingSet q) : seq (n + 1) ∈ Set.range seq :=
  seq_in_range (n + 1)

end HittingSetContainment

/-! ## Part 3: Guardian-Active/Inactive Classification -/

section GuardianClassification

/-- A step n is guardian-active if some missing prime divides prod(n)+1. -/
def GuardianActive (n : Nat) : Prop :=
  ∃ q ∈ MissingPrimes, q ∣ prod n + 1

/-- A step n is guardian-inactive if no missing prime divides prod(n)+1. -/
def GuardianInactive (n : Nat) : Prop :=
  ∀ q ∈ MissingPrimes, ¬(q ∣ prod n + 1)

/-- Steps are either guardian-active or guardian-inactive. -/
theorem guardian_active_or_inactive (n : Nat) :
    GuardianActive n ∨ GuardianInactive n := by
  by_cases h : ∃ q ∈ MissingPrimes, q ∣ prod n + 1
  · left; exact h
  · right
    push_neg at h
    exact h

/-- Active/inactive are exclusive. -/
theorem guardian_active_inactive_exclusive (n : Nat) :
    ¬(GuardianActive n ∧ GuardianInactive n) := by
  intro ⟨⟨q, hqm, hqdvd⟩, hinactive⟩
  exact hinactive q hqm hqdvd

/-- At an active step, the guardian (seq(n+1)) shields all missing prime divisors. -/
theorem active_step_shielded {n : Nat} (_h : GuardianActive n) :
    ∀ q ∈ MissingPrimes, q ∣ prod n + 1 → seq (n + 1) < q := by
  intro q hq hdvd
  exact (factor_dichotomy_strong hq n hdvd).1

/-- Under ShieldedHitting, there are infinitely many guardian-active steps
    (at least those in HittingSet q). -/
theorem shielded_hitting_implies_infinitely_many_active {q : Nat}
    (hsh : ShieldedHitting q) : Set.Infinite {n | GuardianActive n} := by
  have hsub : HittingSet q ⊆ {n | GuardianActive n} := by
    intro n hn
    exact ⟨q, hsh.1, hn⟩
  exact hsh.2.mono hsub

end GuardianClassification

/-! ## Part 4: Hitting Correlation -/

section HittingCorrelation

/-- HittingMultiplicity: the number of primes in F that divide prod(n)+1. -/
noncomputable def hittingMultiplicity (n : Nat) (F : Finset Nat) : Nat :=
  (F.filter (fun q => q ∣ prod n + 1)).card

/-- Hitting multiplicity is at most |F|. -/
theorem hittingMultiplicity_le (n : Nat) (F : Finset Nat) :
    hittingMultiplicity n F ≤ F.card :=
  Finset.card_filter_le F _

/-- At inactive steps, hitting multiplicity is 0 for any F of missing primes. -/
theorem hittingMultiplicity_inactive {n : Nat} (h : GuardianInactive n)
    {F : Finset Nat} (hF : ↑F ⊆ MissingPrimes) :
    hittingMultiplicity n F = 0 := by
  rw [hittingMultiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  exact h q (hF (Finset.mem_coe.mpr hq))

/-- Hitting set structure landscape: conjunction of key results. -/
theorem hitting_set_landscape :
    -- (1) Dichotomy
    (∀ q, q ∈ MissingPrimes → ShieldedHitting q ∨ EventualPerpetualAvoidance q) ∧
    -- (2) Exclusivity
    (∀ q, ¬(ShieldedHitting q ∧ EventualPerpetualAvoidance q)) ∧
    -- (3) Guardian at hitting steps
    (∀ q, q ∈ MissingPrimes → ∀ n, n ∈ HittingSet q → seq (n + 1) < q) ∧
    -- (4) Active/inactive classification
    (∀ n, GuardianActive n ∨ GuardianInactive n) ∧
    -- (5) Hitting multiplicity bounded
    (∀ n F, hittingMultiplicity n F ≤ F.card) :=
  ⟨fun _ hq => perpetual_avoidance_dichotomy hq,
   sh_epa_exclusive,
   fun _ hq _ hn => hitting_step_guardian hq hn,
   guardian_active_or_inactive,
   hittingMultiplicity_le⟩

end HittingCorrelation
