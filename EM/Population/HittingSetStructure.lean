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

**The dichotomy of Part 1 is now COLLAPSED.**  Part 2b (Finite Hitting) proves that
`HittingSet q` is *always* finite for a missing `q`, so `ShieldedHitting q` is never
satisfiable (`not_shieldedHitting`) and every missing prime satisfies
`EventualPerpetualAvoidance` (`missing_implies_epa`).  The Part 1 statements remain true
but the disjunction always lands in the right branch, and every theorem whose hypothesis
is `ShieldedHitting` is vacuously conditioned.

### Part 2: Hitting Set Containment
* `hitting_step_guardian` : at shielded hitting steps, seq(n+1) < q
* `hitting_event_has_guardian` : guardian prime exists with full properties
* `guardian_is_appeared` : the guardian is always an appeared prime

### Part 2b: Finite Hitting
* `hittingSet_finite` : for missing q, `HittingSet q` is finite
* `hittingSet_ncard_le` : `(HittingSet q).ncard ≤ q`
* `not_shieldedHitting` : `ShieldedHitting q` is unsatisfiable
* `missing_implies_epa` : every missing prime has `EventualPerpetualAvoidance`

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

### Part 5: Self-Referential Shield Supply
* `AppearingPrimesBelow` : primes below q that already occur in the sequence
* `hittingSet_ncard_le_appearing` : hits of a missing q are bounded by the *appearing*
  primes below q (sharpens `hittingSet_ncard_le`)
* `hittingSet_ncard_le_appearing_odd` : the guardian is never 2, so the bound may drop 2

### Part 6: Finite Missing Confinement
* `missing_not_dvd_prod` : a missing prime never divides the accumulator
* `finite_missing_confinement` : past a finite time, the accumulator avoids both 0 and −1
  modulo every prime of a finite family of missing primes

### Part 7: The Shield Ledger
* `candidate_factor_is_hit` : every prime factor of Pₙ+1 hits at step n
* `guardian_mem_candidate_factors` / `guardian_min_candidate_factor` : the multiplier is the
  least candidate factor
* `hittingMultiplicity_succ_le_omega` : shields at step n cost at most ω(Pₙ+1) − 1 slots
* `hitting_ledger_sum` : Fubini identity for the total shield count below N
* `hitting_ledger_bound` : total shields below N plus N is at most ∑ ω(Pₙ+1)
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
  simp only [HittingSet, Set.mem_ofPred_eq]
  exact (walkZ_eq_neg_one_iff n).symm

/-- **Perpetual avoidance dichotomy**: every missing prime q either has
    ShieldedHitting (HittingSet infinite) or EventualPerpetualAvoidance
    (HittingSet finite). This is an exhaustive, exclusive dichotomy.

    NOTE (collapsed): by `hittingSet_finite` (Part 2b) the left branch is never
    taken — see `not_shieldedHitting` and `missing_implies_epa`. The statement
    remains true, but it is now strictly weaker than `missing_implies_epa`. -/
theorem perpetual_avoidance_dichotomy {q : Nat} (hq : q ∈ MissingPrimes) :
    ShieldedHitting q ∨ EventualPerpetualAvoidance q := by
  rcases Set.finite_or_infinite (HittingSet q) with h | h
  · right; exact ⟨hq, h⟩
  · left; exact ⟨hq, h⟩

/-- The dichotomy is exclusive: ShieldedHitting and EPA are incompatible.

    NOTE (collapsed): `not_shieldedHitting` (Part 2b) shows the first conjunct is
    already unsatisfiable, so this exclusivity statement is now vacuous. Kept
    because it is still true and is referenced by `hitting_set_landscape`. -/
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

/-! ## Part 2b: Finite Hitting

For a missing prime `q`, every step `n` with `q ∣ Pₙ + 1` is *shielded*: the captured
factor `seq (n+1) = minFac (Pₙ + 1)` is a prime `< q` (`hitting_step_guardian`).  Since
primes never repeat in the sequence (`seq_injective`), the map `n ↦ seq (n+1)` injects
`HittingSet q` into the primes below `q`, so the hitting set is finite of size `≤ q`.

This is **min-specific**: the guardian bound `minFac (Pₙ+1) < q` fails for `maxFac`. -/

section FiniteHitting

/-- **Finite Hitting.**  For a missing prime `q`, the hitting set is finite. -/
theorem hittingSet_finite {q : Nat} (hq : q ∈ MissingPrimes) : (HittingSet q).Finite := by
  apply Set.Finite.of_finite_image (f := fun n => seq (n + 1))
  · apply Set.Finite.subset (Set.finite_Iio q)
    rintro x ⟨n, hn, rfl⟩
    exact hitting_step_guardian hq hn
  · intro a _ b _ hab
    have := seq_injective (a + 1) (b + 1) hab
    omega

/-- Explicit cardinality bound: a missing prime `q` is hit at most `q` times
    (indeed only at steps whose guardian is one of the primes below `q`). -/
theorem hittingSet_ncard_le {q : Nat} (hq : q ∈ MissingPrimes) :
    (HittingSet q).ncard ≤ q := by
  have h1 : (HittingSet q).ncard ≤ (Set.Iio q).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun n => seq (n + 1))
    · intro n hn; exact hitting_step_guardian hq hn
    · intro a _ b _ hab
      have := seq_injective (a + 1) (b + 1) hab
      omega
  rwa [← Finset.coe_Iio, Set.ncard_coe_finset, Nat.card_Iio] at h1

/-- **`ShieldedHitting` is unsatisfiable.**  It demands a missing prime whose hitting
    set is infinite, which `hittingSet_finite` forbids.  Consequently every theorem
    in this development whose hypothesis is `ShieldedHitting` is vacuously conditioned. -/
theorem not_shieldedHitting (q : Nat) : ¬ ShieldedHitting q := by
  rintro ⟨hq, hinf⟩
  exact hinf.not_finite (hittingSet_finite hq)

/-- **Every missing prime is eventually perpetually avoiding.**  Immediate from
    `hittingSet_finite`; this is the surviving (right) branch of
    `perpetual_avoidance_dichotomy`. -/
theorem missing_implies_epa {q : Nat} (hq : q ∈ MissingPrimes) :
    EventualPerpetualAvoidance q :=
  ⟨hq, hittingSet_finite hq⟩

/-- Restatement of Finite Hitting as an explicit tail bound: past some step `N₀`,
    a missing prime never divides `Pₙ + 1` again. -/
theorem missing_eventually_not_dvd {q : Nat} (hq : q ∈ MissingPrimes) :
    ∃ N₀, ∀ n, N₀ ≤ n → ¬ (q ∣ prod n + 1) := by
  obtain ⟨b, hb⟩ := (hittingSet_finite hq).bddAbove
  refine ⟨b + 1, fun n hn hdvd => ?_⟩
  have := hb (show n ∈ HittingSet q from hdvd)
  omega

end FiniteHitting

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
    push Not at h
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
    (at least those in HittingSet q).

    NOTE (vacuous): the hypothesis `ShieldedHitting q` is unsatisfiable by
    `not_shieldedHitting`, so this theorem now carries no content. Kept because it
    is still true and documents the shape of the argument that Finite Hitting killed. -/
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

/-- Hitting set structure landscape: conjunction of key results.

    Clause (1) records the **collapsed** dichotomy: Finite Hitting upgrades the
    disjunction `ShieldedHitting ∨ EPA` to its right branch outright, and rules
    `ShieldedHitting` out entirely. -/
theorem hitting_set_landscape :
    -- (1) Collapsed dichotomy: EPA always, ShieldedHitting never
    (∀ q, q ∈ MissingPrimes → EventualPerpetualAvoidance q) ∧
    (∀ q, ¬ ShieldedHitting q) ∧
    -- (2) Exclusivity
    (∀ q, ¬(ShieldedHitting q ∧ EventualPerpetualAvoidance q)) ∧
    -- (3) Guardian at hitting steps
    (∀ q, q ∈ MissingPrimes → ∀ n, n ∈ HittingSet q → seq (n + 1) < q) ∧
    -- (4) Active/inactive classification
    (∀ n, GuardianActive n ∨ GuardianInactive n) ∧
    -- (5) Hitting multiplicity bounded
    (∀ n F, hittingMultiplicity n F ≤ F.card) :=
  ⟨fun _ hq => missing_implies_epa hq,
   not_shieldedHitting,
   sh_epa_exclusive,
   fun _ hq _ hn => hitting_step_guardian hq hn,
   guardian_active_or_inactive,
   hittingMultiplicity_le⟩

end HittingCorrelation

/-! ## Part 5: Self-Referential Shield Supply

`hittingSet_ncard_le` bounds the hits of a missing `q` by the count of *all* naturals below
`q`.  That is wasteful: the guardian `seq (n+1)` is not merely a prime below `q`, it is a
prime that has **already appeared** in the sequence.  So the shield supply available to a
missing prime is drawn from the sequence's own past — a self-referential constraint. -/

section ShieldSupply

/-- The primes below `q` that already occur as terms of the Euclid–Mullin sequence.
    These are exactly the primes available as guardians for `q`. -/
def AppearingPrimesBelow (q : Nat) : Set Nat := {p | p ∈ Set.range seq ∧ p < q}

/-- The appearing primes below `q` form a finite set (they sit inside `Set.Iio q`). -/
theorem appearingPrimesBelow_finite (q : Nat) : (AppearingPrimesBelow q).Finite :=
  Set.Finite.subset (Set.finite_Iio q) (fun _ hp => hp.2)

/-- Every appearing prime below `q` is indeed prime. -/
theorem appearingPrimesBelow_prime {q p : Nat} (hp : p ∈ AppearingPrimesBelow q) :
    Nat.Prime p := by
  obtain ⟨⟨k, hk⟩, -⟩ := hp
  exact hk ▸ (isPrime_iff_natPrime _).mp (seq_isPrime k)

/-- The guardian at a hitting step of a missing prime is an appearing prime below `q`. -/
theorem guardian_mem_appearingPrimesBelow {q : Nat} (hq : q ∈ MissingPrimes) {n : Nat}
    (hn : n ∈ HittingSet q) : seq (n + 1) ∈ AppearingPrimesBelow q :=
  ⟨seq_in_range (n + 1), hitting_step_guardian hq hn⟩

/-- **Self-referential shield supply.**  For a missing prime `q`, the number of steps at
    which `q` is hit is at most the number of *appearing* primes below `q`.

    This sharpens `hittingSet_ncard_le` (`≤ q`): the shields spent on `q` must all be
    sequence terms already produced, so the sequence must have paid for them itself. -/
theorem hittingSet_ncard_le_appearing {q : Nat} (hq : q ∈ MissingPrimes) :
    (HittingSet q).ncard ≤ (AppearingPrimesBelow q).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun n => seq (n + 1))
    (fun n hn => guardian_mem_appearingPrimesBelow hq hn) ?_ (appearingPrimesBelow_finite q)
  intro a _ b _ hab
  have := seq_injective (a + 1) (b + 1) hab
  omega

/-- The accumulator is always even, so the candidate `Pₙ + 1` is odd and its least prime
    factor — the multiplier `seq (n+1)` — is never `2`. -/
theorem seq_succ_ne_two (n : Nat) : seq (n + 1) ≠ 2 := by
  intro h
  have h2 : (2 : Nat) ∣ prod n := by
    have := seq_dvd_prod 0 n (Nat.zero_le n)
    rwa [seq_zero] at this
  have h2' : (2 : Nat) ∣ prod n + 1 := by
    rw [← h]; exact seq_dvd_succ_prod n
  omega

/-- `2` is always an appearing prime below any `q > 2` (it is `seq 0`). -/
theorem two_mem_appearingPrimesBelow {q : Nat} (hq : 2 < q) :
    2 ∈ AppearingPrimesBelow q :=
  ⟨⟨0, seq_zero⟩, hq⟩

/-- **Sharpened shield supply.**  Since the guardian is never `2` (`seq_succ_ne_two`), the
    hits of a missing `q` inject into the appearing primes below `q` *with `2` removed*.
    For `q > 2` this is a strictly smaller receptacle than in
    `hittingSet_ncard_le_appearing`. -/
theorem hittingSet_ncard_le_appearing_odd {q : Nat} (hq : q ∈ MissingPrimes) :
    (HittingSet q).ncard ≤ (AppearingPrimesBelow q \ {2}).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun n => seq (n + 1))
    (fun n hn => ⟨guardian_mem_appearingPrimesBelow hq hn, seq_succ_ne_two n⟩) ?_
    ((appearingPrimesBelow_finite q).sdiff)
  intro a _ b _ hab
  have := seq_injective (a + 1) (b + 1) hab
  omega

end ShieldSupply

/-! ## Part 6: Finite Missing Confinement

The Detection payload.  For a *finite* family `Q` of missing primes, the accumulator is
eventually confined away from the two distinguished residues `0` and `−1` modulo every
`q ∈ Q`: `0` forever (a missing prime never divides `Pₙ`), and `−1` past the last hit. -/

section FiniteConfinement

/-- A missing prime never divides the accumulator. -/
theorem missing_not_dvd_prod {q : Nat} (hq : q ∈ MissingPrimes) (n : Nat) :
    ¬ (q ∣ prod n) :=
  prime_not_in_seq_not_dvd_prod ((isPrime_iff_natPrime q).mpr hq.1) hq.2 n

/-- Modular form: the walk never sits at `0` modulo a missing prime. -/
theorem missing_walkZ_ne_zero {q : Nat} (hq : q ∈ MissingPrimes) (n : Nat) :
    walkZ q n ≠ 0 := by
  intro h
  exact missing_not_dvd_prod hq n ((ZMod.natCast_eq_zero_iff _ _).mp h)

/-- **Finite Missing Confinement.**  Given finitely many missing primes `Q`, there is a
    time `T` past which the accumulator avoids both `0` and `−1` modulo every `q ∈ Q`.
    The `0` clause holds for all `n` (`missing_not_dvd_prod`); the `−1` clause is Finite
    Hitting (`missing_eventually_not_dvd`) uniformised over the finite family. -/
theorem finite_missing_confinement {Q : Finset Nat} (hQ : ∀ q ∈ Q, q ∈ MissingPrimes) :
    ∃ T, ∀ n, T ≤ n → ∀ q ∈ Q, (prod n : ZMod q) ≠ 0 ∧ (prod n : ZMod q) ≠ -1 := by
  have key : ∀ q : Nat, ∃ N₀ : Nat, q ∈ Q → ∀ n, N₀ ≤ n → ¬ (q ∣ prod n + 1) := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨N, hN⟩ := missing_eventually_not_dvd (hQ q hq)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose N hN using key
  refine ⟨Q.sup N, fun n hn q hqQ => ⟨?_, ?_⟩⟩
  · exact missing_walkZ_ne_zero (hQ q hqQ) n
  · intro h
    exact hN q hqQ n (le_trans (Finset.le_sup hqQ) hn)
      ((walkZ_eq_neg_one_iff (q := q) n).mp h)

/-- Walk-language restatement of `finite_missing_confinement`. -/
theorem finite_missing_confinement_walkZ {Q : Finset Nat} (hQ : ∀ q ∈ Q, q ∈ MissingPrimes) :
    ∃ T, ∀ n, T ≤ n → ∀ q ∈ Q, walkZ q n ≠ 0 ∧ walkZ q n ≠ -1 :=
  finite_missing_confinement hQ

end FiniteConfinement

/-! ## Part 7: The Shield Ledger

Every prime factor of the candidate `Pₙ + 1` is a hit at step `n`, and exactly one of them
— the least — is consumed as the multiplier `seq (n+1)`.  So the *shields* spent at step
`n` on missing primes are drawn from the remaining `ω(Pₙ+1) − 1` factor slots. -/

section ShieldLedger

/-- The candidate `Pₙ + 1` is at least `3`, in particular nonzero. -/
theorem candidate_ne_zero (n : Nat) : prod n + 1 ≠ 0 := by
  have := prod_ge_two n; omega

/-- **Every prime factor of the candidate is a hit.**  Nearly definitional, but it is the
    bridge that turns factorisation data at step `n` into hitting-set membership. -/
theorem candidate_factor_is_hit {n p : Nat} (hp : p ∈ (prod n + 1).primeFactors) :
    n ∈ HittingSet p :=
  Nat.dvd_of_mem_primeFactors hp

/-- The multiplier is a prime factor of the candidate. -/
theorem guardian_mem_candidate_factors (n : Nat) :
    seq (n + 1) ∈ (prod n + 1).primeFactors :=
  Nat.mem_primeFactors.mpr
    ⟨(isPrime_iff_natPrime _).mp (seq_isPrime (n + 1)), seq_dvd_succ_prod n, candidate_ne_zero n⟩

/-- The multiplier is the *least* prime factor of the candidate: every other candidate
    factor is a strictly larger prime that the step declined to consume. -/
theorem guardian_min_candidate_factor {n p : Nat} (hp : p ∈ (prod n + 1).primeFactors) :
    seq (n + 1) ≤ p := by
  rw [seq_succ]
  exact minFac_min' (prod n + 1) p (by have := prod_ge_two n; omega)
    (Nat.mem_primeFactors.mp hp).1.two_le (Nat.dvd_of_mem_primeFactors hp)

/-- A missing prime is a candidate factor at only finitely many steps. -/
theorem missing_candidate_steps_finite {p : Nat} (hp : p ∈ MissingPrimes) :
    {n | p ∈ (prod n + 1).primeFactors}.Finite :=
  (hittingSet_finite hp).subset (fun _ hn => candidate_factor_is_hit hn)

/-- For a finite family of missing primes, *all* shielding events happen in finite time. -/
theorem missing_family_candidate_steps_finite {F : Finset Nat}
    (hF : ∀ q ∈ F, q ∈ MissingPrimes) :
    {n | ∃ q ∈ F, q ∈ (prod n + 1).primeFactors}.Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion F.finite_toSet
    (fun q hq => hittingSet_finite (hF q hq))) ?_
  rintro n ⟨q, hqF, hq⟩
  exact Set.mem_biUnion (Finset.mem_coe.mpr hqF) (candidate_factor_is_hit hq)

/-- **Ledger inequality at a single step.**  The missing primes shielded at step `n` occupy
    distinct prime-factor slots of `Pₙ + 1`, none of which is the multiplier's slot (the
    multiplier appears in the sequence, missing primes do not).  Hence

      `#{shielded missing primes at n} + 1 ≤ ω(Pₙ + 1)`.

    In particular a step with `ω(Pₙ+1) = 1` shields nothing. -/
theorem hittingMultiplicity_succ_le_omega (n : Nat) {F : Finset Nat}
    (hF : ↑F ⊆ MissingPrimes) :
    hittingMultiplicity n F + 1 ≤ (prod n + 1).primeFactors.card := by
  set S := F.filter (fun q => q ∣ prod n + 1) with hS
  have hsub : insert (seq (n + 1)) S ⊆ (prod n + 1).primeFactors := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hpS
    · exact guardian_mem_candidate_factors n
    · obtain ⟨hpF, hpd⟩ := Finset.mem_filter.mp hpS
      exact Nat.mem_primeFactors.mpr
        ⟨(hF (Finset.mem_coe.mpr hpF)).1, hpd, candidate_ne_zero n⟩
  have hnot : seq (n + 1) ∉ S := by
    intro hmem
    exact (hF (Finset.mem_coe.mpr (Finset.mem_filter.mp hmem).1)).2 (n + 1) rfl
  calc hittingMultiplicity n F + 1 = (insert (seq (n + 1)) S).card := by
        rw [Finset.card_insert_of_notMem hnot, hittingMultiplicity, ← hS]
    _ ≤ (prod n + 1).primeFactors.card := Finset.card_le_card hsub

/-- **Ledger identity (Fubini).**  Counting shields by step or by shielded prime gives the
    same total: the double sum over `n < N` of the hitting multiplicity equals the sum over
    `q ∈ F` of the number of hits of `q` below `N`. -/
theorem hitting_ledger_sum (N : Nat) (F : Finset Nat) :
    ∑ n ∈ Finset.range N, hittingMultiplicity n F
      = ∑ q ∈ F, ((Finset.range N).filter (fun n => q ∣ prod n + 1)).card := by
  simp only [hittingMultiplicity, Finset.card_filter]
  exact Finset.sum_comm

/-- **Ledger bound.**  Combining the two: the total number of shields spent below `N` on a
    finite family of missing primes, plus `N` (one multiplier consumed per step), is at
    most the total number of prime-factor slots `∑_{n<N} ω(Pₙ+1)`.

    Since each summand on the left is eventually `0` (Finite Hitting), this says the
    shield ledger is a *finite* charge against an unbounded supply. -/
theorem hitting_ledger_bound (N : Nat) {F : Finset Nat} (hF : ↑F ⊆ MissingPrimes) :
    (∑ q ∈ F, ((Finset.range N).filter (fun n => q ∣ prod n + 1)).card) + N
      ≤ ∑ n ∈ Finset.range N, (prod n + 1).primeFactors.card := by
  rw [← hitting_ledger_sum N F]
  have : ∑ n ∈ Finset.range N, (hittingMultiplicity n F + 1)
      ≤ ∑ n ∈ Finset.range N, (prod n + 1).primeFactors.card :=
    Finset.sum_le_sum (fun n _ => hittingMultiplicity_succ_le_omega n hF)
  simpa [Finset.sum_add_distrib] using this

/-- Consumption landscape: the three sharpenings of Finite Hitting. -/
theorem consumption_landscape :
    -- (1) Shields for a missing prime come from its own past (self-referential supply)
    (∀ q, q ∈ MissingPrimes →
      (HittingSet q).ncard ≤ (AppearingPrimesBelow q \ {2}).ncard) ∧
    -- (2) Finite families of missing primes are eventually confined off 0 and −1
    (∀ Q : Finset Nat, (∀ q ∈ Q, q ∈ MissingPrimes) →
      ∃ T, ∀ n, T ≤ n → ∀ q ∈ Q, walkZ q n ≠ 0 ∧ walkZ q n ≠ -1) ∧
    -- (3) Shields at step n cost factor slots of Pₙ+1, one of which is the multiplier's
    (∀ n (F : Finset Nat), ↑F ⊆ MissingPrimes →
      hittingMultiplicity n F + 1 ≤ (prod n + 1).primeFactors.card) ∧
    -- (4) The ledger balances
    (∀ N (F : Finset Nat), ↑F ⊆ MissingPrimes →
      (∑ q ∈ F, ((Finset.range N).filter (fun n => q ∣ prod n + 1)).card) + N
        ≤ ∑ n ∈ Finset.range N, (prod n + 1).primeFactors.card) :=
  ⟨fun _ hq => hittingSet_ncard_le_appearing_odd hq,
   fun _ hQ => finite_missing_confinement_walkZ hQ,
   fun n _ hF => hittingMultiplicity_succ_le_omega n hF,
   fun N _ hF => hitting_ledger_bound N hF⟩

end ShieldLedger
