import EM.Group.CRT
import EM.Obstruction.Fragment
import EM.Reciprocity.NoReciprocityInvariant
import EM.Equidist.OneHorizon
import EM.Ensemble.MinFacShifted
import EM.Obstruction.RuleTransition

/-!
# What the Bag Determines About the Next Prime

The state of the Euclid–Mullin construction at step `n` is the *bag* `Sₙ` of primes
collected so far, and the dynamics is `Sₙ₊₁ = Sₙ ∪ {minFac (∏Sₙ + 1)}`.  A recurring
intuition about the sequence is that the new prime has "nothing to do with" the old ones:
the `+1` destroys the multiplicative structure, and taking the least factor forgets what
produced it.

This file assembles what the formalization actually establishes about that intuition.  It
is worth doing because the intuition is *nearly* right, is right in three precise senses,
and is **false** in two others — and the two failures are exactly the structure the whole
project runs on.

## The intuition is right in three senses

* **The multiplier ignores coordinates.**  `crt_multiplier_invariance_finset`: the least
  factor of `P+1` is unchanged if `P` is altered at any finite set of coordinates at which
  death does not occur.  The accumulator's residues at those primes are invisible to the
  selection.
* **Congruence data does not constrain the multiplier.**  `free_transition`: from a free
  state, *every* unit of `ZMod m` is reachable in one transition.  So no residue datum
  mod `m` predicts the next multiplier's class.
* **No invariant of the killed classes blocks a prime.**  Congruence invariants at a fixed
  modulus — *every* modulus, including the even ones where Cox–van der Poorten's max-side
  proof lives (`RuleTransition.no_congruence_induction_proof_of_ne_zero`) — at a growing
  symbol modulus, stage-dependent ones, and ones weakened by size, `ω` or smoothness
  guards: all fail (`Obstruction.guard_analysis_complete`,
  `Reciprocity.no_reciprocity_induction_proof`).

## The intuition is false in two senses, and this is the content of the problem

* **The new prime is not in the bag.**  `seq_not_dvd_prod_succ`: no prime already
  collected divides the next Euclid number.  This is Euclid's argument, and it is a strong
  and permanent dependence of the new prime on the old ones.
* **At a missing prime it is bounded below.**  Past the stage at which all primes below `q`
  have appeared, every subsequent multiplier exceeds `q`
  (`OneHorizon.multipliers_exceed`).

So the honest statement is not "nothing to do with" but **"nothing beyond the exclusion
and the resulting roughness"** — and that conditional independence, stated
distributionally, is exactly `ConditionalMultiplierEquidist`, which is open and is the
sharpest sufficient condition for Mullin's conjecture.

## Two scope warnings

*Independence is not uniformity.*  On the correct-parity ensemble the first multiplier
equals `3` for exactly half the starting points (`MinFacShifted.tendsto_minFacThree_density`),
so the multiplier is wildly non-uniform.  Any reading of "the bag tells you nothing" as
"the next prime is uniformly distributed" is refuted.  Clause (6) of the landscape below
is included precisely to block that reading.

*Two axes, one closed.*  The no-go results concern invariants whose **state** is
congruence data (at a fixed or growing modulus) and proofs whose **obligations** are
weakened by guards.  An invariant whose state records *anatomy* — `ω`, the largest prime
factor, smoothness — is a different object and is not covered by anything here.  That is
where the `maxFac` omission proofs live, and it is the residue of the programme.
-/

noncomputable section

open Mullin Euclid MullinGroup

namespace BagInformation

/-! ## The orthogonal-bag property, in Lean

Euclid's argument: a prime already in the bag divides the accumulator, hence cannot divide
the accumulator plus one. -/

/-- **No prime already collected divides the next Euclid number.** -/
theorem seq_not_dvd_prod_succ {k n : ℕ} (h : k ≤ n) : ¬ (seq k ∣ prod n + 1) := by
  intro hdvd
  have hk : seq k ∣ prod n := seq_dvd_prod k n h
  have h1 : seq k ∣ 1 := by simpa using Nat.dvd_sub hdvd hk
  have h2 : Nat.Prime (seq k) := (isPrime_iff_natPrime _).mp (seq_isPrime k)
  have := Nat.le_of_dvd one_pos h1
  have := h2.two_le
  omega

/-! ## The landscape -/

/-- **What the bag determines about the next prime.**  Six clauses: three in which the
intuition "the new prime has nothing to do with the bag" is correct, two in which it is
provably false, and one guarding against the wrong reading of the first three.

Read together they say: *the bag determines that the next prime avoids it and (at a
missing prime) exceeds that prime, and — across every invariant class killed here —
nothing else; but the resulting distribution is very far from uniform.* -/
theorem bag_information_landscape :
    -- (1) the multiplier ignores any finite death-free set of coordinates
    (∀ (P P' : ℕ) (T : Finset ℕ), 2 ≤ P + 1 → 2 ≤ P' + 1 →
      (∀ r, Nat.Prime r → r ∉ T → P % r = P' % r) →
      (∀ r ∈ T, ¬ r ∣ P + 1) → (∀ r ∈ T, ¬ r ∣ P' + 1) →
      Nat.minFac (P + 1) = Nat.minFac (P' + 1)) ∧
    -- (2) congruence data does not constrain it: every unit is one transition away
    (∀ (m : ℕ), m ≠ 0 → ∀ (r : ZMod m), IsUnit (r + 1) → ∀ s : (ZMod m)ˣ,
      CvdP.Transition m r (r * (s : ZMod m))) ∧
    -- (3) no congruence-invariant induction proof blocks a missing prime, at ANY modulus …
    (∀ q m : ℕ, q ∈ MissingPrimes → m ≠ 0 →
      IsEmpty (Obstruction.CongruenceInductionProof q m)) ∧
    -- … nor any invariant at the growing symbol modulus
    (∀ q m : ℕ, q ∈ MissingPrimes → m ≠ 0 →
      IsEmpty (Reciprocity.ReciprocityInductionProof q m)) ∧
    -- (4) BUT the bag does determine that the new prime avoids it,
    (∀ k n : ℕ, k ≤ n → ¬ (seq k ∣ prod n + 1)) ∧
    -- and at a missing prime, past the sieve gap, that it exceeds q
    (∀ (q : ℕ), Nat.Prime q → (∀ k, seq k ≠ q) → ∀ N₀ : ℕ,
      (∀ p, p < q → Nat.Prime p → ∃ m, m ≤ N₀ ∧ seq m = p) →
      ∀ n ≥ N₀, q < seq (n + 1)) ∧
    -- (5) and the resulting distribution is NOT uniform: half of the correct-parity
    -- ensemble has first multiplier exactly 3
    Filter.Tendsto
      (fun σ : ℝ => MinFacShifted.minFacThreeSum σ / IK.DirichletDensity.primeZetaSum σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / 2)) :=
  ⟨fun _ _ T hP hP' hcrt hT hT' =>
      MullinCRT.crt_multiplier_invariance_finset T hP hP' hcrt hT hT',
    fun _ hm r hr s => CvdP.free_transition hm r hr s,
    fun _ _ hq hm => RuleTransition.no_congruence_induction_proof_of_ne_zero hq hm,
    fun _ _ hq hm => Reciprocity.no_reciprocity_induction_proof hq hm,
    fun _ _ h => seq_not_dvd_prod_succ h,
    fun _ _ hne N₀ hbelow => OneHorizon.multipliers_exceed hne N₀ hbelow,
    MinFacShifted.tendsto_minFacThree_density⟩

end BagInformation

end
