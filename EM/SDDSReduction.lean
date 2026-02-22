import EM.SDDSBridge
import EM.EquidistBootstrap

/-!
# Reduction: SDDS Hypotheses to Mullin's Conjecture

This file proves that sieve-map equidistribution for the Euclid-Mullin
SDDS implies Mullin's Conjecture. The main results are:

* `sme_implies_dvd_euclid` — SME at a single prime q implies q divides
  some Euclid number prod(n) + 1.
* `StrongSME` — cofinal SME: the walk hits every unit past any bound.
* `strong_sme_implies_hh` — StrongSME implies HittingHypothesis.
* `strong_sme_implies_mc` — StrongSME implies MullinConjecture (via HH).
* `sme_for_all_implies_euclid_divisibility` — basic SME for all primes
  implies every missing prime divides some Euclid number.

## Design

The basic `SieveMapEquidistribution` from `SieveDefinedDynamics.lean`
guarantees that the walk hits every unit at least once. This suffices
to show q divides some prod(n) + 1, but does NOT guarantee the hit
occurs past the sieve gap (where all primes < q have been absorbed
into the running product). Therefore, basic SME alone does not
immediately yield MC.

The cofinal variant `StrongSME` guarantees hits past any bound,
which directly gives `HittingHypothesis`. The existing reduction
`hh_implies_mullin` then closes the argument.
-/

open Mullin Euclid MullinGroup

section
open Classical

/-! ## Basic SME to divisibility -/

/-- SME at a single prime q implies q divides some Euclid number.

Given that the EM SDDS walk at q hits every unit, in particular it
hits -1. By `walkZ_eq_neg_one_iff`, this means q divides prod(n) + 1
for some n. This is a necessary condition for q to appear in the
sequence, but not sufficient on its own (the hit might occur before
the sieve gap). -/
theorem sme_implies_dvd_euclid (q : ℕ) (hq : Nat.Prime q)
    [Fact (Nat.Prime q)]
    (hsme : SieveMapEquidistribution (emSDDS q hq)) :
    ∃ n : ℕ, q ∣ (Mullin.prod n + 1) := by
  obtain ⟨n, hn⟩ := sme_implies_walkZ_hits_neg_one q hq hsme
  exact ⟨n, (walkZ_eq_neg_one_iff n).mp hn⟩

/-! ## Strong (cofinal) SME -/

/-- **Strong Sieve Map Equidistribution**: the walk of the EM SDDS
hits every unit in (ZMod q)^times cofinally — that is, past any
given bound N.

This is strictly stronger than `SieveMapEquidistribution`, which
only guarantees at least one hit per unit. The cofinal property
is what the strong induction in `hh_implies_mullin` needs: the
hit must occur past the sieve gap, where all smaller primes have
already been absorbed into the running product. -/
noncomputable def StrongSME : Prop :=
  ∀ (q : ℕ) (hq : Nat.Prime q),
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    ∀ (u : (ZMod q)ˣ) (N : ℕ), ∃ n, N ≤ n ∧ (emSDDS q hq).walk n = (u : ZMod q)

/-- StrongSME implies HittingHypothesis.

Proof: HH requires that for every prime q not in the sequence, and
every bound N, there exists n >= N with q | prod(n) + 1.

From StrongSME, take u = -1 (a unit in ZMod q for any prime q) and
the given bound N. This yields n >= N with walk(n) = -1. Converting
via `emSDDS_walk_eq_walkZ` and `walkZ_eq_neg_one_iff` gives the
required divisibility. The hypothesis "q not in seq" is not even
needed — StrongSME provides the hitting unconditionally. -/
theorem strong_sme_implies_hh (hstrong : StrongSME) :
    Mullin.HittingHypothesis := by
  intro q hq _hne N
  have hqp : Nat.Prime q := IsPrime.toNatPrime hq
  haveI : Fact (Nat.Prime q) := ⟨hqp⟩
  -- -1 is a unit in ZMod q
  let u : (ZMod q)ˣ := Units.mkOfMulEqOne (-1) (-1) (by ring)
  -- StrongSME gives n >= N with walk(n) = -1
  obtain ⟨n, hn_ge, hn_walk⟩ := hstrong q hqp u N
  -- Convert SDDS walk to walkZ
  rw [emSDDS_walk_eq_walkZ] at hn_walk
  -- Convert walkZ = -1 to divisibility
  exact ⟨n, hn_ge, (walkZ_eq_neg_one_iff n).mp hn_walk⟩

/-- **StrongSME implies Mullin's Conjecture.**

Composes `strong_sme_implies_hh` with the existing `hh_implies_mullin`
(from `MullinConjectures.lean`), which uses strong induction + the
capture lemma to show every prime appears in the sequence. -/
theorem strong_sme_implies_mc (hstrong : StrongSME) :
    Mullin.MullinConjecture :=
  Mullin.hh_implies_mullin (strong_sme_implies_hh hstrong)

/-! ## Weak result from basic SME -/

/-- Basic SME for all primes implies every missing prime divides
some Euclid number.

This is a partial step toward MC: for any prime q that never appears
in the sequence, SME gives `walkZ q n = -1` for some n, hence
q | prod(n) + 1. The result does not guarantee the hit occurs past
the sieve gap, so it cannot be directly composed with `captures_target`.

This shows that basic SME rules out the possibility that q is
"arithmetically invisible" to the sequence — every prime has at least
one chance to be captured. Whether it IS captured depends on the hit
occurring after all smaller primes have been absorbed. -/
theorem sme_for_all_implies_euclid_divisibility
    (hsme : ∀ (q : ℕ) (hq : Nat.Prime q),
      haveI : Fact (Nat.Prime q) := ⟨hq⟩
      SieveMapEquidistribution (emSDDS q hq)) :
    ∀ q, Nat.Prime q → (∀ k, Mullin.seq k ≠ q) →
      ∃ n, q ∣ (Mullin.prod n + 1) := by
  intro q hq _hne
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  exact sme_implies_dvd_euclid q hq (hsme q hq)

end
