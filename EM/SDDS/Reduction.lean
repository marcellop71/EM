import EM.SDDS.Bridge
import EM.Equidist.Bootstrap

/-!
# Reduction: SDDS Hypotheses to Mullin's Conjecture

This file relates sieve-map equidistribution for the Euclid-Mullin
SDDS to divisibility of Euclid numbers. The remaining live result is:

* `sme_implies_dvd_euclid` — SME at a single prime q implies q divides
  some Euclid number prod(n) + 1.

## Design

The basic `SieveMapEquidistribution` from `EM/SDDS/Dynamics.lean`
guarantees that the walk hits every unit at least once. This suffices
to show q divides some prod(n) + 1, but does NOT guarantee the hit
occurs past the sieve gap (where all primes < q have been absorbed
into the running product). Therefore, basic SME alone does not
immediately yield MC.

## Archived 2026-11-10

The cofinal variant `StrongSME` (and the hypothesis "basic SME for all primes" of
`sme_for_all_implies_euclid_divisibility`) was found false as stated on 2026-11-10: it
quantifies over every prime, and modulo `2` the walk is identically `0`
(`HypothesisAudit.not_strongSME`).  `strong_sme_implies_hh`, `strong_sme_implies_mc` and
`sme_for_all_implies_euclid_divisibility` are archived in
`EM/Archive/SDDS/ReductionArchive.lean`.
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

/-! ## Strong (cofinal) SME — archived

`StrongSME` (cofinal SME for *every* prime) was found false on 2026-11-10: it has no
missing-prime guard, and modulo `2` the walk is identically `0`
(`HypothesisAudit.not_strongSME`).  Its definition now lives next to that refutation in
`EM/Meta/HypothesisAudit.lean`; the consumers are archived. -/

-- strong_sme_implies_hh archived to EM/Archive/SDDS/ReductionArchive.lean (RED #15)
-- strong_sme_implies_mc archived to EM/Archive/SDDS/ReductionArchive.lean (RED #15)
-- sme_for_all_implies_euclid_divisibility archived to EM/Archive/SDDS/ReductionArchive.lean (RED #15)

end
