import EM.FunctionField.FFCharacterSums
import EM.FunctionField.FactorTree

/-!
# FF sieve chain: the counting proxies

**What this file proves** (review 2026-11-10, P11): elementary facts about the number
`π_p(d) = ffIrredCount p d` of monic irreducibles of degree `d` over `𝔽_p`, all consequences of
the necklace identity.  The definitions carry the names of the steps of the integer-side chain

  PrimesEquidistInAP -> FCD -> SPV -> PSCD -> almost-all GenMixedMC

from `MixedEnsemble.lean`, but they are COUNTING PROXIES, not the function-field analogues of
those statements: none of them mentions a residue class, a character, a sieve product or a
starting point.

| Name | Statement |
|------|-----------|
| `FFCharSumCancellation` | necklace identity `∑_{d ∣ n} d·π_p(d) = p^n` |
| `FFPNTInAPs` | `π_p(d) ≥ 1` for `d ≥ 1` |
| `FFFCD` | `∑_{d ≤ D} π_p(d) ≥ D` |
| `FFSieveProductVanishing` | `n·π_p(n) ≤ p^n` |
| `FFPSCD` | `π_p(n) ≤ p^n / n` |
| `FFAlmostAllGenMixedMC` | `π_p(d) ≥ 1` ∧ `n·π_p(n) ≤ p^n` |

The genuine statements — per-subset confined-density decay and "the proportion of starts from
which `Q` is not tree-reachable tends to 0" — are `ff_density_pscd` and
`FFAlmostAllGenMixedDensity` in `EM/FunctionField/DensityMC.lean`, proved there conditionally
on `FFDirichletDensity` (Kornblum).  Nothing in this file shows that "density-1 starts reach
every target".

## Main definitions

* `FFSieveProductVanishing` -- necklace upper bound: n * pi(n) <= p^n
* `FFPSCD` -- irred density bound: pi(n) <= p^n / n (COUNTING PROXY; the
  genuine per-subset confined-density decay is `ff_density_pscd` in
  `EM/FunctionField/DensityMC.lean`)
* `FFAlmostAllGenMixedMC` -- PNT + necklace conjunction (COUNTING PROXY; the
  genuine trapped-density statement is `FFAlmostAllGenMixedDensity` in
  `EM/FunctionField/DensityMC.lean`)

## Main results

* `ff_fcd_implies_spv` -- FFFCD => sieve product vanishing
* `ff_spv_implies_pscd` -- SPV => PSCD
* `ff_fcd_implies_pscd` -- FFFCD => PSCD (composition)
* `ff_pscd_implies_almost_all` -- PSCD => almost-all GenMixedMC
* `ff_fcd_implies_almost_all` -- FFFCD => almost-all GenMixedMC
* `ff_almost_all_unconditional` -- the counting proxy `FFAlmostAllGenMixedMC`
* `ff_full_chain_unconditional` -- all six counting proxies
* `ff_sieve_landscape` -- landscape summary (8 clauses)

## References

* Integer-side chain: `EM/Ensemble/MixedEnsemble.lean` (PSCD, pigeonhole, almost-all)
* FF-FCD: `EM/FunctionField/FFCharacterSums.lean` (unconditional)
* Factor tree: `EM/FunctionField/FactorTree.lean` (mixed selection)
-/

namespace FunctionFieldAnalog

open Polynomial Classical Filter

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Part 1: FF Analog of Confined/Sieved Counting -/

/-- FF sieve product vanishing: the necklace upper bound.

    For every n >= 1, n * ffIrredCount(p,n) <= p^n.

    This bounds the "sieve weight" of each degree level: the number
    of irreducibles times their degree cannot exceed the total count
    of monic polynomials. This is the key input to sieve product
    vanishing: the product over degrees of (1 - weight_d) tends to 0.

    Over F_p[t] this follows from the necklace identity:
    sum_{d|n} d * pi(d) = p^n, so the single term n * pi(n) <= p^n.

    **COUNTING PROXY.**  Despite the name, no sieve product occurs in the statement and
    nothing is shown to vanish; it is the single-term consequence of the necklace identity.
    It is NOT the FF analogue of `sieve_product_vanishing_proved` from MixedEnsemble.lean. -/
def FFSieveProductVanishing : Prop :=
  ∀ n : ℕ, 0 < n → n * ffIrredCount p n ≤ p ^ n

/-- FF sieve product vanishing is unconditional over F_p[t]. -/
theorem ff_spv_proved : FFSieveProductVanishing p :=
  necklace_count_mul_le p (necklaceIdentity_holds p)

/-! ## Part 2: FF-PSCD (Population Sieve Confinement Decay) -/

/-- FF-PSCD: the irred density bound.

    For every n >= 1, ffIrredCount(p,n) <= p^n / n.

    **COUNTING PROXY.** Despite the name, this is NOT the FF analogue of the
    integer-side density statement `PSCD` from `MixedEnsemble.lean` (which says
    each confined density tends to 0); it is only the elementary counting bound
    on the irreducible density at each degree level, which follows
    unconditionally from the necklace identity (n * pi(n) <= p^n implies
    pi(n) <= p^n / n).

    The GENUINE function-field analogue of `PSCD` — for every proper residue
    subset, the density of sieve-confined starting points tends to 0 — is
    `ff_density_pscd` in `EM/FunctionField/DensityMC.lean`, proved there
    conditional on the Kornblum divergence hypothesis `FFDirichletDensity`. -/
def FFPSCD : Prop :=
  ∀ n : ℕ, 0 < n → ffIrredCount p n ≤ p ^ n / n

/-- FF-PSCD is unconditional over F_p[t]. -/
theorem ff_pscd_proved : FFPSCD p :=
  necklace_irred_count_le p (necklaceIdentity_holds p)

/-! ## Part 3: FF-AlmostAllGenMixedMC -/

/-- Almost-all GenMixedMC over F_p[t]: the conjunction of PNT-in-APs
    (every degree has irreducibles) and the necklace upper bound
    (irred count times degree bounded by p^n).

    **COUNTING PROXY.** Despite the name, this Prop is NOT a density statement
    about starting points: it is only the conjunction of two unconditional
    counting bounds (irreducible-count positivity and the necklace upper
    bound), the two facts that the sieve argument consumes. It does NOT assert
    that the factor tree reaches Q from density-1 starting points.

    The GENUINE density statement — among monic squarefree starting points of
    degree 1..n, the proportion with Q ∤ m from which Q is NOT ffTreeReachable
    tends to 0 — is `FFAlmostAllGenMixedDensity` in
    `EM/FunctionField/DensityMC.lean`, proved there
    (`ff_almost_all_genmixed_density`) by the trapped/confined pigeonhole and
    the exact congruence sieve, conditional on the SINGLE hypothesis
    `FFDirichletDensity` (Kornblum's theorem, the FF Dirichlet analogue). -/
def FFAlmostAllGenMixedMC : Prop :=
  (∀ d : ℕ, 0 < d → 0 < ffIrredCount p d) ∧
  (∀ n : ℕ, 0 < n → n * ffIrredCount p n ≤ p ^ n)

/-- Almost-all GenMixedMC is unconditional over F_p[t]. -/
theorem ff_almost_all_gen_mixed_mc_proved : FFAlmostAllGenMixedMC p :=
  ⟨ffIrredCount_pos p, necklace_count_mul_le p (necklaceIdentity_holds p)⟩

/-! ## Part 4: Implication Chain -/

/-- FFFCD implies sieve product vanishing.

    From the linear supply growth (FFFCD), we get that each degree has
    at least one irreducible. Combined with the necklace identity
    (which is unconditional), we obtain n * pi(n) <= p^n. -/
theorem ff_fcd_implies_spv : FFFCD p → FFSieveProductVanishing p := by
  intro _
  exact ff_spv_proved p

/-- Sieve product vanishing implies PSCD.

    From n * pi(n) <= p^n, dividing both sides by n gives pi(n) <= p^n / n. -/
theorem ff_spv_implies_pscd : FFSieveProductVanishing p → FFPSCD p := by
  intro hspv n hn
  exact (Nat.le_div_iff_mul_le hn).mpr (by linarith [hspv n hn])

/-- FFFCD implies PSCD (composition of the two steps above). -/
theorem ff_fcd_implies_pscd : FFFCD p → FFPSCD p :=
  fun h => ff_spv_implies_pscd p (ff_fcd_implies_spv p h)

/-- PSCD implies almost-all GenMixedMC.

    The PSCD bound pi(n) <= p^n / n, together with the unconditional
    fact that pi(n) >= 1, gives the conjunction. -/
theorem ff_pscd_implies_almost_all : FFPSCD p → FFAlmostAllGenMixedMC p := by
  intro hpscd
  exact ⟨ffIrredCount_pos p,
         fun n hn => by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hn).mp (hpscd n hn)⟩

/-- FFFCD implies almost-all GenMixedMC (full chain composition).

    FFFCD -> SPV -> PSCD -> almost-all GenMixedMC. -/
theorem ff_fcd_implies_almost_all : FFFCD p → FFAlmostAllGenMixedMC p :=
  fun h => ff_pscd_implies_almost_all p (ff_fcd_implies_pscd p h)

/-! ## Part 5: Unconditional Final Theorem -/

/-- The counting proxy `FFAlmostAllGenMixedMC` (`π_p(d) ≥ 1` and `n·π_p(n) ≤ p^n`) holds.

    This is NOT the statement that the factor tree reaches every target from a density-1 set
    of starting points; see the module docstring and `FFAlmostAllGenMixedDensity` in
    `EM/FunctionField/DensityMC.lean` for that (conditional) statement. -/
theorem ff_almost_all_unconditional : FFAlmostAllGenMixedMC p :=
  ff_almost_all_gen_mixed_mc_proved p

/-- The full chain is unconditional: every intermediate step holds. -/
theorem ff_full_chain_unconditional :
    FFCharSumCancellation p ∧
    FFPNTInAPs p ∧
    FFFCD p ∧
    FFSieveProductVanishing p ∧
    FFPSCD p ∧
    FFAlmostAllGenMixedMC p :=
  ⟨ff_char_sum_cancellation_proved p,
   ff_pnt_in_aps_proved p,
   ff_fcd_proved p,
   ff_spv_proved p,
   ff_pscd_proved p,
   ff_almost_all_unconditional p⟩

/-! ## Part 6: Comparison with Integer Case -/

/-- The six counting proxies and the (trivial) implications among them.  This is a statement
    about irreducible counts only; it does not compare the integer and function-field sieve
    chains, whose function-field form is in `DensityMC.lean`. -/
theorem ff_vs_integer_chain :
    -- (1) counting proxy
    FFAlmostAllGenMixedMC p ∧
    -- (2) counting proxies
    (FFFCD p ∧ FFPSCD p ∧ FFSieveProductVanishing p) ∧
    -- (3) necklace identity -> π ≥ 1 -> ∑ π ≥ D
    (FFCharSumCancellation p → FFPNTInAPs p → FFFCD p) ∧
    -- (4) Each implication in the sieve chain holds
    ((FFFCD p → FFSieveProductVanishing p) ∧
     (FFSieveProductVanishing p → FFPSCD p) ∧
     (FFPSCD p → FFAlmostAllGenMixedMC p)) :=
  ⟨ff_almost_all_unconditional p,
   ⟨ff_fcd_proved p, ff_pscd_proved p, ff_spv_proved p⟩,
   fun _ hpnt => ff_pnt_implies_fcd p hpnt,
   ⟨ff_fcd_implies_spv p, ff_spv_implies_pscd p, ff_pscd_implies_almost_all p⟩⟩

/-! ## Part 7: Connection to Factor Tree Infrastructure -/

-- ff_gen_mixed_mc_implies_almost_all archived to EM/Archive/FunctionField/FFGenMixedMCArchive.lean (RED #19)

/-- FFMullinConjecture (from X) implies factor-tree reachability from X for any target Q.

    If the greedy walk from X captures every monic irreducible, then a fortiori
    the standard greedy selection (viewed as a mixed selection) captures Q.
    This is the FF analog of: MC -> MixedMC (the greedy walk is a particular
    mixed selection). -/
theorem ff_mc_implies_mixed_mc_from_X (d : FFEMData p) (hmc : FFMullinConjecture p)
    (Q : Polynomial (ZMod p)) (hQm : Q.Monic) (hQi : Irreducible Q) :
    ffTreeReachable p (X : Polynomial (ZMod p)) Q :=
  ffmc_implies_tree_reachable_from_X d hmc Q hQm hQi

/-- The unconditional almost-all statement and the chain from FCD.

    The original middle clause `FFGenMixedMC p → FFAlmostAllGenMixedMC p` was vacuous:
    `FFGenMixedMC` was found false on 2026-11-10 (`FunctionFieldAnalog.not_ffGenMixedMC`).
    The original three-clause statement is archived in
    `EM/Archive/FunctionField/FFGenMixedMCArchive.lean` (RED #19). -/
theorem ff_mc_hierarchy :
    -- (1) Almost-all GenMixedMC is unconditional
    FFAlmostAllGenMixedMC p ∧
    -- (2) Full chain from FCD is unconditional
    (FFFCD p → FFAlmostAllGenMixedMC p) :=
  ⟨ff_almost_all_unconditional p,
   ff_fcd_implies_almost_all p⟩

/-! ## Part 8: Landscape -/

/-- Summary of the counting proxies of this file (see the module docstring for what each is). -/
theorem ff_sieve_landscape :
    -- (1) Sieve product vanishing (unconditional)
    FFSieveProductVanishing p ∧
    -- (2) PSCD (unconditional)
    FFPSCD p ∧
    -- (3) counting proxy π_p(d) ≥ 1 ∧ n·π_p(n) ≤ p^n
    FFAlmostAllGenMixedMC p ∧
    -- (4) FCD -> SPV
    (FFFCD p → FFSieveProductVanishing p) ∧
    -- (5) SPV -> PSCD
    (FFSieveProductVanishing p → FFPSCD p) ∧
    -- (6) PSCD -> almost-all GenMixedMC
    (FFPSCD p → FFAlmostAllGenMixedMC p) ∧
    -- (7) Full chain from FCD (unconditional)
    (FFFCD p → FFAlmostAllGenMixedMC p) ∧
    -- (8) Full chain is unconditional (every step holds)
    (FFCharSumCancellation p ∧ FFPNTInAPs p ∧ FFFCD p ∧
     FFSieveProductVanishing p ∧ FFPSCD p ∧ FFAlmostAllGenMixedMC p) :=
  ⟨ff_spv_proved p,
   ff_pscd_proved p,
   ff_almost_all_unconditional p,
   ff_fcd_implies_spv p,
   ff_spv_implies_pscd p,
   ff_pscd_implies_almost_all p,
   ff_fcd_implies_almost_all p,
   ff_full_chain_unconditional p⟩

end FunctionFieldAnalog
