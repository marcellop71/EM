import EM.CME.Reduction
import EM.Equidist.OneHorizon
import EM.Reduction.SelfCorrecting
import EM.LargeSieve.Spectral

/-!
# The missing-prime hypotheses are equivalent to Mullin's Conjecture

Every hypothesis of the residue-walk layer — `HittingHypothesis`, `DynamicalHitting`,
`SingleHitHypothesis`, `WalkEquidistribution`, `ConditionalMultiplierEquidist`,
`ComplexCharSumBound`, `DecorrelationHypothesis`, `MultiModularCSB`, `SubquadraticVisitEnergy`,
`VisitEquidistribution`, `SelfCorrectingDrift`, `OneHorizon.WindowFourierGain` — is quantified
over primes `q` **that never appear** (`hne : ∀ k, seq k ≠ q`).  Under `MullinConjecture` there is
no such prime, so each of them holds vacuously: `MC → H` for every `H` in the list.  Combined with
the proved `H → MC` (for those without a threshold), each is *equivalent* to MC.

This file puts the converses on record.  It changes nothing about the mathematics — the
content of `cme_implies_mc` is the *direction* CME ⇒ MC, which turns a hitting problem into an
equidistribution problem — but it fixes the language: CME, CCSB, DH, SHH, WFG are
**reformulations of MC in the language of the walk**, not sufficient conditions strictly weaker
than MC, and none of them is "the single open hypothesis" in any sense stronger than MC itself.
Statements with a threshold (`MultiModularCSB`, `SubquadraticVisitEnergy`,
`VisitEquidistribution`, `SelfCorrectingDrift`, `DecorrelationHypothesis`) are still implied by MC
vacuously; their converses need `FiniteMCBelow Q₀` (or, for `Dec`, are open).

A hypothesis with content independent of MC would have to be a statement about the residues of
`seq n` *not* conditioned on missingness (uniformly in `q`); the population layer that tried to
supply one was refuted (Dead End #160).
-/

open Mullin Euclid

section MissingPrimeVacuity

variable (hmc : MullinConjecture)
include hmc

/-- Under MC no prime is missing: `hne` is unsatisfiable. -/
theorem no_missing_prime_of_mc {q : ℕ} (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) : False := by
  obtain ⟨n, hn⟩ := hmc q hq
  exact hne n hn

theorem mc_implies_hh : HittingHypothesis := fun _q hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_dh : DynamicalHitting := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_shh : SingleHitHypothesis := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_walkEquidist : WalkEquidistribution := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_cme : ConditionalMultiplierEquidist := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_ccsb : ComplexCharSumBound := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_dec : DecorrelationHypothesis := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_mmcsb : MultiModularCSB :=
  ⟨0, fun _q _ _ hq hne => (no_missing_prime_of_mc hmc hq hne).elim⟩

theorem mc_implies_sve : SubquadraticVisitEnergy :=
  ⟨0, fun _q _ _ hq hne => (no_missing_prime_of_mc hmc hq hne).elim⟩

theorem mc_implies_ve : VisitEquidistribution :=
  ⟨0, fun _q _ _ hq hne => (no_missing_prime_of_mc hmc hq hne).elim⟩

theorem mc_implies_scd : SelfCorrectingDrift := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

theorem mc_implies_wfg : OneHorizon.WindowFourierGain := fun _q _ hq hne =>
  (no_missing_prime_of_mc hmc hq hne).elim

end MissingPrimeVacuity

/-! ## The equivalences -/

theorem hh_iff_mc : HittingHypothesis ↔ MullinConjecture :=
  ⟨hh_implies_mullin, mc_implies_hh⟩

theorem dh_iff_mc : DynamicalHitting ↔ MullinConjecture :=
  ⟨dynamical_hitting_implies_mullin, mc_implies_dh⟩

theorem shh_iff_mc : SingleHitHypothesis ↔ MullinConjecture :=
  ⟨single_hit_implies_mc, mc_implies_shh⟩

theorem walkEquidist_iff_mc : WalkEquidistribution ↔ MullinConjecture :=
  ⟨walk_equidist_mc, mc_implies_walkEquidist⟩

/-- **CME is a reformulation of MC**, not a hypothesis strictly weaker than it. -/
theorem cme_iff_mc : ConditionalMultiplierEquidist ↔ MullinConjecture :=
  ⟨cme_implies_mc, mc_implies_cme⟩

theorem ccsb_iff_mc : ComplexCharSumBound ↔ MullinConjecture :=
  ⟨complex_csb_mc', mc_implies_ccsb⟩

theorem wfg_iff_mc : OneHorizon.WindowFourierGain ↔ MullinConjecture :=
  ⟨OneHorizon.windowFourierGain_implies_mc, mc_implies_wfg⟩

/-- All the missing-prime reformulations coincide. -/
theorem walk_layer_equivalences :
    (ConditionalMultiplierEquidist ↔ MullinConjecture) ∧
    (ComplexCharSumBound ↔ MullinConjecture) ∧
    (DynamicalHitting ↔ MullinConjecture) ∧
    (SingleHitHypothesis ↔ MullinConjecture) ∧
    (HittingHypothesis ↔ MullinConjecture) ∧
    (WalkEquidistribution ↔ MullinConjecture) ∧
    (OneHorizon.WindowFourierGain ↔ MullinConjecture) ∧
    (MullinConjecture → DecorrelationHypothesis) ∧
    (MullinConjecture → MultiModularCSB) ∧
    (MullinConjecture → SubquadraticVisitEnergy) ∧
    (MullinConjecture → VisitEquidistribution) ∧
    (MullinConjecture → SelfCorrectingDrift) :=
  ⟨cme_iff_mc, ccsb_iff_mc, dh_iff_mc, shh_iff_mc, hh_iff_mc, walkEquidist_iff_mc, wfg_iff_mc,
   mc_implies_dec, mc_implies_mmcsb, mc_implies_sve, mc_implies_ve, mc_implies_scd⟩
