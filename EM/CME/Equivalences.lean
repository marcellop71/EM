import EM.CME.Reduction
import EM.Equidist.OneHorizon
import EM.Reduction.SelfCorrecting
import EM.LargeSieve.Spectral
import EM.Population.WeakMullin

/-!
# The missing-prime hypotheses are equivalent to Mullin's Conjecture

Every hypothesis of the residue-walk layer — `HittingHypothesis`, `DynamicalHitting`,
`SingleHitHypothesis`, `WalkEquidistribution`, `ConditionalMultiplierEquidist`,
`ComplexCharSumBound`, `DecorrelationHypothesis`, `MultiModularCSB`, `SubquadraticVisitEnergy`,
`VisitEquidistribution`, `SelfCorrectingDrift`, `OneHorizon.WindowFourierGain` — is quantified
over primes `q` **that never appear** (`hne : ∀ k, seq k ≠ q`).  Under `MullinConjecture` there is
no such prime, so each of them holds vacuously: `MC → H` for every `H` in the list.  Combined with
the proved `H → MC` (for HH, DH, SHH, WE, CME, CCSB, WFG and — since 2026-11-10 — SCD), each of
those is *equivalent* to MC.

This file puts the converses on record.  It changes nothing about the mathematics — the
content of `cme_implies_mc` is the *direction* CME ⇒ MC, which turns a hitting problem into an
equidistribution problem — but it fixes the language: CME, CCSB, DH, SHH, WFG are
**reformulations of MC in the language of the walk**, not sufficient conditions strictly weaker
than MC, and none of them is "the single open hypothesis" in any sense stronger than MC itself.

Three statements carry an existential threshold `∃ Q₀, ∀ q ≥ Q₀, …`: `MultiModularCSB`,
`SubquadraticVisitEnergy`, `VisitEquidistribution`.  They are implied by MC vacuously, but they
are **not** equivalent to MC as far as anyone knows: each is equivalent to *cofinite* MC,
`MissingFinite` (`mmcsb_iff_missingFinite`, `sve_iff_missingFinite`, `ve_iff_missingFinite`), and
reaches MC only together with `FiniteMCBelow Q₀` at the same explicit threshold
(`mmcsbAt_implies_mc`, `sveAt_implies_mc`, `veAt_implies_mc`).  The older theorems
`mmcsb_implies_mc`, `sve_implies_mc` state that side condition at an `Exists.choose` and cannot be
applied to a known threshold.

Two statements were listed here, until 2026-11-10, among those "with a threshold", wrongly: both
are quantified over **all** primes.
* `SelfCorrectingDrift` implies MC with no side condition (`scd_implies_mc'`), so
  `scd_iff_mc`: one more reformulation of MC.
* `DecorrelationHypothesis`: only `MC → Dec` is on record (`mc_implies_dec`); `Dec → MC` is
  not proved in this repository (the bridge from decorrelation to character-sum cancellation,
  `PEDImpliesComplexCSB`, is open).

A hypothesis with content independent of MC would have to be a statement about the residues of
`seq n` *not* conditioned on missingness (uniformly in `q`); the population layer that tried to
supply one was refuted (Dead End #160).
-/

open Mullin Euclid MullinGroup

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

/-- **SCD is a reformulation of MC** (added 2026-11-10; SCD has no threshold). -/
theorem scd_iff_mc : SelfCorrectingDrift ↔ MullinConjecture :=
  ⟨scd_implies_mc', mc_implies_scd⟩

/-- **VE at `Q₀` captures every prime `q ≥ Q₀`**, unconditionally. -/
theorem veAt_appears {Q₀ : ℕ} (h : VisitEquidistributionAt Q₀)
    {q : ℕ} (hq : IsPrime q) (hge : Q₀ ≤ q) : ∃ k, seq k = q := by
  by_contra hne
  have hne' : ∀ k, seq k ≠ q := fun k e => hne ⟨k, e⟩
  have : Fact (Nat.Prime q) := ⟨(isPrime_iff_natPrime q).mp hq⟩
  refine hne (exists_seq_eq_of_cofinal_dvd hq (fun N => ?_))
  obtain ⟨n, hn, heq⟩ := veAt_walk_cofinal h hq hne' hge (-1) N
  refine ⟨n, hn, (walkZ_eq_neg_one_iff n).mp ?_⟩
  have h' := congr_arg Units.val heq
  simp only [emWalkUnit, Units.val_mk0, Units.val_neg, Units.val_one] at h'
  exact h'

/-- **VE at an explicit threshold + finite verification below it ⟹ MC.** -/
theorem veAt_implies_mc {Q₀ : ℕ} (h : VisitEquidistributionAt Q₀)
    (hfin : FiniteMCBelow Q₀) : MullinConjecture := by
  intro q hq
  rcases Nat.lt_or_ge q Q₀ with hlt | hge
  · exact hfin q hq hlt
  · exact veAt_appears h hq hge

/-- **`VisitEquidistribution` ⟺ `MissingFinite`.** -/
theorem ve_iff_missingFinite : VisitEquidistribution ↔ MissingFinite := by
  rw [missingFinite_iff_exists_threshold]
  constructor
  · rintro ⟨Q₀, h⟩
    exact ⟨Q₀, fun q hq hge => veAt_appears (Q₀ := Q₀) h hq hge⟩
  · rintro ⟨Q₀, h⟩
    refine ⟨Q₀, fun q _ hge hq hne => ?_⟩
    obtain ⟨k, hk⟩ := h q hq hge
    exact absurd hk (hne k)

/-- **The thresholded walk hypotheses are reformulations of cofinite MC**, and coincide. -/
theorem walk_layer_cofinite_equivalences :
    (MultiModularCSB ↔ MissingFinite) ∧
    (SubquadraticVisitEnergy ↔ MissingFinite) ∧
    (VisitEquidistribution ↔ MissingFinite) :=
  ⟨mmcsb_iff_missingFinite, sve_iff_missingFinite, ve_iff_missingFinite⟩

/-- All the missing-prime reformulations coincide.

    Note (2026-11-10).  Only the first seven conjuncts are equivalences.  The last five record
    the vacuous direction `MC → ·` alone, and their status differs:
    * `SelfCorrectingDrift` is in fact equivalent to MC (`scd_iff_mc`);
    * `MultiModularCSB`, `SubquadraticVisitEnergy`, `VisitEquidistribution` are equivalent to
      `MissingFinite`, i.e. to *cofinite* MC (`walk_layer_cofinite_equivalences`), not to MC;
    * for `DecorrelationHypothesis` no converse is proved. -/
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
