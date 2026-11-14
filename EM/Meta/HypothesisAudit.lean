import EM.Adelic.Profinite
import EM.SDDS.Reduction
import EM.Equidist.Fourier
import EM.Stochastic.ReachableSets
import EM.Stochastic.TreeSieveDecay
import EM.Equidist.SieveTransfer
import EM.FunctionField.FactorTree
import EM.IK.Ch7AdditiveLS
import EM.Obstruction.NoInvariant
import EM.Equidist.FourierB
import EM.Transfer.Excursion
import EM.Stochastic.RandomTwoPointMCB
import EM.Stochastic.DenseCapture
import EM.Stochastic.IteratedProductCoverage
import EM.Ensemble.UncenteredRefutations
import EM.FunctionField.Finiteness
import EM.FunctionField.SubgroupEscape
import EM.FunctionField.StableTower
import EM.LargeSieve.Harmonic
import EM.LargeSieve.Basic
import EM.IK.Ch5

/-!
# Hypothesis audit (review of 2026-11-10)

Machine-checked verdicts on hypotheses that the review `docs/analysis/review_2026-11-10.md`
found false, contradictory or trivial *as stated*.  Each theorem here refutes (or collapses) a
`def … : Prop` that some file presented as an open hypothesis; the theorems that consumed such a
hypothesis were therefore vacuous.  Nothing here touches the headline results.

**Archived 2026-11-10.**  Five of these hypotheses — `StrongSME` (H3), `CharSumCancellation`
(H7), `Regeneration` (H8), `FactorEscapeHypothesis` (H9), `FFMixedMC` / `FFGenMixedMC` (H14) —
have been removed from their original files, and every theorem that took one of them as a
hypothesis is archived under `EM/Archive/` (RED #15–#19, see `EM/Archive/README.md`).  Their
*definitions* are kept here, in their original namespaces, directly above the refutation, so
that each false statement and its refutation sit together and nothing else in the live tree can
consume it.

Two further hypotheses found false by the same review were *repaired* in place rather than
refuted here: `UniformProfiniteEquidist` (false at `k = 0`; now requires `0 < k`),
`IK.AdditiveLargeSieve` (now stated with circular spacing; the old form is refuted below) and
`StrongSieveEquidist` (`L₀` was universally quantified, which forced every multiplier to equal
every unit; now `∃ L₀`).  Their earlier refutations are in the git history of this file.

**Second batch, 2026-11-11** (walk layer, ensemble, stochastic; RED #20–#24).

* `CharSumBound` (H5): asserts that the walk is almost always in `ker χ`; contradictory at a
  missing prime, `HypothesisAudit.charSumBound_iff_mc`.  It was an unused argument of
  `char_sum_bound_implies_we / _dh / _mc`, which now depend on `HitCountLowerBound` only.
* `BoundedMaxExcursion`, `UniversalBoundedMax`, `ExcursionIndependence`, `UniversalEIP` (H6):
  an `Excursion` is any pair of visits, and lists may repeat.
  `HypothesisAudit.universalBoundedMax_iff_mc` (contradictory at a missing prime) and
  `HypothesisAudit.excursionCharSum_eq_zero_of_excursionIndependence` (every excursion sum
  vanishes).  Consumers archived.
* `PathSurvival` (H10): means "no two-point path ever captures `q`";
  `HypothesisAudit.not_pathSurvival_three`.  The general collapse to
  `∀ N, deathCount q N = 0` is not machine-checked.  Consumer archived.
* Dense capture (H11), *repaired* in `EM/Stochastic/DenseCapture.lean`: `minFacSeq` was the
  all-second-factor selection (`HypothesisAudit.epsWalkFactorFrom_const_false`), and the density
  hypotheses lacked the guard `¬ q ∣ acc` (`captureSet_eq_empty_of_dvd`,
  `HypothesisAudit.not_denseCapture_unguarded`,
  `HypothesisAudit.not_forall_prime_dense_captureSet`).
* `JSEMarginalEquidist` (H12): the step-`0` instance of `EnsembleMultiplierEquidist`;
  `HypothesisAudit.not_jseMarginalEquidist`.  Consumers archived.
* `IteratedProduct.FactorBagCoverage` (H13): `S k = {1, -1}`;
  `HypothesisAudit.not_factorBagCoverage` for every prime `q ≥ 5`.  No consumers.

Handled outside this file in the same batch: `EnsembleConcentration` (H1) repaired to the
`(ε, δ)` shape in `EM/Population/TransferStrategy.lean` (the falsity of the old form is argued
in its docstring, not machine-checked); `BSESMSBChainImpliesMC` (H26) proved vacuous in
`UncenteredRefutations.bseSMSBChainImpliesMC_vacuous`.

**Third batch, 2026-11-11** (function field, analytic layer, GaussEM; RED #25–#32).

* Function-field bridges (H17): `FFMultCCSBImpliesFFDH`, `FFDSLImpliesFFDH`, `FFDH_from_SE`,
  `FFCMEImpliesFFMC`, `FFLMChainImpliesFFMC` each have a `True`-bodied placeholder (or, for the
  last, a provable proxy) as premise and FF-MC (or `FFDynamicalHitting`, which is FF-MC:
  `FunctionFieldAnalog.ffDynamicalHitting_iff_ffmc`) as conclusion.  Each is equivalent to
  `FFMullinConjecture p` (`ffMultCCSBImpliesFFDH_iff_ffmc`, `ffDSLImpliesFFDH_iff_ffmc`,
  `ffDH_from_SE_iff_ffmc`, `ffCMEImpliesFFMC_iff_ffmc`, `ffLMChainImpliesFFMC_iff_ffmc`) and
  false at `p = 5` (`not_ffBridges_five`).  Consumers archived (RED #25).
* `WeilDoesNotImplyFFDSL` (H16): `¬ (True → True)`; `not_weilDoesNotImplyFFDSL`.  No consumers
  (RED #26).
* `FFLargeMonodromy` (H15) is *not* here: it is the proxy `|Gal| > 1`, which is true
  (`FunctionFieldAnalog.ffLargeMonodromy`, `EM/FunctionField/Finiteness.lean`); the intended
  statement fails because the group is cyclic (`ffGaloisGroup_isCyclic`, `Analog.lean`).
* `DegreeBoundedHitting` (H18): trivially true as stated (`degreeBoundedHitting_trivial`); the
  cofinal form its docstring described is *false* for every sequence
  (`not_degreeBoundedHittingCofinal`, from `eventually_euclid_factors_natDegree_gt`), so it was
  not repaired.  `ff_dh_implies_degree_bounded` archived with RED #25.
* `KernelRowSumBound` (H20): absolute row sums of the trigonometric kernel exceed
  `N - 1 + δ⁻¹`; `HypothesisAudit.not_kernelRowSumBound` (exact instance at the cube roots of
  unity).  Consumer archived (RED #27).
* `EMHasLevelOfDistribution θ` (H22): trivially true for `θ ∈ (0, 1]`,
  `HypothesisAudit.emHasLevelOfDistribution_iff`.  Consumers archived (RED #29).
* IK Chapter 5 samples (H24): `IK.not_grandRiemannHypothesis`, `IK.not_siegelBound`,
  `IK.not_dirichletConvexityBound`: a value that should be tied to an `L`-function is a free
  universally quantified variable.  The other fourteen definitions of that kind, and the two
  Mellin transforms of Chapter 4, are archived without a Lean refutation (RED #31).

Handled outside this file in the same batch: `GramOffDiagBilinearBound`, `CscBilinearBound`,
`HilbertCscBilinearBridge` (H19) restated with circular spacing; `IK.LinnikSmallQNR` (H21)
restated as Linnik's theorem (the proof of its degenerate former statement archived, RED #28);
four mis-stated IK Chapter 1 transcriptions archived (H23, RED #30); the GaussEM existential
stubs archived (H25, RED #32).

**Close-out, 2026-11-11** (section 2 of the review).  No new refutation was added to this file.
* The thresholded walk hypotheses `MultiModularCSB`, `SubquadraticVisitEnergy`,
  `VisitEquidistribution` are not defective but were mis-described: each is equivalent to
  cofinite MC (`mmcsb_iff_missingFinite`, `sve_iff_missingFinite`, `ve_iff_missingFinite`), and
  the chain to MC is now stated at an explicit threshold (`MultiModularCSBAt`,
  `mmcsbAt_implies_mc`; `EM/LargeSieve/Basic.lean`).  `SelfCorrectingDrift` has no threshold
  and is equivalent to MC (`scd_iff_mc`).
* `JSEConditionalEquidist` and `PerPrimeConditionalEquidist` (`EM/Ensemble/BaseCase.lean`) are
  **false as stated but not refuted in Lean**: the limits `1/(q-1)` over the `q - 1` nonzero
  classes add up to `1`, which forces the class `genSeq n 1 = q` to have conditional density
  `0`, and it has positive density.  The refutation needs a lower density for squarefree
  numbers in a residue class, which the repository does not have; the definitions stay where
  they are, with a warning, and are not archived.

The recurring cause is a degenerate parameter value left inside a quantifier: `k = 0`,
`N = 0`, `ε = 0`, the prime `2`, a seed equal to (or divisible by) the target, a repeated list
element, fractional parts in place of the distance on the circle; in the third batch also a
`True` placeholder on one side of an implication, and a free variable standing for a value
that the statement had no way to name.
-/

open Mullin Euclid MullinGroup

namespace HypothesisAudit

/-! ## Walk-layer hypotheses -/

theorem two_dvd_prod (n : ℕ) : 2 ∣ prod n := by
  induction n with
  | zero => rw [prod_zero]
  | succ n ih => rw [prod_succ]; exact ih.mul_right _

end HypothesisAudit

open Classical in
/-- **Strong Sieve Map Equidistribution** (refuted, kept only as the target of
`HypothesisAudit.not_strongSME`; originally in `EM/SDDS/Reduction.lean`): the walk of the EM
SDDS hits every unit in `(ZMod q)ˣ` cofinally — that is, past any given bound `N` — for every
prime `q`. -/
noncomputable def StrongSME : Prop :=
  ∀ (q : ℕ) (hq : Nat.Prime q),
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    ∀ (u : (ZMod q)ˣ) (N : ℕ), ∃ n, N ≤ n ∧ (emSDDS q hq).walk n = (u : ZMod q)

namespace HypothesisAudit

/-- `StrongSME` is false: it has no missing-prime guard, and modulo `2` the walk is
identically `0`, never the unit `1`.  (H3.) -/
theorem not_strongSME : ¬ StrongSME := by
  intro h
  obtain ⟨n, -, hn⟩ := h 2 Nat.prime_two 1 0
  rw [emSDDS_walk_eq_walkZ, walkZ, (ZMod.natCast_eq_zero_iff (prod n) 2).mpr (two_dvd_prod n)]
    at hn
  simp only [Units.val_one] at hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (zero_ne_one (α := ZMod 2)) hn

end HypothesisAudit

/-- **CharSumCancellation** (collapsed to MC, kept only as the target of
`HypothesisAudit.charSumCancellation_iff_mc`; originally in `EM/Equidist/Fourier.lean`): for
every missing prime `q` and every `N`, the walk collision count satisfies
`C_N < N² / (q − 2)`. -/
def CharSumCancellation : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)]
    (_hq : IsPrime q) (_hne : ∀ k, seq k ≠ q),
    ∀ N, (WalkCollisionCount q N : ℚ) < (N : ℚ)^2 / ((q : ℚ) - 2)

namespace HypothesisAudit

/-- `CharSumCancellation` is contradictory at any missing prime (`0 < 0` at `N = 0`), so it is
MC by logic alone.  (H7.) -/
theorem charSumCancellation_iff_mc : CharSumCancellation ↔ MullinConjecture := by
  constructor
  · intro h p hp
    by_contra hne
    push Not at hne
    have : Fact (Nat.Prime p) := ⟨(isPrime_iff_natPrime p).mp hp⟩
    have := h p hp hne 0
    simp [WalkCollisionCount] at this
  · intro hmc q _ hq hne
    obtain ⟨n, hn⟩ := hmc q hq
    exact absurd hn (hne n)

/-! ## Factor-tree hypotheses -/

end HypothesisAudit

/-- **Factor Escape Hypothesis** (refuted, kept only as the target of
`HypothesisAudit.not_factorEscapeHypothesis`; originally in
`EM/Stochastic/ReachableSets.lean`): for any step-dependent family of proper sets
`F n ⊊ ZMod q`, the Euclid numbers `prod n + 1` are not eventually all-factors-confined to
`F n`. -/
def FactorEscapeHypothesis (q : ℕ) : Prop :=
  ∀ (F : ℕ → Set (ZMod q)),
    (∀ n, F n ≠ Set.univ) →
    ¬(∃ N₀, ∀ n ≥ N₀, AllFactorsInSet q (prod n + 1) (F n))

namespace HypothesisAudit

/-- `FactorEscapeHypothesis q` is false for every prime `q`: the proper set of nonzero
residues eventually contains every prime factor of every Euclid number.  (H9.) -/
theorem not_factorEscapeHypothesis {q : ℕ} (hq : q.Prime) : ¬ FactorEscapeHypothesis q := by
  intro h
  have : Fact q.Prime := ⟨hq⟩
  refine h (fun _ => {x | x ≠ 0}) (fun n hF => ?_) ?_
  · have : (0 : ZMod q) ∈ ({x | x ≠ 0} : Set (ZMod q)) := by rw [hF]; trivial
    exact this rfl
  · obtain ⟨N₀, hN₀⟩ := CvdP.eventually_not_dvd_succ q hq
    refine ⟨N₀, fun n hn p hp hdvd h0 => hN₀ n hn ?_⟩
    rw [ZMod.natCast_eq_zero_iff] at h0
    rwa [(Nat.prime_dvd_prime_iff_eq hq hp).mp h0]

end HypothesisAudit

namespace FunctionFieldAnalog

open Polynomial

/-- Mixed MC at target `Q` (refuted, kept only as the target of
`FunctionFieldAnalog.not_ffMixedMC`; originally in `EM/FunctionField/FactorTree.lean`): for
every valid starting point, there exists a valid selection capturing `Q`. -/
def FFMixedMC (p : ℕ) [hp : Fact (Nat.Prime p)] (Q : Polynomial (ZMod p)) : Prop :=
  ∀ start : Polynomial (ZMod p), start.Monic → 0 < start.natDegree →
  ∃ σ : FFMixedSelection p, FFMixedSelectionValid p start σ ∧
    ffMixedCaptures p start σ Q

/-- Generalized Mixed MC (refuted, kept only as the target of
`FunctionFieldAnalog.not_ffGenMixedMC`; originally in `EM/FunctionField/FactorTree.lean`): for
all monic irreducible `Q`, `FFMixedMC` holds. -/
def FFGenMixedMC (p : ℕ) [hp : Fact (Nat.Prime p)] : Prop :=
  ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q → FFMixedMC p Q

/-- `FFMixedMC p Q` is false for every irreducible `Q`: the start `Q` itself is never captured
(`start_not_capturable`).  The definition lacks the guard `¬ Q ∣ start`.  (H14.) -/
theorem not_ffMixedMC (p : ℕ) [Fact (Nat.Prime p)] {Q : Polynomial (ZMod p)} (hm : Q.Monic)
    (hQ : Irreducible Q) : ¬ FFMixedMC p Q := by
  intro h
  obtain ⟨σ, hv, hc⟩ := h Q hm hQ.natDegree_pos
  exact start_not_capturable hv hQ hc

/-- Hence `FFGenMixedMC p` is false for every `p`. -/
theorem not_ffGenMixedMC (p : ℕ) [Fact (Nat.Prime p)] : ¬ FFGenMixedMC p := fun h =>
  not_ffMixedMC p (monic_X) (irreducible_X) (h X monic_X irreducible_X)

end FunctionFieldAnalog

namespace IK

open Finset

/-- The additive large sieve with spacing of *fractional parts* (`IsSpaced`) is false: the
three points `0, 2/5, 4/5` are `2/5`-spaced in that sense although `4/5` and `0` are at distance
`1/5` on the circle, and with `N = 1` the inequality reads `3 ≤ 5/2`.  This was the statement
of `IK.AdditiveLargeSieve` until 2026-11-10; it now uses `IsCircularSpaced`, and so do the
intermediate hypotheses `GramOffDiagBilinearBound`, `CscBilinearBound` and
`HilbertCscBilinearBridge` since 2026-11-11.  (The fractional-parts form of
`GramOffDiagBilinearBound` implied the statement refuted here, by the argument of
`gram_offdiag_bilinear_implies_als`; that derivation is not repeated in Lean.)  (H19.) -/
theorem not_additiveLargeSieve_fractSpaced :
    ¬ ∀ (R N : ℕ) (α : Fin R → ℝ) (a : Fin N → ℂ) (δ : ℝ),
      0 < δ → δ ≤ 1 / 2 → 1 ≤ N → IsSpaced α δ →
      (∑ r, ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2) ≤ (1 / δ + ↑N - 1) * l2NormSq a := by
  intro h
  have h1 : Int.fract (2 / 5 : ℝ) = 2 / 5 :=
    Int.fract_eq_iff.mpr ⟨by norm_num, by norm_num, 0, by norm_num⟩
  have h2 : Int.fract (4 / 5 : ℝ) = 4 / 5 :=
    Int.fract_eq_iff.mpr ⟨by norm_num, by norm_num, 0, by norm_num⟩
  have hsp : IsSpaced (![0, 2 / 5, 4 / 5] : Fin 3 → ℝ) (2 / 5) := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;> simp_all <;> norm_num [abs_le, le_abs]
  have := h 3 1 ![0, 2 / 5, 4 / 5] ![1] (2 / 5) (by norm_num) (by norm_num) le_rfl hsp
  simp [l2NormSq, eAN] at this
  norm_num at this

end IK

namespace HypothesisAudit

open Mullin Euclid MullinGroup

theorem dvd_mixedWalkProd (acc : ℕ) (σ : MixedSelection) (n : ℕ) :
    acc ∣ mixedWalkProd acc σ n := by
  induction n with
  | zero => rw [mixedWalkProd_zero]
  | succ n ih => rw [mixedWalkProd_succ]; exact ih.mul_right _

end HypothesisAudit

/-- The regeneration property (refuted, kept only as the target of
`HypothesisAudit.not_regeneration`; originally in `EM/Stochastic/TreeSieveDecay.lean`): every
valid walk from `m` leads to good intermediate accumulators at every step. -/
def Regeneration (q : ℕ) (m : ℕ) : Prop :=
  ∀ (σ : MixedSelection) (K : ℕ), ValidMixedSelection m σ →
    GoodAccumulator q (mixedWalkProd m σ K)

namespace HypothesisAudit

/-- `Regeneration q m` is unsatisfiable for an odd prime `q` and `m ≥ 2`: it makes `m` a good
accumulator, hence some valid walk captures `q`; after the capture the accumulator is a multiple
of `q`, every accumulator reachable from it is `0` modulo `q`, and `Regeneration` demands that it
be good again.  The definition lacks "while `q` has not been captured".  (H8.) -/
theorem not_regeneration {q : ℕ} (hq : q.Prime) (hq2 : 2 < q) {m : ℕ} (hm : 2 ≤ m) :
    ¬ Regeneration q m := by
  intro h
  have : Fact q.Prime := ⟨hq⟩
  have hvalid0 : ValidMixedSelection m (fun _ => none) := fun _ => trivial
  have hgood : GoodAccumulator q m := by
    have := h (fun _ => none) 0 hvalid0
    rwa [mixedWalkProd_zero] at this
  obtain ⟨σ, n, hv, hcap, -⟩ := good_accumulator_implies_capture q hq hq2 m hm hgood 1 one_pos
  have hdvd : q ∣ mixedWalkProd m σ (n + 1) := by
    rw [mixedWalkProd_succ, hcap]; exact dvd_mul_left _ _
  have hbad := h σ (n + 1) hv 1
  simp only [reachableEver, reachableAt, Set.mem_iUnion, Set.mem_ofPred_eq, Units.val_one] at hbad
  obtain ⟨k, τ, -, hk⟩ := hbad
  rw [(ZMod.natCast_eq_zero_iff _ q).mpr (hdvd.trans (dvd_mixedWalkProd _ τ k))] at hk
  exact zero_ne_one hk

end HypothesisAudit

/-! ## Second batch (2026-11-11): walk layer, ensemble, stochastic -/

open Classical in
/-- **CharSumBound** (collapsed to MC, kept only as the target of
`HypothesisAudit.charSumBound_iff_mc`; originally in `EM/Equidist/FourierB.lean`, where it was
described as "non-trivial character sums over the EM walk are `o(N)`"): for a missing prime
`q` and a non-trivial homomorphism `χ : (ZMod q)ˣ →* G`, the number of steps `n < N` with
`χ (emWalkUnit q n) ≠ 1` is at most `(ε_num / ε_den) · N` for large `N`.

This says that the walk is almost always in `ker χ` — concentration, the opposite of
cancellation — and `ε_num = 0` is allowed. -/
def CharSumBound : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ {G : Type*} [CommGroup G] (χ : (ZMod q)ˣ →* G) (_hχ : ∃ g, χ g ≠ 1),
  ∀ (ε_num ε_den : ℕ) (_hε : 0 < ε_den),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ((Finset.range N).filter (fun n => χ (emWalkUnit q hq hne n) ≠ 1)).card * ε_den ≤
    ε_num * N

namespace HypothesisAudit

/-- `CharSumBound` is contradictory at any missing prime `q`: with `χ` the identity of
`(ZMod q)ˣ` and `ε_num = 0` it forces the walk to be constantly `1` from step `0` on, while
`walk 0 = 2 ≠ 1`.  Hence it is MC by logic alone, with no character-sum content.  (H5.) -/
theorem charSumBound_iff_mc.{u} : CharSumBound.{u} ↔ MullinConjecture := by
  constructor
  · intro h p hp
    by_contra hne
    push Not at hne
    have : Fact (Nat.Prime p) := ⟨(isPrime_iff_natPrime p).mp hp⟩
    let χ : (ZMod p)ˣ →* ULift.{u} (ZMod p)ˣ :=
      (MulEquiv.ulift.symm : (ZMod p)ˣ ≃* ULift.{u} (ZMod p)ˣ).toMonoidHom
    have hχ1 : ∀ g, χ g = 1 → g = 1 := fun g hg =>
      (MulEquiv.map_eq_one_iff (MulEquiv.ulift.symm : (ZMod p)ˣ ≃* ULift.{u} (ZMod p)ˣ)).mp hg
    have hw0 : emWalkUnit p hp hne 0 ≠ 1 := by
      intro h1
      have h2 := congrArg Units.val h1
      simp only [emWalkUnit, Units.val_mk0, walkZ_zero, Units.val_one] at h2
      exact one_ne_zero (α := ZMod p) (by linear_combination h2)
    obtain ⟨N₀, hN₀⟩ := h p hp hne χ ⟨_, fun h1 => hw0 (hχ1 _ h1)⟩ 0 1 one_pos
    have h0 := hN₀ (N₀ + 1) (Nat.le_succ _)
    simp only [zero_mul, mul_one, Nat.le_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff] at h0
    exact h0 (Finset.mem_range.mpr (Nat.succ_pos _)) (fun h1 => hw0 (hχ1 _ h1))
  · intro hmc q _ hq hne
    obtain ⟨n, hn⟩ := hmc q hq
    exact absurd hn (hne n)

end HypothesisAudit

/-- **Excursion Independence Principle (EIP)** (defective, kept only as the subject of
`HypothesisAudit.excursionCharSum_eq_zero_of_excursionIndependence`; originally in
`EM/Transfer/Excursion.lean`): the squared norm of the sum of excursion character sums is
bounded by a constant times the sum of the individual squared norms, over *every list* of
excursions — repetitions allowed. -/
def ExcursionIndependence (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (c : (ZMod q)ˣ) (χ : (ZMod q)ˣ →* ℂˣ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (excs : List (Excursion q hq hne c)),
    ‖(excs.map (excursionCharSum χ)).sum‖ ^ 2 ≤
      C * (excs.map (fun e => ‖excursionCharSum χ e‖ ^ 2)).sum

/-- **Bounded Maximum Excursion** (contradictory at a missing prime, kept only as the subject
of `HypothesisAudit.universalBoundedMax_iff_mc`; originally in `EM/Transfer/Excursion.lean`):
for any `δ > 0`, eventually all excursions ending before step `N` have length at most `δ N`.
An `Excursion` is any pair of visits to `c`, not a first return. -/
def BoundedMaxExcursion (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (c : (ZMod q)ˣ) : Prop :=
  ∀ (δ : ℝ), δ > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (exc : Excursion q hq hne c), exc.stop ≤ N →
      (exc.len : ℝ) ≤ δ * N

/-- **Universal Excursion Independence** (defective, see `ExcursionIndependence`): EIP for
all missing primes, all positions and all nontrivial characters. -/
def UniversalEIP : Prop :=
  ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (c : (ZMod q)ˣ) (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ExcursionIndependence q hq hne c χ

/-- **Universal Bounded Maximum Excursion** (collapsed to MC by
`HypothesisAudit.universalBoundedMax_iff_mc`): `BoundedMaxExcursion` for all missing primes
and all positions. -/
def UniversalBoundedMax : Prop :=
  ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (c : (ZMod q)ˣ),
    BoundedMaxExcursion q hq hne c

namespace HypothesisAudit

/-- `UniversalBoundedMax` is contradictory at any missing prime `q`: by pigeonhole some
position `c` is visited infinitely often; fix a visit `s` and take a later visit
`t > max N₀ (2 s)`.  The pair `(s, t)` is an `Excursion` (the structure does not ask for a
first return) of length `t − s > t / 2`, against the bound `δ · N` at `δ = 1/2`, `N = t`.
Hence it is MC by logic alone.  (H6.) -/
theorem universalBoundedMax_iff_mc : UniversalBoundedMax ↔ MullinConjecture := by
  constructor
  · intro h p hp
    by_contra hne
    push Not at hne
    have : Fact (Nat.Prime p) := ⟨(isPrime_iff_natPrime p).mp hp⟩
    obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber (emWalkUnit p hp hne)
    have hinf : (emWalkUnit p hp hne ⁻¹' {c}).Infinite := Set.infinite_coe_iff.mp hc
    obtain ⟨s, hs⟩ := hinf.nonempty
    obtain ⟨N₀, hN₀⟩ := h p hp hne c (1 / 2) (by norm_num)
    obtain ⟨t, ht, hlt⟩ := hinf.exists_gt (max N₀ (2 * s))
    have h1 : N₀ ≤ t := (le_max_left N₀ (2 * s)).trans hlt.le
    have h2 : 2 * s < t := lt_of_le_of_lt (le_max_right N₀ (2 * s)) hlt
    have hst : s < t := by omega
    have hb := hN₀ t h1 ⟨s, t, hst, hs, ht⟩ le_rfl
    rw [show (Excursion.len (⟨s, t, hst, hs, ht⟩ : Excursion p hp hne c)) = t - s from rfl,
      Nat.cast_sub hst.le] at hb
    have h2' : (2 * s : ℝ) < t := by exact_mod_cast h2
    linarith
  · intro hmc q _ hq hne
    obtain ⟨n, hn⟩ := hmc q hq
    exact absurd hn (hne n)

/-- `ExcursionIndependence` forces every excursion character sum to vanish: the list made of
`m > C` copies of one excursion `e` gives `m² ‖σ_e‖² ≤ C m ‖σ_e‖²`.  So the hypothesis is exact
cancellation over every pair of visits, not approximate independence of disjoint excursions
(in particular it forbids two consecutive visits, whose sum is `1`).  (H6.) -/
theorem excursionCharSum_eq_zero_of_excursionIndependence
    {q : ℕ} [Fact (Nat.Prime q)] {hq : IsPrime q} {hne : ∀ k, seq k ≠ q} {c : (ZMod q)ˣ}
    {χ : (ZMod q)ˣ →* ℂˣ} (h : ExcursionIndependence q hq hne c χ)
    (e : Excursion q hq hne c) : excursionCharSum χ e = 0 := by
  obtain ⟨C, hC, hall⟩ := h
  by_contra hne0
  have hpos : 0 < ‖excursionCharSum χ e‖ := norm_pos_iff.mpr hne0
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have hm0 : (0 : ℝ) < m := lt_trans hC hm
  have key := hall (List.replicate m e)
  simp only [List.map_replicate, List.sum_replicate, nsmul_eq_mul, norm_mul,
    Complex.norm_natCast, mul_pow] at key
  nlinarith [mul_pos (mul_pos hm0 (pow_pos hpos 2)) (sub_pos.mpr hm)]

end HypothesisAudit

open Classical in
/-- **PathSurvival** (refuted at `q = 3`, kept only as the target of
`HypothesisAudit.not_pathSurvival_three`; originally in
`EM/Stochastic/RandomTwoPointMCB.lean`): the survival-to-death ratio of the two-point path
tree grows without bound.  Since dead paths stay dead and the tree is binary, the death
count at least doubles per level, so this can only hold if no path ever dies. -/
def PathSurvival (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (C : ℝ), 0 < C → ∃ N₀, ∀ N, N₀ ≤ N →
    (C : ℝ) * ↑(deathCount q N) < ↑(survivalCount q N)

namespace HypothesisAudit

/-- From the accumulator `2` both choices at step `0` are the prime `3 = 2 + 1`, so `3`
divides every later accumulator. -/
theorem three_dvd_epsWalkProdFrom_two (σ : ℕ → Bool) {N : ℕ} (hN : 1 ≤ N) :
    3 ∣ epsWalkProdFrom 2 σ N := by
  have hmin : Nat.minFac 3 = 3 := Nat.Prime.minFac_eq (by norm_num)
  have h1 : epsWalkFactorFrom 2 σ 0 = 3 := by
    show (if σ 0 then Nat.minFac 3 else secondMinFac 3) = 3
    split
    · exact hmin
    · simp [secondMinFac, hmin]
  have h3 : 3 ∣ epsWalkProdFrom 2 σ 1 := by
    rw [epsWalkProdFrom_succ, h1]; exact dvd_mul_left _ _
  by_contra hnd
  exact not_dvd_epsWalkProdFrom_of_le hnd hN h3

/-- `PathSurvival 3` is false: every two-point path from `2` captures `3` at step `1`, so
`survivalCount 3 N = 0` for `N ≥ 1`.  (H10.) -/
theorem not_pathSurvival_three : ¬ PathSurvival 3 := by
  intro h
  obtain ⟨N₀, hN₀⟩ := h 1 one_pos
  have hlt := hN₀ (N₀ + 1) (Nat.le_succ _)
  have hS : survivalCount 3 (N₀ + 1) = 0 := by
    unfold survivalCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ hu
    rw [(ZMod.natCast_eq_zero_iff _ 3).mpr
      (three_dvd_epsWalkProdFrom_two (finDecisionExtend σ) (Nat.succ_pos N₀))] at hu
    exact not_isUnit_zero hu
  rw [hS, Nat.cast_zero] at hlt
  linarith [Nat.cast_nonneg (α := ℝ) (deathCount 3 (N₀ + 1))]

/-! ### Dense capture (H11): the two defects of the earlier statements

`EM/Stochastic/DenseCapture.lean` was repaired in place; the theorems here record what was
wrong with the earlier forms. -/

/-- The all-`false` selection — the definition of `minFacSeq` until 2026-11-11 — selects the
*second* factor at every step: in `epsWalkFactorFrom`, `true` selects `minFac`. -/
theorem epsWalkFactorFrom_const_false (acc k : ℕ) :
    epsWalkFactorFrom acc (fun _ => false) k =
      secondMinFac (epsWalkProdFrom acc (fun _ => false) k + 1) := by
  simp [epsWalkFactorFrom]

/-- A concrete instance: from the accumulator `5` the all-`false` selection picks `3`, not
`minFac 6 = 2`. -/
theorem epsWalkFactorFrom_const_false_five :
    epsWalkFactorFrom 5 (fun _ => false) 0 = 3 ∧ Nat.minFac (5 + 1) = 2 := by
  have h6 : Nat.minFac 6 = 2 := by norm_num
  have h3 : Nat.minFac 3 = 3 := Nat.Prime.minFac_eq (by norm_num)
  refine ⟨?_, h6⟩
  show secondMinFac 6 = 3
  simp [secondMinFac, h6, h3]

/-- The unguarded dense-capture hypothesis (`DenseCaptureHypothesis q` as stated until
2026-11-11) is false for every `q ≥ 2`: at `acc = q` the capture set is empty. -/
theorem not_denseCapture_unguarded {q : ℕ} (hq : 2 ≤ q) :
    ¬ ∀ acc : ℕ, 2 ≤ acc → Dense (captureSet q acc) := by
  intro h
  have hd := h q hq
  rw [captureSet_eq_empty_of_dvd hq hq dvd_rfl] at hd
  obtain ⟨σ, hσ⟩ := hd.nonempty
  exact (Set.mem_empty_iff_false σ).mp hσ

/-- The hypothesis that `fullCapture_nonempty` and its siblings carried until 2026-11-11 —
density of `captureSet q acc` for *every* prime `q` — is unsatisfiable for every seed
`acc ≥ 2`: it fails at `q = minFac acc`. -/
theorem not_forall_prime_dense_captureSet {acc : ℕ} (hacc : 2 ≤ acc) :
    ¬ ∀ q, Nat.Prime q → Dense (captureSet q acc) := by
  intro h
  have hp : (Nat.minFac acc).Prime := Nat.minFac_prime (by omega)
  have hd := h _ hp
  rw [captureSet_eq_empty_of_dvd hp.two_le hacc (Nat.minFac_dvd acc)] at hd
  obtain ⟨σ, hσ⟩ := hd.nonempty
  exact (Set.mem_empty_iff_false σ).mp hσ

end HypothesisAudit

/-! ### Ensemble base case (H12) -/

/-- **Marginal equidistribution of `genSeq n 0` mod `q`** (refuted, kept only as the target
of `HypothesisAudit.not_jseMarginalEquidist`; originally in `EM/Ensemble/BaseCase.lean`): the
density of squarefree `n` with `genSeq n 0 ≡ a (mod q)`, `a ≠ 0`, tends to `1/(q-1)`.  This
is the step-`0` instance of `EnsembleMultiplierEquidist`. -/
noncomputable def JSEMarginalEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a : ZMod q), a ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeSeqDensity X 0 q a)
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1)))

namespace HypothesisAudit

/-- `JSEMarginalEquidist` is false: at `q = 5` the class of `2` has density `≥ 1/2`, since
`genSeq n 0 = 2` for every odd squarefree seed.  The review described this as "the `k = 0`
instance already refuted by `not_ensembleMultiplierEquidist`"; strictly, refuting `∀ k` does
not refute the instance, but the proof of that theorem used only `k = 0`, and its core is now
`UncenteredRefutations.not_tendsto_sqfreeSeqDensity_zero_five`, from which both follow.
(H12.) -/
theorem not_jseMarginalEquidist : ¬ JSEMarginalEquidist := fun h =>
  UncenteredRefutations.not_tendsto_sqfreeSeqDensity_zero_five
    (h 5 (by decide) (2 : ZMod 5) (by decide))

end HypothesisAudit

/-! ### Factor-bag coverage (H13) -/

namespace IteratedProduct

/-- **FactorBagCoverage** (refuted, kept only as the target of
`HypothesisAudit.not_factorBagCoverage`; originally in
`EM/Stochastic/IteratedProductCoverage.lean`): for *any* sequence of subsets of `(ZMod q)ˣ`
of size `≥ 2`, the iterated product after `q − 2` steps is the whole group. -/
def FactorBagCoverage (q : ℕ) : Prop :=
  ∀ [Fact (Nat.Prime q)], ∀ (S : ℕ → Finset (ZMod q)ˣ),
    (∀ k, (S k).Nonempty) →
    (∀ k, 2 ≤ (S k).card) →
    ∀ a : (ZMod q)ˣ, a ∈ iteratedMulFinset S (Fintype.card (ZMod q)ˣ - 1)

end IteratedProduct

namespace HypothesisAudit

open IteratedProduct in
/-- `FactorBagCoverage q` is false for every prime `q ≥ 5`: with `S k = {1, -1}` for all `k`
the iterated product never leaves the subgroup `{1, -1}`, which has `2 < q − 1` elements.
The true statement needs `minOrder G = |G|` (`IteratedProduct.target_reached`).  (H13.) -/
theorem not_factorBagCoverage {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) :
    ¬ FactorBagCoverage q := by
  intro h
  have : Fact q.Prime := ⟨hq⟩
  have hne : (1 : (ZMod q)ˣ) ≠ -1 := by
    intro h1
    have h2 : (1 : ZMod q) = -1 := by simpa using congrArg Units.val h1
    have h3 : ((2 : ℕ) : ZMod q) = 0 := by push_cast; linear_combination h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hsub : ∀ n, iteratedMulFinset (fun _ => ({1, -1} : Finset (ZMod q)ˣ)) n ⊆ {1, -1} := by
    intro n
    induction n with
    | zero => rw [iteratedMulFinset_zero]; simp
    | succ n ih =>
      rw [iteratedMulFinset_succ]
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
      have ha' := ih ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb ⊢
      rcases ha' with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  have hcard : 4 ≤ Fintype.card (ZMod q)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]; omega
  obtain ⟨a, ha⟩ : ∃ a : (ZMod q)ˣ, a ∉ ({1, -1} : Finset (ZMod q)ˣ) := by
    by_contra hall
    push Not at hall
    have h1 : Fintype.card (ZMod q)ˣ ≤ ({1, -1} : Finset (ZMod q)ˣ).card := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (fun x _ => hall x)
    have h2 : ({1, -1} : Finset (ZMod q)ˣ).card ≤ 2 := Finset.card_le_two
    omega
  exact ha (hsub _ (h (fun _ => {1, -1}) (fun _ => ⟨1, by simp⟩)
    (fun _ => by rw [Finset.card_pair hne]) a))

end HypothesisAudit

/-! ## Third batch (2026-11-11): function field, analytic layer -/

namespace FunctionFieldAnalog

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### Function-field "bridges" (H17): each is `FFMullinConjecture p` -/

/-- `FFDynamicalHitting` and `FFMullinConjecture` are equivalent.  The forward direction is the
bootstrap `ff_dh_implies_ffmc_unconditional`; the converse is by logic alone, because
`FFDynamicalHitting` only speaks about irreducibles that never appear. -/
theorem ffDynamicalHitting_iff_ffmc : FFDynamicalHitting (p := p) ↔ FFMullinConjecture p :=
  ⟨ff_dh_implies_ffmc_unconditional,
   fun h d Q hQm hQi hne => absurd (h d Q hQm hQi) (fun ⟨n, hn⟩ => hne n hn)⟩

/-- The bridge `FFMultiplierCCSB ⟹ FFDynamicalHitting` (collapsed, kept only as the target of
`ffMultCCSBImpliesFFDH_iff_ffmc`; originally in `EM/FunctionField/MultiplierCCSB.lean`).  Its
premise is a `True`-bodied placeholder. -/
def FFMultCCSBImpliesFFDH : Prop :=
  FFMultiplierCCSB p → FFDynamicalHitting (p := p)

/-- The bridge `FFDSLAnalog ⟹ FFDynamicalHitting` (collapsed; originally in
`EM/FunctionField/MultiplierCCSB.lean`).  Its premise is a `True`-bodied placeholder. -/
def FFDSLImpliesFFDH : Prop :=
  FFDSLAnalog p → FFDynamicalHitting (p := p)

/-- The bridge "subgroup escape at all degrees ⟹ FF-MC" (collapsed; originally in
`EM/FunctionField/SubgroupEscape.lean`).  Its premise is a `True`-bodied placeholder. -/
def FFDH_from_SE : Prop :=
  (∀ d, FFSubgroupEscape p d) → FFMullinConjecture p

/-- The bridge `FFCME ⟹ FF-MC` (collapsed; originally in `EM/FunctionField/Analog.lean`).  Its
premise is a `True`-bodied placeholder. -/
def FFCMEImpliesFFMC : Prop :=
  FFCME p → FFMullinConjecture p

/-- The "monodromy chain" `FFLargeMonodromy ⟹ DeligneEquidistribution ⟹ FF-MC` (collapsed;
originally in `EM/FunctionField/Analog.lean`).  The first premise is the proxy `|Gal| > 1`,
which is a theorem (`ffLargeMonodromy`); the second is a `True`-bodied placeholder. -/
def FFLMChainImpliesFFMC : Prop :=
  FFLargeMonodromy p → DeligneEquidistribution p → FFMullinConjecture p

/-- `FFMultCCSBImpliesFFDH p` is `FFMullinConjecture p`.  (H17.) -/
theorem ffMultCCSBImpliesFFDH_iff_ffmc : FFMultCCSBImpliesFFDH p ↔ FFMullinConjecture p :=
  ⟨fun h => (ffDynamicalHitting_iff_ffmc p).mp (h fun _ _ _ _ _ _ => trivial),
   fun h _ => (ffDynamicalHitting_iff_ffmc p).mpr h⟩

/-- `FFDSLImpliesFFDH p` is `FFMullinConjecture p`.  (H17.) -/
theorem ffDSLImpliesFFDH_iff_ffmc : FFDSLImpliesFFDH p ↔ FFMullinConjecture p :=
  ⟨fun h => (ffDynamicalHitting_iff_ffmc p).mp (h fun _ _ _ _ _ => trivial),
   fun h _ => (ffDynamicalHitting_iff_ffmc p).mpr h⟩

/-- `FFDH_from_SE p` is `FFMullinConjecture p`.  (H17.) -/
theorem ffDH_from_SE_iff_ffmc : FFDH_from_SE p ↔ FFMullinConjecture p :=
  ⟨fun h => h fun _ _ _ _ _ => trivial, fun h _ => h⟩

/-- `FFCMEImpliesFFMC p` is `FFMullinConjecture p`.  (H17.) -/
theorem ffCMEImpliesFFMC_iff_ffmc : FFCMEImpliesFFMC p ↔ FFMullinConjecture p :=
  ⟨fun h => h fun _ _ _ _ _ _ => trivial, fun h _ => h⟩

/-- `FFLMChainImpliesFFMC p` is `FFMullinConjecture p`.  (H15, H17.) -/
theorem ffLMChainImpliesFFMC_iff_ffmc : FFLMChainImpliesFFMC p ↔ FFMullinConjecture p :=
  ⟨fun h => h ffLargeMonodromy (fun _ _ => trivial), fun h _ _ => h⟩

/-- All five bridges are false over `𝔽_5`, where the function-field Mullin conjecture fails
(`not_ffMullinConjecture_five`).  Every theorem that assumed one of them was therefore vacuous
at `p = 5` and, for every `p`, assumed its own conclusion. -/
theorem not_ffBridges_five :
    ¬ FFMultCCSBImpliesFFDH 5 ∧ ¬ FFDSLImpliesFFDH 5 ∧ ¬ FFDH_from_SE 5 ∧
      ¬ FFCMEImpliesFFMC 5 ∧ ¬ FFLMChainImpliesFFMC 5 :=
  ⟨fun h => not_ffMullinConjecture_five ((ffMultCCSBImpliesFFDH_iff_ffmc 5).mp h),
   fun h => not_ffMullinConjecture_five ((ffDSLImpliesFFDH_iff_ffmc 5).mp h),
   fun h => not_ffMullinConjecture_five ((ffDH_from_SE_iff_ffmc 5).mp h),
   fun h => not_ffMullinConjecture_five ((ffCMEImpliesFFMC_iff_ffmc 5).mp h),
   fun h => not_ffMullinConjecture_five ((ffLMChainImpliesFFMC_iff_ffmc 5).mp h)⟩

theorem not_ffMultCCSBImpliesFFDH_five : ¬ FFMultCCSBImpliesFFDH 5 := not_ffBridges_five.1

/-! ### `WeilDoesNotImplyFFDSL` (H16) -/

/-- "The Weil bound does not imply FF-DSL" (refuted, kept only as the target of
`not_weilDoesNotImplyFFDSL`; originally in `EM/FunctionField/Analog.lean`, where it was called
the precise formal statement of Dead End #127).  Both `WeilBound` and `FFDSL` are `True`-bodied
placeholders, so this is `¬ (True → True)`. -/
def WeilDoesNotImplyFFDSL : Prop :=
  ¬ (WeilBound p → FFDSL p)

/-- `WeilDoesNotImplyFFDSL p` is false for every `p`.  Dead End #127 has no formal statement.
(H16.) -/
theorem not_weilDoesNotImplyFFDSL : ¬ WeilDoesNotImplyFFDSL p :=
  fun h => h fun _ _ _ _ _ _ => trivial

/-! ### `DegreeBoundedHitting` (H18) -/

/-- Degree-bounded hitting as originally stated (trivial, kept only as the target of
`degreeBoundedHitting_trivial`; originally in `EM/FunctionField/MultiplierCCSB.lean`): for every
degree bound `D ≥ 1` there is *some* `n` such that `ffProd n + 1` has an irreducible factor of
degree `≤ D`. -/
def DegreeBoundedHitting : Prop :=
  ∀ (d : FFEMData p) (D : ℕ), 1 ≤ D →
    ∃ n, ∃ f : Polynomial (ZMod p),
      f.Monic ∧ Irreducible f ∧ f ∣ (d.ffProd n + 1) ∧ f.natDegree ≤ D

/-- `DegreeBoundedHitting p` holds for every `p`, with `n = 0`: `ffProd 0 + 1 = X + 1` is
linear.  (This is the proof of the archived `ff_dh_implies_degree_bounded`, which never used its
hypothesis `FFDynamicalHitting`.)  (H18.) -/
theorem degreeBoundedHitting_trivial : DegreeBoundedHitting p := by
  intro d D hD
  have hX : (X : Polynomial (ZMod p)) + 1 = X - C (-1) := by simp [sub_eq_add_neg]
  refine ⟨0, X + 1, ?_, ?_, ?_, ?_⟩
  · rw [hX]; exact monic_X_sub_C _
  · rw [hX]; exact irreducible_X_sub_C _
  · rw [d.ffProd_zero]
  · rw [hX, natDegree_X_sub_C]; exact hD

/-- The cofinal form that the docstring of `DegreeBoundedHitting` described ("the minimum degree
of the irreducible factors of `ffProd n + 1` does not tend to infinity").  Refuted below. -/
def DegreeBoundedHittingCofinal : Prop :=
  ∀ (d : FFEMData p), ∃ D : ℕ, ∀ N, ∃ n, N ≤ n ∧ ∃ f : Polynomial (ZMod p),
    f.Monic ∧ Irreducible f ∧ f ∣ (d.ffProd n + 1) ∧ f.natDegree ≤ D

/-- For every sequence and every bound `D`, from some stage on every monic irreducible factor
of the Euclid polynomial has degree `> D`: the selected factor has least degree, and the
selected degree tends to infinity (`ffSeq_degree_tendsto_atTop_unconditional`). -/
theorem eventually_euclid_factors_natDegree_gt (d : FFEMData p) (D : ℕ) :
    ∃ N₀, ∀ n, N₀ ≤ n → ∀ f : Polynomial (ZMod p),
      f.Monic → Irreducible f → f ∣ (d.ffProd n + 1) → D < f.natDegree := by
  have ht := ffSeq_degree_tendsto_atTop_unconditional d
  obtain ⟨N₀, hN₀⟩ := (Filter.tendsto_atTop.mp ht (D + 1)).exists_forall_of_atTop
  refine ⟨N₀, fun n hn f hfm hfi hfd => ?_⟩
  have h1 := d.ffSeq_minimal n f hfm hfi hfd
  have h2 := hN₀ (n + 1) (by omega)
  omega

/-- The cofinal form of degree-bounded hitting is false for every `p`: the minimum degree of the
irreducible factors of `ffProd n + 1` *does* tend to infinity, for every sequence.  So the
repair of `DegreeBoundedHitting` suggested by its docstring yields a refutable statement; in
particular it is not "weaker than `FFDynamicalHitting`".  (H18.) -/
theorem not_degreeBoundedHittingCofinal : ¬ DegreeBoundedHittingCofinal p := by
  intro h
  obtain ⟨d⟩ := (inferInstance : Nonempty (FFEMData p))
  obtain ⟨D, hD⟩ := h d
  obtain ⟨N₀, hN₀⟩ := eventually_euclid_factors_natDegree_gt p d D
  obtain ⟨n, hn, f, hfm, hfi, hfd, hdeg⟩ := hD N₀
  have := hN₀ n hn f hfm hfi hfd
  omega

end FunctionFieldAnalog

/-! ### `KernelRowSumBound` (H20) -/

/-- The kernel row-sum hypothesis (refuted, kept only as the target of
`HypothesisAudit.not_kernelRowSumBound`; originally in `EM/LargeSieve/Harmonic.lean`): for
well-separated `α` with minimal circular distance `δ`, every *absolute* row sum of the
trigonometric kernel is at most `N - 1 + δ⁻¹`. -/
def KernelRowSumBound : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (R : ℕ) (α : Fin R → ℝ) (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hsep : ∀ r s : Fin R, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|),
    ∀ m : Fin N, ∑ n : Fin N, ‖trigKernel R α (↑m - ↑n)‖ ≤ (N : ℝ) - 1 + δ⁻¹

namespace HypothesisAudit

/-- `e(-1/3)` is a primitive cube root of unity: `ζ³ = 1`, `ζ ≠ 1`, hence `1 + ζ + ζ² = 0`. -/
theorem eAN_neg_third :
    eAN (-(1 / 3)) ^ 3 = 1 ∧ 1 + eAN (-(1 / 3)) + eAN (-(1 / 3)) ^ 2 = 0 := by
  set ζ : ℂ := eAN (-(1 / 3)) with hζ
  have h3 : ζ ^ 3 = 1 := by
    have : ζ ^ 3 = eAN ((-1 : ℤ) : ℝ) := by
      rw [hζ, pow_succ, pow_two, ← eAN_add, ← eAN_add]; congr 1; push_cast; ring
    rw [this, eAN_intCast]
  have hne : ζ ≠ 1 := by
    intro h1
    rw [hζ, eAN, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : ((-(1 / 3) : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      rw [hn]; ring
    have h4 : (-(1 / 3) : ℝ) = (n : ℝ) := by exact_mod_cast h2
    have h5 : (3 * n : ℝ) = -1 := by rw [← h4]; norm_num
    have h6 : (3 * n : ℤ) = -1 := by exact_mod_cast h5
    omega
  refine ⟨h3, ?_⟩
  have hfac : (ζ - 1) * (1 + ζ + ζ ^ 2) = 0 := by ring_nf; rw [h3]; ring
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)

/-- `KernelRowSumBound` is false.  Take `R = 2`, `α = (0, 1/3)`, `δ = 1/3`, `N = 7`: the kernel
is `K(k) = 1 + e(k/3)`, of absolute value `2` when `3 ∣ k` and `1` otherwise, so the row `m = 0`
sums to `2+1+1+2+1+1+2 = 10 > 9 = N - 1 + δ⁻¹`.  The sharp large sieve bound holds for the
bilinear form (with cancellation between the kernel values), not for absolute row sums, which
exceed `N` by a constant factor.  (H20.) -/
theorem not_kernelRowSumBound : ¬ KernelRowSumBound := by
  intro h
  set α : Fin 2 → ℝ := ![0, 1 / 3] with hα
  have hsep : ∀ r s : Fin 2, r ≠ s → (1 / 3 : ℝ) ≤ |α r - α s - round (α r - α s)| := by
    intro r s hrs
    apply IK.le_abs_sub_round_of_abs
    · fin_cases r <;> fin_cases s <;> simp [hα] at hrs ⊢
    · fin_cases r <;> fin_cases s <;> simp [hα] at hrs ⊢ <;> norm_num [abs_le, le_abs]
  have key := h 7 (by norm_num) 2 α (1 / 3) (by norm_num) (by norm_num) hsep ⟨0, by norm_num⟩
  obtain ⟨h3, hsum⟩ := eAN_neg_third
  set ζ : ℂ := eAN (-(1 / 3)) with hζ
  have hnorm : ‖ζ‖ = 1 := eAN_norm _
  have hpow : ∀ n : ℕ, eAN (-(n : ℝ) * (1 / 3)) = ζ ^ n := by
    intro n
    induction n with
    | zero => simp [eAN_zero]
    | succ n ih =>
      rw [pow_succ, ← ih, hζ, ← eAN_add]; congr 1; push_cast; ring
  have hK : ∀ n : Fin 7, trigKernel 2 α (((⟨0, by norm_num⟩ : Fin 7) : ℕ) - (n : ℕ)) =
      1 + ζ ^ (n : ℕ) := by
    intro n
    rw [trigKernel, Fin.sum_univ_two, ← hpow]
    simp [hα, eAN_zero]
  have h1 : ‖(1 : ℂ) + 1‖ = 2 := by norm_num
  have h2 : ‖1 + ζ‖ = 1 := by
    have : 1 + ζ = -ζ ^ 2 := by linear_combination hsum
    rw [this, norm_neg, norm_pow, hnorm, one_pow]
  have h4 : ‖1 + ζ ^ 2‖ = 1 := by
    have : 1 + ζ ^ 2 = -ζ := by linear_combination hsum
    rw [this, norm_neg, hnorm]
  have e4 : ζ ^ 4 = ζ := by rw [show 4 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  have e5 : ζ ^ 5 = ζ ^ 2 := by rw [show 5 = 3 + 2 from rfl, pow_add, h3, one_mul]
  have e6 : ζ ^ 6 = 1 := by rw [show 6 = 3 + 3 from rfl, pow_add, h3, one_mul]
  simp only [hK] at key
  rw [Fin.sum_univ_eq_sum_range (fun n => ‖1 + ζ ^ n‖) 7] at key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, h3, e4, e5, e6, h1,
    h2, h4] at key
  norm_num at key

end HypothesisAudit

/-! ### `EMHasLevelOfDistribution` (H22) -/

/-- "EM has level of distribution `θ`" (trivial, kept only as the target of
`HypothesisAudit.emHasLevelOfDistribution_iff`; originally in `EM/LargeSieve/Basic.lean`): for
every `A > 0` and all large `N`, the walk character sum of length `N` at a missing prime
`q ≤ (prod N)^θ / (log prod N)^A` is at most `(prod N)^θ / (log prod N)^A`. -/
def EMHasLevelOfDistribution (θ : ℝ) : Prop :=
  0 < θ ∧ θ ≤ 1 ∧
  ∀ (A : ℝ) (_ : 0 < A),
  ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    (q : ℝ) ≤ (prod N : ℝ) ^ θ / (Real.log (prod N : ℝ)) ^ A →
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_ : χ ≠ 1),
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
      (prod N : ℝ) ^ θ / (Real.log (prod N : ℝ)) ^ A

namespace HypothesisAudit

/-- `EMHasLevelOfDistribution θ` holds for every `θ ∈ (0, 1]`, i.e. it says nothing about the
sequence: its bound `(prod N)^θ / (log prod N)^A` eventually exceeds the trivial bound `N`,
because `prod N ≥ 2^N` gives `N ≤ 2 log (prod N)` and `(log x)^{A+1} = o(x^θ)`.  Hence
`LoDImpliesMMCSB θ` was `MultiModularCSB` itself and `lod_chain_mc` was `mmcsb_implies_mc`.
(H22; Dead End #96.) -/
theorem emHasLevelOfDistribution_iff (θ : ℝ) : EMHasLevelOfDistribution θ ↔ 0 < θ ∧ θ ≤ 1 := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨h0, h1⟩ => ⟨h0, h1, fun A hA => ?_⟩⟩
  have hev := (isLittleO_log_rpow_rpow_atTop (A + 1) h0).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨N₀, hN₀⟩ := prod_growth_eventually_exceeds (max ⌈X₀⌉₊ 3)
  refine ⟨N₀, fun N hN q _ hq hne _ χ _ => ?_⟩
  have hP3 : (3 : ℝ) ≤ (prod N : ℝ) := by
    exact_mod_cast le_trans (le_max_right _ _) (hN₀ N hN)
  have hPX : X₀ ≤ (prod N : ℝ) :=
    (Nat.le_ceil X₀).trans (by exact_mod_cast le_trans (le_max_left _ _) (hN₀ N hN))
  have hL : 0 < Real.log (prod N : ℝ) := Real.log_pos (by linarith)
  have hLA : 0 < Real.log (prod N : ℝ) ^ A := Real.rpow_pos_of_pos hL A
  -- the trivial bound
  have htriv : ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ N := by
    calc ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖
        ≤ ∑ n ∈ Finset.range N, ‖(χ (emWalkUnit q hq hne n) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_congr rfl fun n _ => char_norm_one_of_hom χ _
      _ = N := by simp
  -- `N ≤ 2 log (prod N)`
  have hN2 : (N : ℝ) ≤ 2 * Real.log (prod N : ℝ) := by
    have h2N : ((2 : ℝ) ^ N) ≤ (prod N : ℝ) := by exact_mod_cast prod_exponential_lower N
    have := Real.log_le_log (by positivity) h2N
    rw [Real.log_pow] at this
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  -- `2 (log P)^{A+1} ≤ P^θ`
  have hb := hX₀ (prod N : ℝ) hPX
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_add_one hL.ne'] at hb
  refine htriv.trans ((le_div_iff₀ hLA).mpr ?_)
  nlinarith [mul_le_mul_of_nonneg_right hN2 hLA.le]

end HypothesisAudit

/-! ### Iwaniec–Kowalski Chapter 5 samples (H24) -/

namespace IK

/-- "The Grand Riemann Hypothesis for `L`" as transcribed in `EM/IK/Ch5.lean` (refuted, kept
only as the target of `IK.not_grandRiemannHypothesis`): the variable `ρ` ranges over *all*
complex numbers in the open strip, not over the zeros of `L(f, s)`, and `_L` is unused. -/
def GrandRiemannHypothesis (_L : LFunctionData) : Prop :=
  ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2

/-- The transcription says "every point of the critical strip lies on the critical line";
`ρ = 1/4` refutes it, for every `L`.  (H24.) -/
theorem not_grandRiemannHypothesis (L : LFunctionData) : ¬ GrandRiemannHypothesis L := by
  intro h
  have := h (1 / 4 : ℝ) (by norm_num) (by norm_num)
  norm_num at this

/-- Siegel's bound as transcribed in `EM/IK/Ch5.lean` (refuted, kept only as the target of
`IK.not_siegelBound`): `β` ranges over all real numbers, not over the exceptional zero of a
real primitive character modulo `q`. -/
def SiegelBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ (c : ℝ), 0 < c ∧
      ∀ (q : ℕ), 1 ≤ q →
        ∀ (β : ℝ), β ≤ 1 - c / (q : ℝ) ^ ε

/-- The transcription bounds every real number by `1 - c`; `β = 1` refutes it.  (H24.) -/
theorem not_siegelBound : ¬ SiegelBound := by
  intro h
  obtain ⟨c, hc, hb⟩ := h 1 one_pos
  have := hb 1 le_rfl 1
  simp at this
  linarith

/-- The convexity bound for Dirichlet `L`-functions as transcribed in `EM/IK/Ch5.lean` (refuted,
kept only as the target of `IK.not_dirichletConvexityBound`): `Lfs` ranges over all complex
numbers, not over the value `L(s, χ)`. -/
def DirichletConvexityBound : Prop :=
  ∃ (C : ℝ), 0 < C ∧
    ∀ (q : ℕ), 1 ≤ q →
      ∀ (s : ℂ), s.re = 1 / 2 →
        ∀ (Lfs : ℂ), ‖Lfs‖ ≤ C * ((q : ℝ) * ‖s‖) ^ (1 / 4 : ℝ)

/-- The transcription bounds every complex number by a fixed constant.  (H24.) -/
theorem not_dirichletConvexityBound : ¬ DirichletConvexityBound := by
  rintro ⟨C, -, h⟩
  have := h 1 le_rfl (1 / 2 : ℝ) (by simp)
    ((C * (((1 : ℕ) : ℝ) * ‖((1 / 2 : ℝ) : ℂ)‖) ^ (1 / 4 : ℝ) + 1 : ℝ) : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  linarith [le_abs_self (C * (((1 : ℕ) : ℝ) * ‖((1 / 2 : ℝ) : ℂ)‖) ^ (1 / 4 : ℝ) + 1)]

end IK
