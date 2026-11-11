import EM.Adelic.Profinite
import EM.SDDS.Reduction
import EM.Equidist.Fourier
import EM.Stochastic.ReachableSets
import EM.Stochastic.TreeSieveDecay
import EM.Equidist.SieveTransfer
import EM.FunctionField.FactorTree
import EM.IK.Ch7AdditiveLS
import EM.Obstruction.NoInvariant

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

The recurring cause is a degenerate parameter value left inside a quantifier: `k = 0`,
`N = 0`, the prime `2`, a seed equal to the target, fractional parts in place of the distance
on the circle.
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
of `IK.AdditiveLargeSieve` until 2026-11-10; it now uses `IsCircularSpaced`.  The intermediate
hypotheses `GramOffDiagBilinearBound` and `CscBilinearBound` still use `IsSpaced`.  (H19.) -/
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
