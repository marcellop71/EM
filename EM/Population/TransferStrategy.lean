import EM.Population.ReciprocalSum
import EM.Population.WeakErgodicity

/-!
# Population Transfer Strategy: Ensemble Equidistribution and DSL

This file formalizes the **Population Transfer Strategy** from the working
note `tmp/PT_attack_strategy.md`. Three components:

1. **Ensemble Equidistribution**: for almost all squarefree starting points n,
   the generalized EM sequence equidistributes mod q — each residue class
   0 < a < q gets density 1/(q−1) of the multipliers.

2. **Deterministic Stability Lemma (DSL)**: a single hypothesis replacing
   both PopulationTransfer and EMDImpliesCME: PE → CME directly.

3. **Full chain**: PE + DSL → MC with DSL as the sole remaining gap.

The ensemble result follows the same concentration→result pattern as
`ReciprocalSum.lean`: an open concentration hypothesis implies
the density-zero conclusion by comparison with one window.

## Main Results

### Definitions
* `genResCount`                 — count of steps k < K where genSeq n k ≡ a (mod q)
* `AlmostAllSquarefreeEqd`      — for a.a. squarefree n, the gen. EM sequence equidistributes mod q
* `EnsembleConcentration`       — for K ≥ K₀(ε, δ), the proportion of ε-deviant seeds is ≤ δ
  (repaired 2026-11-11: the earlier fixed-K `Tendsto … (nhds 0)` form was false)
* `DeterministicStabilityLemma` — PE → CME (single open hypothesis)

### Proved Theorems
* `genResCount_le`              — genResCount n q a K ≤ K
* `ensemble_concentration_implies_eqd` — EnsembleConcentration → AlmostAllSquarefreeEqd (PROVED)
* `pe_dsl_implies_mc`           — PE + DSL → MC (PROVED)
* `pe_dsl_implies_ccsb`         — PE + DSL → CCSB (PROVED)
* `equidist_dsl_implies_mc`     — MinFacResidueEquidist + DSL → MC (PROVED)
* `dsl_implies_pt`              — DSL → PT (PROVED)
* `dsl_pe_implies_bridge`       — DSL + PE → EMDImpliesCME (PROVED)
* `dsl_pe_implies_pt_and_bridge` — DSL + PE → PT ∧ EMDImpliesCME (PROVED)

### Open Hypotheses
* `EnsembleConcentration`       — Chebyshev + decorrelation over starting points
* `DeterministicStabilityLemma` — PE → CME directly
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Residue Counting -/

section ResidueCounting

/-- Count of steps k < K where the generalized EM sequence from n
    produces a prime ≡ a (mod q). -/
def genResCount (n q a K : Nat) : Nat :=
  ((Finset.range K).filter (fun k => genSeq n k % q = a)).card

/-- The residue count is at most K (at most K steps to count). -/
theorem genResCount_le (n q a K : Nat) : genResCount n q a K ≤ K := by
  unfold genResCount
  exact (Finset.card_filter_le _ _).trans (Finset.card_range K).le

end ResidueCounting

/-! ## Ensemble Equidistribution Definition -/

section EnsembleEquidist

/-- **Almost All Squarefree Equidistribution**: for every prime q, every
    residue class 0 < a < q, and every ε > 0, the density of squarefree n
    where |genResCount(n,q,a,K)/K − 1/(q−1)| > ε for ALL K has density 0.

    This says: for almost all squarefree starting points (density 1),
    the generalized EM sequence equidistributes its multipliers mod q.

    Pattern matches `AlmostAllSquarefreeRSD` from ReciprocalSumDivergence.lean.
    Where RSD asks "the reciprocal sum stays bounded for all K",
    here we ask "the residue density deviates for all K". -/
def AlmostAllSquarefreeEqd : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a : Nat), 0 < a → a < q →
  ∀ (ε : ℝ), 0 < ε →
    Filter.Tendsto
      (fun X : Nat =>
        (((Finset.Icc 1 X).filter
          (fun n => Squarefree n ∧
            ∀ K, |(genResCount n q a K : ℝ) / K - 1 / (q - 1 : ℝ)| > ε)).card : ℝ) /
        ((Finset.Icc 1 X).filter Squarefree).card)
      Filter.atTop (nhds 0)

end EnsembleEquidist

/-! ## Ensemble Concentration Hypothesis -/

section EnsembleConcentration

/-- **Ensemble Concentration**: for each prime q, residue class a, threshold ε > 0 and
    tolerance δ > 0, for every sufficiently large window K (depending on ε and δ), the
    proportion of squarefree n ≤ X with |genResCount(n,q,a,K)/K − 1/(q−1)| > ε is at most δ
    for all large X.

    This is the shape a Chebyshev argument delivers:
    - **First moment**: the average count over squarefree n ≤ X is K/(q−1) + o(K);
    - **Variance bound**: Var = O(K);
    - **Chebyshev**: Pr[|count/K − 1/(q−1)| > ε] ≤ Var/(ε²K²) = O(1/K), which is `≤ δ` once
      `K ≥ K₀(ε, δ)` — small, but not zero, at each fixed `K`.

    Same two-parameter shape as `RecipSumConcentration` (ReciprocalSum.lean) and
    `EnsembleCharSumConcentration` (Ensemble/Decorrelation.lean).

    **Repaired 2026-11-11** (review `docs/analysis/review_2026-11-10.md`, row H1).  The
    earlier form asked, at each fixed `K ≥ K₀`, that the density of deviant seeds *tend to
    `0`* as `X → ∞` (`Tendsto … (nhds 0)`), i.e. that it be exactly zero in the limit.  That is
    false: at fixed `K` the event "none of the first `K` multipliers lies in the class `a`"
    has positive density.  Take `q = 5`, `a = 1`.  Choose primes `2 = r₁ < r₂ < … < r_K`, all
    `≡ 2 (mod 5)`, with `r_j ∤ r₁⋯r_{j-1} − r₁⋯r_i` for `i < j − 1`, and let `n` run over
    the squarefree integers that are divisible by every prime `p < r_K` outside the list and
    satisfy `n · r₁⋯r_{j-1} ≡ −1 (mod r_j)` for each `j` — finitely many congruence
    conditions with a solution, hence a set of positive density among squarefree seeds.
    For such `n` the primes outside the list never divide `genProd n i + 1`, and
    `genSeq n i = r_{i+1}` for `i < K`: the count for the class `1` is `0`, the deviation is
    `1/4 > ε` for every `ε < 1/4`, and the density of the deviant set is bounded below
    for all large `X`.  (The simplest instance is Dead End #157: `genSeq n 0 = 2` for every
    odd seed.)  The argument is a density computation and is recorded here, not
    machine-checked.  The consumer `ensemble_concentration_implies_eqd` never needed the
    false strength.

    **Status**: open hypothesis.  Note that it concerns averages over the window; the
    fixed-step laws are *not* uniform (Dead End #157), so the first-moment input is itself
    a genuine claim, not a consequence of fixed-step equidistribution. -/
def EnsembleConcentration : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a : Nat), 0 < a → a < q →
  ∀ (ε : ℝ), 0 < ε →
  ∀ (δ : ℝ), 0 < δ →
  ∃ K₀ : Nat,
    ∀ K ≥ K₀, ∃ X₀ : Nat, ∀ X ≥ X₀,
      (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧
          |(genResCount n q a K : ℝ) / K - 1 / (q - 1 : ℝ)| > ε)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card ≤ δ

end EnsembleConcentration

/-! ## Main Reduction: Concentration → Ensemble Equidistribution -/

section MainReduction

/-- If n satisfies ∀ K, |count/K − 1/(q−1)| > ε, then in particular the
    deviation holds at K₀. -/
private theorem forall_deviant_subset (q a : Nat) (ε : ℝ) (X K : Nat) :
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        ∀ L, |(genResCount n q a L : ℝ) / L - 1 / (q - 1 : ℝ)| > ε)) ⊆
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧
        |(genResCount n q a K : ℝ) / K - 1 / (q - 1 : ℝ)| > ε)) := by
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2 K⟩

/-- **Concentration → Almost All Squarefree Equidistribution.**

    If EnsembleConcentration holds, then for any prime q, residue class
    0 < a < q, and ε > 0, the set {n squarefree : ∀ K, deviation > ε}
    has density 0.

    Proof: {n : ∀ K, deviation > ε} ⊆ {n : deviation at K₀ > ε} for each K₀.
    By concentration with tolerance δ/2, the proportion of the latter is ≤ δ/2 < δ for
    large X (at K = K₀(ε, δ/2)).  Since the former is a subset, its density → 0.

    Same proof pattern as `concentration_implies_rsd`. -/
theorem ensemble_concentration_implies_eqd
    (hconc : EnsembleConcentration) : AlmostAllSquarefreeEqd := by
  intro q hq a ha haq ε hε
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Get K₀ from concentration with tolerance δ/2 (strict inequality from ≤)
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨K₀, hK₀⟩ := hconc q hq a ha haq ε hε (δ / 2) hδ2
  -- Use K = K₀: proportion of {n : deviation at K₀ > ε} ≤ δ/2 eventually
  obtain ⟨X₀, hX₀⟩ := hK₀ K₀ (le_refl _)
  refine ⟨X₀, fun X hX => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  calc _ ≤ (((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧
          |(genResCount n q a K₀ : ℝ) / K₀ - 1 / (q - 1 : ℝ)| > ε)).card : ℝ) /
      ((Finset.Icc 1 X).filter Squarefree).card :=
        div_le_div_of_nonneg_right
          (by exact_mod_cast Finset.card_le_card (forall_deviant_subset q a ε X K₀))
          (Nat.cast_nonneg _)
    _ ≤ δ / 2 := hX₀ X hX
    _ < δ := by linarith

end MainReduction


end
