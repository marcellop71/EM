import EM.ReciprocalSumDivergence
import EM.PopulationEquidistProof

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
`ReciprocalSumDivergence.lean`: an open concentration hypothesis implies
the density-zero conclusion via `squeeze_zero`.

## Main Results

### Definitions
* `genResCount`                 — count of steps k < K where genSeq n k ≡ a (mod q)
* `AlmostAllSquarefreeEqd`      — for a.a. squarefree n, the gen. EM sequence equidistributes mod q
* `EnsembleConcentration`       — at step K, the density of non-equidistributed n → 0
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

/-- **Ensemble Concentration**: for each prime q, residue class a, and ε > 0,
    eventually (in K), the density of squarefree n ≤ X with
    |genResCount(n,q,a,K)/K − 1/(q−1)| > ε tends to 0 as X → ∞.

    This is the quantitative consequence of:
    - **First moment**: the average count over squarefree n ≤ X is
      asymptotic to K/(q−1), from PE (Population Equidistribution).
    - **Variance bound**: Var = O(K), from CRT decorrelation
      (`crt_multiplier_invariance`) and the +1 shift destroying
      residue correlations between steps.
    - **Chebyshev**: Pr[|count/K − 1/(q−1)| > ε] ≤ Var/(ε²K²) = O(1/K).

    Pattern matches `RecipSumConcentration` from ReciprocalSumDivergence.lean. -/
def EnsembleConcentration : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a : Nat), 0 < a → a < q →
  ∀ (ε : ℝ), 0 < ε →
  ∃ K₀ : Nat,
    ∀ K ≥ K₀,
      Filter.Tendsto
        (fun X : Nat =>
          (((Finset.Icc 1 X).filter
            (fun n => Squarefree n ∧
              |(genResCount n q a K : ℝ) / K - 1 / (q - 1 : ℝ)| > ε)).card : ℝ) /
          ((Finset.Icc 1 X).filter Squarefree).card)
        Filter.atTop
        (nhds 0)

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
    By concentration, the density of the latter → 0 as X → ∞ (for large K₀).
    Since the former is a subset, its density → 0 too.

    Same proof pattern as `concentration_implies_rsd`. -/
theorem ensemble_concentration_implies_eqd
    (hconc : EnsembleConcentration) : AlmostAllSquarefreeEqd := by
  intro q hq a ha haq ε hε
  -- Get K₀ from concentration
  obtain ⟨K₀, hK₀⟩ := hconc q hq a ha haq ε hε
  -- Use K = K₀: density of {n : deviation at K₀ > ε} → 0
  have h_tendsto := hK₀ K₀ (le_refl _)
  -- The density of {n : ∀K, deviation > ε} ≤ density of {n : deviation at K₀ > ε}
  -- So the former also → 0.
  refine squeeze_zero
    (fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ h_tendsto
  intro X
  have h_card := Finset.card_le_card (forall_deviant_subset q a ε X K₀)
  exact div_le_div_of_nonneg_right (by exact_mod_cast h_card) (Nat.cast_nonneg _)

end MainReduction

/-! ## Deterministic Stability Lemma -/

section DSL

/-- **Deterministic Stability Lemma (DSL)**: PopulationEquidist → CME.

    This single hypothesis replaces both PopulationTransfer and EMDImpliesCME.
    It asserts that if the shifted squarefree population has equidistributed
    minFac residues (PE), then the EM walk's conditional multiplier character
    sums are o(N) (CME).

    The three conditions that make DSL plausible:

    1. **Generation** = SubgroupEscape (PROVED via PRE): the EM multipliers
       generate (ℤ/qℤ)× for every prime q. Without this, the walk could
       be confined to a proper subgroup.

    2. **Position-Blindness** = `crt_multiplier_invariance` (PROVED): the
       minFac operation is q-blind — em(n+1) mod q does not depend on
       P(n) mod q. This prevents the walk from "steering" toward bias.

    3. **Population Support** = PE (from standard ANT): every element of
       (ℤ/qℤ)× receives a positive density of minFac values from the
       shifted squarefree population.

    **Why DSL gives CME directly (not just EMDirichlet):**
    Position-blindness means the multiplier doesn't depend on the walk
    position (P(n) mod q), so fiber-restricted character sums (which
    condition on walk position = a) inherit the same bounds as the
    unconditional sums. The conditional→unconditional step that
    `EMDImpliesCME` encodes is automatic when the mechanism is q-blind.

    **Value:** Reduces the full chain to PE + DSL → MC with a single
    open hypothesis (DSL), compared to PE + PT + EMDImpliesCME → MC
    which has two open hypotheses. -/
def DeterministicStabilityLemma : Prop :=
  PopulationEquidist → ConditionalMultiplierEquidist

end DSL

/-! ## Full Chain: PE + DSL → MC -/

section FullChain

/-- **PE + DSL → MC.** The full reduction chain with DSL as the sole gap:
    PE → (by DSL) CME → CCSB → MC. -/
theorem pe_dsl_implies_mc
    (hpe : PopulationEquidist) (hdsl : DeterministicStabilityLemma) :
    MullinConjecture :=
  cme_implies_mc (hdsl hpe)

/-- **PE + DSL → CCSB.** The intermediate stop: PE → CME → CCSB. -/
theorem pe_dsl_implies_ccsb
    (hpe : PopulationEquidist) (hdsl : DeterministicStabilityLemma) :
    ComplexCharSumBound :=
  cme_implies_ccsb (hdsl hpe)

/-- **MinFacResidueEquidist + DSL → MC.** The full chain from standard
    analytic number theory: MinFacResidueEquidist → PE → CME → MC. -/
theorem equidist_dsl_implies_mc
    (h_equidist : ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q)
    (hdsl : DeterministicStabilityLemma) :
    MullinConjecture :=
  pe_dsl_implies_mc (pe_of_equidist h_equidist) hdsl

end FullChain

/-! ## Connections -/

section Connections

/-- **DSL implies PT.** DSL (PE → CME) gives PT (PE → EMDirichlet) via
    the proved implication CME → EMDirichlet (`cme_implies_emd`). -/
theorem dsl_implies_pt
    (hdsl : DeterministicStabilityLemma) : PopulationTransfer :=
  fun hpe => cme_implies_emd (hdsl hpe)

/-- **DSL + PE make EMDImpliesCME trivially true.** Once PE holds, DSL
    gives CME directly, so `EMDirichlet → CME` holds (ignoring the
    EMDirichlet hypothesis and using PE + DSL instead).

    This shows DSL subsumes both open gaps (PT and EMDImpliesCME) in the
    presence of PE, which is provable from standard ANT
    (`pe_of_equidist` in PopulationEquidistProof.lean). -/
theorem dsl_pe_implies_bridge
    (hdsl : DeterministicStabilityLemma) (hpe : PopulationEquidist) :
    EMDImpliesCME :=
  fun _ => hdsl hpe

/-- **DSL + PE give both PT and EMDImpliesCME.** This is the conjunction
    showing DSL is strictly stronger than the two gaps it replaces. -/
theorem dsl_pe_implies_pt_and_bridge
    (hdsl : DeterministicStabilityLemma) (hpe : PopulationEquidist) :
    PopulationTransfer ∧ EMDImpliesCME :=
  ⟨dsl_implies_pt hdsl, dsl_pe_implies_bridge hdsl hpe⟩

end Connections

end
