import EM.Ensemble.MixedEnsemble

/-!
# Positive Probability Capture via Mixed Walk

## Overview

For a.a. squarefree starting points m and any epsilon > 0, the (1-epsilon) minFac +
epsilon random process from m captures every prime q with positive probability.

The "probability" is formalized as the weight of a finite valid path through the
mixed walk tree. No measure theory on infinite paths is needed.

## Key Results

* `stepWeightLB_pos` -- per-step weight epsilon/omega(P+1) > 0
* `pathWeightLB_pos` -- finite product of positive reals is positive
* `reachable_implies_positive_prob_capture` -- reachability implies positive weight path
* `almost_all_positive_prob_capture` -- PEAP implies a.a. positive probability capture
* `interpolation_mc_landscape` -- summary conjunction

## Mathematical Content

For any prime q and starting point m >= 2:
1. If -1 is reachable mod q from m via some mixed walk, then for ANY epsilon > 0,
   the capturing path has weight >= prod_{k<n} (epsilon / omega(P_k+1)) > 0.
2. Under PEAP, almost all squarefree m coprime to q have -1 reachable.
3. Therefore, a.a. squarefree m have positive-probability capture of q.

The weight lower bound is conservative: each step contributes at least
epsilon / omega(P+1), where omega counts distinct prime factors. This is a
valid lower bound for BOTH the minFac choice (probability 1-epsilon + epsilon/omega
>= epsilon/omega) and any specific random factor choice (probability epsilon/omega).
-/

noncomputable section

open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Step and Path Weight Definitions -/

section Definitions

/-- Lower bound on the probability of ANY single valid factor choice at accumulator P.
    For the (1-epsilon) minFac + epsilon uniform process, any prime factor p of P+1
    is chosen with probability >= epsilon / omega(P+1), where omega counts distinct
    prime factors. MinFac has probability 1-epsilon + epsilon/omega >= epsilon/omega. -/
noncomputable def stepWeightLB (ε : ℝ) (P : ℕ) : ℝ :=
  ε / ((P + 1).primeFactors.card : ℝ)

/-- Lower bound on the probability of following a specific valid path sigma for n steps
    from accumulator m. This is prod_{k<n} (epsilon / omega(P_sigma(k)+1)). -/
noncomputable def pathWeightLB (ε : ℝ) (m : ℕ) (σ : MixedSelection) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, stepWeightLB ε (mixedWalkProd m σ k)

/-- For starting point m, prime q, and epsilon > 0: there exists a finite valid path
    that captures q AND has positive weight under the (1-epsilon) process. -/
def PositiveProbCapture (q : ℕ) (m : ℕ) (ε : ℝ) : Prop :=
  ∃ (σ : MixedSelection) (n : ℕ),
    ValidMixedSelection m σ ∧
    mixedWalkFactor m σ n = q ∧
    0 < pathWeightLB ε m σ (n + 1)

end Definitions

/-! ## Part 2: Positivity of Step and Path Weights -/

section Positivity

/-- The per-step weight lower bound is positive when epsilon > 0 and P+1 >= 2.
    The key: omega(P+1) >= 1 since P+1 has at least one prime factor. -/
theorem stepWeightLB_pos {ε : ℝ} {P : ℕ} (hε : 0 < ε) (hP : 2 ≤ P + 1) :
    0 < stepWeightLB ε P := by
  unfold stepWeightLB
  apply div_pos hε
  have hne : (P + 1).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr (by omega)
  exact Nat.cast_pos.mpr hne.card_pos

/-- The path weight lower bound is positive when epsilon > 0, m >= 2, and sigma
    is a valid mixed selection. Each step contributes a positive factor. -/
theorem pathWeightLB_pos {ε : ℝ} {m : ℕ} {σ : MixedSelection} {n : ℕ}
    (hε : 0 < ε) (hm : 2 ≤ m) (hv : ValidMixedSelection m σ) :
    0 < pathWeightLB ε m σ n := by
  unfold pathWeightLB
  apply Finset.prod_pos
  intro k _
  apply stepWeightLB_pos hε
  have hge : 2 ≤ mixedWalkProd m σ k := mixedWalkProd_ge_two m hm σ hv k
  omega

end Positivity

/-! ## Part 3: Reachability Implies Positive Probability Capture -/

section ReachableCapture

/-- If -1 is reachable mod q from m via some mixed walk, then for any epsilon > 0,
    there exists a valid path that captures q with positive weight. -/
theorem reachable_implies_positive_prob_capture
    {q : ℕ} (hq : Nat.Prime q)
    {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hreach : (-1 : ZMod q) ∈ reachableEver q m) :
    PositiveProbCapture q m ε := by
  -- Extract a witness: some walk reaches -1 at some step
  rw [reachableEver, Set.mem_iUnion] at hreach
  obtain ⟨n, σ, hv, hmod⟩ := hreach
  -- From (mixedWalkProd m σ n : ZMod q) = -1, deduce q | mixedWalkProd m σ n + 1
  have hdvd : q ∣ mixedWalkProd m σ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hmod]; ring
  obtain ⟨σ', hv', k, hk⟩ := hit_implies_capture' hq m σ hv n hdvd
  exact ⟨σ', k, hv', hk, pathWeightLB_pos hε hm hv'⟩

/-- Contrapositive: if positive probability capture fails, then -1 is not reachable. -/
theorem not_positive_prob_capture_implies_trapped
    {q : ℕ} (hq : Nat.Prime q)
    {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hfail : ¬PositiveProbCapture q m ε) :
    (-1 : ZMod q) ∉ reachableEver q m := by
  intro hreach
  exact hfail (reachable_implies_positive_prob_capture hq hm hε hreach)

end ReachableCapture

/-! ## Part 4: Almost All Positive Probability Capture -/

section AlmostAll

variable {q : ℕ}

/-- The count of squarefree m in [1,X] coprime to q that fail to have positive
    probability capture is bounded by the trapped count. -/
private theorem failure_count_le_trapped (hq : Nat.Prime q) (hε : 0 < ε) (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
      Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card
    ≤ sqfreeTrappedCount q X := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  refine ⟨hm.1, hm.2.1, hm.2.2.1, ?_⟩
  -- Need: -1 ∉ reachableEver q m
  -- From: ¬PositiveProbCapture q m ε
  have hm_ge_1 : 1 ≤ m := (Finset.mem_Icc.mp hm.1).1
  intro hreach
  apply hm.2.2.2
  -- Show PositiveProbCapture from hreach
  -- Extract a hitting walk from reachability
  rw [reachableEver, Set.mem_iUnion] at hreach
  obtain ⟨n, σ, hv, hmod⟩ := hreach
  have h0 : (mixedWalkProd m σ n : ZMod q) + 1 = 0 := by rw [hmod]; ring
  have h1 : ((mixedWalkProd m σ n + 1 : ℕ) : ZMod q) = 0 := by push_cast; exact h0
  have hdvd : q ∣ mixedWalkProd m σ n + 1 := by rwa [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨σ', hv', k, hk⟩ := hit_implies_capture' hq m σ hv n hdvd
  -- Walk product ≥ 1 for all steps (since m ≥ 1 and each factor ≥ 2)
  have hwalk_ge : ∀ i, 1 ≤ mixedWalkProd m σ' i := by
    intro i
    induction i with
    | zero => simp [mixedWalkProd]; exact hm_ge_1
    | succ j ih =>
      simp only [mixedWalkProd]
      have hfac : 1 ≤ mixedWalkFactor m σ' j := by
        unfold mixedWalkFactor
        match hσj : σ' j with
        | none => exact Nat.minFac_pos _
        | some p =>
          have := hv' j
          rw [hσj] at this
          exact this.1.pos
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.one_le_iff_ne_zero.mp ih) (Nat.one_le_iff_ne_zero.mp hfac))
  -- Construct PositiveProbCapture: the path weight is positive
  exact ⟨σ', k, hv', hk, by
    unfold pathWeightLB
    apply Finset.prod_pos
    intro i _
    unfold stepWeightLB
    apply div_pos hε
    have : 1 < mixedWalkProd m σ' i + 1 := by linarith [hwalk_ge i]
    exact Nat.cast_pos.mpr ((Nat.nonempty_primeFactors.mpr this).card_pos)⟩

/-- Under PEAP, the density of squarefree m failing positive probability capture
    tends to 0. This follows from the trapped density tending to 0 (which is
    proved in MixedEnsemble.lean) and the subset bound. -/
theorem almost_all_positive_prob_capture (hq : Nat.Prime q)
    (hPEAP : IK.PrimesEquidistributedInAP)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun X => (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- The trapped density tends to 0
  have htrapped := weak_fmcd_chain_implies_almost_all hq hPEAP
  -- Squeeze: 0 ≤ failure density ≤ trapped density → 0
  apply squeeze_zero
  · intro X
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro X
    have hle : ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card
      ≤ sqfreeTrappedCount q X := failure_count_le_trapped hq hε X
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) (Nat.cast_nonneg _)
  · exact htrapped

end AlmostAll

/-! ## Part 5: Content Theorem -/

section Content

/-- **Main content theorem**: For any prime q, starting point m >= 2, and epsilon > 0,
    not being trapped (i.e., -1 reachable) implies positive probability capture. -/
theorem not_trapped_implies_positive_prob_capture
    (q : ℕ) (hq : Nat.Prime q)
    (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε)
    (hreach : (-1 : ZMod q) ∈ reachableEver q m) :
    PositiveProbCapture q m ε :=
  reachable_implies_positive_prob_capture hq hm hε hreach

end Content

/-! ## Part 6: Landscape Summary -/

section Landscape

/-- **Interpolation MC Landscape**: Summary of the positive-probability capture
    framework. The chain is:

    1. stepWeightLB_pos: per-step weight > 0
    2. pathWeightLB_pos: product of step weights > 0
    3. reachable ⟹ PositiveProbCapture (deterministic implication)
    4. PEAP ⟹ a.a. PositiveProbCapture (density result)
    5. ¬PositiveProbCapture ⟹ trapped (contrapositive) -/
theorem interpolation_mc_landscape
    {q : ℕ} (hq : Nat.Prime q)
    (hPEAP : IK.PrimesEquidistributedInAP)
    {ε : ℝ} (hε : 0 < ε) :
    -- 1. Per-step weight positive for P+1 >= 2
    (∀ P : ℕ, 2 ≤ P + 1 → 0 < stepWeightLB ε P)
    ∧
    -- 2. Path weight positive for valid walks from m >= 2
    (∀ (m : ℕ), 2 ≤ m → ∀ (σ : MixedSelection), ValidMixedSelection m σ → ∀ (n : ℕ),
      0 < pathWeightLB ε m σ n)
    ∧
    -- 3. Reachability implies positive probability capture
    (∀ (m : ℕ), 2 ≤ m →
      (-1 : ZMod q) ∈ reachableEver q m → PositiveProbCapture q m ε)
    ∧
    -- 4. Almost all squarefree have positive probability capture
    Filter.Tendsto
      (fun X => (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0)
    ∧
    -- 5. Failure implies trapped
    (∀ (m : ℕ), 2 ≤ m →
      ¬PositiveProbCapture q m ε → (-1 : ZMod q) ∉ reachableEver q m) :=
  ⟨fun _ hP => stepWeightLB_pos hε hP,
   fun _ hm _ hv _ => pathWeightLB_pos hε hm hv,
   fun _ hm hreach => reachable_implies_positive_prob_capture hq hm hε hreach,
   almost_all_positive_prob_capture hq hPEAP hε,
   fun _ hm hfail => not_positive_prob_capture_implies_trapped hq hm hε hfail⟩

end Landscape

/-! ## Part 7: Block Coverage and Iterated Hitting (Layer 2)

Layer 2 extends the positive-probability capture framework with:
1. **Block coverage**: if every unit of (Z/qZ)× is reachable from m, there exists
   a uniform depth bound N₀ such that every unit can be reached within N₀ steps.
2. **GoodAccumulator / Regeneration**: definitions for the regeneration property.
3. **Iterated hitting**: under Regeneration, from a good accumulator, every target
   number of -1 hits is achievable by some valid path with positive weight.
-/

/-! ### Part 7a: GoodAccumulator and Regeneration Definitions -/

section RegenerationDefs

/-- An accumulator P is "good" for prime q if every unit of (Z/qZ)× is reachable
    from P by some valid mixed walk. This means the reachable set R_∞(q, P)
    contains every unit class. -/
def GoodAccumulator (q : ℕ) (P : ℕ) : Prop :=
  ∀ a : (ZMod q)ˣ, (a : ZMod q) ∈ reachableEver q P

/-- The regeneration property: every valid walk from a good starting point
    leads to good intermediate accumulators at every step.

    **Evidence**: Accumulators grow super-exponentially and are squarefree.
    By CRT blindness, large squarefree integers behave generically mod q.
    The density-1 set of good starting points should include almost all
    accumulators encountered during the walk.

    This is the sole gap between single-hit capture (Layer 1) and
    iterated/almost-sure capture (Layer 2).

    **Status**: open hypothesis. -/
def Regeneration (q : ℕ) (m : ℕ) : Prop :=
  ∀ (σ : MixedSelection) (K : ℕ), ValidMixedSelection m σ →
    GoodAccumulator q (mixedWalkProd m σ K)

end RegenerationDefs

/-! ### Part 7b: Block Coverage -/

section BlockCoverage

/-- Block Coverage: if every unit of (Z/qZ)× is reachable from m, then there exists
    a uniform depth bound N₀ such that every unit can be reached within N₀ steps
    with positive weight.

    The proof extracts a witness path for each unit (from reachableEver), takes the
    supremum of the step counts over the finite type (ZMod q)ˣ, and shows the
    original witnesses still work (since their step counts are bounded by N₀).

    The path weight is positive by `pathWeightLB_pos`. -/
theorem block_coverage (q : ℕ) (hq : Nat.Prime q) (_hq2 : 2 < q)
    (m : ℕ) (hm : 2 ≤ m)
    (hgood : GoodAccumulator q m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ a : (ZMod q)ˣ,
      ∃ (σ : MixedSelection) (n : ℕ),
        n ≤ N₀ ∧
        ValidMixedSelection m σ ∧
        (mixedWalkProd m σ n : ZMod q) = a ∧
        0 < pathWeightLB ε m σ n := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- For each unit a, extract a witness (step count and selection)
  -- from hgood : a ∈ reachableEver q m
  have hwit : ∀ a : (ZMod q)ˣ, ∃ (n : ℕ) (σ : MixedSelection),
      ValidMixedSelection m σ ∧ (mixedWalkProd m σ n : ZMod q) = ↑a := by
    intro a
    have ha := hgood a
    rw [reachableEver, Set.mem_iUnion] at ha
    obtain ⟨n, σ, hv, hmod⟩ := ha
    exact ⟨n, σ, hv, hmod⟩
  -- Use choose to extract functions
  choose n_fn σ_fn hv_fn hmod_fn using hwit
  -- Take N₀ = supremum of depths over all units
  let N₀ := Finset.univ.sup n_fn
  refine ⟨N₀, fun a => ?_⟩
  refine ⟨σ_fn a, n_fn a, ?_, hv_fn a, hmod_fn a, pathWeightLB_pos hε hm (hv_fn a)⟩
  -- n_fn a ≤ N₀ = univ.sup n_fn
  exact Finset.le_sup (Finset.mem_univ a)

end BlockCoverage

/-! ### Part 7c: Good Accumulator Implies -1 Reachable -/

section GoodNegOne

/-- -1 is nonzero in ZMod q when q is prime with q ≥ 3. -/
private theorem neg_one_ne_zero_zmod (q : ℕ) (hq : Nat.Prime q) (_hq2 : 2 < q) :
    (-1 : ZMod q) ≠ 0 := by
  haveI : Fact q.Prime := ⟨hq⟩; exact neg_ne_zero.mpr one_ne_zero

/-- -1 is a unit in ZMod q when q is prime with q ≥ 3. -/
private theorem neg_one_isUnit (q : ℕ) (hq : Nat.Prime q) (_hq2 : 2 < q) :
    IsUnit (-1 : ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact IsUnit.mk0 (-1) (neg_one_ne_zero_zmod q hq _hq2)

/-- From a good accumulator, -1 mod q is reachable. This is immediate because
    -1 is a unit in ZMod q (for q prime, q ≥ 3), and GoodAccumulator says
    every unit is reachable. -/
theorem good_accumulator_neg_one_reachable (q : ℕ) (hq : Nat.Prime q)
    (hq2 : 2 < q) (P : ℕ) (hgood : GoodAccumulator q P) :
    (-1 : ZMod q) ∈ reachableEver q P := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact hgood (IsUnit.mk0 (-1) (neg_one_ne_zero_zmod q hq hq2)).unit

/-- From a good accumulator with m ≥ 2, positive probability capture holds.
    Composition of good_accumulator_neg_one_reachable + reachable_implies_positive_prob_capture. -/
theorem good_accumulator_implies_capture (q : ℕ) (hq : Nat.Prime q)
    (hq2 : 2 < q) (m : ℕ) (hm : 2 ≤ m)
    (hgood : GoodAccumulator q m) (ε : ℝ) (hε : 0 < ε) :
    PositiveProbCapture q m ε :=
  reachable_implies_positive_prob_capture hq hm hε
    (good_accumulator_neg_one_reachable q hq hq2 m hgood)

end GoodNegOne

/-! ### Part 7d: Walk Concatenation -/

section WalkConcat

/-- Concatenate two mixed selections: use σ₁ for steps [0, n), use σ₂ shifted
    for steps [n, ∞). -/
private def concatMixedSelection (σ₁ σ₂ : MixedSelection) (n : ℕ) : MixedSelection :=
  fun k => if k < n then σ₁ k else σ₂ (k - n)

/-- The concatenated selection agrees with σ₁ on the first n steps. -/
private theorem concat_prefix (σ₁ σ₂ : MixedSelection) (n : ℕ) :
    ∀ i, i < n → concatMixedSelection σ₁ σ₂ n i = σ₁ i :=
  fun i hi => by simp [concatMixedSelection, hi]

/-- The walk under the concatenated selection agrees with σ₁ for the first n steps. -/
private theorem concat_walk_prefix (acc : ℕ) (σ₁ σ₂ : MixedSelection) (n : ℕ) :
    mixedWalkProd acc (concatMixedSelection σ₁ σ₂ n) n =
    mixedWalkProd acc σ₁ n :=
  mixedWalkProd_depends_on_prefix acc _ σ₁ n (concat_prefix σ₁ σ₂ n)

/-- The walk from step n onward under the concatenated selection matches the
    walk from the intermediate accumulator under σ₂. -/
private theorem concat_walk_tail (acc : ℕ) (σ₁ σ₂ : MixedSelection) (n j : ℕ) :
    mixedWalkProd acc (concatMixedSelection σ₁ σ₂ n) (n + j) =
    mixedWalkProd (mixedWalkProd acc σ₁ n) σ₂ j := by
  -- Strategy: mixedWalkProd_tail_restart decomposes σ' walk at (n+j) into
  -- walk from (mixedWalkProd acc σ' n) with shifted selection (fun i => σ' (n+i)).
  -- Then use concat_walk_prefix for the accumulator, and show shifted σ' = σ₂.
  have hrestart := mixedWalkProd_tail_restart acc (concatMixedSelection σ₁ σ₂ n) n j
  rw [hrestart, concat_walk_prefix]
  -- Goal: mixedWalkProd (mixedWalkProd acc σ₁ n) (fun i => concatMixedSelection σ₁ σ₂ n (n + i)) j
  --     = mixedWalkProd (mixedWalkProd acc σ₁ n) σ₂ j
  apply mixedWalkProd_depends_on_prefix
  intro i _
  -- Goal: concatMixedSelection σ₁ σ₂ n (n + i) = σ₂ i
  unfold concatMixedSelection
  rw [if_neg (by omega : ¬(n + i < n))]
  congr 1; omega

/-- Validity of the concatenated selection, given validity of both parts and
    that σ₂ is valid from the intermediate accumulator P = mixedWalkProd acc σ₁ n. -/
private theorem concat_valid (acc : ℕ) (σ₁ σ₂ : MixedSelection) (n : ℕ)
    (hv₁ : ValidMixedSelection acc σ₁)
    (hv₂ : ValidMixedSelection (mixedWalkProd acc σ₁ n) σ₂) :
    ValidMixedSelection acc (concatMixedSelection σ₁ σ₂ n) := by
  intro k
  by_cases hlt : k < n
  · -- k < n: agrees with σ₁
    rw [concat_prefix σ₁ σ₂ n k hlt]
    have hwk : mixedWalkProd acc (concatMixedSelection σ₁ σ₂ n) k =
        mixedWalkProd acc σ₁ k :=
      mixedWalkProd_depends_on_prefix acc _ σ₁ k
        (fun i hi => concat_prefix σ₁ σ₂ n i (by omega))
    have hspec := hv₁ k
    cases hσk : σ₁ k with
    | none => trivial
    | some p =>
      simp only [hσk] at hspec ⊢
      exact ⟨hspec.1, by rw [hwk]; exact hspec.2⟩
  · -- k ≥ n: write k = n + j
    obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
    -- concatMixedSelection σ₁ σ₂ n (n + j) = σ₂ j
    have hsel : concatMixedSelection σ₁ σ₂ n (n + j) = σ₂ j := by
      show (if n + j < n then σ₁ (n + j) else σ₂ (n + j - n)) = σ₂ j
      rw [if_neg (by omega : ¬(n + j < n))]
      congr 1; omega
    rw [hsel, concat_walk_tail]
    exact hv₂ j

end WalkConcat

/-! ### Part 7e: Iterated Hitting from Regeneration -/

section IteratedHitting

/-- Under Regeneration, cofinal hitting: for every threshold K, there exists a valid
    path from m that hits -1 mod q at some step n ≥ K, with positive path weight.

    This formulation avoids the counting subtlety of tracking multiple distinct hits.
    It directly shows that -1 can be hit at arbitrarily late steps, which is the
    essential content for ergodic-type conclusions.

    Proof: The accumulator at step K is good by Regeneration (applied to the all-minFac
    path). So -1 is reachable from P_K. Extract a path σ₁ of length n₁ from P_K
    reaching -1. Concatenate the minFac path (length K) with σ₁. The resulting path
    hits -1 at step K + n₁ ≥ K. -/
theorem regeneration_implies_cofinal_hitting
    (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (m : ℕ) (hm : 2 ≤ m)
    (hregen : Regeneration q m)
    (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) :
    ∃ (σ : MixedSelection) (n : ℕ),
      K ≤ n ∧
      ValidMixedSelection m σ ∧
      (mixedWalkProd m σ n : ZMod q) = -1 ∧
      0 < pathWeightLB ε m σ n := by
  -- The all-minFac path is valid
  have hv_mf : ValidMixedSelection m minFacMixed := minFacMixed_valid m
  -- The accumulator at step K (via minFac path) is good by Regeneration
  have hgoodK : GoodAccumulator q (mixedWalkProd m minFacMixed K) :=
    hregen minFacMixed K hv_mf
  -- So -1 is reachable from P_K
  have hreach : (-1 : ZMod q) ∈ reachableEver q (mixedWalkProd m minFacMixed K) :=
    good_accumulator_neg_one_reachable q hq hq2 _ hgoodK
  -- Extract witness: path σ₁ of length n₁ from P_K reaching -1
  rw [reachableEver, Set.mem_iUnion] at hreach
  obtain ⟨n₁, σ₁, hv₁, hmod₁⟩ := hreach
  -- Concatenate minFac path (length K) with σ₁
  let σ' := concatMixedSelection minFacMixed σ₁ K
  have hv' : ValidMixedSelection m σ' := concat_valid m minFacMixed σ₁ K hv_mf hv₁
  -- At step K + n₁, the walk hits -1
  have hhit : (mixedWalkProd m σ' (K + n₁) : ZMod q) = -1 := by
    rw [concat_walk_tail]; exact hmod₁
  exact ⟨σ', K + n₁, Nat.le_add_right K n₁, hv', hhit, pathWeightLB_pos hε hm hv'⟩

/-- Under Regeneration, for each step K along any valid walk, the accumulator
    at step K supports positive probability capture of q. -/
theorem regeneration_implies_capture_at_every_step
    (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (m : ℕ) (hm : 2 ≤ m)
    (hregen : Regeneration q m)
    (ε : ℝ) (hε : 0 < ε)
    (σ : MixedSelection) (hv : ValidMixedSelection m σ) (K : ℕ) :
    PositiveProbCapture q (mixedWalkProd m σ K) ε := by
  have hgoodK : GoodAccumulator q (mixedWalkProd m σ K) := hregen σ K hv
  have hmK : 2 ≤ mixedWalkProd m σ K := mixedWalkProd_ge_two m hm σ hv K
  exact good_accumulator_implies_capture q hq hq2 _ hmK hgoodK ε hε

/-- Under Regeneration, iterated hitting: for every target number of -1 hits,
    there exists a valid path from m that hits -1 mod q at least that many times,
    with positive path weight at each hit step.

    The proof proceeds by induction on target_hits. At each step we:
    1. Take the existing path to step n₀ (with K hits).
    2. Advance one step from n₀ (via minFac) to ensure the walk moves to a NEW position.
    3. From the new accumulator (which is good by Regeneration), reach -1 again.
    4. The new hit at step n₀ + 1 + n₁ is strictly past n₀, hence genuinely new. -/
theorem regeneration_implies_iterated_hitting
    (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (m : ℕ) (hm : 2 ≤ m)
    (_hgood : GoodAccumulator q m)
    (hregen : Regeneration q m)
    (ε : ℝ) (hε : 0 < ε)
    (target_hits : ℕ) :
    ∃ (σ : MixedSelection) (steps : Finset ℕ),
      ValidMixedSelection m σ ∧
      target_hits ≤ steps.card ∧
      (∀ n ∈ steps, (mixedWalkProd m σ n : ZMod q) = -1) ∧
      (∀ n ∈ steps, 0 < pathWeightLB ε m σ n) := by
  induction target_hits with
  | zero =>
    exact ⟨minFacMixed, ∅, minFacMixed_valid m, Nat.zero_le _,
      fun _ h => absurd h (by simp),
      fun _ h => absurd h (by simp)⟩
  | succ K ih =>
    obtain ⟨σ₀, steps₀, hv₀, hcard₀, hhits₀, _⟩ := ih
    -- n₀ is strictly past all existing hit steps; accumulator there is good by Regeneration
    let n₀ := steps₀.sup id + 1
    have hreach : (-1 : ZMod q) ∈ reachableEver q (mixedWalkProd m σ₀ n₀) :=
      good_accumulator_neg_one_reachable q hq hq2 _ (hregen σ₀ n₀ hv₀)
    rw [reachableEver, Set.mem_iUnion] at hreach
    obtain ⟨n₁, σ₁, hv₁, hmod₁⟩ := hreach
    let σ' := concatMixedSelection σ₀ σ₁ n₀
    have hv' : ValidMixedSelection m σ' := concat_valid m σ₀ σ₁ n₀ hv₀ hv₁
    have hnew_not_old : n₀ + n₁ ∉ steps₀ := by
      intro h; have := Finset.le_sup (f := id) h; simp at this; omega
    refine ⟨σ', insert (n₀ + n₁) steps₀, hv', ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnew_not_old]; omega
    · intro n hn
      rw [Finset.mem_insert] at hn
      rcases hn with rfl | hn
      · rw [concat_walk_tail]; exact hmod₁
      · rw [mixedWalkProd_depends_on_prefix m _ σ₀ n (fun i hi =>
            concat_prefix σ₀ σ₁ n₀ i (by
              have := Finset.le_sup (f := id) hn; simp at this; omega))]
        exact hhits₀ n hn
    · intro n _; exact pathWeightLB_pos hε hm hv'

end IteratedHitting

/-! ### Part 7f: Layer 2 Landscape Summary -/

section Layer2Landscape

/-- **Layer 2 Landscape**: Summary of the block coverage + regeneration framework.

    Given a prime q ≥ 3, a starting point m ≥ 2, epsilon > 0:
    1. Block coverage: GoodAccumulator → uniform depth for all units
    2. GoodAccumulator → -1 reachable → PositiveProbCapture
    3. Regeneration → cofinal hitting (hit -1 past any threshold K)
    4. Regeneration → iterated hitting (hit -1 at least target_hits times)
    5. Regeneration → capture at every intermediate step -/
theorem layer2_landscape
    (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (m : ℕ) (hm : 2 ≤ m)
    (hgood : GoodAccumulator q m)
    (hregen : Regeneration q m)
    (ε : ℝ) (hε : 0 < ε) :
    -- 1. Block coverage: uniform depth for all targets
    (∃ N₀, ∀ a : (ZMod q)ˣ, ∃ (σ : MixedSelection) (n : ℕ),
      n ≤ N₀ ∧ ValidMixedSelection m σ ∧
      (mixedWalkProd m σ n : ZMod q) = a ∧ 0 < pathWeightLB ε m σ n)
    ∧
    -- 2. Single capture (from GoodAccumulator)
    PositiveProbCapture q m ε
    ∧
    -- 3. Cofinal hitting: for every K, hit -1 at some step ≥ K
    (∀ K, ∃ (σ : MixedSelection) (n : ℕ),
      K ≤ n ∧ ValidMixedSelection m σ ∧
      (mixedWalkProd m σ n : ZMod q) = -1 ∧
      0 < pathWeightLB ε m σ n)
    ∧
    -- 4. Iterated hitting: for every target, achieve that many -1 hits
    (∀ target_hits, ∃ (σ : MixedSelection) (steps : Finset ℕ),
      ValidMixedSelection m σ ∧
      target_hits ≤ steps.card ∧
      (∀ n ∈ steps, (mixedWalkProd m σ n : ZMod q) = -1) ∧
      (∀ n ∈ steps, 0 < pathWeightLB ε m σ n))
    ∧
    -- 5. Capture at every intermediate step
    (∀ (σ : MixedSelection), ValidMixedSelection m σ →
      ∀ K, PositiveProbCapture q (mixedWalkProd m σ K) ε) :=
  ⟨block_coverage q hq hq2 m hm hgood ε hε,
   good_accumulator_implies_capture q hq hq2 m hm hgood ε hε,
   regeneration_implies_cofinal_hitting q hq hq2 m hm hregen ε hε,
   regeneration_implies_iterated_hitting q hq hq2 m hm hgood hregen ε hε,
   regeneration_implies_capture_at_every_step q hq hq2 m hm hregen ε hε⟩

end Layer2Landscape

/-! ## Part 8: TreeSieveDecay and Bridge to Regeneration

TreeSieveDecay is a pointwise sieve-theoretic hypothesis asserting that all
sufficiently large squarefree integers have "good" factor trees (covering all
units mod q). Combined with the proved infrastructure (squarefree accumulators,
monotone growth), it implies Regeneration and hence iterated hitting.

The conditional chain: PEAP + TreeSieveDecay -> Regeneration -> Iterated Hitting
-/

/-! ### Part 8a: Mixed Walk Squarefree -/

section MixedWalkSquarefree

/-- The mixed walk accumulator is squarefree at every step, given a squarefree
    starting point. The proof is by induction on the step count:
    - Base: accumulator = acc, squarefree by hypothesis
    - Step: P(n+1) = P(n) * f(n). P(n) is squarefree (IH), f(n) is prime
      (hence squarefree), and f(n) does not divide P(n) (coprime).
      Use Nat.squarefree_mul_iff for the conclusion. -/
theorem mixedWalkProd_squarefree (acc : ℕ) (hacc : 2 ≤ acc) (hsf : Squarefree acc)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ) (n : ℕ) :
    Squarefree (mixedWalkProd acc σ n) := by
  induction n with
  | zero => simp [mixedWalkProd]; exact hsf
  | succ k ih =>
    rw [mixedWalkProd_succ]
    have hge := mixedWalkProd_ge_two acc hacc σ hv k
    have hfp := mixedWalkFactor_prime acc σ hv k hge
    have hndvd := mixedWalkFactor_not_dvd_prod acc hacc σ hv k
    have hcop : (mixedWalkProd acc σ k).Coprime (mixedWalkFactor acc σ k) :=
      (hfp.coprime_iff_not_dvd.mpr hndvd).symm
    exact Nat.squarefree_mul_iff.mpr ⟨hcop, ih, hfp.squarefree⟩

end MixedWalkSquarefree

/-! ### Part 8b: TreeSieveDecay Definition -/

section TreeSieveDecayDef

/-- **TreeSieveDecay** (corrected): all sufficiently large squarefree integers
    COPRIME TO q are good accumulators -- every unit mod q is reachable via
    the factor tree.

    This is a POINTWISE sieve-theoretic statement:
    - NOT orbit-specific (about ALL large integers, not one orbit)
    - NOT a density condition (about EVERY P >= P0, not density-1 of P)
    - Supported by super-exponential growth: at tree depth k, Euclid numbers
      have size >= P^{2^k}, making total factor confinement exponentially unlikely

    The coprimality condition Nat.Coprime P q is NECESSARY: when q | P, the walk
    position (P : ZMod q) = 0 and every subsequent position is 0 * factor = 0
    (absorption). So reachableEver q P = {0}, and no unit is reachable.

    TreeSieveDecay is the sole sieve-theoretic input needed for the full
    Interpolation MC conditional chain. -/
def TreeSieveDecay (q : ℕ) : Prop :=
  ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → Squarefree P → Nat.Coprime P q → GoodAccumulator q P

/-- **TreeSieveDecayHitting**: weaker variant of TreeSieveDecay that only requires
    -1 to be reachable (not ALL units). This suffices for the MC chain since
    we only need to hit -1 mod q.

    TreeSieveDecay implies TreeSieveDecayHitting (for q prime, q >= 3). -/
def TreeSieveDecayHitting (q : ℕ) : Prop :=
  ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P → Squarefree P → Nat.Coprime P q →
    (-1 : ZMod q) ∈ reachableEver q P

end TreeSieveDecayDef

/-! ### Part 8c: Coprimality Propagation -/

section CoprimePropagation

/-- Mixed walk accumulators remain coprime to q when the walk never hits -1 mod q.

    Proof by induction:
    - Base: m is coprime to q by hypothesis.
    - Step: if the accumulator P at step k is coprime to q and (P : ZMod q) != -1,
      then the factor f at step k satisfies f != q. Since f is prime and f | P+1,
      if f = q then q | P+1 so (P : ZMod q) = -1, contradicting the no-death
      assumption. Hence f != q, and since q is prime, gcd(f, q) = 1.
      Since P is coprime to q and f is coprime to q, P * f is coprime to q. -/
theorem mixedWalkProd_coprime_of_no_death (q : ℕ) (hq : Nat.Prime q)
    (m : ℕ) (hm : 2 ≤ m) (hcop : Nat.Coprime m q)
    (σ : MixedSelection) (hv : ValidMixedSelection m σ)
    (hno_death : ∀ k, (mixedWalkProd m σ k : ZMod q) ≠ -1)
    (n : ℕ) : Nat.Coprime (mixedWalkProd m σ n) q := by
  induction n with
  | zero => simp [mixedWalkProd]; exact hcop
  | succ k ih =>
    rw [mixedWalkProd_succ]
    have hge := mixedWalkProd_ge_two m hm σ hv k
    have hfp := mixedWalkFactor_prime m σ hv k hge
    have hfdvd := mixedWalkFactor_dvd m σ hv k
    -- Show the factor is coprime to q
    have hfcop : Nat.Coprime (mixedWalkFactor m σ k) q := by
      -- If factor = q, then q | P+1, so (P : ZMod q) = -1, contradiction
      rw [hfp.coprime_iff_not_dvd]
      intro hdvd
      -- factor | q and q prime means factor = q
      have hfeq : mixedWalkFactor m σ k = q :=
        (hq.eq_one_or_self_of_dvd _ hdvd).resolve_left hfp.ne_one
      -- Then q | P+1
      have hqdvd : q ∣ mixedWalkProd m σ k + 1 := hfeq ▸ hfdvd
      -- So (P : ZMod q) = -1
      have hmod : (mixedWalkProd m σ k : ZMod q) = -1 := by
        have : ((mixedWalkProd m σ k + 1 : ℕ) : ZMod q) = 0 := by
          rwa [ZMod.natCast_eq_zero_iff]
        rwa [Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg] at this
      exact hno_death k hmod
    exact (ih.symm.mul_right hfcop.symm).symm

end CoprimePropagation

/-! ### Part 8d: Bridge -- TreeSieveDecay implies Hitting -/

section TSDHittingBridge

/-- For accumulators starting above the TreeSieveDecay threshold, every
    intermediate step has a good accumulator -- provided the intermediate
    accumulator is coprime to q. The proof combines:
    1. mixedWalkProd_squarefree: accumulators stay squarefree
    2. mixedWalkProd_mono: accumulators are monotonically increasing
    3. TreeSieveDecay: large squarefree coprime implies good -/
theorem treeSieveDecay_implies_good_at
    (q : ℕ) (P₀ : ℕ)
    (hP₀ : ∀ P, P₀ ≤ P → Squarefree P → Nat.Coprime P q → GoodAccumulator q P)
    (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (hlarge : P₀ ≤ m)
    (σ : MixedSelection) (hv : ValidMixedSelection m σ) (K : ℕ)
    (hcop : Nat.Coprime (mixedWalkProd m σ K) q) :
    GoodAccumulator q (mixedWalkProd m σ K) :=
  hP₀ _ (le_trans hlarge (mixedWalkProd_mono m hm σ hv (Nat.zero_le K)))
    (mixedWalkProd_squarefree m hm hsf σ hv K) hcop

/-- **Key bridge**: TreeSieveDecay implies -1 is reachable from any sufficiently
    large squarefree starting point coprime to q. The proof uses the dichotomy:

    Consider the all-minFac walk from m. Either:
    - Case A: the walk hits -1 at some step k. Then -1 is reachable (done).
    - Case B: the walk never hits -1. Then by `coprime_of_no_death`, all
      intermediate accumulators are coprime to q. In particular m itself is
      coprime (hypothesis), squarefree (hypothesis), and large (hypothesis).
      TSD gives GoodAccumulator m, which means -1 is reachable.

    So in either case, -1 is reachable from m. -/
theorem tsd_implies_neg_one_reachable (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q) :
    ∃ M : ℕ, ∀ m, M ≤ m → 2 ≤ m → Squarefree m → Nat.Coprime m q →
      (-1 : ZMod q) ∈ reachableEver q m := by
  obtain ⟨P₀, hP₀⟩ := hTSD
  refine ⟨max P₀ 2, fun m hlarge hm hsf hcop => ?_⟩
  have hP₀m : P₀ ≤ m := le_trans (le_max_left P₀ 2) hlarge
  -- Dichotomy on the all-minFac walk
  by_cases hdeath : ∃ k, (mixedWalkProd m minFacMixed k : ZMod q) = -1
  · -- Case A: walk hits -1 at some step k
    obtain ⟨k, hk⟩ := hdeath
    rw [reachableEver, Set.mem_iUnion]
    exact ⟨k, minFacMixed, minFacMixed_valid m, hk⟩
  · -- Case B: walk never hits -1 => GoodAccumulator m by TSD
    push Not at hdeath
    exact good_accumulator_neg_one_reachable q hq hq2 m (hP₀ m hP₀m hsf hcop)

/-- TreeSieveDecay implies TreeSieveDecayHitting for primes q >= 3. -/
theorem tsd_implies_tsdh (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q) : TreeSieveDecayHitting q := by
  obtain ⟨M, hM⟩ := tsd_implies_neg_one_reachable q hq hq2 hTSD
  exact ⟨max M 2, fun P hP hsf hcop =>
    hM P (le_trans (le_max_left M 2) hP)
      (le_trans (le_max_right M 2) hP) hsf hcop⟩

/-- Under TreeSieveDecay, all sufficiently large squarefree m coprime to q
    satisfy GoodAccumulator. -/
theorem tsd_implies_good (q : ℕ) (hTSD : TreeSieveDecay q) :
    ∃ M : ℕ, ∀ m, M ≤ m → Squarefree m → Nat.Coprime m q →
      GoodAccumulator q m :=
  hTSD

/-- Under TreeSieveDecay with q prime, q >= 3, single capture holds for
    sufficiently large squarefree m coprime to q. -/
theorem tsd_implies_capture (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m, M ≤ m → 2 ≤ m → Squarefree m → Nat.Coprime m q →
      PositiveProbCapture q m ε := by
  obtain ⟨M, hM⟩ := tsd_implies_neg_one_reachable q hq hq2 hTSD
  exact ⟨M, fun m hlarge hm hsf hcop =>
    reachable_implies_positive_prob_capture hq hm hε (hM m hlarge hm hsf hcop)⟩

end TSDHittingBridge

/-! ### Part 8e: Full Interpolation Landscape -/

section FullInterpolationLandscape

/-- **Full Interpolation MC Landscape**: Summary of TreeSieveDecay-based chain.

    Under TreeSieveDecay(q) for a prime q >= 3:
    1. Mixed walk accumulators are squarefree (unconditional)
    2. TreeSieveDecay implies GoodAccumulator above threshold (coprime)
    3. TreeSieveDecay implies -1 reachable above threshold (coprime)
    4. TreeSieveDecay implies single capture above threshold (coprime)

    The sole sieve-theoretic input is TreeSieveDecay. Regeneration and iterated
    hitting require extra infrastructure to handle post-absorption walks.
    For single hitting (which suffices for MC), the dichotomy argument is clean. -/
theorem full_interpolation_landscape
    (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q)
    (ε : ℝ) (hε : 0 < ε) :
    -- 1. Squarefree preservation (unconditional)
    (∀ (acc : ℕ), 2 ≤ acc → Squarefree acc →
      ∀ (σ : MixedSelection), ValidMixedSelection acc σ →
        ∀ n, Squarefree (mixedWalkProd acc σ n))
    ∧
    -- 2. GoodAccumulator above threshold (coprime)
    (∃ M, ∀ m, M ≤ m → Squarefree m → Nat.Coprime m q →
      GoodAccumulator q m)
    ∧
    -- 3. -1 reachable above threshold (coprime)
    (∃ M, ∀ m, M ≤ m → 2 ≤ m → Squarefree m → Nat.Coprime m q →
      (-1 : ZMod q) ∈ reachableEver q m)
    ∧
    -- 4. Single capture above threshold (coprime)
    (∃ M, ∀ m, M ≤ m → 2 ≤ m → Squarefree m → Nat.Coprime m q →
      PositiveProbCapture q m ε) :=
  ⟨mixedWalkProd_squarefree,
   tsd_implies_good q hTSD,
   tsd_implies_neg_one_reachable q hq hq2 hTSD,
   tsd_implies_capture q hq hq2 hTSD ε hε⟩

end FullInterpolationLandscape

/-! ## Part 9: Accumulator Commutativity (Orbit Melting)

Squarefree accumulators are determined by their prime factorizations. Two walks
that accumulate the same set of primes reach the same integer and therefore face
identical futures. This means the factor tree is not a pure tree but a DAG with
merges: distinct walk paths can "melt" together when they produce the same
accumulator.

Key consequences:
1. The number of distinct reachable accumulators grows polynomially (bounded by
   the number of subsets of primes), not exponentially (2^N paths).
2. Any walk that ever passes through a good accumulator can capture any prime,
   regardless of the preceding path.
3. PositiveProbCapture propagates backward: if an intermediate accumulator is
   good, the starting point has positive probability capture.
-/

section AccumulatorCommutativity

/-- Two squarefree positive integers with the same set of prime factors are equal.

    Squarefree integers are uniquely determined by their prime factorizations:
    since each prime appears with exponent exactly 1, the integer equals the
    product of its prime factor set. If two squarefree integers share the same
    prime factor set, they share the same product, hence are equal. -/
theorem eq_of_same_primeFactors_squarefree {P Q : ℕ}
    (hP : Squarefree P) (hQ : Squarefree Q)
    (heq : P.primeFactors = Q.primeFactors) : P = Q := by
  have h1 := Nat.prod_primeFactors_of_squarefree hP
  have h2 := Nat.prod_primeFactors_of_squarefree hQ
  rw [heq] at h1
  linarith

/-- If two mixed walks from the same starting point reach the same accumulator,
    their reachable sets (mod q) from that point onward are identical.

    This is trivially true because `reachableEver q P` depends only on the
    integer P, not on the walk history that produced P. The significance is
    mathematical: accumulator commutativity means the factor tree is a DAG,
    not a tree. Walk paths that produce the same accumulator "melt" together
    and face identical futures. -/
theorem same_accumulator_same_future (q : ℕ) (m : ℕ)
    (σ₁ σ₂ : MixedSelection) (n₁ n₂ : ℕ)
    (heq : mixedWalkProd m σ₁ n₁ = mixedWalkProd m σ₂ n₂) :
    reachableEver q (mixedWalkProd m σ₁ n₁) =
    reachableEver q (mixedWalkProd m σ₂ n₂) := by
  rw [heq]

/-- If -1 mod q is reachable from an intermediate accumulator along a valid walk
    from m, then -1 mod q is reachable from m itself.

    Proof: compose the first n steps of σ (reaching the intermediate accumulator)
    with the witnessing path from that accumulator. The concatenated path is valid
    and hits -1 mod q at step n + j.

    This captures the "regeneration structure": if the walk EVER reaches a good
    accumulator, the game is already won from the starting point. -/
theorem tail_reachable_implies_reachable (q : ℕ) (m : ℕ)
    (σ : MixedSelection) (hv : ValidMixedSelection m σ) (n : ℕ)
    (hreach : (-1 : ZMod q) ∈ reachableEver q (mixedWalkProd m σ n)) :
    (-1 : ZMod q) ∈ reachableEver q m := by
  rw [reachableEver, Set.mem_iUnion] at hreach ⊢
  obtain ⟨j, σ', hv', hmod'⟩ := hreach
  -- Concatenate σ (up to step n) with σ' to get a path from m
  let σ_cat := concatMixedSelection σ σ' n
  have hv_cat : ValidMixedSelection m σ_cat := concat_valid m σ σ' n hv hv'
  -- At step n + j, the walk hits -1
  have hhit : (mixedWalkProd m σ_cat (n + j) : ZMod q) = -1 := by
    rw [concat_walk_tail]; exact hmod'
  exact ⟨n + j, σ_cat, hv_cat, hhit⟩

/-- If an intermediate accumulator along a valid walk is a GoodAccumulator,
    then the starting point has PositiveProbCapture.

    Proof: GoodAccumulator at the intermediate point means -1 is reachable
    from there (for q >= 3). By `tail_reachable_implies_reachable`, -1 is
    reachable from m. Then `reachable_implies_positive_prob_capture` gives
    PositiveProbCapture. -/
theorem good_accumulator_propagates_to_start
    (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (m : ℕ) (hm : 2 ≤ m)
    (σ : MixedSelection) (hv : ValidMixedSelection m σ) (n : ℕ)
    (hgood : GoodAccumulator q (mixedWalkProd m σ n))
    (ε : ℝ) (hε : 0 < ε) :
    PositiveProbCapture q m ε := by
  have hreach_intermediate :=
    good_accumulator_neg_one_reachable q hq hq2 _ hgood
  have hreach_start := tail_reachable_implies_reachable q m σ hv n hreach_intermediate
  exact reachable_implies_positive_prob_capture hq hm hε hreach_start

/-- **Orbit Melting Landscape**: Summary of accumulator commutativity results.

    1. Squarefree integers with the same prime factors are equal
    2. Same accumulator implies same future reachable set
    3. Reachability propagates backward through walk prefixes
    4. GoodAccumulator at any intermediate step implies PositiveProbCapture
       at the starting point -/
theorem orbit_melting_landscape
    (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    -- 1. Squarefree uniqueness by prime factors
    (∀ (P Q : ℕ), Squarefree P → Squarefree Q →
      P.primeFactors = Q.primeFactors → P = Q)
    ∧
    -- 2. Same accumulator, same future
    (∀ (σ₁ σ₂ : MixedSelection) (n₁ n₂ : ℕ),
      mixedWalkProd m σ₁ n₁ = mixedWalkProd m σ₂ n₂ →
      reachableEver q (mixedWalkProd m σ₁ n₁) =
      reachableEver q (mixedWalkProd m σ₂ n₂))
    ∧
    -- 3. Backward reachability propagation
    (∀ (σ : MixedSelection) (n : ℕ), ValidMixedSelection m σ →
      (-1 : ZMod q) ∈ reachableEver q (mixedWalkProd m σ n) →
      (-1 : ZMod q) ∈ reachableEver q m)
    ∧
    -- 4. GoodAccumulator backward propagation to PositiveProbCapture
    (∀ (σ : MixedSelection) (n : ℕ), ValidMixedSelection m σ →
      GoodAccumulator q (mixedWalkProd m σ n) →
      PositiveProbCapture q m ε) :=
  ⟨fun _ _ hP hQ heq => eq_of_same_primeFactors_squarefree hP hQ heq,
   same_accumulator_same_future q m,
   fun σ n hv hreach => tail_reachable_implies_reachable q m σ hv n hreach,
   fun σ n hv hgood => good_accumulator_propagates_to_start q hq hq2 m hm σ hv n hgood ε hε⟩

end AccumulatorCommutativity

/-! ## Part 10: TSD-Hitting(3) Unconditional

For q = 3, TreeSieveDecayHitting holds unconditionally: every squarefree P >= 2
coprime to 3 has (-1 : ZMod 3) reachable. The proof uses the mod-3 dichotomy:
- P ≡ 2 mod 3: walk starts at -1, trivially reachable.
- P ≡ 1 mod 3: P+1 ≡ 2 mod 3, and some prime factor of P+1 is ≡ 2 mod 3
  (otherwise the product would be ≡ 1). Choosing that factor gives position
  P * factor ≡ 1 * 2 = 2 ≡ -1 mod 3.

This is the SOLE unconditional TSD-Hitting result (beyond q=2 which is trivial).
-/

section TSDHittingThree

/-- In ZMod 3, 2 = -1. -/
private theorem zmod3_two_eq_neg_one : (2 : ZMod 3) = -1 := by decide

/-- Coprime P 3 implies 3 does not divide P. -/
private theorem not_dvd_of_coprime_three {P : ℕ} (hcop : Nat.Coprime P 3) : ¬(3 ∣ P) := by
  intro h
  have : 3 ∣ Nat.gcd P 3 := Nat.dvd_gcd h (dvd_refl 3)
  rw [hcop] at this; omega

/-- Coprime P 3 implies (P : ZMod 3) ≠ 0. -/
private theorem ne_zero_zmod3_of_coprime {P : ℕ} (hcop : Nat.Coprime P 3) :
    (P : ZMod 3) ≠ 0 := by
  intro h
  have : 3 ∣ P := by rwa [ZMod.natCast_eq_zero_iff] at h
  exact not_dvd_of_coprime_three hcop this

/-- In ZMod 3, if x ≠ 0, then x = 1 or x = 2. -/
private theorem zmod3_nonzero_cases {x : ZMod 3} (hx : x ≠ 0) :
    x = 1 ∨ x = 2 := by
  revert hx; revert x; decide

/-- If N >= 2, (N : ZMod 3) = 2, and 3 does not divide N, then N has a
    prime factor p with (p : ZMod 3) = 2.

    Proof by strong induction on N. Let p = minFac(N). If (p : ZMod 3) = 2,
    done. Since 3 does not divide N, (p : ZMod 3) != 0. So the remaining
    case is (p : ZMod 3) = 1, giving N/p ≡ 2 mod 3 (same residue) with
    N/p < N and N/p >= 2 (since N is not prime with residue 2, or if N is
    prime then its own residue is 2 and we already won). -/
private theorem exists_prime_factor_mod3_eq_two :
    ∀ N : ℕ, 2 ≤ N → (N : ZMod 3) = 2 → ¬(3 ∣ N) →
      ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ (p : ZMod 3) = 2 := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro hN hmod hndvd
    -- Let p = minFac N
    let p := N.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpdvd : p ∣ N := Nat.minFac_dvd N
    -- p ≠ 3 (since 3 does not divide N)
    have hp3 : p ≠ 3 := fun heq => hndvd (heq ▸ hpdvd)
    -- So (p : ZMod 3) ≠ 0
    have hp_ne_zero : (p : ZMod 3) ≠ 0 := by
      intro h
      have : 3 ∣ p := by rwa [ZMod.natCast_eq_zero_iff] at h
      have := hp.eq_one_or_self_of_dvd 3 this
      rcases this with h1 | h1 <;> omega
    -- Case split on (p : ZMod 3)
    rcases zmod3_nonzero_cases hp_ne_zero with hp1 | hp2
    · -- (p : ZMod 3) = 1: then N/p ≡ 2 mod 3 and N/p < N
      have hN_ne_p : N ≠ p := by
        intro heq
        rw [heq, hp1] at hmod; exact absurd hmod (by decide)
      -- N/p ≥ 2
      have hNp := Nat.div_dvd_of_dvd hpdvd
      have hplt : p < N :=
        lt_of_le_of_ne (Nat.minFac_le (by omega)) (Ne.symm hN_ne_p)
      have hN_div_ge : 2 ≤ N / p := by
        by_contra h; push Not at h
        have hpos := Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hp.pos
        have heq1 : N / p = 1 := by omega
        exact hN_ne_p (by rw [← Nat.div_mul_cancel hpdvd, heq1, one_mul])
      -- (N/p : ZMod 3) = 2
      have hmod_div : ((N / p : ℕ) : ZMod 3) = 2 := by
        have : (N : ZMod 3) = (p : ZMod 3) * ((N / p : ℕ) : ZMod 3) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' hpdvd]
        rw [hmod, hp1, one_mul] at this; exact this.symm
      have hndvd_div : ¬(3 ∣ N / p) := fun h => hndvd (dvd_trans h hNp)
      -- N / p < N
      have hlt : N / p < N := Nat.div_lt_self (by omega) hp.one_lt
      -- Apply IH
      obtain ⟨q, hqp, hqdvd, hqmod⟩ := ih (N / p) hlt hN_div_ge hmod_div hndvd_div
      exact ⟨q, hqp, dvd_trans hqdvd hNp, hqmod⟩
    · -- (p : ZMod 3) = 2: done
      exact ⟨p, hp, hpdvd, hp2⟩

/-- For P ≡ 1 mod 3 with P >= 2, there exists a prime factor of P+1
    that is ≡ 2 mod 3. -/
private theorem exists_factor_of_succ_mod3 (P : ℕ) (hP : 2 ≤ P)
    (hmod : (P : ZMod 3) = 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ (P + 1) ∧ (p : ZMod 3) = 2 := by
  -- (↑(P + 1) : ZMod 3) = 2
  have hmod_succ : ((P + 1 : ℕ) : ZMod 3) = 2 := by
    push_cast; rw [hmod]; decide
  have hndvd : ¬(3 ∣ P + 1) := by
    intro h; have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hmod_succ] at this; exact absurd this (by decide)
  exact exists_prime_factor_mod3_eq_two (P + 1) (by omega) hmod_succ hndvd

/-- **TreeSieveDecayHitting(3) Unconditional**: Every squarefree integer P >= 2
    coprime to 3 has (-1 : ZMod 3) in its reachable set.

    Proof by mod-3 dichotomy:
    - P ≡ 2 mod 3: (P : ZMod 3) = 2 = -1, reachable at step 0.
    - P ≡ 1 mod 3: P+1 ≡ 2 mod 3. By `exists_factor_of_succ_mod3`,
      some prime p | P+1 has (p : ZMod 3) = 2. Choosing p gives walk position
      P * p ≡ 1 * 2 = 2 = -1 mod 3 at step 1, via `reachableAt_from_factor`. -/
theorem tsd_hitting_three_unconditional : TreeSieveDecayHitting 3 := by
  refine ⟨2, fun P hP _hsf hcop => ?_⟩
  -- Case split on (P : ZMod 3)
  have hp_ne_zero := ne_zero_zmod3_of_coprime hcop
  rcases zmod3_nonzero_cases hp_ne_zero with hmod1 | hmod2
  · -- P ≡ 1 mod 3: find factor ≡ 2 mod 3 of P+1
    obtain ⟨p, hprime, hpdvd, hpmod⟩ := exists_factor_of_succ_mod3 P hP hmod1
    -- Use reachableAt_from_factor: P * p ∈ reachableAt 3 P 1
    have hreach1 : (P * p : ZMod 3) ∈ reachableAt 3 P 1 :=
      reachableAt_from_factor (minFacMixed_valid P) hprime hpdvd
    -- (P * p : ZMod 3) = 1 * 2 = 2 = -1
    have hval : (P * p : ZMod 3) = -1 := by
      rw [hmod1, hpmod]; decide
    -- So -1 ∈ reachableAt 3 P 1 ⊆ reachableEver 3 P
    exact Set.subset_iUnion (reachableAt 3 P) 1 (hval ▸ hreach1)
  · -- P ≡ 2 mod 3 = -1 mod 3: reachable at step 0
    have hval : (P : ZMod 3) = -1 := by rw [hmod2]; exact zmod3_two_eq_neg_one
    -- P ∈ reachableAt 3 P 0
    have h0 : (P : ZMod 3) ∈ reachableAt 3 P 0 := by
      rw [reachableAt_zero]; exact Set.mem_singleton_iff.mpr rfl
    exact Set.subset_iUnion (reachableAt 3 P) 0 (hval ▸ h0)

/-- **TSD-Hitting(3) landscape**: summary of the unconditional q=3 result.
    1. TreeSieveDecayHitting(3) is unconditionally true.
    2. (-1 : ZMod 3) = 2 in ZMod 3.
    3. Coprime to 3 means P ≡ 1 or P ≡ 2 mod 3. -/
theorem tsd_hitting_three_landscape :
    TreeSieveDecayHitting 3
    ∧ (2 : ZMod 3) = (-1 : ZMod 3)
    ∧ (∀ P : ℕ, Nat.Coprime P 3 → (P : ZMod 3) = 1 ∨ (P : ZMod 3) = 2) :=
  ⟨tsd_hitting_three_unconditional,
   by decide,
   fun P hcop => zmod3_nonzero_cases (ne_zero_zmod3_of_coprime hcop)⟩

end TSDHittingThree

/-! ## Part 11: TSD → MixedMC Composition

The key observation: `tsd_implies_neg_one_reachable` requires the starting point m
to be above the TreeSieveDecay threshold P₀. But for ANY m >= 2, the minFac walk
from m produces accumulators that grow exponentially (at least m * 2^k at step k).
So eventually the accumulator exceeds P₀.

Combined with the death/no-death dichotomy:
- If the minFac walk hits -1 at some step: done.
- If not: accumulators stay coprime to q, stay squarefree, and eventually exceed P₀.
  TSD gives GoodAccumulator at that point, and `tail_reachable_implies_reachable`
  propagates -1 reachability back to m.

This eliminates the large-m threshold, giving -1 reachable from ANY m ≥ 2 that is
squarefree and coprime to q. In particular, m = 2 works.
-/

section TSDMixedMCComposition

/-! ### Part 11a: Exponential Growth of Mixed Walk -/

/-- The mixed walk accumulator grows exponentially: at step k, the accumulator
    is at least acc * 2^k. The proof is by induction: at each step, the factor
    is a prime ≥ 2, so the accumulator at least doubles. -/
theorem mixedWalkProd_exp_growth (acc : ℕ) (hacc : 2 ≤ acc)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ) (k : ℕ) :
    acc * 2 ^ k ≤ mixedWalkProd acc σ k := by
  induction k with
  | zero => simp [mixedWalkProd]
  | succ n ih =>
    rw [mixedWalkProd_succ]
    have hge := mixedWalkProd_ge_two acc hacc σ hv n
    have hfp := mixedWalkFactor_prime acc σ hv n hge
    have hfge : 2 ≤ mixedWalkFactor acc σ n := hfp.two_le
    calc acc * 2 ^ (n + 1)
        = acc * 2 ^ n * 2 := by ring
      _ ≤ mixedWalkProd acc σ n * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ mixedWalkProd acc σ n * mixedWalkFactor acc σ n :=
          Nat.mul_le_mul_left _ hfge

/-- The mixed walk accumulator is eventually above any threshold. -/
theorem mixedWalkProd_eventually_large (acc : ℕ) (hacc : 2 ≤ acc)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ) (P₀ : ℕ) :
    ∃ K : ℕ, P₀ ≤ mixedWalkProd acc σ K := by
  -- acc * 2^K → ∞, so eventually exceeds P₀
  -- Choose K large enough that acc * 2^K ≥ P₀
  suffices ∃ K, P₀ ≤ acc * 2 ^ K by
    obtain ⟨K, hK⟩ := this
    exact ⟨K, le_trans hK (mixedWalkProd_exp_growth acc hacc σ hv K)⟩
  exact ⟨P₀, le_trans (le_trans Nat.lt_two_pow_self.le
    (Nat.le_mul_of_pos_left _ (by omega))) (le_refl _)⟩

/-! ### Part 11b: TSD → Reachable from Any Squarefree Coprime -/

/-- **Key theorem**: TreeSieveDecay(q) implies -1 is reachable from ANY
    squarefree m ≥ 2 coprime to q, with NO threshold requirement on m.

    Proof: Consider the all-minFac walk from m.
    - Case A: the walk hits -1 at some step. Done.
    - Case B: the walk never hits -1. Then by `mixedWalkProd_coprime_of_no_death`,
      all accumulators stay coprime to q. By `mixedWalkProd_squarefree`, they stay
      squarefree. By `mixedWalkProd_eventually_large`, they eventually exceed P₀.
      TSD gives GoodAccumulator at that point. By `good_accumulator_neg_one_reachable`,
      -1 is reachable from that accumulator. By `tail_reachable_implies_reachable`,
      -1 is reachable from m. -/
theorem tsd_implies_reachable_from_any (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q)
    (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (hcop : Nat.Coprime m q) :
    (-1 : ZMod q) ∈ reachableEver q m := by
  obtain ⟨P₀, hP₀⟩ := hTSD
  -- Dichotomy on the all-minFac walk
  by_cases hdeath : ∃ k, (mixedWalkProd m minFacMixed k : ZMod q) = -1
  · -- Case A: walk hits -1 at some step k
    obtain ⟨k, hk⟩ := hdeath
    rw [reachableEver, Set.mem_iUnion]
    exact ⟨k, minFacMixed, minFacMixed_valid m, hk⟩
  · -- Case B: walk never hits -1
    push Not at hdeath
    -- All accumulators stay coprime to q
    have hcop_all : ∀ n, Nat.Coprime (mixedWalkProd m minFacMixed n) q :=
      mixedWalkProd_coprime_of_no_death q hq m hm hcop minFacMixed
        (minFacMixed_valid m) hdeath
    -- All accumulators stay squarefree
    have hsf_all : ∀ n, Squarefree (mixedWalkProd m minFacMixed n) :=
      mixedWalkProd_squarefree m hm hsf minFacMixed (minFacMixed_valid m)
    -- Eventually exceed P₀
    obtain ⟨K, hK⟩ := mixedWalkProd_eventually_large m hm minFacMixed
      (minFacMixed_valid m) P₀
    -- The accumulator at step K is good by TSD
    have hgood : GoodAccumulator q (mixedWalkProd m minFacMixed K) :=
      hP₀ _ hK (hsf_all K) (hcop_all K)
    -- So -1 is reachable from the accumulator at step K
    have hreach_K := good_accumulator_neg_one_reachable q hq hq2 _ hgood
    -- Propagate back to m
    exact tail_reachable_implies_reachable q m minFacMixed (minFacMixed_valid m) K hreach_K

/-! ### Part 11c: Specialization to m = 2 -/

/-- For any prime q ≥ 3, 2 is coprime to q. -/
private theorem coprime_two_of_prime_gt_two (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q) :
    Nat.Coprime 2 q := by
  rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
  intro hdvd; exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- **TSD → reachable from 2**: TreeSieveDecay(q) for q prime, q ≥ 3, implies
    -1 is reachable from acc = 2. This is the starting point of the Euler-Mullin
    sequence. -/
theorem tsd_implies_reachable_from_two (q : ℕ) (hq : Nat.Prime q) (hq2 : 2 < q)
    (hTSD : TreeSieveDecay q) :
    (-1 : ZMod q) ∈ reachableEver q 2 :=
  tsd_implies_reachable_from_any q hq hq2 hTSD 2 le_rfl Nat.squarefree_two
    (coprime_two_of_prime_gt_two q hq hq2)

/-- TSD → MixedMC for a single prime q ≥ 5.

    Proof: TSD gives -1 reachable from 2. Extract a witness walk σ and step n
    with (mixedWalkProd 2 σ n : ZMod q) = -1. This means q | mixedWalkProd 2 σ n + 1.
    Then `hit_implies_capture'` constructs a valid capturing selection. -/
theorem tsd_implies_mixed_mc_single (q : ℕ) (hq : Nat.Prime q) (hq5 : 5 ≤ q)
    (hTSD : TreeSieveDecay q) :
    MixedMC q := by
  intro _
  right
  have hq2 : 2 < q := by omega
  -- -1 reachable from 2
  have hreach := tsd_implies_reachable_from_two q hq hq2 hTSD
  -- Extract witness
  rw [reachableEver, Set.mem_iUnion] at hreach
  obtain ⟨n, σ, hv, hmod⟩ := hreach
  -- Convert -1 reachability to divisibility and capture
  have hdvd : q ∣ mixedWalkProd 2 σ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hmod]; ring
  exact hit_implies_capture' hq 2 σ hv n hdvd

/-! ### Part 11d: TSD for All Primes → MixedMullinConjecture -/

/-- **TSD for all primes → MixedMullinConjecture**: If TreeSieveDecay holds for
    every prime q ≥ 5, then MixedMullinConjecture holds.

    Proof: For q = 2, use mixed_mc_two. For q = 3, use mixed_mc_three.
    For q ≥ 5, use tsd_implies_mixed_mc_single. -/
theorem tsd_all_implies_mixed_mc
    (hTSD : ∀ q, q.Prime → 5 ≤ q → TreeSieveDecay q) :
    MixedMullinConjecture := by
  intro q hq
  by_cases hq2 : q = 2
  · subst hq2; exact mixed_mc_two
  by_cases hq3 : q = 3
  · subst hq3; exact mixed_mc_three
  · have hq5 : 5 ≤ q := by
      by_contra h; push Not at h
      interval_cases q <;> first | omega | exact absurd hq (by decide)
    exact tsd_implies_mixed_mc_single q hq hq5 (hTSD q hq hq5)

/-! ### Part 11e: TSD Composition Landscape -/

/-- **TSD Composition Landscape**: Summary of the TSD → MixedMC chain.

    1. Exponential growth: mixedWalkProd acc σ k ≥ acc * 2^k (unconditional)
    2. Eventually large: accumulators eventually exceed any threshold
    3. Reachable from any: TSD → -1 reachable from any sqfree coprime m ≥ 2
    4. Reachable from 2: TSD → -1 reachable from acc = 2
    5. TSD → MixedMC(q) for each q ≥ 5
    6. TSD for all primes → MixedMullinConjecture -/
theorem tsd_mixed_mc_landscape
    (hTSD_all : ∀ q, q.Prime → 5 ≤ q → TreeSieveDecay q) :
    -- 1. Exponential growth
    (∀ (acc : ℕ), 2 ≤ acc → ∀ (σ : MixedSelection), ValidMixedSelection acc σ →
      ∀ k, acc * 2 ^ k ≤ mixedWalkProd acc σ k)
    ∧
    -- 2. Eventually large
    (∀ (acc : ℕ), 2 ≤ acc → ∀ (σ : MixedSelection), ValidMixedSelection acc σ →
      ∀ P₀, ∃ K, P₀ ≤ mixedWalkProd acc σ K)
    ∧
    -- 3. Reachable from any squarefree coprime m ≥ 2
    (∀ q, q.Prime → 2 < q → TreeSieveDecay q →
      ∀ m, 2 ≤ m → Squarefree m → Nat.Coprime m q →
        (-1 : ZMod q) ∈ reachableEver q m)
    ∧
    -- 4. Reachable from 2
    (∀ q, q.Prime → 2 < q → TreeSieveDecay q →
      (-1 : ZMod q) ∈ reachableEver q 2)
    ∧
    -- 5. TSD → MixedMC for each q ≥ 5
    (∀ q, q.Prime → 5 ≤ q → TreeSieveDecay q → MixedMC q)
    ∧
    -- 6. TSD for all primes → MixedMullinConjecture
    MixedMullinConjecture :=
  ⟨mixedWalkProd_exp_growth,
   mixedWalkProd_eventually_large,
   tsd_implies_reachable_from_any,
   tsd_implies_reachable_from_two,
   tsd_implies_mixed_mc_single,
   tsd_all_implies_mixed_mc hTSD_all⟩

end TSDMixedMCComposition

/-! ## Part 12: Coset Ambiguity Gap

The structural reason TSD-Hitting(3) is unconditional but TSD-Hitting(q) for q >= 5 is not.

For q = 3, (Z/3Z)x = {1, 2} has only ONE non-identity element, which IS -1 = 2.
So any prime factor escaping the trivial subgroup {1} must land at 2 = -1.
For q = 5, (Z/5Z)x = {1, 2, 3, 4} has the unique proper subgroup H = {1, 4} = {1, -1},
and escaping H can land in EITHER coset {2} or {3}. Choosing the "wrong" coset
bounces the walk (e.g., 2 * 3 = 1 mod 5) instead of hitting -1.

Concrete counterexample: P = 2 (squarefree, coprime to 5, P = 2 mod 5).
P + 1 = 3 is prime with 3 = 3 mod 5. The only available factor is 3,
giving new accumulator 2 * 3 = 6 = 1 mod 5 (bounce, not hit). There is
NO factor in the same residue class 2 mod 5 to choose for a direct hit.
-/

section CosetAmbiguityGap

/-- Counterexample: P = 2 is a valid accumulator for q = 5 where P + 1 = 3 is prime
    and its only factor (3) is in the "wrong" coset mod 5.
    Specifically: 3 mod 5 = 3, not 2, so no same-class factor exists. -/
theorem coset_ambiguity_counterexample :
    2 ≥ 2
    ∧ Squarefree 2
    ∧ Nat.Coprime 2 5
    ∧ (2 : ZMod 5) = 2
    ∧ Nat.Prime 3
    ∧ 3 ∣ (2 + 1)
    ∧ (3 : ZMod 5) ≠ (2 : ZMod 5) :=
  ⟨le_refl 2, Nat.squarefree_two, by decide, by decide, by decide, ⟨1, by norm_num⟩, by decide⟩

/-- For q = 3, every prime p with p != 3 and (p : ZMod 3) != 1
    must have (p : ZMod 3) = 2 (= -1 mod 3). This is the structural
    reason TSD-Hitting(3) works: the only non-identity residue IS -1.

    Proof: ZMod 3 has elements {0, 1, 2}. Since p is prime and p != 3,
    we have (p : ZMod 3) != 0. Given (p : ZMod 3) != 1, the only option is 2. -/
theorem single_coset_implies_immediate_hit (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (hne1 : (p : ZMod 3) ≠ 1) : (p : ZMod 3) = 2 := by
  have hp0 : (p : ZMod 3) ≠ 0 := fun h => by
    have := hp.eq_one_or_self_of_dvd 3 ((ZMod.natCast_eq_zero_iff _ _).mp h)
    rcases this with h1 | h1 <;> omega
  exact (zmod3_nonzero_cases hp0).resolve_left hne1

/-- For q = 5, there exist non-identity residues in (ZMod 5)x that escape
    the subgroup {1, -1} = {1, 4} but are NOT equal to -1 = 4.
    Both 2 and 3 are such elements, witnessing the two distinct cosets
    of {1, 4} in (ZMod 5)x outside the subgroup itself. -/
theorem two_cosets_counterexample_five :
    (2 : ZMod 5) ≠ (4 : ZMod 5)
    ∧ (3 : ZMod 5) ≠ (4 : ZMod 5)
    ∧ ¬((2 : ZMod 5) = 1 ∨ (2 : ZMod 5) = 4)
    ∧ ¬((3 : ZMod 5) = 1 ∨ (3 : ZMod 5) = 4) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Coset ambiguity landscape: combines the three structural facts that
    explain why TSD-Hitting(3) is unconditional but TSD-Hitting(5) is not.

    1. Counterexample at q = 5: a valid accumulator P = 2 where P + 1 = 3
       has no factor in the same residue class as P.
    2. Single-coset property at q = 3: every coprime-to-3 non-identity
       residue equals -1 mod 3.
    3. Two-coset property at q = 5: there exist coprime-to-5 non-identity
       residues that are NOT -1 mod 5. -/
theorem coset_ambiguity_landscape :
    -- 1. Counterexample: valid accumulator with no same-class factor
    (∃ P : ℕ, P ≥ 2 ∧ Squarefree P ∧ Nat.Coprime P 5
      ∧ Nat.Prime (P + 1) ∧ (P + 1 : ZMod 5) ≠ (P : ZMod 5))
    ∧
    -- 2. q = 3 single-coset: every non-identity coprime-to-3 residue equals -1
    (∀ p : ℕ, p.Prime → p ≠ 3 → (p : ZMod 3) ≠ 1 → (p : ZMod 3) = 2)
    ∧
    -- 3. q = 5 two-coset: non-identity residues outside {1, -1} exist
    (∃ a b : ZMod 5, a ≠ 0 ∧ b ≠ 0
      ∧ ¬(a = 1 ∨ a = 4) ∧ ¬(b = 1 ∨ b = 4)
      ∧ a ≠ 4 ∧ b ≠ 4) :=
  ⟨⟨2, le_refl 2, Nat.squarefree_two, by decide, by decide, by decide⟩,
   single_coset_implies_immediate_hit,
   ⟨2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

end CosetAmbiguityGap

/-! ## Part 13: Perpetual Primality Periodicity

Under perpetual primality (all P(n)+1 prime from some step onward), the walk mod q
follows the autonomous map w -> w*(w+1) on the finite set ZMod q. By pigeonhole,
the walk is eventually periodic mod q. For specific small q (e.g., q = 5), the orbit
can be computed and shown to avoid -1, providing structural obstructions to hitting. -/

section PerpetualPrimalityPeriodicity

/-- Under perpetual primality, the walk mod q follows an autonomous recurrence:
    w(n+1) = w(n) * (w(n) + 1) mod q. This is because P(n+1) = P(n) * (P(n)+1)
    under perpetual primality (minFac of a prime is itself). -/
theorem perpetual_prime_autonomous_mod (acc : ℕ) (_hacc : 2 ≤ acc) (q : ℕ)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    (mixedWalkProd acc minFacMixed (N + k + 1) : ZMod q) =
    (mixedWalkProd acc minFacMixed (N + k) : ZMod q) *
    ((mixedWalkProd acc minFacMixed (N + k) : ZMod q) + 1) := by
  rw [perpetual_prime_recurrence acc N hperp k]
  push_cast
  ring

/-- Helper: the autonomous mod-q function applied to a walk value gives the next. -/
private theorem perpetual_prime_step_eq (acc : ℕ) (hacc : 2 ≤ acc) (q : ℕ)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime)
    (i j : ℕ) (heq : (mixedWalkProd acc minFacMixed (N + i) : ZMod q) =
                      (mixedWalkProd acc minFacMixed (N + j) : ZMod q)) :
    (mixedWalkProd acc minFacMixed (N + i + 1) : ZMod q) =
    (mixedWalkProd acc minFacMixed (N + j + 1) : ZMod q) := by
  rw [perpetual_prime_autonomous_mod acc hacc q N hperp i,
      perpetual_prime_autonomous_mod acc hacc q N hperp j, heq]

/-- Under perpetual primality, the walk is eventually periodic mod q.
    Since the map w -> w*(w+1) is autonomous on the finite set ZMod q,
    pigeonhole gives a collision, and the autonomous recurrence propagates periodicity. -/
theorem perpetual_prime_eventually_periodic (acc : ℕ) (hacc : 2 ≤ acc) (q : ℕ) (hq : 2 ≤ q)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) :
    ∃ n₀ T : ℕ, N ≤ n₀ ∧ 0 < T ∧
    ∀ j, (mixedWalkProd acc minFacMixed (n₀ + j + T) : ZMod q) =
         (mixedWalkProd acc minFacMixed (n₀ + j) : ZMod q) := by
  -- Define the sequence mod q on Fin (q+1) → ZMod q
  haveI : NeZero q := ⟨by omega⟩
  let f : Fin (q + 1) → ZMod q := fun i => (mixedWalkProd acc minFacMixed (N + i.val) : ZMod q)
  -- Pigeonhole: q+1 > q = card (ZMod q), so f is not injective
  have hcard : Fintype.card (ZMod q) < Fintype.card (Fin (q + 1)) := by
    rw [ZMod.card q, Fintype.card_fin]
    omega
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  -- Extract i < j with f(i) = f(j) using WLOG a < b or b < a
  have hval_ne : a.val ≠ b.val := Fin.val_ne_of_ne hab
  -- Get i, j with i < j
  obtain ⟨i, j, hij, hfij⟩ : ∃ i j : ℕ, i < j ∧
      (mixedWalkProd acc minFacMixed (N + i) : ZMod q) =
      (mixedWalkProd acc minFacMixed (N + j) : ZMod q) := by
    rcases Nat.lt_or_gt_of_ne hval_ne with h | h
    · exact ⟨a.val, b.val, h, hfab⟩
    · exact ⟨b.val, a.val, h, hfab.symm⟩
  -- Set n₀ = N + i, T = j - i
  refine ⟨N + i, j - i, by omega, by omega, ?_⟩
  -- Prove periodicity by induction on j
  intro m
  induction m with
  | zero =>
    simp only [Nat.add_zero]
    have e : N + i + (j - i) = N + j := by omega
    rw [e]; exact hfij.symm
  | succ m ih =>
    -- Goal: f(n₀ + (m+1) + T) = f(n₀ + (m+1))
    -- By autonomous map: f(n₀ + m + T + 1) = f(n₀ + m + T) * (f(n₀ + m + T) + 1)
    -- and f(n₀ + m + 1) = f(n₀ + m) * (f(n₀ + m) + 1)
    -- By IH: f(n₀ + m + T) = f(n₀ + m), so they're equal.
    have e1 : N + i + (m + 1) + (j - i) = N + (i + m + (j - i)) + 1 := by omega
    have e2 : N + i + (m + 1) = N + (i + m) + 1 := by omega
    have e3 : N + i + m + (j - i) = N + (i + m + (j - i)) := by omega
    have e4 : N + i + m = N + (i + m) := by omega
    show (mixedWalkProd acc minFacMixed (N + i + (m + 1) + (j - i)) : ZMod q) =
         (mixedWalkProd acc minFacMixed (N + i + (m + 1)) : ZMod q)
    rw [e1, e2]
    rw [perpetual_prime_autonomous_mod acc hacc q N hperp (i + m + (j - i)),
        perpetual_prime_autonomous_mod acc hacc q N hperp (i + m)]
    rw [show N + (i + m + (j - i)) = N + i + m + (j - i) from by omega,
        show N + (i + m) = N + i + m from by omega]
    rw [ih]

/-- The autonomous map on ZMod 5: w * (w + 1). We show it maps 1 -> 2 and 2 -> 1. -/
private theorem autonomous_map_mod5_one :
    (1 : ZMod 5) * ((1 : ZMod 5) + 1) = 2 := by decide

private theorem autonomous_map_mod5_two :
    (2 : ZMod 5) * ((2 : ZMod 5) + 1) = 1 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 5 is 1 or 2,
    then it stays in {1, 2} forever, never reaching -1 = 4 mod 5. -/
theorem perpetual_prime_mod5_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod5 : (mixedWalkProd 2 minFacMixed N : ZMod 5) = 2 ∨
               (mixedWalkProd 2 minFacMixed N : ZMod 5) = 1) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) ≠ -1 := by
  -- First show that the walk stays in {1, 2} by induction on k
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) = 1 by
    -- Since -1 = 4 in ZMod 5, and 1 ≠ 4, 2 ≠ 4, done
    rcases h with h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod5
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 5 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 5) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 5) from by rw [e]]
    rw [hstep]
    rcases ih with h | h <;> rw [h]
    · -- w = 2: 2 * (2 + 1) = 6 = 1 mod 5
      right; decide
    · -- w = 1: 1 * (1 + 1) = 2 mod 5
      left; decide

-- === Mod-11 orbit exclusion ===

/-- The autonomous map on ZMod 11: 2 * 3 = 6 mod 11. -/
private theorem autonomous_map_mod11_two :
    (2 : ZMod 11) * ((2 : ZMod 11) + 1) = 6 := by decide

/-- The autonomous map on ZMod 11: 6 * 7 = 42 = 9 mod 11. -/
private theorem autonomous_map_mod11_six :
    (6 : ZMod 11) * ((6 : ZMod 11) + 1) = 9 := by decide

/-- The autonomous map on ZMod 11: 9 * 10 = 90 = 2 mod 11. -/
private theorem autonomous_map_mod11_nine :
    (9 : ZMod 11) * ((9 : ZMod 11) + 1) = 2 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 11 is in {2, 6, 9},
    then it stays in {2, 6, 9} forever, never reaching -1 = 10 mod 11.
    The orbit is a 3-cycle: 2 -> 6 -> 9 -> 2. -/
theorem perpetual_prime_mod11_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod11 : (mixedWalkProd 2 minFacMixed N : ZMod 11) = 2 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 11) = 6 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 11) = 9) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) ≠ -1 := by
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) = 6 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) = 9 by
    rcases h with h | h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod11
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 11 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 11) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 11) from by rw [e]]
    rw [hstep]
    rcases ih with h | h | h <;> rw [h]
    · -- w = 2: 2 * 3 = 6 mod 11
      right; left; decide
    · -- w = 6: 6 * 7 = 9 mod 11
      right; right; decide
    · -- w = 9: 9 * 10 = 2 mod 11
      left; decide

-- === Mod-17 orbit exclusion ===

/-- The autonomous map on ZMod 17: 2 * 3 = 6 mod 17. -/
private theorem autonomous_map_mod17_two :
    (2 : ZMod 17) * ((2 : ZMod 17) + 1) = 6 := by decide

/-- The autonomous map on ZMod 17: 6 * 7 = 42 = 8 mod 17. -/
private theorem autonomous_map_mod17_six :
    (6 : ZMod 17) * ((6 : ZMod 17) + 1) = 8 := by decide

/-- The autonomous map on ZMod 17: 8 * 9 = 72 = 4 mod 17. -/
private theorem autonomous_map_mod17_eight :
    (8 : ZMod 17) * ((8 : ZMod 17) + 1) = 4 := by decide

/-- The autonomous map on ZMod 17: 4 * 5 = 20 = 3 mod 17. -/
private theorem autonomous_map_mod17_four :
    (4 : ZMod 17) * ((4 : ZMod 17) + 1) = 3 := by decide

/-- The autonomous map on ZMod 17: 3 * 4 = 12 mod 17. -/
private theorem autonomous_map_mod17_three :
    (3 : ZMod 17) * ((3 : ZMod 17) + 1) = 12 := by decide

/-- The autonomous map on ZMod 17: 12 * 13 = 156 = 3 mod 17. -/
private theorem autonomous_map_mod17_twelve :
    (12 : ZMod 17) * ((12 : ZMod 17) + 1) = 3 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 17 is in
    {2, 3, 4, 6, 8, 12}, then it stays in that set forever, never reaching -1 = 16 mod 17.
    The dynamics: 2 -> 6 -> 8 -> 4 -> 3 -> 12 -> 3 (tail + 2-cycle {3, 12}). -/
theorem perpetual_prime_mod17_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod17 : (mixedWalkProd 2 minFacMixed N : ZMod 17) = 2 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 6 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 8 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 4 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 3 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 12) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) ≠ -1 := by
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 6 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 8 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 4 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 3 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 12 by
    rcases h with h | h | h | h | h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod17
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 17 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 17) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 17) from by rw [e]]
    rw [hstep]
    rcases ih with h | h | h | h | h | h <;> rw [h]
    · -- w = 2: 2 * 3 = 6 mod 17
      right; left; decide
    · -- w = 6: 6 * 7 = 8 mod 17
      right; right; left; decide
    · -- w = 8: 8 * 9 = 4 mod 17
      right; right; right; left; decide
    · -- w = 4: 4 * 5 = 3 mod 17
      right; right; right; right; left; decide
    · -- w = 3: 3 * 4 = 12 mod 17
      right; right; right; right; right; decide
    · -- w = 12: 12 * 13 = 3 mod 17
      right; right; right; right; left; decide

-- === Mod-23 orbit exclusion ===

/-- The autonomous map on ZMod 23: 2 * 3 = 6 mod 23. -/
private theorem autonomous_map_mod23_two :
    (2 : ZMod 23) * ((2 : ZMod 23) + 1) = 6 := by decide

/-- The autonomous map on ZMod 23: 6 * 7 = 42 = 19 mod 23. -/
private theorem autonomous_map_mod23_six :
    (6 : ZMod 23) * ((6 : ZMod 23) + 1) = 19 := by decide

/-- The autonomous map on ZMod 23: 19 * 20 = 380 = 12 mod 23. -/
private theorem autonomous_map_mod23_nineteen :
    (19 : ZMod 23) * ((19 : ZMod 23) + 1) = 12 := by decide

/-- The autonomous map on ZMod 23: 12 * 13 = 156 = 18 mod 23. -/
private theorem autonomous_map_mod23_twelve :
    (12 : ZMod 23) * ((12 : ZMod 23) + 1) = 18 := by decide

/-- The autonomous map on ZMod 23: 18 * 19 = 342 = 20 mod 23. -/
private theorem autonomous_map_mod23_eighteen :
    (18 : ZMod 23) * ((18 : ZMod 23) + 1) = 20 := by decide

/-- The autonomous map on ZMod 23: 20 * 21 = 420 = 6 mod 23. -/
private theorem autonomous_map_mod23_twenty :
    (20 : ZMod 23) * ((20 : ZMod 23) + 1) = 6 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 23 is in
    {2, 6, 12, 18, 19, 20}, then it stays in that set forever, never reaching -1 = 22 mod 23.
    The dynamics: 2 -> 6 -> 19 -> 12 -> 18 -> 20 -> 6 (tail {2} + 5-cycle {6,19,12,18,20}). -/
theorem perpetual_prime_mod23_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod23 : (mixedWalkProd 2 minFacMixed N : ZMod 23) = 2 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 6 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 19 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 12 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 18 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 20) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) ≠ -1 := by
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 6 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 19 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 12 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 18 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 20 by
    rcases h with h | h | h | h | h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod23
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 23 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 23) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 23) from by rw [e]]
    rw [hstep]
    rcases ih with h | h | h | h | h | h <;> rw [h]
    · -- w = 2: 2 * 3 = 6 mod 23
      right; left; decide
    · -- w = 6: 6 * 7 = 19 mod 23
      right; right; left; decide
    · -- w = 19: 19 * 20 = 12 mod 23
      right; right; right; left; decide
    · -- w = 12: 12 * 13 = 18 mod 23
      right; right; right; right; left; decide
    · -- w = 18: 18 * 19 = 20 mod 23
      right; right; right; right; right; decide
    · -- w = 20: 20 * 21 = 6 mod 23
      right; left; decide

-- === Multi-prime perpetual primality exclusion landscape ===

/-- **Multi-prime perpetual primality exclusion landscape**:
    Under perpetual primality, the walk simultaneously avoids -1 mod 5, 11, 17, and 23.
    For each prime q in {5, 11, 17, 23}, the autonomous map w -> w*(w+1) on ZMod q
    has a closed orbit (starting from w = 2) that does not contain -1.
    This provides structural obstructions: these primes CANNOT appear in the EM sequence
    under perpetual primality (from the appropriate initial condition). -/
theorem perpetual_primality_multi_exclusion :
    -- 1. Mod 5: orbit {1, 2}, -1 = 4 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 5) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 5) = 1),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) ≠ -1)
    ∧
    -- 2. Mod 11: orbit {2, 6, 9}, -1 = 10 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 11) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 11) = 6 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 11) = 9),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) ≠ -1)
    ∧
    -- 3. Mod 17: orbit {2, 3, 4, 6, 8, 12}, -1 = 16 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 17) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 6 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 8 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 4 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 3 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 12),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) ≠ -1)
    ∧
    -- 4. Mod 23: orbit {2, 6, 12, 18, 19, 20}, -1 = 22 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 23) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 6 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 19 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 12 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 18 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 20),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) ≠ -1) :=
  ⟨perpetual_prime_mod5_orbit, perpetual_prime_mod11_orbit,
   perpetual_prime_mod17_orbit, perpetual_prime_mod23_orbit⟩

/-- **Perpetual primality periodicity landscape**: structural consequences of perpetual primality
    for the walk mod q.

    1. Autonomous recurrence: w(n+1) = w(n) * (w(n) + 1) mod q
    2. Eventually periodic mod q (pigeonhole + autonomous propagation)
    3. Mod-3 exclusion (walk never = 1 mod 3, from EpsilonRandomMC)
    4. Multi-prime orbit exclusion for q in {5, 11, 17, 23} -/
theorem perpetual_primality_periodicity_landscape (acc : ℕ) (hacc : 2 ≤ acc) (q : ℕ) (hq : 2 ≤ q)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) :
    -- 1. Autonomous recurrence mod q
    (∀ k, (mixedWalkProd acc minFacMixed (N + k + 1) : ZMod q) =
      (mixedWalkProd acc minFacMixed (N + k) : ZMod q) *
      ((mixedWalkProd acc minFacMixed (N + k) : ZMod q) + 1))
    ∧
    -- 2. Eventually periodic mod q
    (∃ n₀ T : ℕ, N ≤ n₀ ∧ 0 < T ∧
      ∀ j, (mixedWalkProd acc minFacMixed (n₀ + j + T) : ZMod q) =
           (mixedWalkProd acc minFacMixed (n₀ + j) : ZMod q))
    ∧
    -- 3. Walk never = 1 mod 3
    (∀ k, (mixedWalkProd acc minFacMixed (N + k)) % 3 ≠ 1) :=
  ⟨perpetual_prime_autonomous_mod acc hacc q N hperp,
   perpetual_prime_eventually_periodic acc hacc q hq N hperp,
   perpetual_prime_excludes_mod3_one acc hacc N hperp⟩

end PerpetualPrimalityPeriodicity

-- ============================================================================
-- ## Part 14: Reachable Set Monotonicity
-- ============================================================================

/-- **Reachable set monotonicity**: if a position is reachable from a descendant
    accumulator P_n = mixedWalkProd acc σ n, it is also reachable from acc.

    Proof: prefix the first n steps of σ to the witness walk.

    This generalizes `tail_reachable_implies_reachable` (which handles only -1)
    to arbitrary elements a ∈ (ZMod q).

    Structure: If τ is a valid walk from mixedWalkProd acc σ n that hits a
    at step j, then concatenating σ (first n steps) with τ (remaining steps)
    gives a valid walk from acc that hits a at step n + j. -/
theorem reachableEver_mono_along_walk (q acc : ℕ)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ) (n : ℕ)
    (a : ZMod q) (ha : a ∈ reachableEver q (mixedWalkProd acc σ n)) :
    a ∈ reachableEver q acc := by
  rw [reachableEver, Set.mem_iUnion] at ha ⊢
  obtain ⟨j, τ, hτ_valid, hτ_hit⟩ := ha
  -- Concatenate σ (up to step n) with τ to get a path from acc
  let σ_cat := concatMixedSelection σ τ n
  have hv_cat : ValidMixedSelection acc σ_cat := concat_valid acc σ τ n hv hτ_valid
  -- At step n + j, the concatenated walk hits a
  have hhit : (mixedWalkProd acc σ_cat (n + j) : ZMod q) = a := by
    rw [concat_walk_tail]; exact hτ_hit
  exact ⟨n + j, σ_cat, hv_cat, hhit⟩

end
