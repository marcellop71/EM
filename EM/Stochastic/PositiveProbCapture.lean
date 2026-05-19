import EM.Ensemble.MixedEnsemble
import EM.Ensemble.UnconditionalPSCD

/-!
# Positive Probability Capture via Mixed Walk

## Overview

For a.a. squarefree starting points m and any epsilon > 0, the (1-epsilon) minFac +
epsilon random process from m captures every prime q with positive probability.
(Parts 1-6 of the original interpolation MC development, "Layer 1".)

The "probability" is formalized as the weight of a finite valid path through the
mixed walk tree. No measure theory on infinite paths is needed.

## Contents

* Part 1: Step and path weight definitions -- `stepWeightLB`, `pathWeightLB`,
  `PositiveProbCapture`
* Part 2: Positivity -- `stepWeightLB_pos`, `pathWeightLB_pos`
* Part 3: Reachability implies positive probability capture --
  `reachable_implies_positive_prob_capture`
* Part 4: Almost all positive probability capture --
  `not_positive_prob_capture_implies_trapped`, `failure_count_le_trapped`,
  `almost_all_positive_prob_capture` (PEAP-conditional, superseded),
  `almost_all_positive_prob_capture_unconditional` (**UNCONDITIONAL**, via the
  Dirichlet-density chain of `EM/Ensemble/UnconditionalPSCD.lean`)
* Part 5: Content theorem -- `not_trapped_implies_positive_prob_capture`
* Part 6: Landscape summary -- `interpolation_mc_landscape`

## Mathematical Content

For any prime q and starting point m >= 2:
1. If -1 is reachable mod q from m via some mixed walk, then for ANY epsilon > 0,
   the capturing path has weight >= prod_{k<n} (epsilon / omega(P_k+1)) > 0.
2. Almost all squarefree m coprime to q have -1 reachable — UNCONDITIONALLY
   since Session 302 (`almost_all_mixed_hitting_unconditional`, Dirichlet-density
   chain; the original PEAP-conditional route is kept as
   `almost_all_positive_prob_capture` for the record).
3. Therefore, a.a. squarefree m have positive-probability capture of q,
   unconditionally (`almost_all_positive_prob_capture_unconditional`).

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
private theorem failure_count_le_trapped {ε : ℝ} (hq : Nat.Prime q) (hε : 0 < ε) (X : ℕ) :
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
    proved in MixedEnsemble.lean) and the subset bound.

    SUPERSEDED: `almost_all_positive_prob_capture_unconditional` below discharges
    the PEAP hypothesis via the Dirichlet-density chain. Kept for the record. -/
theorem almost_all_positive_prob_capture (hq : Nat.Prime q)
    (hPEAP : IK.PrimesEquidistributedInAP)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun X => (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  have : NeZero q := ⟨hq.ne_zero⟩
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

/-- **Almost-all positive-probability capture, UNCONDITIONALLY.**

    For every prime `q` and every `ε > 0`: the density of squarefree `m` coprime
    to `q` from which the `(1-ε)·minFac + ε·random` process fails to capture `q`
    with positive probability tends to `0`. In other words, from almost every
    squarefree starting point, the noisy Euclid--Mullin process can reach any
    given prime.

    No open hypothesis: composes `failure_count_le_trapped` with the
    unconditional trapped-density theorem `almost_all_mixed_hitting_unconditional`
    (Dirichlet-density chain, `EM/Ensemble/UnconditionalPSCD.lean`), replacing
    the PEAP hypothesis of `almost_all_positive_prob_capture`.

    Scoping (same as the route-1 theorem): the statement is per-`q` — the
    density-1 set of good starting points depends on `q`, and countably many
    density-1 sets need not intersect in a density-1 set. Any finite set of
    primes can be captured from a common density-1 set of starting points. -/
theorem almost_all_positive_prob_capture_unconditional (hq : Nat.Prime q)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun X => (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have htrapped := almost_all_mixed_hitting_unconditional q hq
  apply squeeze_zero
  · intro X
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro X
    have hle : ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card
      ≤ sqfreeTrappedCount q X := failure_count_le_trapped hq hε X
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) (Nat.cast_nonneg _)
  · exact htrapped

/-- **Diagonal almost-all capture (unconditional): all small primes simultaneously.**

    For every `ε > 0` there is a bound `B : ℕ → ℕ` with `B X → ∞` such that the
    density of squarefree `m ∈ [1, X]` failing positive-probability capture for
    SOME prime `q ≤ B X` (coprime to `m`) tends to `0`: almost all squarefree
    starting points capture, under the `(1-ε)` process, EVERY prime up to a
    bound growing with the window — simultaneously.

    This is the strongest quantifier arrangement derivable from the per-`q`
    chain without uniform-in-`q` sieve rates ("almost all `m` capture every
    prime" would need such uniformity and remains open). The bound `B` comes
    from `almost_all_mixed_hitting_diagonal` and is independent of `ε`. -/
theorem almost_all_positive_prob_capture_diagonal {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ → ℕ, Filter.Tendsto B Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun X =>
        (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
          ∃ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
            Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  obtain ⟨B, hB_top, hB_density⟩ := almost_all_mixed_hitting_diagonal
  refine ⟨B, hB_top, ?_⟩
  -- failure for some q ≤ B X implies trapped for some q ≤ B X, except possibly m = 1
  have hcount : ∀ X : ℕ,
      ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        ∃ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
          Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card
      ≤ sqfreeTrappedUpToCount (B X) X + 1 := by
    intro X
    calc ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
          ∃ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
            Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card
        ≤ (insert 1 ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
            ∃ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
              Nat.Coprime m q ∧ (-1 : ZMod q) ∉ reachableEver q m))).card := by
          apply Finset.card_le_card
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_insert] at hm ⊢
          obtain ⟨hmem, hsf, q, hq, hcop, hfail⟩ := hm
          rcases Nat.lt_or_ge m 2 with hm1 | hm2
          · left
            have := (Finset.mem_Icc.mp hmem).1
            omega
          · right
            refine ⟨hmem, hsf, q, hq, hcop, ?_⟩
            have hqprime : Nat.Prime q := hq.2
            exact not_positive_prob_capture_implies_trapped hqprime hm2 hε hfail
      _ ≤ sqfreeTrappedUpToCount (B X) X + 1 := by
          rw [sqfreeTrappedUpToCount]
          exact Finset.card_insert_le _ _
  -- 1 / sqfreeCount X → 0 via the quarter bound
  have hone : Filter.Tendsto (fun X : ℕ => (1 : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (g := fun X : ℕ => 4 / (X : ℝ))
    · exact Filter.Eventually.of_forall (fun X => by positivity)
    · filter_upwards [Filter.eventually_ge_atTop 4] with X hX
      have hquarter := sqfreeCount_ge_quarter_real X hX
      have hXpos : (0 : ℝ) < (X : ℝ) / 4 := by
        have : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
        linarith
      calc (1 : ℝ) / sqfreeCount X ≤ 1 / ((X : ℝ) / 4) :=
            one_div_le_one_div_of_le hXpos hquarter
        _ = 4 / (X : ℝ) := by rw [one_div_div]
    · exact tendsto_const_div_atTop_nhds_zero_nat 4
  -- squeeze against trappedUpTo density + 1/sqfreeCount
  apply squeeze_zero
  · intro X
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro X
    calc (((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
          ∃ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
            Nat.Coprime m q ∧ ¬PositiveProbCapture q m ε)).card : ℝ) / sqfreeCount X
        ≤ ((sqfreeTrappedUpToCount (B X) X : ℝ) + 1) / sqfreeCount X := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast hcount X
      _ = (sqfreeTrappedUpToCount (B X) X : ℝ) / sqfreeCount X +
          1 / sqfreeCount X := by rw [add_div]
  · have := hB_density.add hone
    simpa using this

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
