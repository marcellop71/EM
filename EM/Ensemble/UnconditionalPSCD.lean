import EM.Ensemble.MixedEnsemble
import EM.IK.DirichletDensity

/-!
# Unconditional PSCD: the weak-FMCD chain with no open hypothesis

This file is the bridge between `EM/IK/DirichletDensity.lean` (the unconditional
Dirichlet-density theorem: `∑ 1/p` diverges over each invertible residue class mod `q`)
and the ensemble framework of `EM/Ensemble/MixedEnsemble.lean`. It discharges the sole
analytic input of the weak-FMCD chain, making the entire chain

  `ForbiddenClassDivergent q  ⇒  PSCD q  ⇒  trapped density → 0  (a.a. mixed hitting)`

**UNCONDITIONAL** (previously the chain was conditional on the open hypothesis
`IK.PrimesEquidistributedInAP`, via `peap_implies_fcd_proved`).

## Main results (all PROVED, unconditional)

* `fcd_unconditional` -- `ForbiddenClassDivergent q` holds for every `q ≥ 2`.
* `pscd_unconditional` -- `PSCD q` holds for every prime `q`.
* `almost_all_mixed_hitting_unconditional` -- for every prime `q`, the trapped density
  among squarefree `m` tends to `0`: almost all coprime-to-`q` squarefree `m` have
  `(-1 : ZMod q) ∈ reachableEver q m` (mixed hitting).

The composition uses `weak_fmcd_fcd_implies_pscd` and
`pscd_implies_almost_all_mixed_hitting` from `MixedEnsemble` (Parts 7 and 19), which
were already proved there with FCD as the only hypothesis.
-/

/-- **ForbiddenClassDivergent, unconditionally**: for every modulus `q ≥ 2`, every unit
class `a : ZMod q` has divergent prime reciprocal sum. Replaces the PEAP-conditional
`peap_implies_fcd_proved`. -/
theorem fcd_unconditional (q : ℕ) (hq : 2 ≤ q) : ForbiddenClassDivergent q := by
  intro a ha
  unfold PrimeReciprocalClassDivergent
  exact IK.DirichletDensity.prime_reciprocal_class_divergent hq ha

/-- **PSCD, unconditionally**: Population Sieve Confinement Decay holds for every prime
modulus. Composes `fcd_unconditional` with the weak-FMCD chain. -/
theorem pscd_unconditional {q : ℕ} (hq : q.Prime) : PSCD q :=
  weak_fmcd_fcd_implies_pscd hq (fcd_unconditional q hq.two_le)

/-- **Almost-all mixed hitting, unconditionally**: for every prime `q`, the density of
trapped `m` (coprime-to-`q`, squarefree, `-1` never reachable) among squarefree `m`
tends to `0`. -/
theorem almost_all_mixed_hitting_unconditional (q : ℕ) (hq : q.Prime) :
    Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  exact pscd_implies_almost_all_mixed_hitting q hq (pscd_unconditional hq)

/-! ## The diagonal strengthening: all small primes simultaneously

`almost_all_mixed_hitting_unconditional` is a per-`q` statement: the density-1
set of good starting points depends on the target prime `q`, and countably many
density-1 sets need not intersect in a density-1 set — so "almost all `m` reach
EVERY prime" does not follow. The strongest form reachable from the per-`q`
limits without uniform-in-`q` sieve rates is the DIAGONAL: there is a bound
`B X → ∞` such that the density of squarefree `m ≤ X` trapped for SOME prime
`q ≤ B X` tends to `0` — almost all starting points reach every prime up to a
bound growing with the window. -/

noncomputable section
open Classical

/-- The count of squarefree `m ∈ [1, X]` trapped for SOME prime `q ≤ j`:
`m` is coprime to `q` yet `-1` is not tree-reachable mod `q`. -/
noncomputable def sqfreeTrappedUpToCount (j X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
    ∃ q ∈ (Finset.range (j + 1)).filter Nat.Prime,
      Nat.Coprime m q ∧ (-1 : ZMod q) ∉ reachableEver q m)).card

/-- Union bound: trapped-for-some-`q ≤ j` is at most the sum of the per-`q`
trapped counts. -/
theorem sqfreeTrappedUpToCount_le_sum (j X : ℕ) :
    sqfreeTrappedUpToCount j X ≤
      ∑ q ∈ (Finset.range (j + 1)).filter Nat.Prime, sqfreeTrappedCount q X := by
  calc sqfreeTrappedUpToCount j X
      ≤ (((Finset.range (j + 1)).filter Nat.Prime).biUnion (fun q =>
          (Finset.Icc 1 X).filter (fun m => Squarefree m ∧
            Nat.Coprime m q ∧ (-1 : ZMod q) ∉ reachableEver q m))).card := by
        apply Finset.card_le_card
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_biUnion] at hm ⊢
        obtain ⟨hmem, hsf, q, hq, hcop, hre⟩ := hm
        exact ⟨q, hq, hmem, hsf, hcop, hre⟩
    _ ≤ ∑ q ∈ (Finset.range (j + 1)).filter Nat.Prime, sqfreeTrappedCount q X :=
        Finset.card_biUnion_le

/-- The summed trapped density over the primes up to a FIXED bound `j` tends
to `0` (finite sum of the per-`q` limits). -/
theorem trapped_sum_density_tendsto_zero (j : ℕ) :
    Filter.Tendsto
      (fun X => ∑ q ∈ (Finset.range (j + 1)).filter Nat.Prime,
        (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  have h0 : (0 : ℝ) = ∑ _q ∈ (Finset.range (j + 1)).filter Nat.Prime, (0 : ℝ) := by simp
  rw [h0]
  apply tendsto_finsetSum
  intro q hq
  rw [Finset.mem_filter] at hq
  exact almost_all_mixed_hitting_unconditional q hq.2

/-- **Diagonal almost-all mixed hitting (unconditional).**

There is a bound `B : ℕ → ℕ` with `B X → ∞` such that the density of squarefree
`m ∈ [1, X]` that are trapped for SOME prime `q ≤ B X` tends to `0`:
almost all squarefree starting points reach, in the factor tree, EVERY prime up
to a bound growing with the window — simultaneously.

This is the strongest quantifier arrangement derivable from the per-`q` chain
without uniform-in-`q` sieve rates; the literal "almost all `m` reach every
prime" (density-one GenMixedMC itself) would require such uniformity and
remains open. -/
theorem almost_all_mixed_hitting_diagonal :
    ∃ B : ℕ → ℕ, Filter.Tendsto B Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun X => (sqfreeTrappedUpToCount (B X) X : ℝ) / sqfreeCount X)
        Filter.atTop (nhds 0) := by
  -- Per-bound thresholds: for each j, beyond N j the summed density is < 1/(j+1)
  have hthresh : ∀ j : ℕ, ∃ N : ℕ, ∀ X ≥ N,
      ∑ q ∈ (Finset.range (j + 1)).filter Nat.Prime,
        (sqfreeTrappedCount q X : ℝ) / sqfreeCount X < 1 / (j + 1) := by
    intro j
    have h := Metric.tendsto_atTop.mp (trapped_sum_density_tendsto_zero j)
      (1 / (j + 1)) (by positivity)
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun X hX => ?_⟩
    have := hN X hX
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  choose N hN using hthresh
  -- Monotone-enough threshold sequence: Ξ j ≥ N j and Ξ j ≥ j
  set Ξ : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup N + j with hΞ
  have hΞ_ge_N : ∀ j, N j ≤ Ξ j := fun j =>
    le_trans (Finset.le_sup (Finset.self_mem_range_succ j)) (Nat.le_add_right _ _)
  have hΞ_ge_id : ∀ j, j ≤ Ξ j := fun j => Nat.le_add_left _ _
  -- The diagonal bound: the largest j with Ξ j ≤ X
  set B : ℕ → ℕ := fun X =>
    if h : ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).Nonempty
    then ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).max' h
    else 0 with hB
  -- B X ≥ j whenever X ≥ Ξ j
  have hB_ge : ∀ j X, Ξ j ≤ X → j ≤ B X := by
    intro j X hjX
    have hmem : j ∈ (Finset.range (X + 1)).filter (fun i => Ξ i ≤ X) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (le_trans (hΞ_ge_id j) hjX), hjX⟩
    have hne : ((Finset.range (X + 1)).filter (fun i => Ξ i ≤ X)).Nonempty := ⟨j, hmem⟩
    have hBX : B X = ((Finset.range (X + 1)).filter (fun i => Ξ i ≤ X)).max' hne := by
      simp only [hB]
      exact dif_pos hne
    rw [hBX]
    exact Finset.le_max' _ j hmem
  -- Ξ (B X) ≤ X whenever the defining set is nonempty
  have hB_spec : ∀ X, Ξ 0 ≤ X → Ξ (B X) ≤ X := by
    intro X h0X
    have hne : ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.succ_pos X, h0X⟩
    have hBX : B X = ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).max' hne := by
      simp only [hB]
      exact dif_pos hne
    have hmem := Finset.max'_mem _ hne
    rw [Finset.mem_filter] at hmem
    rw [hBX]
    exact hmem.2
  refine ⟨B, ?_, ?_⟩
  · -- B X → ∞
    rw [Filter.tendsto_atTop]
    intro j
    filter_upwards [Filter.eventually_ge_atTop (Ξ j)] with X hX
    exact hB_ge j X hX
  · -- diagonal trapped density → 0
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    refine ⟨max (Ξ j) (Ξ 0), fun X hX => ?_⟩
    have hXj : Ξ j ≤ X := le_trans (le_max_left _ _) hX
    have hX0 : Ξ 0 ≤ X := le_trans (le_max_right _ _) hX
    have hBj : j ≤ B X := hB_ge j X hXj
    have hXB : Ξ (B X) ≤ X := hB_spec X hX0
    -- the density is bounded by the summed density at bound B X, which is < 1/(B X + 1)
    have hsum := hN (B X) X (le_trans (hΞ_ge_N (B X)) hXB)
    have hnonneg : (0 : ℝ) ≤ (sqfreeTrappedUpToCount (B X) X : ℝ) / sqfreeCount X :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hle : (sqfreeTrappedUpToCount (B X) X : ℝ) / sqfreeCount X ≤
        ∑ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
          (sqfreeTrappedCount q X : ℝ) / sqfreeCount X := by
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast sqfreeTrappedUpToCount_le_sum (B X) X
    have hstep : (sqfreeTrappedUpToCount (B X) X : ℝ) / sqfreeCount X <
        1 / (B X + 1) := lt_of_le_of_lt hle hsum
    have hmono : (1 : ℝ) / (B X + 1) ≤ 1 / (j + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hBj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact lt_of_lt_of_le hstep (le_trans hmono (le_of_lt hj))

/-- **Expected number of missed small primes → 0 (diagonal, unconditional).**

There is a bound `B : ℕ → ℕ` with `B X → ∞` such that the EXPECTED number of
missed primes `q ≤ B X` of a uniformly random squarefree starting point
`m ∈ [1, X]` — the sum over primes `q ≤ B X` of the per-`q` trapped densities,
i.e. `E[#(Miss(m) ∩ [0, B X])]` by linearity of expectation — tends to `0`.

Same diagonal extraction as `almost_all_mixed_hitting_diagonal`; here the
threshold bound `hN` IS the target sum, so no union-bound comparison step is
needed. -/
theorem expected_missed_smallprimes_diagonal :
    ∃ B : ℕ → ℕ, Filter.Tendsto B Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun X => ∑ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
          (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
        Filter.atTop (nhds 0) := by
  -- Per-bound thresholds: for each j, beyond N j the summed density is < 1/(j+1)
  have hthresh : ∀ j : ℕ, ∃ N : ℕ, ∀ X ≥ N,
      ∑ q ∈ (Finset.range (j + 1)).filter Nat.Prime,
        (sqfreeTrappedCount q X : ℝ) / sqfreeCount X < 1 / (j + 1) := by
    intro j
    have h := Metric.tendsto_atTop.mp (trapped_sum_density_tendsto_zero j)
      (1 / (j + 1)) (by positivity)
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun X hX => ?_⟩
    have := hN X hX
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  choose N hN using hthresh
  -- Monotone-enough threshold sequence: Ξ j ≥ N j and Ξ j ≥ j
  set Ξ : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup N + j with hΞ
  have hΞ_ge_N : ∀ j, N j ≤ Ξ j := fun j =>
    le_trans (Finset.le_sup (Finset.self_mem_range_succ j)) (Nat.le_add_right _ _)
  have hΞ_ge_id : ∀ j, j ≤ Ξ j := fun j => Nat.le_add_left _ _
  -- The diagonal bound: the largest j with Ξ j ≤ X
  set B : ℕ → ℕ := fun X =>
    if h : ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).Nonempty
    then ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).max' h
    else 0 with hB
  -- B X ≥ j whenever X ≥ Ξ j
  have hB_ge : ∀ j X, Ξ j ≤ X → j ≤ B X := by
    intro j X hjX
    have hmem : j ∈ (Finset.range (X + 1)).filter (fun i => Ξ i ≤ X) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (le_trans (hΞ_ge_id j) hjX), hjX⟩
    have hne : ((Finset.range (X + 1)).filter (fun i => Ξ i ≤ X)).Nonempty := ⟨j, hmem⟩
    have hBX : B X = ((Finset.range (X + 1)).filter (fun i => Ξ i ≤ X)).max' hne := by
      simp only [hB]
      exact dif_pos hne
    rw [hBX]
    exact Finset.le_max' _ j hmem
  -- Ξ (B X) ≤ X whenever the defining set is nonempty
  have hB_spec : ∀ X, Ξ 0 ≤ X → Ξ (B X) ≤ X := by
    intro X h0X
    have hne : ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.succ_pos X, h0X⟩
    have hBX : B X = ((Finset.range (X + 1)).filter (fun j => Ξ j ≤ X)).max' hne := by
      simp only [hB]
      exact dif_pos hne
    have hmem := Finset.max'_mem _ hne
    rw [Finset.mem_filter] at hmem
    rw [hBX]
    exact hmem.2
  refine ⟨B, ?_, ?_⟩
  · -- B X → ∞
    rw [Filter.tendsto_atTop]
    intro j
    filter_upwards [Filter.eventually_ge_atTop (Ξ j)] with X hX
    exact hB_ge j X hX
  · -- expected missed-small-primes count → 0
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    refine ⟨max (Ξ j) (Ξ 0), fun X hX => ?_⟩
    have hXj : Ξ j ≤ X := le_trans (le_max_left _ _) hX
    have hX0 : Ξ 0 ≤ X := le_trans (le_max_right _ _) hX
    have hBj : j ≤ B X := hB_ge j X hXj
    have hXB : Ξ (B X) ≤ X := hB_spec X hX0
    -- the summed density at bound B X is < 1/(B X + 1) beyond the threshold
    have hsum := hN (B X) X (le_trans (hΞ_ge_N (B X)) hXB)
    have hnonneg : (0 : ℝ) ≤ ∑ q ∈ (Finset.range (B X + 1)).filter Nat.Prime,
        (sqfreeTrappedCount q X : ℝ) / sqfreeCount X :=
      Finset.sum_nonneg fun q _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hmono : (1 : ℝ) / (B X + 1) ≤ 1 / (j + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hBj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact lt_of_lt_of_le hsum (le_trans hmono (le_of_lt hj))

end
