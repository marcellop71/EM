import EM.Population.AvoidanceTube

/-!
# Spectral Conspiracy and Guardian Exhaustion

Under the negation of Weak Mullin (i.e., the reciprocal sum over missing primes
diverges), we assemble multi-prime structural consequences:

1. **Missing primes are infinite**: ¬WM implies infinitely many primes are missing
2. **Joint excess energy diverges**: the sum of log((q-1)/(q-2)) over missing
   primes can be made arbitrarily large
3. **Guardian demand exceeds capacity**: for any finite "guardian pool" G of
   appeared primes, the demand from missing primes (measured by sum 1/(q-1))
   eventually exceeds |G|
4. **Many rogue characters**: under ¬WM, arbitrarily many missing primes exist,
   each witnessing a nontrivial character with linear growth

These results formalize the "spectral conspiracy" obstruction: if many primes
are missing, the walk simultaneously carries linearly growing biases at each
missing prime, creating incompatible constraints that accumulate without bound.

## Main Results

### S100. Missing Primes Infinite under ¬WM
* `not_wm_implies_missing_infinite` : ¬WM implies MissingPrimes is Set.Infinite

### S101. Joint Excess Energy Divergence
* `joint_excess_energy_diverges` : ¬WM implies sum of log((q-1)/(q-2)) unbounded

### S102. Guardian Exhaustion
* `guardian_demand_exceeds_capacity` : ¬WM implies reciprocal demand from
  missing primes exceeds any finite guardian capacity

### S103. Many Rogue Characters
* `many_rogue_characters` : ¬WM implies arbitrarily many missing primes

### S104. Landscape
* `spectral_conspiracy_landscape` : conjunction of all results
-/

open Mullin Euclid MullinGroup RotorRouter
open Finset Real

/-! ## S100. Missing Primes Infinite under ¬WM -/

section MissingInfinite

open Classical

/-- Under ¬WM, MissingPrimes is infinite. Contrapositive of `missing_finite_implies_wm`:
    if MissingPrimes were finite, WeakMullin would hold. -/
theorem not_wm_implies_missing_infinite (hnwm : ¬ WeakMullin) :
    Set.Infinite MissingPrimes := by
  intro hfin
  exact hnwm (missing_finite_implies_wm hfin)

/-- An infinite set of naturals has arbitrarily large finite subsets
    with all elements satisfying a given predicate. -/
private theorem infinite_nat_set_card_unbounded {S : Set ℕ} (hinf : Set.Infinite S) (k : ℕ) :
    ∃ F : Finset ℕ, k ≤ F.card ∧ (↑F : Set ℕ) ⊆ S := by
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq k
  exact ⟨T, le_of_eq hTcard.symm, hTsub⟩

/-- Under ¬WM, there exist arbitrarily many missing primes. -/
theorem many_missing_primes (hnwm : ¬ WeakMullin) (k : ℕ) :
    ∃ F : Finset ℕ, k ≤ F.card ∧ (∀ q ∈ F, q ∈ MissingPrimes) := by
  obtain ⟨F, hcard, hsub⟩ := infinite_nat_set_card_unbounded
    (not_wm_implies_missing_infinite hnwm) k
  exact ⟨F, hcard, fun q hq => hsub (Finset.mem_coe.mpr hq)⟩

end MissingInfinite

/-! ## S101. Joint Excess Energy Divergence -/

section JointExcessEnergy

open Classical

/-- Missing primes in any finite subset of MissingPrimes satisfy q >= 3.
    (They are primes different from 2 = seq 0.) -/
private theorem missing_primes_ge_three {F : Finset ℕ}
    (hF : (↑F : Set ℕ) ⊆ MissingPrimes) :
    ∀ q ∈ F, 3 ≤ q := by
  intro q hq
  have ⟨hqp, hqne⟩ := hF (Finset.mem_coe.mpr hq)
  have hge2 := hqp.two_le
  have h2 : q ≠ 2 := fun heq => hqne 0 (by rw [seq_zero]; exact heq.symm)
  omega

/-- Each factor (q-1)/(q-2) is > 1 for q >= 3. -/
private theorem inv_tube_factor_gt_one {q : ℕ} (hq : 3 ≤ q) :
    1 < ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
  have hq2 : (0 : ℝ) < (q : ℝ) - 2 := by
    linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq]
  rw [one_lt_div hq2]; linarith

/-- Each factor (q-1)/(q-2) is > 0 for q >= 3. -/
private theorem inv_tube_factor_pos {q : ℕ} (hq : 3 ≤ q) :
    0 < ((q : ℝ) - 1) / ((q : ℝ) - 2) :=
  lt_trans zero_lt_one (inv_tube_factor_gt_one hq)

/-- The inverted tube product is always positive for F subset of primes >= 3. -/
private theorem inv_tube_prod_pos {F : Finset ℕ} (hF : ∀ q ∈ F, 3 ≤ q) :
    0 < ∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2) :=
  Finset.prod_pos (fun q hq => inv_tube_factor_pos (hF q hq))

/-- Joint excess energy divergence: the sum of log((q-1)/(q-2)) over missing
    primes can be made arbitrarily large under ¬WM.

    Proof: `not_wm_product_diverges` gives that the product
    prod_{q in F} (q-1)/(q-2) can exceed exp(C) for any C.
    Taking log of both sides gives the sum exceeds C. -/
theorem joint_excess_energy_diverges (hnwm : ¬ WeakMullin) :
    ∀ C : ℝ, ∃ F : Finset ℕ, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      C < ∑ q ∈ F, Real.log (((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
  intro C
  -- Get F with product >= exp(C) + 1
  obtain ⟨F, hF_sub, hF_prod⟩ := not_wm_product_diverges hnwm (Real.exp C + 1)
  have hF_ge3 := missing_primes_ge_three hF_sub
  refine ⟨F, fun q hq => hF_sub (Finset.mem_coe.mpr hq), ?_⟩
  -- The product is > exp(C)
  have hprod_gt : Real.exp C < ∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
    linarith
  -- Take log: C < log(product) = sum of logs
  have hprod_pos := inv_tube_prod_pos hF_ge3
  rw [← Real.log_exp C]
  calc Real.log (Real.exp C)
      < Real.log (∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2)) :=
        Real.log_lt_log (Real.exp_pos C) hprod_gt
    _ = ∑ q ∈ F, Real.log (((q : ℝ) - 1) / ((q : ℝ) - 2)) :=
        Real.log_prod (fun q hq => ne_of_gt (inv_tube_factor_pos (hF_ge3 q hq)))

end JointExcessEnergy

/-! ## S102. Guardian Exhaustion

If the walk is "guarded" by a finite set G of appeared primes, those guardians
have limited capacity. The demand from missing primes grows without bound. -/

section GuardianExhaustion

open Classical

/-- Each 1/(q-1) is bounded below by 1/(2q) for q >= 2. -/
private theorem recip_q_sub_one_ge {q : ℕ} (hq : 3 ≤ q) :
    1 / (2 * (q : ℝ)) ≤ 1 / ((q : ℝ) - 1) := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq]
  have h2q : (0 : ℝ) < 2 * (q : ℝ) := by
    linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq]
  rw [div_le_div_iff₀ h2q hq1]; nlinarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq]

/-- Under ¬WM, the reciprocal sum 1/(q-1) over missing primes exceeds any bound.
    This follows from 1/(q-1) >= 1/(2q) and the divergence of sum 1/q over
    missing primes (= ¬WM). -/
theorem guardian_demand_exceeds_capacity (hnwm : ¬ WeakMullin) :
    ∀ (B : ℝ), ∃ F : Finset ℕ,
      (∀ q ∈ F, q ∈ MissingPrimes) ∧
      B < ∑ q ∈ F, (1 : ℝ) / ((q : ℝ) - 1) := by
  intro B
  -- Use not_wm_product_diverges to get a large product
  obtain ⟨F, hF_sub, hF_prod⟩ := not_wm_product_diverges hnwm (Real.exp (2 * max B 0) + 1)
  have hF_ge3 := missing_primes_ge_three hF_sub
  refine ⟨F, fun q hq => hF_sub (Finset.mem_coe.mpr hq), ?_⟩
  -- From product_divergence proof structure: sum 1/(q-1) >= (sum 1/q) / 2
  -- and product >= exp(sum/2), so sum >= 2*log(product) >= 2*max B 0 >= B
  -- More directly: use the log route
  have hprod_pos := inv_tube_prod_pos hF_ge3
  have hprod_gt : Real.exp (2 * max B 0) < ∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
    linarith
  -- log(product) > 2 * max B 0
  have hlog_gt : 2 * max B 0 < Real.log (∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
    rw [← Real.log_exp (2 * max B 0)]
    exact Real.log_lt_log (Real.exp_pos _) hprod_gt
  -- log(product) = sum of log((q-1)/(q-2))
  have hlog_eq : Real.log (∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2)) =
      ∑ q ∈ F, Real.log (((q : ℝ) - 1) / ((q : ℝ) - 2)) :=
    Real.log_prod (fun q hq => ne_of_gt (inv_tube_factor_pos (hF_ge3 q hq)))
  -- Each log((q-1)/(q-2)) = log(1 + 1/(q-2)) <= 1/(q-2) <= 1/(q-1)
  -- More precisely, for x > 0: log(1+x) <= x, so log((q-1)/(q-2)) <= 1/(q-2)
  -- We need: sum log((q-1)/(q-2)) <= sum 1/(q-1)? No -- we want the sum to be LARGE.
  -- Actually we need the reverse direction. We have sum log (...) > 2*max(B,0).
  -- And we need sum 1/(q-1) > B.
  -- Note: log((q-1)/(q-2)) = log(1 + 1/(q-2)) <= 1/(q-2) for q >= 3.
  -- And 1/(q-2) <= 2/(q-1) for q >= 4 (since q-1 <= 2(q-2) iff q >= 3).
  -- So sum log(...) <= sum 1/(q-2) <= sum 2/(q-1) = 2 * sum 1/(q-1).
  -- Therefore sum 1/(q-1) >= (sum log(...))/2 > max(B,0) >= B.
  suffices h : ∑ q ∈ F, Real.log (((q : ℝ) - 1) / ((q : ℝ) - 2)) ≤
      2 * ∑ q ∈ F, 1 / ((q : ℝ) - 1) by
    have h2 : 2 * max B 0 < 2 * ∑ q ∈ F, 1 / ((q : ℝ) - 1) := by
      linarith [hlog_eq ▸ hlog_gt]
    linarith [le_max_left B 0]
  -- Prove: log((q-1)/(q-2)) <= 2/(q-1) for q >= 3
  -- Rewrite 2 * sum as sum of 2 * f
  rw [show 2 * ∑ q ∈ F, 1 / ((q : ℝ) - 1) = ∑ q ∈ F, 2 / ((q : ℝ) - 1)
    from by rw [Finset.mul_sum]; congr 1; ext q; ring]
  apply Finset.sum_le_sum
  intro q hq
  have hq3 := hF_ge3 q hq
  have hq2_pos : (0 : ℝ) < (q : ℝ) - 2 := by
    linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq3]
  have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  -- log((q-1)/(q-2)) = log(1 + 1/(q-2))
  have hrewrite : ((q : ℝ) - 1) / ((q : ℝ) - 2) = 1 + 1 / ((q : ℝ) - 2) := by
    field_simp; ring
  rw [hrewrite]
  -- log(1 + 1/(q-2)) <= 1/(q-2) since log(1+x) <= x for x >= 0
  have h_log_le : Real.log (1 + 1 / ((q : ℝ) - 2)) ≤ 1 / ((q : ℝ) - 2) := by
    have hx : 0 ≤ 1 / ((q : ℝ) - 2) := div_nonneg zero_le_one (le_of_lt hq2_pos)
    linarith [Real.add_one_le_exp (1 / ((q : ℝ) - 2)),
              Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 1 / ((q : ℝ) - 2))]
  -- 1/(q-2) <= 2/(q-1) for q >= 3
  have h_recip_le : 1 / ((q : ℝ) - 2) ≤ 2 / ((q : ℝ) - 1) := by
    rw [div_le_div_iff₀ hq2_pos hq1_pos]
    nlinarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq3]
  linarith

end GuardianExhaustion

/-! ## S103. Many Rogue Characters

Under ¬WM, we can find arbitrarily many missing primes. Combined with
the per-prime rogue character existence (from AvoidanceTube.lean), this
shows the walk simultaneously carries unboundedly many independent
linear biases. -/

section ManyRogueCharacters

open Classical

/-- The number of independent linear biases (rogue characters) grows
    without bound: for any k, under ¬WM there exist k missing primes,
    each of which is a prime >= 3 with a forbidden multiplier class. -/
theorem many_rogue_characters (hnwm : ¬ WeakMullin) (k : ℕ) :
    ∃ F : Finset ℕ, k ≤ F.card ∧
      (∀ q ∈ F, q ∈ MissingPrimes) ∧
      (∀ q ∈ F, 3 ≤ q) := by
  obtain ⟨F, hcard, hmem⟩ := many_missing_primes hnwm k
  exact ⟨F, hcard, hmem, fun q hq => by
    have ⟨hqp, hqne⟩ := hmem q hq
    have hge2 := hqp.two_le
    have h2 : q ≠ 2 := fun heq => hqne 0 (by rw [seq_zero]; exact heq.symm)
    omega⟩

/-- Under ¬WM, for any N, there exist at least N missing primes q >= 3,
    and each contributes an excess energy ratio (q-1)/(q-2) > 1.
    The product of these ratios exceeds any given bound. -/
theorem spectral_conspiracy_product (hnwm : ¬ WeakMullin) :
    ∀ C : ℝ, ∃ F : Finset ℕ,
      (∀ q ∈ F, q ∈ MissingPrimes) ∧
      C ≤ ∏ q ∈ F, (((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
  exact not_wm_product_diverges hnwm

/-- The tube ratio (proportion of "allowed" multiplier classes) can be made
    arbitrarily small. Combined with spectral_conspiracy_product, this shows
    the walk is squeezed into an ever-narrowing tube. -/
theorem tube_squeeze (hnwm : ¬ WeakMullin) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ,
      (∀ q ∈ F, q ∈ MissingPrimes) ∧ tubeRatio F < ε := by
  intro ε hε
  obtain ⟨F, hF_sub, hF_tube⟩ := tube_collapse hnwm ε hε
  exact ⟨F, fun q hq => hF_sub (Finset.mem_coe.mpr hq), hF_tube⟩

end ManyRogueCharacters

/-! ## S104. Landscape -/

section Landscape

open Classical

/-- Spectral conspiracy landscape: under ¬WM, the walk faces
    unboundedly many simultaneous structural obstructions.

    (1) MissingPrimes is infinite
    (2) Joint excess energy sum diverges
    (3) Guardian demand exceeds any finite capacity
    (4) Arbitrarily many missing primes exist (each >= 3)
    (5) Tube ratio can be made arbitrarily small
    (6) Inverted tube product can be made arbitrarily large -/
theorem spectral_conspiracy_landscape (hnwm : ¬ WeakMullin) :
    -- (1) Missing primes are infinite
    Set.Infinite MissingPrimes ∧
    -- (2) Joint excess energy diverges
    (∀ C : ℝ, ∃ F : Finset ℕ, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      C < ∑ q ∈ F, Real.log (((q : ℝ) - 1) / ((q : ℝ) - 2))) ∧
    -- (3) Guardian demand exceeds capacity
    (∀ B : ℝ, ∃ F : Finset ℕ, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      B < ∑ q ∈ F, (1 : ℝ) / ((q : ℝ) - 1)) ∧
    -- (4) Arbitrarily many missing primes, each >= 3
    (∀ k : ℕ, ∃ F : Finset ℕ, k ≤ F.card ∧
      (∀ q ∈ F, q ∈ MissingPrimes) ∧ (∀ q ∈ F, 3 ≤ q)) ∧
    -- (5) Tube ratio can be made arbitrarily small
    (∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ,
      (∀ q ∈ F, q ∈ MissingPrimes) ∧ tubeRatio F < ε) ∧
    -- (6) Inverted tube product can be made arbitrarily large
    (∀ C : ℝ, ∃ F : Finset ℕ, (∀ q ∈ F, q ∈ MissingPrimes) ∧
      C ≤ ∏ q ∈ F, (((q : ℝ) - 1) / ((q : ℝ) - 2))) :=
  ⟨not_wm_implies_missing_infinite hnwm,
   joint_excess_energy_diverges hnwm,
   guardian_demand_exceeds_capacity hnwm,
   many_rogue_characters hnwm,
   tube_squeeze hnwm,
   spectral_conspiracy_product hnwm⟩

end Landscape
