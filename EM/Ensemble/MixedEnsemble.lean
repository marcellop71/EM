import EM.Advanced.EpsilonRandomMC
import EM.Ensemble.FirstMoment
import EM.IK.Ch2

/-!
# Mixed Ensemble: Population Sieve Implies Almost All Mixed Hitting

## Overview

This file proves that under a population sieve hypothesis (PSCD),
almost all squarefree starting points m coprime to q have
`(-1 : ZMod q) ∈ reachableEver q m` for the mixed walk. This gives
almost-all MixedHitting -- bypassing Dead End #117 (MultCancelToWalkCancel).

The key idea: if -1 is NOT reachable from m (with m coprime to q), then
-1 ∉ reachableEver(q, m), and since -1 ≠ 0 in ZMod q (for q ≥ 2),
the set R_inf misses a nonzero element. At step 0, all prime factors of
m+1 are confined to the allowed factor set for this proper R_inf.
The Population Sieve Confinement Decay (PSCD) hypothesis says confinement
to any finset missing a nonzero element has density 0.

### Correction Note (Session 247)
The original PSCD required decay for ALL proper R (R ≠ Set.univ). This
is FALSE for R = {all nonzero elements}: confinement to this R just means
q ∤ m+1, which has density (q-1)/q > 0. The corrected PSCD restricts
to R that miss at least one NONZERO element, which suffices for the
pigeonhole because hitting-failure m coprime to q have R_inf missing
the nonzero element -1.

## Main Results

### Definitions
* `PSCD q`                   -- Population Sieve Confinement Decay hypothesis
* `sqfreeTrappedCount q X`   -- count of coprime-to-q squarefree m with -1 not reachable
* `sqfreeConfinedCount q X R` -- count of squarefree m confined to factor set R

### Proved Theorems
* `mixedWalkProd_minFac_eq_genProd` -- bridge: mixed walk = generalized EM walk
* `allowedFactors_mono`             -- monotonicity of allowed factor sets
* `step_zero_confinement`           -- trapped m has factors confined at step 0
* `sqfreeConfinedCount_le`          -- confined count <= sqfreeCount
* `trapped_le_sum_confined`         -- trapped count <= sum over finsets of confined
* `pscd_implies_trapped_density_zero` -- PSCD implies trapped density -> 0
* `pscd_implies_almost_all_mixed_hitting` -- PSCD implies almost all coprime-to-q hitting
* `mixed_ensemble_landscape`        -- summary conjunction

### Open Hypotheses
* `PSCD q` -- Population Sieve Confinement Decay

## PSCD Reduction Chain (Session 249)

The chain PEAP -> PSCD now has only 1 open hypothesis (SieveUpperBound):

- PEAPImpliesForbiddenClassDivergent: PROVED (peap_implies_fcd_proved)
- SieveUpperBound: OPEN (fundamental lemma of sieve theory)
- SieveProductVanishing: PROVED (sieve_product_vanishing_proved)

Composition: PEAP + SieveUpperBound ==> PSCD ==> a.a. mixed hitting.
This is the strongest density result in the formalization.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Bridge Between Mixed Walk and Generalized EM -/

section Bridge

/-- The all-minFac mixed walk from starting point m equals the generalized
    EM accumulator genProd m k. Both start at m and multiply by minFac(P+1)
    at each step. -/
theorem mixedWalkProd_minFac_eq_genProd (m : ℕ) (k : ℕ) :
    mixedWalkProd m minFacMixed k = genProd m k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mixedWalkProd, minFacMixed, genProd_succ, genSeq]
    rw [ih]

/-- The generalized EM sequence's prime genSeq(m, k) divides
    the mixed walk accumulator + 1. -/
theorem genSeq_dvd_mixedWalkProd_succ (m : ℕ) (k : ℕ) :
    genSeq m k ∣ mixedWalkProd m minFacMixed k + 1 := by
  rw [mixedWalkProd_minFac_eq_genProd]
  exact Nat.minFac_dvd _

/-- All prime factors of genProd(m, k) + 1 are confined to the allowed
    factor set of the mixed walk's reachable set. This is a direct
    consequence of `all_factors_confined` with sigma = minFacMixed. -/
theorem genProd_factors_confined (q m : ℕ) (k : ℕ) :
    AllFactorsInSet q (genProd m k + 1)
      (allowedFactors q ((genProd m k : ℕ) : ZMod q) (reachableEver q m)) := by
  have h := all_factors_confined (q := q) (acc := m) (n := k)
    (σ := minFacMixed) (minFacMixed_valid m)
  rwa [mixedWalkProd_minFac_eq_genProd] at h

end Bridge

/-! ## Part 2: Monotonicity of Allowed Factors -/

section Monotonicity

/-- The allowed factor set is monotone in the target set R:
    if R is a subset of S, then allowedFactors(c, R) is a subset of
    allowedFactors(c, S). -/
theorem allowedFactors_mono (q : ℕ) (c : ZMod q) {R S : Set (ZMod q)}
    (h : R ⊆ S) : allowedFactors q c R ⊆ allowedFactors q c S :=
  fun _ hm => h hm

end Monotonicity

/-! ## Part 3: Counting Definitions -/

section Counting

/-- Count of squarefree m in [1,X] where all prime factors of m+1 have
    residues in the set `allowedFactors q (m : ZMod q) R` for a given R
    (passed as a Finset, coerced to Set).
    This captures the "confined" population for a fixed target set R. -/
def sqfreeConfinedCount (q X : ℕ) (R : Finset (ZMod q)) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
    AllFactorsInSet q (m + 1) (allowedFactors q (m : ZMod q) (↑R : Set (ZMod q))))).card

/-- Count of squarefree m in [1,X] coprime to q where -1 is NOT reachable.
    These are the "hitting failure" starting points among coprime-to-q
    squarefree integers. -/
def sqfreeTrappedCount (q X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
    Nat.Coprime m q ∧ (-1 : ZMod q) ∉ reachableEver q m)).card

/-- The confined count is at most the total squarefree count. -/
theorem sqfreeConfinedCount_le (q X : ℕ) (R : Finset (ZMod q)) :
    sqfreeConfinedCount q X R ≤ sqfreeCount X := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1⟩

/-- The trapped count is at most the total squarefree count. -/
theorem sqfreeTrappedCount_le (q X : ℕ) :
    sqfreeTrappedCount q X ≤ sqfreeCount X := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1⟩

end Counting

/-! ## Part 4: Step-0 Confinement for Trapped Starting Points -/

section StepZeroConfinement

/-- If the reachable set R_inf(q, m) is contained in some set R,
    then at step 0 (walk position = m), all factors of m+1 are in
    the allowed set at position m mod q with respect to R. -/
theorem step_zero_confinement (q m : ℕ) (R : Set (ZMod q))
    (hR : reachableEver q m ⊆ R) :
    AllFactorsInSet q (m + 1) (allowedFactors q (m : ZMod q) R) := by
  have h0 := genProd_factors_confined q m 0
  simp only [genProd] at h0
  exact allFactorsInSet_mono (allowedFactors_mono q _ hR) h0

/-- Any starting point m satisfies the factor confinement condition
    with R = reachableEver itself (unconditionally). -/
theorem unconditional_confinement (q m : ℕ) :
    AllFactorsInSet q (m + 1)
      (allowedFactors q (m : ZMod q) (reachableEver q m)) :=
  step_zero_confinement q m _ Set.Subset.rfl

end StepZeroConfinement

/-! ## Part 4b: Zero Not Reachable for Trapped Starting Points -/

section ZeroNotReachable

/-- For valid mixed walks, the factor at each step divides acc+1 and hence
    the factor is prime when acc+1 ≥ 2 (i.e., acc ≥ 1). -/
private theorem mixedWalkFactor_prime_of_ge_one
    {m : ℕ} (_hm : 1 ≤ m) (σ : MixedSelection)
    (hv : ValidMixedSelection m σ) (n : ℕ)
    (hge : 1 ≤ mixedWalkProd m σ n) :
    (mixedWalkFactor m σ n).Prime := by
  simp only [mixedWalkFactor]
  have hspec := hv n
  cases hσ : σ n with
  | none =>
    exact Nat.minFac_prime (by omega)
  | some p =>
    simp only [hσ] at hspec
    exact hspec.1

/-- For any valid walk from a coprime-to-q starting point m, if -1 is never
    reached by ANY walk, then the walk position at step n is a unit in ZMod q
    (hence never 0). -/
theorem walk_position_isUnit_of_coprime_trapped
    {q m : ℕ} (hq : q.Prime) (hcop : Nat.Coprime m q)
    (hm1 : 1 ≤ m) (hneg : (-1 : ZMod q) ∉ reachableEver q m)
    (σ : MixedSelection) (hv : ValidMixedSelection m σ) (n : ℕ) :
    IsUnit (mixedWalkProd m σ n : ZMod q) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- Also show the accumulator is ≥ 1 at each step
  suffices h : IsUnit (mixedWalkProd m σ n : ZMod q) ∧ 1 ≤ mixedWalkProd m σ n from h.1
  induction n with
  | zero =>
    simp only [mixedWalkProd]
    exact ⟨(ZMod.isUnit_iff_coprime m q).mpr hcop, hm1⟩
  | succ n ih =>
    obtain ⟨ih_unit, ih_ge⟩ := ih
    have hfac_dvd := mixedWalkFactor_dvd m σ hv n
    have hfac_prime := mixedWalkFactor_prime_of_ge_one hm1 σ hv n ih_ge
    -- The factor is not q
    have hfac_ne_q : mixedWalkFactor m σ n ≠ q := by
      intro heq
      rw [heq] at hfac_dvd
      have hzmod : ((mixedWalkProd m σ n + 1 : ℕ) : ZMod q) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact hfac_dvd
      have hmod : (mixedWalkProd m σ n : ZMod q) = -1 := by
        have h1 : ((mixedWalkProd m σ n : ℕ) : ZMod q) + (1 : ZMod q) = 0 := by
          push_cast at hzmod; exact hzmod
        exact eq_neg_of_add_eq_zero_left h1
      exact hneg (Set.mem_iUnion.mpr ⟨n, σ, hv, hmod⟩)
    have hfac_unit : IsUnit (mixedWalkFactor m σ n : ZMod q) := by
      rw [ZMod.isUnit_prime_iff_not_dvd hfac_prime]
      intro hdvd
      exact hfac_ne_q ((hq.eq_one_or_self_of_dvd _ hdvd).resolve_left (by have := hfac_prime.two_le; omega))
    constructor
    · rw [mixedWalkProd_succ]; push_cast; exact ih_unit.mul hfac_unit
    · rw [mixedWalkProd_succ]
      calc 1 ≤ 1 * 2 := by omega
        _ ≤ mixedWalkProd m σ n * mixedWalkFactor m σ n :=
          Nat.mul_le_mul ih_ge hfac_prime.two_le

/-- For m coprime to q with -1 not reachable, 0 is also not reachable.

    This follows from `walk_position_isUnit_of_coprime_trapped`: every
    walk position is a unit, hence nonzero. -/
theorem zero_not_reachable_of_coprime_trapped
    {q m : ℕ} (hq : q.Prime) (hcop : Nat.Coprime m q)
    (hm1 : 1 ≤ m) (hneg : (-1 : ZMod q) ∉ reachableEver q m) :
    (0 : ZMod q) ∉ reachableEver q m := by
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  intro h0
  rw [reachableEver, Set.mem_iUnion] at h0
  obtain ⟨n, hn⟩ := h0
  obtain ⟨σ, hv, hpos⟩ := hn
  have hunit := walk_position_isUnit_of_coprime_trapped hq hcop hm1 hneg σ hv n
  rw [hpos] at hunit
  exact not_isUnit_zero hunit

end ZeroNotReachable

/-! ## Part 5: Population Sieve Confinement Decay -/

section PSCD

/-- **Population Sieve Confinement Decay**: Among squarefree integers,
    the fraction where ALL prime factors of m+1 have residues confined
    to `allowedFactors(m mod q, R)` for a finset R that misses at least
    one nonzero element of ZMod q AND does not contain 0 tends to 0.

    The condition `∃ a, a ≠ 0 ∧ a ∉ R` ensures R is a proper subset
    of the nonzero elements, giving the sieve a forbidden residue class.
    The condition `0 ∉ R` ensures that factor q is always forbidden,
    so confined m must have gcd(m+1, q) = 1. Without this condition,
    R = {all nonzero} would have confinement density (q-1)/q > 0.

    This is a consequence of the Landau-Selberg-Delange method:
    integers whose prime factors all avoid a residue class
    have density 0 (asymptotic X/(log X)^{1-alpha} where
    alpha < 1 for proper F).

    The `0 ∉ R` condition is always satisfied in the pigeonhole
    application: for trapped m (coprime to q, -1 not reachable),
    the walk stays in units of ZMod q, so 0 ∉ reachableEver q m. -/
def PSCD (q : ℕ) : Prop :=
  ∀ (R : Finset (ZMod q)),
    (∃ a : ZMod q, a ≠ 0 ∧ a ∉ (↑R : Set (ZMod q))) →
    (0 : ZMod q) ∉ (↑R : Set (ZMod q)) →
    Filter.Tendsto
      (fun X => (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0)

end PSCD

/-! ## Part 6: Pigeonhole over Proper Subsets -/

section Pigeonhole

variable {q : ℕ} [NeZero q]

/-- The set of finsets of ZMod q that miss at least one nonzero element
    and do not contain 0.
    Since ZMod q is Fintype, the type `Finset (ZMod q)` is also Fintype. -/
private def properFinsets (q : ℕ) [NeZero q] : Finset (Finset (ZMod q)) :=
  Finset.univ.filter (fun S =>
    (∃ a : ZMod q, a ≠ 0 ∧ a ∉ (↑S : Set (ZMod q))) ∧
    (0 : ZMod q) ∉ (↑S : Set (ZMod q)))

/-- A set that misses a nonzero element and does not contain 0 has its
    toFinset in the proper finsets collection. -/
private theorem proper_set_mem_properFinsets
    {R : Set (ZMod q)} {a : ZMod q} (ha : a ≠ 0) (haR : a ∉ R)
    (h0 : (0 : ZMod q) ∉ R) :
    R.toFinset ∈ properFinsets q := by
  simp only [properFinsets, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨a, ha, by rwa [Set.coe_toFinset]⟩, by rwa [Set.coe_toFinset]⟩

omit [NeZero q] in
/-- In ZMod q with q ≥ 2, (-1 : ZMod q) ≠ 0. -/
private theorem neg_one_ne_zero_of_ge_two (hq2 : 2 ≤ q) :
    (-1 : ZMod q) ≠ (0 : ZMod q) := by
  haveI : Fact (1 < q) := ⟨by omega⟩
  exact neg_ne_zero.mpr one_ne_zero

/-- Each trapped m (coprime to q, hitting failure) satisfies the confinement
    condition for some R in properFinsets. The witness R is
    (reachableEver q m).toFinset, which misses the nonzero element -1
    and does not contain 0 (since the walk stays in units). -/
private theorem trapped_mem_some_confined (hq : q.Prime) (X : ℕ)
    (m : ℕ) (hm : m ∈ (Finset.Icc 1 X).filter
      (fun m => Squarefree m ∧ Nat.Coprime m q ∧
        (-1 : ZMod q) ∉ reachableEver q m)) :
    ∃ R ∈ properFinsets q,
      m ∈ (Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        AllFactorsInSet q (m + 1)
          (allowedFactors q (m : ZMod q) (↑R : Set (ZMod q)))) := by
  obtain ⟨hmIcc, hsf, hcop, hnotreach⟩ := Finset.mem_filter.mp hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
  have hq2 : 2 ≤ q := hq.two_le
  -- 0 ∉ reachableEver q m since the walk stays in units
  have h0 : (0 : ZMod q) ∉ reachableEver q m :=
    zero_not_reachable_of_coprime_trapped hq hcop (by omega) hnotreach
  refine ⟨(reachableEver q m).toFinset,
    proper_set_mem_properFinsets (neg_one_ne_zero_of_ge_two hq2)
      hnotreach h0, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hmIcc, hsf, ?_⟩
  rw [Set.coe_toFinset]
  exact unconditional_confinement q m

/-- The trapped set is contained in the biUnion over proper finsets of
    the confined sets. -/
theorem trapped_subset_biUnion_confined (hq : q.Prime) (X : ℕ) :
    (Finset.Icc 1 X).filter
      (fun m => Squarefree m ∧ Nat.Coprime m q ∧
        (-1 : ZMod q) ∉ reachableEver q m)
    ⊆ (properFinsets q).biUnion (fun R =>
      (Finset.Icc 1 X).filter (fun m => Squarefree m ∧
        AllFactorsInSet q (m + 1)
          (allowedFactors q (m : ZMod q) (↑R : Set (ZMod q))))) := by
  intro m hm
  obtain ⟨R, hR, hmR⟩ := trapped_mem_some_confined hq X m hm
  exact Finset.mem_biUnion.mpr ⟨R, hR, hmR⟩

/-- **Trapped count bound**: The number of hitting-failure coprime-to-q
    squarefree m in [1,X] is at most the sum over all proper finsets R
    of the confined count for R. -/
theorem trapped_le_sum_confined (hq : q.Prime) (X : ℕ) :
    sqfreeTrappedCount q X ≤
      ∑ R ∈ properFinsets q, sqfreeConfinedCount q X R := by
  calc sqfreeTrappedCount q X
      = ((Finset.Icc 1 X).filter
          (fun m => Squarefree m ∧ Nat.Coprime m q ∧
            (-1 : ZMod q) ∉ reachableEver q m)).card := rfl
    _ ≤ ((properFinsets q).biUnion (fun R =>
          (Finset.Icc 1 X).filter (fun m => Squarefree m ∧
            AllFactorsInSet q (m + 1)
              (allowedFactors q (m : ZMod q) (↑R : Set (ZMod q)))))).card :=
        Finset.card_le_card (trapped_subset_biUnion_confined hq X)
    _ ≤ ∑ R ∈ properFinsets q,
          ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
            AllFactorsInSet q (m + 1)
              (allowedFactors q (m : ZMod q) (↑R : Set (ZMod q))))).card :=
        Finset.card_biUnion_le
    _ = ∑ R ∈ properFinsets q, sqfreeConfinedCount q X R := rfl

end Pigeonhole

/-! ## Part 7: PSCD Implies Trapped Density Tends to 0 -/

section MainTheorem

/-- The trapped density is bounded above by the sum of confined densities. -/
theorem trapped_density_le_sum (q X : ℕ) [NeZero q] (hq : q.Prime)
    (hX : 0 < sqfreeCount X) :
    (sqfreeTrappedCount q X : ℝ) / sqfreeCount X ≤
      ∑ R ∈ properFinsets q,
        (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X := by
  have hpos : (0 : ℝ) < sqfreeCount X := Nat.cast_pos.mpr hX
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
  exact_mod_cast trapped_le_sum_confined hq X

/-- **PSCD implies trapped density tends to 0**: Under PSCD, the fraction
    of coprime-to-q squarefree m with hitting failure tends to 0.

    Proof: The trapped density is at most the sum of confined densities
    (pigeonhole). PSCD says each confined density tends to 0. The sum is
    over finitely many terms, so it tends to 0 by `tendsto_finset_sum`.
    Squeeze gives the conclusion. -/
theorem pscd_implies_trapped_density_zero (q : ℕ) [NeZero q] (hq : q.Prime)
    (hPSCD : PSCD q) :
    Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  -- The sum of confined densities tends to 0
  have hsum : Filter.Tendsto
      (fun X => ∑ R ∈ properFinsets q,
        (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) = ∑ _ ∈ properFinsets q, (0 : ℝ) := by simp
    rw [h0]
    apply Filter.Tendsto.congr (fun _ => rfl)
    apply tendsto_finset_sum
    intro R hR
    obtain ⟨hR_nonzero, hR_zero⟩ := (Finset.mem_filter.mp hR).2
    exact hPSCD R hR_nonzero hR_zero
  -- Trapped density is nonneg and at most the sum: use squeeze
  apply squeeze_zero
  · -- Trapped density >= 0
    intro X
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · -- Trapped density <= sum of confined densities
    intro X
    by_cases hsc : sqfreeCount X = 0
    · have htr0 : sqfreeTrappedCount q X = 0 := by
        have := sqfreeTrappedCount_le q X; omega
      show (sqfreeTrappedCount q X : ℝ) / sqfreeCount X ≤
        ∑ R ∈ properFinsets q, (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X
      rw [htr0, hsc, Nat.cast_zero, zero_div]
      exact Finset.sum_nonneg fun R _ =>
        div_nonneg (Nat.cast_nonneg _) (le_refl 0)
    · exact trapped_density_le_sum q X hq (Nat.pos_of_ne_zero hsc)
  · exact hsum

end MainTheorem

/-! ## Part 8: Corollaries -/

section Corollaries

/-- **PSCD implies almost all coprime-to-q squarefree m have mixed hitting**:
    Under PSCD, the density of hitting-failure m (coprime-to-q, squarefree,
    -1 not reachable) among all squarefree m tends to 0.

    This means: among squarefree m coprime to q, almost all have
    (-1 : ZMod q) ∈ reachableEver q m, giving MixedHitting at m. -/
theorem pscd_implies_almost_all_mixed_hitting (q : ℕ) [NeZero q]
    (hq : q.Prime)
    (hPSCD : PSCD q) :
    Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) :=
  pscd_implies_trapped_density_zero q hq hPSCD

end Corollaries

/-! ## Part 9: Landscape Summary -/

section Landscape

/-- **Mixed Ensemble Landscape**: Summary of the main results.

    1. mixedWalkProd_minFac_eq_genProd -- all-minFac walk = genProd (PROVED)
    2. genProd_factors_confined -- factors confined for all steps (PROVED)
    3. unconditional_confinement -- any m confined at step 0 (PROVED)
    4. trapped_le_sum_confined -- pigeonhole bound (PROVED)
    5. pscd_implies_trapped_density_zero -- PSCD gives trapped density -> 0 (PROVED)
    6. zero_not_reachable_of_coprime_trapped -- 0 ∉ R_∞ for trapped m (PROVED)
    7. PSCD q is the sole open hypothesis -/
theorem mixed_ensemble_landscape (q : ℕ) [NeZero q] (hq : q.Prime)
    (hPSCD : PSCD q) :
    -- 1. Bridge: mixed walk = generalized EM walk
    (∀ m k, mixedWalkProd m minFacMixed k = genProd m k)
    ∧
    -- 2. Factor confinement for all steps
    (∀ m k, AllFactorsInSet q (genProd m k + 1)
      (allowedFactors q ((genProd m k : ℕ) : ZMod q) (reachableEver q m)))
    ∧
    -- 3. Unconditional confinement at step 0
    (∀ m, AllFactorsInSet q (m + 1)
      (allowedFactors q (m : ZMod q) (reachableEver q m)))
    ∧
    -- 4. Pigeonhole bound
    (∀ X, sqfreeTrappedCount q X ≤
      ∑ R ∈ properFinsets q, sqfreeConfinedCount q X R)
    ∧
    -- 5. Trapped density tends to 0
    Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) :=
  ⟨mixedWalkProd_minFac_eq_genProd,
   genProd_factors_confined q,
   unconditional_confinement q,
   fun X => trapped_le_sum_confined hq X,
   pscd_implies_trapped_density_zero q hq hPSCD⟩

end Landscape

/-! ## Part 10: Forbidden Class Reciprocal Divergence -/

section ForbiddenClassDivergence

/-- The reciprocal sum of primes in a given residue class a mod q diverges.
    Formally: the indicator-weighted series ∑_n 1_{n prime, n ≡ a mod q} / n
    is not summable. -/
def PrimeReciprocalClassDivergent (q : ℕ) (a : ZMod q) : Prop :=
  ¬Summable (fun n => if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0)

/-- Every coprime (unit) class mod q has divergent prime reciprocal sum.
    This is the key analytic input: for each unit a in ZMod q, the
    series ∑_{p prime, p ≡ a} 1/p diverges.

    Follows from IK.PrimesEquidistributedInAP: the partial sums
    ∑_{p ≤ x, p ≡ a} 1/p ≥ log(log x)/phi(q) - C → ∞.
    If the full series were summable, partial sums would be bounded. -/
def ForbiddenClassDivergent (q : ℕ) : Prop :=
  ∀ (a : ZMod q), IsUnit a → PrimeReciprocalClassDivergent q a

/-- The indicator partial sum over `range (N+1)` includes the PEAP sum
    over `Icc 2 N`. This is because `Icc 2 N ⊆ range (N+1)` and the
    indicator is 0 for n = 0, 1 (not prime). -/
private theorem icc_filter_subset_range_filter (q N : ℕ) (a_val : ℕ) :
    ((Finset.Icc 2 N).filter Nat.Prime).filter (fun p => p % q = a_val % q) ⊆
    (Finset.range (N + 1)).filter
      (fun n => Nat.Prime n ∧ (n : ZMod q) = (a_val : ZMod q)) := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, hp.1.2, ?_⟩
  rw [ZMod.natCast_eq_natCast_iff']
  exact hp.2

/-- The indicator partial sum `∑_{n < N+1} f(n)` is at least the PEAP
    partial sum `∑_{p ≤ N, p prime, p ≡ a} 1/p`. -/
private theorem indicator_sum_ge_peap_sum (q N : ℕ) (a : ZMod q) [NeZero q] :
    ∑ n ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
        (fun p => p % q = a.val % q),
      (1 : ℝ) / n
    ≤ ∑ n ∈ Finset.range (N + 1),
        if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0 := by
  -- The LHS sums 1/n over a subset of the filter appearing on the RHS
  -- We first relate the LHS filter to a filter using ZMod equality
  have ha_eq : (a : ZMod q) = (a.val : ZMod q) := (ZMod.natCast_zmod_val a).symm
  -- Rewrite the LHS to sum over a filtered subset of range (N+1)
  have hsub := icc_filter_subset_range_filter q N a.val
  -- The RHS, when restricted to the filter, gives exactly 1/n
  calc ∑ n ∈ ((Finset.Icc 2 N).filter Nat.Prime).filter
          (fun p => p % q = a.val % q), (1 : ℝ) / n
      ≤ ∑ n ∈ (Finset.range (N + 1)).filter
          (fun n => Nat.Prime n ∧ (n : ZMod q) = (a.val : ZMod q)), (1 : ℝ) / n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _; positivity
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0 := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          exact ⟨hn.1, hn.2.1, by rw [ha_eq]; exact hn.2.2⟩
        · intro n _ _; positivity

/-- **IK.PrimesEquidistributedInAP implies ForbiddenClassDivergent**.

    PROVED. PEAP gives |S(x) - log(log x)/phi(q)| ≤ C
    where S(x) = ∑_{p ≤ x, p ≡ a} 1/p. So S(x) ≥ log(log x)/phi(q) - C → ∞.
    The partial sums of the indicator series dominate the PEAP sums.
    Since partial sums → ∞, the series is not summable. -/
theorem peap_implies_fcd_proved :
    IK.PrimesEquidistributedInAP → ∀ (q : ℕ), 2 ≤ q → ForbiddenClassDivergent q := by
  intro hPEAP q hq2 a ha_unit
  haveI : NeZero q := ⟨by omega⟩
  -- Get natural number representative and coprimality
  have ha_cop : Nat.Coprime a.val q := by
    rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  -- Apply PEAP to get the bound
  obtain ⟨C, hC, hbound⟩ := hPEAP q a.val (by omega) ha_cop
  -- Show the indicator function is nonneg
  set f := fun n => if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0 with hf_def
  have hnonneg : ∀ n, 0 ≤ f n := fun n => by simp only [hf_def]; split_ifs <;> positivity
  -- Use not_summable_iff: show partial sums tend to atTop
  show ¬Summable f
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg]
  rw [Filter.tendsto_atTop]
  intro M
  rw [Filter.eventually_atTop]
  -- Need to find N such that partial sum over range N > M
  -- PEAP gives: for x ≥ 3, |∑_{p≤x, p≡a} 1/p - log(log x)/φ(q)| ≤ C
  -- So ∑_{p≤x, p≡a} 1/p ≥ log(log x)/φ(q) - C
  -- Since our indicator sum dominates the PEAP sum, we get
  -- ∑_{n < N+1} f(n) ≥ log(log N)/φ(q) - C
  -- Choose N large enough that log(log N)/φ(q) - C > M
  have htot := Nat.totient_pos.mpr (by omega : 0 < q)
  have htot_pos : (0 : ℝ) < Nat.totient q := by exact_mod_cast htot
  -- log(log N) → ∞ as N → ∞
  have hloglog_unbounded : Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)))
      Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.comp Real.tendsto_log_atTop
    apply Filter.Tendsto.comp Real.tendsto_log_atTop
    exact tendsto_natCast_atTop_atTop
  have hev := (Filter.tendsto_atTop.mp hloglog_unbounded) ((M + C) * Nat.totient q)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  -- Take K = max N₀ 3 (a natural number)
  set K := max N₀ 3 with hK_def
  use K + 1
  intro N hN
  have hK_ge_N₀ : N₀ ≤ K := le_max_left _ _
  have hK_ge_3 : 3 ≤ K := le_max_right _ _
  have hK_ge_3_real : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_ge_3
  -- PEAP bound at x = K (a natural number, so floor(K) = K)
  have hPEAP_bound := hbound (K : ℝ) hK_ge_3_real
  rw [Nat.floor_natCast] at hPEAP_bound
  have hge_peap := (abs_le.mp hPEAP_bound).1
  -- Indicator sum dominates PEAP sum
  have hind := indicator_sum_ge_peap_sum q K a
  -- log(log K) is large enough
  have hloglog_large := hN₀ K hK_ge_N₀
  -- Now chain the inequalities
  have hMC : M + C ≤ Real.log (Real.log (K : ℝ)) / Nat.totient q :=
    le_div_iff₀ htot_pos |>.mpr hloglog_large
  calc M ≤ Real.log (Real.log (K : ℝ)) / Nat.totient q - C := by linarith
    _ ≤ ∑ n ∈ Finset.range (K + 1), f n := by linarith
    _ ≤ ∑ n ∈ Finset.range N, f n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (show K + 1 ≤ N by omega))
        intro n _ _; exact hnonneg n

/-- Backward-compatible alias: PEAPImpliesForbiddenClassDivergent as a Prop
    (now proved). -/
def PEAPImpliesForbiddenClassDivergent : Prop :=
  IK.PrimesEquidistributedInAP → ∀ (q : ℕ), 2 ≤ q → ForbiddenClassDivergent q

end ForbiddenClassDivergence

/-! ## Part 11: Sieve Product Definition and Bounds -/

section SieveProduct

/-- The "sieve product" for a finset R: the product over primes p ≤ X
    with (p : ZMod q) not in R of (1 - 1/p). When the excluded primes
    have divergent reciprocal sum, this product tends to 0. -/
def sieveProduct (q X : ℕ) (R : Finset (ZMod q)) : ℝ :=
  ∏ p ∈ (Finset.range (X + 1)).filter
    (fun p => Nat.Prime p ∧ (p : ZMod q) ∉ (↑R : Set (ZMod q))),
    (1 - (1 : ℝ) / p)

/-- Each factor in the sieve product is nonneg (since p ≥ 2 for primes). -/
private theorem one_sub_inv_nonneg_of_prime {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - (1 : ℝ) / p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith [show (1 : ℝ) / p ≤ 1 / 2 from div_le_div_of_nonneg_left (by linarith) (by linarith) this]

/-- Each factor in the sieve product is at most 1. -/
private theorem one_sub_inv_le_one_of_prime {p : ℕ} (hp : p.Prime) :
    1 - (1 : ℝ) / p ≤ 1 := by
  linarith [show 0 < (1 : ℝ) / p from div_pos one_pos (by exact_mod_cast hp.pos)]

/-- The sieve product is nonneg. -/
theorem sieveProduct_nonneg (q X : ℕ) (R : Finset (ZMod q)) :
    0 ≤ sieveProduct q X R := by
  apply Finset.prod_nonneg
  intro p hp
  exact one_sub_inv_nonneg_of_prime (Finset.mem_filter.mp hp).2.1

/-- The sieve product is at most 1. -/
theorem sieveProduct_le_one (q X : ℕ) (R : Finset (ZMod q)) :
    sieveProduct q X R ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp; exact one_sub_inv_nonneg_of_prime (Finset.mem_filter.mp hp).2.1
  · intro p hp; exact one_sub_inv_le_one_of_prime (Finset.mem_filter.mp hp).2.1

end SieveProduct

/-! ## Part 12: Sieve Upper Bound and Sieve Vanishing (Open Hypotheses) -/

section SieveHypotheses

/-- **Sieve Upper Bound**: The count of squarefree m in [1,X] whose
    prime factors of m+1 are all confined to `allowedFactors(m mod q, R)`
    is bounded by C * sqfreeCount(X) * sieveProduct(q, X, R).

    This is a consequence of the fundamental lemma of sieve theory
    (Legendre/Brun sieve upper bound): the count of integers n ≤ X
    all of whose prime factors avoid a residue class mod q is at most
    C * X * prod_{excluded p ≤ X}(1 - 1/p), with C uniform in X.

    The constant C depends on q but not on X or R. -/
def SieveUpperBound (q : ℕ) : Prop :=
  ∀ (R : Finset (ZMod q)),
    (∃ a : ZMod q, a ≠ 0 ∧ a ∉ (↑R : Set (ZMod q))) →
    (0 : ZMod q) ∉ (↑R : Set (ZMod q)) →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (sqfreeConfinedCount q X R : ℝ) ≤ C * sqfreeCount X * sieveProduct q X R

/-- The sieve product equals a product over range with indicator factors. -/
private theorem sieveProduct_eq_range_prod (q X : ℕ) (R : Finset (ZMod q)) :
    sieveProduct q X R = ∏ n ∈ Finset.range (X + 1),
      if (Nat.Prime n ∧ (n : ZMod q) ∉ (↑R : Set (ZMod q)))
      then (1 - (1 : ℝ) / n) else 1 := by
  rw [sieveProduct, ← Finset.prod_filter]

/-- The indicator factor function is in [0, 1]. -/
private theorem sieve_factor_nonneg (q : ℕ) (R : Finset (ZMod q)) (n : ℕ) :
    0 ≤ (if (Nat.Prime n ∧ (n : ZMod q) ∉ (↑R : Set (ZMod q)))
      then (1 - (1 : ℝ) / n) else 1) := by
  split_ifs with h
  · exact one_sub_inv_nonneg_of_prime h.1
  · linarith

private theorem sieve_factor_le_one (q : ℕ) (R : Finset (ZMod q)) (n : ℕ) :
    (if (Nat.Prime n ∧ (n : ZMod q) ∉ (↑R : Set (ZMod q)))
      then (1 - (1 : ℝ) / n) else 1) ≤ 1 := by
  split_ifs with h
  · exact one_sub_inv_le_one_of_prime h.1
  · exact le_rfl

/-- The gap `1 - sieve_factor(n)` dominates the class indicator `1/n`
    for the missing class a: if a ∉ R and p is prime with p ≡ a mod q,
    then p ∉ R, so the sieve factor at p is (1-1/p), giving gap 1/p. -/
private theorem sieve_gap_dominates_class (q : ℕ) (R : Finset (ZMod q))
    (a : ZMod q) (ha : a ∉ (↑R : Set (ZMod q))) (n : ℕ) :
    (if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0) ≤
    1 - (if (Nat.Prime n ∧ (n : ZMod q) ∉ (↑R : Set (ZMod q)))
      then (1 - (1 : ℝ) / n) else 1) := by
  by_cases hA : Nat.Prime n ∧ (n : ZMod q) = a
  · -- n prime and n ≡ a mod q. Since a ∉ R, n ∉ R.
    have hB : Nat.Prime n ∧ (n : ZMod q) ∉ (↑R : Set (ZMod q)) :=
      ⟨hA.1, by rw [hA.2]; exact ha⟩
    rw [if_pos hA, if_pos hB]
    -- Goal: 1/n ≤ 1 - (1 - 1/n) = 1/n
    linarith
  · -- n not (prime and ≡ a): indicator = 0
    rw [if_neg hA]
    by_cases hB : Nat.Prime n ∧ (n : ZMod q) ∉ (↑R : Set (ZMod q))
    · -- n ∉ R: gap = 1/n ≥ 0
      rw [if_pos hB]
      linarith [show 0 < (1 : ℝ) / n from div_pos one_pos (by exact_mod_cast hB.1.pos)]
    · -- n ∈ R or not prime: gap = 0
      rw [if_neg hB]; linarith

/-- **Sieve product vanishing**: ForbiddenClassDivergent implies
    the sieve product tends to 0 for any R missing a nonzero unit.

    PROVED via `sparse_product_contraction`: the sieve product
    ∏(1-1/p) over excluded primes has factors in [0,1] with
    divergent gap sum (dominated by the divergent class-a reciprocal sum).
    Reindexing: sieveProduct q X R = (∏ range(X+1) g)(X) where g
    is the indicator factor function. -/
theorem sieve_product_vanishing_proved (q : ℕ) :
    ForbiddenClassDivergent q →
    ∀ (R : Finset (ZMod q)),
      (∃ a : ZMod q, a ≠ 0 ∧ IsUnit a ∧ a ∉ (↑R : Set (ZMod q))) →
      Filter.Tendsto (fun X => sieveProduct q X R) Filter.atTop (nhds 0) := by
  intro hFCD R ⟨a, _, ha_unit, ha_notR⟩
  -- Define the sequential factor function
  set g := fun n => if (Nat.Prime n ∧ (n : ZMod q) ∉ (↑R : Set (ZMod q)))
    then (1 - (1 : ℝ) / n) else 1 with hg_def
  -- g(n) ∈ [0, 1]
  have hg_nonneg : ∀ k, 0 ≤ g k := fun k => sieve_factor_nonneg q R k
  have hg_le_one : ∀ k, g k ≤ 1 := fun k => sieve_factor_le_one q R k
  -- The gap 1 - g(n) is not summable (dominated by class-a indicator)
  have hgap_not_summable : ¬Summable (fun k => 1 - g k) := by
    intro hsummable
    -- Class indicator
    set f := fun n => if (Nat.Prime n ∧ (n : ZMod q) = a) then (1 : ℝ) / n else 0 with hf_def
    have hf_nonneg : ∀ n, 0 ≤ f n := fun n => by simp only [hf_def]; split_ifs <;> positivity
    -- f ≤ 1 - g pointwise
    have hf_le : ∀ n, f n ≤ (1 - g n) := fun n =>
      sieve_gap_dominates_class q R a ha_notR n
    -- So f is also summable
    have hf_summable : Summable f :=
      Summable.of_nonneg_of_le hf_nonneg hf_le hsummable
    -- But FCD says f is NOT summable
    exact (hFCD a ha_unit) hf_summable
  -- Apply sparse_product_contraction: ∏_{k < N} g(k) → 0
  have hprod_vanish : Filter.Tendsto (fun N => ∏ k ∈ Finset.range N, g k)
      Filter.atTop (nhds 0) :=
    sparse_product_contraction g hg_nonneg hg_le_one hgap_not_summable
  -- sieveProduct q X R = ∏_{k < X+1} g(k)
  have heq : ∀ X, sieveProduct q X R = ∏ k ∈ Finset.range (X + 1), g k :=
    fun X => sieveProduct_eq_range_prod q X R
  -- Tendsto (fun X => sieveProduct q X R) = Tendsto (fun X => ∏ range(X+1) g)
  -- = Tendsto ((fun N => ∏ range N g) ∘ (· + 1))
  -- Since (· + 1) : ℕ → ℕ tends to atTop, composition gives the result
  rw [show (fun X => sieveProduct q X R) = (fun N => ∏ k ∈ Finset.range N, g k) ∘ (· + 1)
    from by ext X; simp [heq]]
  exact hprod_vanish.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, by omega⟩)

/-- Backward-compatible alias: SieveProductVanishing as a Prop (now proved). -/
def SieveProductVanishing (q : ℕ) : Prop :=
  ForbiddenClassDivergent q →
    ∀ (R : Finset (ZMod q)),
      (∃ a : ZMod q, a ≠ 0 ∧ IsUnit a ∧ a ∉ (↑R : Set (ZMod q))) →
      Filter.Tendsto (fun X => sieveProduct q X R) Filter.atTop (nhds 0)

end SieveHypotheses

/-! ## Part 13: Composition -- FCD + SUB + SPV implies PSCD -/

section Composition

variable {q : ℕ}

/-- In ZMod p for p prime, every nonzero element is a unit. -/
private theorem isUnit_of_ne_zero_prime (hq : q.Prime) (a : ZMod q)
    (ha : a ≠ 0) : IsUnit a := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact IsUnit.mk0 a ha

/-- **Main composition**: FCD + SieveUpperBound + SieveProductVanishing
    together imply PSCD.

    For each proper R (misses nonzero a, does not contain 0):
    1. a is a unit (q prime, a ≠ 0). By FCD, primes in class a have
       divergent ∑ 1/p.
    2. By SPV, sieveProduct(q, X, R) → 0.
    3. By SUB, sqfreeConfinedCount ≤ C * sqfreeCount * sieveProduct.
    4. Dividing: confined density ≤ C * sieveProduct → 0. -/
theorem fcd_sub_spv_implies_pscd (hq : q.Prime)
    (hFCD : ForbiddenClassDivergent q)
    (hSUB : SieveUpperBound q)
    (hSPV : SieveProductVanishing q) :
    PSCD q := by
  intro R hR h0R
  obtain ⟨a, ha_ne, ha_notR⟩ := hR
  have ha_unit : IsUnit a := isUnit_of_ne_zero_prime hq a ha_ne
  -- Get the sieve upper bound constant C
  obtain ⟨C, hC, hbound⟩ := hSUB R ⟨a, ha_ne, ha_notR⟩ h0R
  -- Get sieve product vanishing
  have hvanish : Filter.Tendsto (fun X => sieveProduct q X R)
      Filter.atTop (nhds 0) :=
    hSPV hFCD R ⟨a, ha_ne, ha_unit, ha_notR⟩
  -- The target: C * sieveProduct → 0
  have hCvanish : Filter.Tendsto (fun X => C * sieveProduct q X R)
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) = C * 0 := by ring
    rw [h0]
    exact hvanish.const_mul C
  -- Squeeze: 0 ≤ confined_density ≤ C * sieveProduct → 0
  apply squeeze_zero
  · -- Lower bound: density ≥ 0
    intro X; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · -- Upper bound: density ≤ C * sieveProduct
    intro X
    by_cases hsc : sqfreeCount X = 0
    · -- When sqfreeCount = 0, confined count is also 0
      have hconf : sqfreeConfinedCount q X R = 0 := by
        have := sqfreeConfinedCount_le q X R; omega
      simp [hconf, hsc]
      exact mul_nonneg (le_of_lt hC) (sieveProduct_nonneg q X R)
    · -- When sqfreeCount > 0, divide the SUB bound
      have hpos : (0 : ℝ) < sqfreeCount X := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsc)
      have h1 := hbound X
      -- confined / sqfreeCount ≤ C * sqfreeCount * sieveProduct / sqfreeCount
      --                       = C * sieveProduct
      calc (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X
          ≤ (C * sqfreeCount X * sieveProduct q X R) / sqfreeCount X :=
            div_le_div_of_nonneg_right h1 (le_of_lt hpos)
        _ = C * sieveProduct q X R := by field_simp
  · -- Limit: C * sieveProduct → 0
    exact hCvanish

/-- **PEAP chain (reduced)**: IK.PrimesEquidistributedInAP + SieveUpperBound
    imply PSCD for all primes q.

    PEAPImpliesForbiddenClassDivergent and SieveProductVanishing are now
    PROVED, reducing the open hypotheses to just SieveUpperBound. -/
theorem peap_chain_implies_pscd (hq : q.Prime)
    (hPEAP : IK.PrimesEquidistributedInAP)
    (hSUB : SieveUpperBound q) :
    PSCD q :=
  fcd_sub_spv_implies_pscd hq (peap_implies_fcd_proved hPEAP q hq.two_le)
    hSUB (sieve_product_vanishing_proved q)

/-- **PSCD then implies almost all mixed hitting** (already proved above).
    The full chain: PEAP + SUB → PSCD → almost all mixed hitting. -/
theorem peap_chain_implies_almost_all_mixed_hitting (hq : q.Prime)
    (hPEAP : IK.PrimesEquidistributedInAP)
    (hSUB : SieveUpperBound q) :
    Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact pscd_implies_trapped_density_zero q hq (peap_chain_implies_pscd hq hPEAP hSUB)

end Composition

/-! ## Part 14: Extended Landscape -/

section ExtendedLandscape

/-- **Extended Mixed Ensemble Landscape**: Summary including the PEAP chain.

    The reduction chain:
    * IK.PrimesEquidistributedInAP (standard ANT = Wiener-Ikehara)
      + SieveUpperBound (fundamental lemma of sieve theory, sole open hyp)
      → PSCD
      → almost all mixed hitting (trapped density → 0)

    Proved bridges: PEAPImpliesForbiddenClassDivergent (PROVED),
    SieveProductVanishing (PROVED). Sole open hypothesis: SieveUpperBound. -/
theorem extended_mixed_ensemble_landscape (q : ℕ) [NeZero q] (hq : q.Prime)
    (hPSCD : PSCD q) :
    -- 1. PSCD implies trapped density → 0
    (Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0))
    ∧
    -- 2. Sieve product is bounded in [0, 1]
    (∀ X R, 0 ≤ sieveProduct q X R ∧ sieveProduct q X R ≤ 1)
    ∧
    -- 3. FCD + SUB → PSCD (SPV now proved, applied internally)
    (ForbiddenClassDivergent q → SieveUpperBound q → PSCD q)
    ∧
    -- 4. PEAP + SUB → PSCD (FCD bridge + SPV now proved)
    (IK.PrimesEquidistributedInAP → SieveUpperBound q → PSCD q) :=
  ⟨pscd_implies_trapped_density_zero q hq hPSCD,
   fun X R => ⟨sieveProduct_nonneg q X R, sieveProduct_le_one q X R⟩,
   fun hFCD hSUB => fcd_sub_spv_implies_pscd hq hFCD hSUB (sieve_product_vanishing_proved q),
   fun hPEAP hSUB => peap_chain_implies_pscd hq hPEAP hSUB⟩

end ExtendedLandscape

/-! ## Part 14c: Squarefree Count Lower Bound -/

section SqfreeCountLower

/-- The count of non-squarefree numbers in [1,X]. -/
private def nonsqfreeCount (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => ¬Squarefree m)).card

/-- Partition: sqfreeCount + nonsqfreeCount = X. -/
private theorem sqfree_nonsqfree_partition (X : ℕ) :
    sqfreeCount X + nonsqfreeCount X = X := by
  unfold sqfreeCount nonsqfreeCount
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _),
      Finset.filter_union_filter_not_eq]
  simp [Nat.card_Icc]

/-- Every non-squarefree number has a prime p with p^2 | m. -/
private theorem exists_prime_sq_dvd_of_not_squarefree {m : ℕ} (hm : ¬Squarefree m) :
    ∃ p, p.Prime ∧ p ^ 2 ∣ m := by
  rw [Nat.squarefree_iff_prime_squarefree] at hm
  push_neg at hm
  obtain ⟨p, hp, hdvd⟩ := hm
  exact ⟨p, hp, by rwa [sq]⟩

/-- Every non-squarefree m in [1,X] is a multiple of d^2 for some d in [2, sqrt X]. -/
private theorem nonsqfree_subset_union_multiples (X : ℕ) :
    (Finset.Icc 1 X).filter (fun m => ¬Squarefree m) ⊆
      (Finset.Icc 2 (Nat.sqrt X)).biUnion (fun d =>
        (Finset.Icc 1 X).filter (fun m => d ^ 2 ∣ m)) := by
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hm1, hmX⟩, hnsf⟩ := hm
  obtain ⟨p, hp, hdvd⟩ := exists_prime_sq_dvd_of_not_squarefree hnsf
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter]
  refine ⟨p, ⟨hp.two_le, ?_⟩, ⟨hm1, hmX⟩, hdvd⟩
  rw [Nat.le_sqrt]
  have hmul : p * p ∣ m := sq p ▸ hdvd
  exact le_trans (Nat.le_of_dvd (by omega) hmul) hmX

/-- The count of multiples of d^2 in [1,X] is at most X/d^2. -/
private theorem multiples_of_sq_count_le (d X : ℕ) (_hd : 2 ≤ d) :
    ((Finset.Icc 1 X).filter (fun m => d ^ 2 ∣ m)).card ≤ X / d ^ 2 := by
  set d2 := d ^ 2
  have hd2_pos : 0 < d2 := by positivity
  -- Multiples of d2 in [1,X] are: d2, 2*d2, ..., (X/d2)*d2
  -- Map m ↦ m/d2 gives injection into Finset.Icc 1 (X/d2)
  have hle : ((Finset.Icc 1 X).filter (fun m => d2 ∣ m)).card ≤ (Finset.Icc 1 (X / d2)).card := by
    apply Finset.card_le_card_of_injOn (· / d2)
    · intro m hm
      have hm' := Finset.mem_filter.mp (Finset.mem_coe.mp hm)
      have hm_icc := Finset.mem_Icc.mp hm'.1
      have hdvd := hm'.2
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr
        ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd2_pos,
         Nat.div_le_div_right hm_icc.2⟩)
    · intro a ha b hb hab
      have ha_dvd := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb_dvd := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      calc a = a / d2 * d2 := (Nat.div_mul_cancel ha_dvd).symm
        _ = b / d2 * d2 := by congr 1
        _ = b := Nat.div_mul_cancel hb_dvd
  simp [Nat.card_Icc] at hle; omega

/-- nonsqfreeCount X <= sum_{d=2}^{sqrt X} X/d^2 -/
private theorem nonsqfreeCount_le_sum (X : ℕ) :
    nonsqfreeCount X ≤
      ∑ d ∈ Finset.Icc 2 (Nat.sqrt X), X / d ^ 2 := by
  unfold nonsqfreeCount
  calc ((Finset.Icc 1 X).filter (fun m => ¬Squarefree m)).card
      ≤ ((Finset.Icc 2 (Nat.sqrt X)).biUnion (fun d =>
          (Finset.Icc 1 X).filter (fun m => d ^ 2 ∣ m))).card :=
        Finset.card_le_card (nonsqfree_subset_union_multiples X)
    _ ≤ ∑ d ∈ Finset.Icc 2 (Nat.sqrt X),
          ((Finset.Icc 1 X).filter (fun m => d ^ 2 ∣ m)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Finset.Icc 2 (Nat.sqrt X), X / d ^ 2 :=
        Finset.sum_le_sum (fun d hd => multiples_of_sq_count_le d X (Finset.mem_Icc.mp hd).1)

/-- Telescoping: sum_{d=3}^n (1/(d-1) - 1/d) = 1/2 - 1/n for n >= 3. -/
private theorem telescope_sum_eq (n : ℕ) (hn : 3 ≤ n) :
    ∑ d ∈ Finset.Icc 3 n, (1 / ((d : ℝ) - 1) - 1 / d) = 1 / 2 - 1 / n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn3 : n + 1 = 3
    · -- Base case: n = 2, n+1 = 3
      have hn2 : n = 2 := by omega
      subst hn2
      simp only [Finset.Icc_self, Finset.sum_singleton]
      norm_num
    · have hn_ge3 : 3 ≤ n := by omega
      rw [show Finset.Icc 3 (n + 1) = Finset.Icc 3 n ∪ {n + 1} from by
        ext d; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]; omega]
      rw [Finset.sum_union (by
        simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_singleton]; omega)]
      rw [Finset.sum_singleton, ih hn_ge3]
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
      have hn1_pos : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
      -- Goal: 1/2 - 1/n + (1/(↑(n+1) - 1) - 1/↑(n+1)) = 1/2 - 1/↑(n+1)
      -- Simplify ↑(n+1) to ↑n + 1 and ↑(n+1) - 1 to ↑n
      have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast1]
      have hsimp : (↑n + 1 : ℝ) - 1 = (↑n : ℝ) := by ring
      rw [hsimp]
      field_simp
      ring

/-- Key real bound: sum_{d=2}^D 1/d^2 < 3/4 for all D >= 2.
    Proof: for d >= 3, 1/d^2 <= 1/(d*(d-1)) = 1/(d-1) - 1/d.
    Telescoping gives sum_{d=3}^D = 1/2 - 1/D < 1/2.
    Add 1/4 for d=2: total < 3/4. -/
private theorem inv_sq_sum_lt_three_quarter (D : ℕ) (hD : 2 ≤ D) :
    ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / (d : ℝ) ^ 2 < 3 / 4 := by
  by_cases hD3 : D < 3
  · -- D = 2: just the term 1/4
    have : Finset.Icc 2 D = {2} := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [this, Finset.sum_singleton]; norm_num
  · push_neg at hD3
    -- Split off d=2
    rw [show Finset.Icc 2 D = {2} ∪ Finset.Icc 3 D from by
      ext d; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]; omega]
    rw [Finset.sum_union (by
      simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_Icc]; intro a ha; omega)]
    simp only [Finset.sum_singleton]
    -- For d >= 3: 1/d^2 <= 1/(d*(d-1)) = 1/(d-1) - 1/d
    have hbd : ∀ d ∈ Finset.Icc 3 D, (1 : ℝ) / d ^ 2 ≤ 1 / ((d : ℝ) - 1) - 1 / d := by
      intro d hd
      have hd3 : (3 : ℕ) ≤ d := (Finset.mem_Icc.mp hd).1
      have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
      have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (d : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast show 2 ≤ d by omega
          linarith
        linarith
      rw [div_sub_div _ _ (ne_of_gt hd1_pos) (ne_of_gt hd_pos)]
      rw [div_le_div_iff₀ (pow_pos hd_pos 2) (mul_pos hd1_pos hd_pos)]
      nlinarith [sq_nonneg ((d : ℝ) - 1)]
    calc (1 : ℝ) / 2 ^ 2 + ∑ d ∈ Finset.Icc 3 D, 1 / (↑d) ^ 2
        ≤ 1 / 2 ^ 2 + ∑ d ∈ Finset.Icc 3 D, (1 / ((↑d : ℝ) - 1) - 1 / ↑d) := by
          linarith [Finset.sum_le_sum hbd]
      _ = 1 / 4 + (1 / 2 - 1 / (D : ℝ)) := by
          rw [telescope_sum_eq D hD3]; norm_num
      _ < 3 / 4 := by
          have hD_pos : (0 : ℝ) < D := by exact_mod_cast show 0 < D by omega
          linarith [div_pos one_pos hD_pos]

/-- Cast version: sum_{d=2}^D (X:R)/d^2 < 3/4 * X for D >= 2. -/
private theorem sum_div_sq_lt (X D : ℕ) (hD : 2 ≤ D) (hX : 0 < X) :
    ∑ d ∈ Finset.Icc 2 D, (X : ℝ) / (d : ℝ) ^ 2 < 3 / 4 * X := by
  simp_rw [show ∀ d : ℕ, (X : ℝ) / (d : ℝ) ^ 2 = (X : ℝ) * (1 / (d : ℝ) ^ 2) from
    fun d => by ring]
  rw [← Finset.mul_sum]
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  calc (X : ℝ) * ∑ d ∈ Finset.Icc 2 D, 1 / (↑d) ^ 2
      < X * (3 / 4) := by nlinarith [inv_sq_sum_lt_three_quarter D hD]
    _ = 3 / 4 * X := by ring

/-- The squarefree count lower bound: sqfreeCount X >= X/4.

    More precisely: (X : R) / 4 <= (sqfreeCount X : R).

    Proof: non-squarefree numbers in [1,X] are covered by multiples of d^2
    for d in [2, sqrt X]. Union bound + the fact that sum 1/d^2 < 3/4 gives
    #{non-sf} < 3X/4, hence #{sf} > X/4. -/
theorem sqfreeCount_ge_quarter_real (X : ℕ) (hX : 4 ≤ X) :
    (X : ℝ) / 4 ≤ (sqfreeCount X : ℝ) := by
  -- From the partition: sqfreeCount + nonsqfreeCount = X
  have hpart := sqfree_nonsqfree_partition X
  -- nonsqfreeCount <= sum X/d^2
  have hnsf := nonsqfreeCount_le_sum X
  -- Cast to R
  have hnsf_real : (nonsqfreeCount X : ℝ) ≤
      ∑ d ∈ Finset.Icc 2 (Nat.sqrt X), ((X / d ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnsf
  -- Each term: (X / d^2 : N) <= (X : R) / d^2
  have hterm_le : ∑ d ∈ Finset.Icc 2 (Nat.sqrt X), ((X / d ^ 2 : ℕ) : ℝ) ≤
      ∑ d ∈ Finset.Icc 2 (Nat.sqrt X), (X : ℝ) / (d : ℝ) ^ 2 := by
    apply Finset.sum_le_sum; intro d _
    have : ((X / d ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / (d ^ 2 : ℕ) := Nat.cast_div_le
    rwa [Nat.cast_pow] at this
  -- sqrt X >= 2
  have hsqrt2 : 2 ≤ Nat.sqrt X := by rw [Nat.le_sqrt]; omega
  -- The sum < 3X/4
  have hsum_lt : ∑ d ∈ Finset.Icc 2 (Nat.sqrt X), (X : ℝ) / (d : ℝ) ^ 2 < 3 / 4 * X :=
    sum_div_sq_lt X (Nat.sqrt X) hsqrt2 (by omega)
  -- nonsqfreeCount < 3X/4
  have hnsf_lt : (nonsqfreeCount X : ℝ) < 3 / 4 * X :=
    lt_of_le_of_lt (le_trans hnsf_real hterm_le) hsum_lt
  -- sqfreeCount = X - nonsqfreeCount (in R)
  have hsf_eq : (sqfreeCount X : ℝ) = X - nonsqfreeCount X := by
    have h := hpart
    have : (sqfreeCount X + nonsqfreeCount X : ℝ) = (X : ℝ) := by exact_mod_cast h
    linarith
  linarith

/-- Nat version: 4 * sqfreeCount X + 3 >= X for X >= 4. -/
theorem sqfreeCount_ge_quarter_nat (X : ℕ) (hX : 4 ≤ X) :
    X ≤ 4 * sqfreeCount X + 3 := by
  by_contra h; push_neg at h
  have h1 : (X : ℝ) / 4 ≤ (sqfreeCount X : ℝ) := sqfreeCount_ge_quarter_real X hX
  have h2 : (4 * sqfreeCount X + 3 : ℕ) < X := h
  have h3 : (4 * (sqfreeCount X : ℝ) + 3 : ℝ) < (X : ℝ) := by exact_mod_cast h2
  linarith

end SqfreeCountLower

/-! ## Part 15: Fixed-Modulus Coprime Density (Replacing SieveUpperBound) -/

section FMCD

/-- Count of squarefree m in [1,X] where no prime in S divides m+1. -/
def sqfreeSievedCount (S : Finset ℕ) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => Squarefree m ∧
    ∀ p ∈ S, ¬(p ∣ (m + 1)))).card

/-- **Fixed-Modulus Coprime Density**: For any FIXED finite set of primes S,
    the fraction of squarefree m in [1,X] with gcd(m+1, ∏S) = 1
    is eventually at most (∏_{p∈S}(1-1/p) + ε) * sqfreeCount(X).

    This is MUCH simpler than SieveUpperBound:
    - FMCD: fixed product ∏S, CRT + inclusion-exclusion
    - SUB: growing sieve level, fundamental lemma (Brun/Selberg)

    The proof is elementary: m+1 avoids all primes in S iff m+1 is coprime
    to ∏S. By CRT (since ∏S is fixed), the integers coprime to ∏S have
    density ∏(1-1/p) in any arithmetic progression. The squarefree
    restriction preserves this ratio up to o(1) error. -/
def FixedModulusCoprimeDensity : Prop :=
  ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    ∀ ε > 0, ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (sqfreeSievedCount S X : ℝ) ≤
        (∏ p ∈ S, (1 - 1 / (p : ℝ)) + ε) * sqfreeCount X

/-- sqfreeSievedCount ≤ sqfreeCount (dropping the coprimality condition). -/
theorem sqfreeSievedCount_le (S : Finset ℕ) (X : ℕ) :
    sqfreeSievedCount S X ≤ sqfreeCount X := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1⟩

/-- Count of squarefree m in [1,X] in a FIXED residue class c mod q
    where no prime in S divides m+1. All arithmetic on ℕ. -/
def sqfreeSievedClassCount {q : ℕ} [NeZero q] (c : ZMod q) (S : Finset ℕ) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m : ℕ =>
    Squarefree m ∧ (m : ZMod q) = c ∧ ∀ p ∈ S, ¬(p ∣ m.succ))).card

/-- Count of squarefree m in [1,X] in a FIXED residue class c mod q
    that are confined to allowed factors of R. All arithmetic on ℕ. -/
def sqfreeConfinedClassCount {q : ℕ} [NeZero q] (c : ZMod q) (X : ℕ)
    (R : Finset (ZMod q)) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m : ℕ =>
    Squarefree m ∧ (m : ZMod q) = c ∧
    AllFactorsInSet q m.succ (allowedFactors q c (↑R : Set (ZMod q))))).card

/-- The "excluded factor residues" for walk position c and target set R. -/
def excludedFactorResidues {q : ℕ} [NeZero q] (c : ZMod q) (R : Finset (ZMod q)) :
    Finset (ZMod q) :=
  Finset.univ.filter (fun b => c * b ∉ (↑R : Set (ZMod q)))

/-- Primes up to Y in excluded factor residue classes. -/
def excludedPrimesUpTo {q : ℕ} [NeZero q] (c : ZMod q) (R : Finset (ZMod q))
    (Y : ℕ) : Finset ℕ :=
  (Finset.range (Y + 1)).filter (fun p =>
    p.Prime ∧ (p : ZMod q) ∈ excludedFactorResidues c R)

/-- All primes in excludedPrimesUpTo are prime. -/
theorem excludedPrimesUpTo_prime {q : ℕ} [NeZero q] (c : ZMod q) (R : Finset (ZMod q))
    (Y : ℕ) (p : ℕ) (hp : p ∈ excludedPrimesUpTo c R Y) : p.Prime := by
  simp only [excludedPrimesUpTo, Finset.mem_filter] at hp
  exact hp.2.1

/-- For m in class c, confinement to R implies no excluded prime divides m+1. -/
theorem confined_avoids_excluded {q : ℕ} [NeZero q]
    {m : ℕ} {c : ZMod q} {R : Finset (ZMod q)}
    (hconf : AllFactorsInSet q (m + 1 : ℕ) (allowedFactors q c (↑R : Set (ZMod q))))
    {p : ℕ} (hp_prime : p.Prime)
    (hp_excl : (p : ZMod q) ∈ excludedFactorResidues c R) :
    ¬(p ∣ (m + 1 : ℕ)) := by
  intro hdvd
  have hallowed := hconf p hp_prime hdvd
  simp only [excludedFactorResidues, Finset.mem_filter] at hp_excl
  exact hp_excl.2 hallowed

/-- The confined class count is bounded by the sieved class count for the
    excluded primes. This is the per-class monotonicity lemma. -/
theorem confinedClass_le_sievedClass {q : ℕ} [NeZero q]
    (c : ZMod q) (R : Finset (ZMod q)) (Y X : ℕ) :
    sqfreeConfinedClassCount c X R ≤
      sqfreeSievedClassCount c (excludedPrimesUpTo c R Y) X := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  refine ⟨hm.1, hm.2.1, hm.2.2.1, fun p hp => ?_⟩
  exact confined_avoids_excluded hm.2.2.2
    (excludedPrimesUpTo_prime c R Y p hp)
    ((Finset.mem_filter.mp hp).2.2)

/-- The sieved class count is bounded by the total sieved count (drop class). -/
theorem sievedClass_le_sieved {q : ℕ} [NeZero q]
    (c : ZMod q) (S : Finset ℕ) (X : ℕ) :
    sqfreeSievedClassCount c S X ≤ sqfreeSievedCount S X := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1, hm.2.2.2⟩

/-- The confined count splits over residue classes mod q. -/
theorem confinedCount_le_sum_classes {q : ℕ} [NeZero q]
    (R : Finset (ZMod q)) (X : ℕ) :
    sqfreeConfinedCount q X R ≤
      ∑ c : ZMod q, sqfreeConfinedClassCount c X R := by
  -- Each confined m contributes to exactly one class
  -- Use biUnion bound: card(⋃ S_c) ≤ ∑ card(S_c)
  apply le_trans _ Finset.card_biUnion_le
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
  exact ⟨(m : ZMod q), hm.1, hm.2.1, rfl, hm.2.2⟩

/-- If R misses a nonzero element a and q is prime, then for each unit c,
    the excluded factor residues include c⁻¹ * a. -/
theorem excluded_contains_unit_class {q : ℕ} [NeZero q] (hq : q.Prime)
    {R : Finset (ZMod q)} {a : ZMod q}
    (_ha_ne : a ≠ 0) (ha_notR : a ∉ (↑R : Set (ZMod q)))
    {c : ZMod q} (hc_ne : c ≠ 0) :
    c⁻¹ * a ∈ excludedFactorResidues c R := by
  haveI : Fact q.Prime := ⟨hq⟩
  simp only [excludedFactorResidues, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show c * (c⁻¹ * a) = a from by rw [← mul_assoc, mul_inv_cancel₀ hc_ne, one_mul]]
  exact ha_notR

/-- The excluded unit class c⁻¹ * a is itself a unit. -/
theorem excluded_unit_isUnit {q : ℕ} [NeZero q] (hq : q.Prime)
    {a : ZMod q} (ha_ne : a ≠ 0)
    {c : ZMod q} (hc_ne : c ≠ 0) :
    IsUnit (c⁻¹ * a : ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero hc_ne) ha_ne)

/-- The excluded class reciprocal sum diverges. -/
private theorem excluded_gap_not_summable {q : ℕ} [NeZero q] (hq : q.Prime)
    {R : Finset (ZMod q)} {a : ZMod q}
    (ha_ne : a ≠ 0) (ha_notR : a ∉ (↑R : Set (ZMod q)))
    {c : ZMod q} (hc_ne : c ≠ 0)
    (hFCD : ForbiddenClassDivergent q) :
    ¬Summable (fun (n : ℕ) => if (Nat.Prime n ∧ (n : ZMod q) ∈ excludedFactorResidues c R)
      then (1 : ℝ) / n else 0) := by
  intro hsum
  set b := c⁻¹ * a with hb_def
  have hb_excl : b ∈ excludedFactorResidues c R :=
    excluded_contains_unit_class hq ha_ne ha_notR hc_ne
  have hb_unit : IsUnit b := excluded_unit_isUnit hq ha_ne hc_ne
  have hle : ∀ (n : ℕ), (if (Nat.Prime n ∧ (n : ZMod q) = b) then (1 : ℝ) / n else 0) ≤
      (if (Nat.Prime n ∧ (n : ZMod q) ∈ excludedFactorResidues c R)
        then (1 : ℝ) / n else 0) := by
    intro n
    by_cases hA : Nat.Prime n ∧ (n : ZMod q) = b
    · rw [if_pos hA, if_pos ⟨hA.1, hA.2 ▸ hb_excl⟩]
    · rw [if_neg hA]; split_ifs <;> positivity
  have hb_summable : Summable (fun (n : ℕ) =>
      if (Nat.Prime n ∧ (n : ZMod q) = b) then (1 : ℝ) / n else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hle hsum
  exact (hFCD b hb_unit) hb_summable

set_option linter.unusedSectionVars false in
/-- The sieve product over excluded primes vanishes as Y → ∞. -/
private theorem excluded_sieve_product_vanishes {q : ℕ} [NeZero q] (hq : q.Prime)
    {R : Finset (ZMod q)} {a : ZMod q}
    (ha_ne : a ≠ 0) (ha_notR : a ∉ (↑R : Set (ZMod q)))
    (_h0R : (0 : ZMod q) ∉ (↑R : Set (ZMod q)))
    {c : ZMod q} (hc_ne : c ≠ 0)
    (hFCD : ForbiddenClassDivergent q) :
    Filter.Tendsto
      (fun Y => ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)))
      Filter.atTop (nhds 0) := by
  set g : ℕ → ℝ := fun n => if (Nat.Prime n ∧ (n : ZMod q) ∈ excludedFactorResidues c R)
    then (1 - 1 / (n : ℝ)) else (1 : ℝ) with hg_def
  have hg_nonneg : ∀ k, 0 ≤ g k := by
    intro k; simp only [hg_def]; split_ifs with h
    · exact one_sub_inv_nonneg_of_prime h.1
    · linarith
  have hg_le_one : ∀ k, g k ≤ 1 := by
    intro k; simp only [hg_def]; split_ifs with h
    · exact one_sub_inv_le_one_of_prime h.1
    · exact le_rfl
  have hgap_dom : ∀ (n : ℕ), (if (Nat.Prime n ∧ (n : ZMod q) ∈ excludedFactorResidues c R)
      then (1 : ℝ) / n else 0) ≤ 1 - g n := by
    intro n; simp only [hg_def]; split_ifs <;> linarith
  have hgap_not_summable : ¬Summable (fun k => 1 - g k) := by
    intro hsum
    exact excluded_gap_not_summable hq ha_ne ha_notR hc_ne hFCD
      (Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hgap_dom hsum)
  have hprod_vanish := sparse_product_contraction g hg_nonneg hg_le_one hgap_not_summable
  have heq : ∀ Y, ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) =
      ∏ k ∈ Finset.range (Y + 1), g k := by
    intro Y; simp only [excludedPrimesUpTo, hg_def]; rw [← Finset.prod_filter]
  rw [show (fun Y => ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ))) =
      (fun N => ∏ k ∈ Finset.range N, g k) ∘ (· + 1) from by ext Y; exact heq Y]
  exact hprod_vanish.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, by omega⟩)

/-- **Main theorem**: FMCD + FCD imply PSCD.

    For each proper R (misses nonzero a, does not contain 0):
    1. Decompose sqfreeConfinedCount over residue classes mod q.
    2. For each class c != 0: confinement implies coprimality with
       excluded primes (per-class monotonicity).
    3. By FMCD, the sieved count is bounded.
    4. The excluded sieve product vanishes (FCD gives divergent sum 1/p).
    5. Sum over classes gives the conclusion. -/
theorem fmcd_fcd_implies_pscd {q : ℕ} (hq : q.Prime)
    (hFMCD : FixedModulusCoprimeDensity)
    (hFCD : ForbiddenClassDivergent q) :
    PSCD q := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  intro R hR h0R
  obtain ⟨a, ha_ne, ha_notR⟩ := hR
  -- Use squeeze_zero: 0 ≤ density ≤ bound → 0 if bound → 0
  -- We'll show: for each ε > 0, eventually density ≤ ε
  -- First prove the density is nonneg
  have hdensity_nonneg : ∀ X, 0 ≤ (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X :=
    fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- Setup
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  set nzc := (Finset.univ : Finset (ZMod q)).filter (· ≠ (0 : ZMod q))
  have hnzc_ne : ∀ c ∈ nzc, c ≠ (0 : ZMod q) := fun c hc => (Finset.mem_filter.mp hc).2
  -- Class 0: confined count is always 0
  have hclass0 : ∀ X, sqfreeConfinedClassCount (0 : ZMod q) X R = 0 := by
    intro X; apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro m hmIcc
    push_neg; intro hsf hm0 hconf
    have hempty : allowedFactors q (0 : ZMod q) (↑R : Set (ZMod q)) = ∅ := by
      ext b; simp only [allowedFactors, Set.mem_setOf_eq, zero_mul,
        Set.mem_empty_iff_false, iff_false]; exact h0R
    have hm_ge : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show (m + 1 : ℕ) ≠ 1 by omega)
    have hmem := hconf p hp (show p ∣ m.succ from hpdvd)
    simp [hempty] at hmem
  -- Use Metric.tendsto_atTop (need < ε, will get via (q-1)/q < 1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : (0 : ℝ) < ε / (2 * q) := div_pos hε (mul_pos two_pos hq_pos)
  -- Step 1: For each nonzero class c, sieve product vanishes
  have hvanish : ∀ c : ZMod q, c ≠ 0 → ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
      ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) < ε / (2 * q) := by
    intro c hc
    have htend := excluded_sieve_product_vanishes hq ha_ne ha_notR h0R hc hFCD
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨Y₀, hY₀⟩ := htend (ε / (2 * q)) hε'
    refine ⟨Y₀, fun Y hY => ?_⟩
    have h := hY₀ Y hY
    rw [Real.dist_eq] at h
    have hnn : 0 ≤ ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) :=
      Finset.prod_nonneg fun p hp => one_sub_inv_nonneg_of_prime (excludedPrimesUpTo_prime c R Y p hp)
    rw [sub_zero] at h
    rwa [abs_of_nonneg hnn] at h
  -- Extract uniform Y for all nonzero classes
  have hchoice : ∀ c ∈ nzc, ∃ Y₀, ∀ Y ≥ Y₀,
      ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) < ε / (2 * q) :=
    fun c hc => hvanish c (hnzc_ne c hc)
  set Yfun : ZMod q → ℕ := fun c =>
    if hc : c ∈ nzc then (hchoice c hc).choose else 0
  set Y := nzc.sup Yfun ⊔ 0
  have hprod_small : ∀ c ∈ nzc,
      ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) < ε / (2 * q) := by
    intro c hc
    apply (hchoice c hc).choose_spec
    have hYfun : Yfun c = (hchoice c hc).choose := dif_pos hc
    calc (hchoice c hc).choose = Yfun c := hYfun.symm
      _ ≤ nzc.sup Yfun := Finset.le_sup hc
      _ ≤ Y := le_sup_left
  -- Step 2: Apply FMCD to get X₀ for each class
  have hfmcd_applied : ∀ c ∈ nzc, ∃ X₀, ∀ X ≥ X₀,
      (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) ≤
        (∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) + ε / (2 * q)) *
          sqfreeCount X :=
    fun c hc => hFMCD _ (excludedPrimesUpTo_prime c R Y) (ε / (2 * q)) hε'
  set Xfun : ZMod q → ℕ := fun c =>
    if hc : c ∈ nzc then (hfmcd_applied c hc).choose else 0
  set X₀ := nzc.sup Xfun ⊔ 1
  refine ⟨X₀, fun X hX => ?_⟩
  -- Each nonzero class: sievedCount ≤ ε/q * sqfreeCount
  have hbound : ∀ c ∈ nzc,
      (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) ≤ ε / ↑q * sqfreeCount X := by
    intro c hc
    have hXge : X ≥ (hfmcd_applied c hc).choose := by
      have : Xfun c = (hfmcd_applied c hc).choose := dif_pos hc
      calc (hfmcd_applied c hc).choose = Xfun c := this.symm
        _ ≤ nzc.sup Xfun := Finset.le_sup hc
        _ ≤ X₀ := le_sup_left
        _ ≤ X := hX
    calc (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ)
        ≤ (∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) + ε / (2 * q)) * sqfreeCount X :=
          (hfmcd_applied c hc).choose_spec X hXge
      _ ≤ (ε / (2 * q) + ε / (2 * q)) * sqfreeCount X := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          linarith [hprod_small c hc]
      _ = ε / ↑q * sqfreeCount X := by ring
  -- Assembly: confined density < ε
  simp only [Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (hdensity_nonneg X)]
  by_cases hsc : sqfreeCount X = 0
  · have := sqfreeConfinedCount_le q X R
    have hconf0 : sqfreeConfinedCount q X R = 0 := by omega
    simp [hconf0, hε]
  · have hsc_pos : (0 : ℝ) < sqfreeCount X := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsc)
    -- Density ≤ sum of class densities
    have hdensity_bound : (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X ≤
        ∑ c ∈ nzc, (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X := by
      calc (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X
          ≤ ∑ c : ZMod q, (sqfreeConfinedClassCount c X R : ℝ) / sqfreeCount X := by
            rw [← Finset.sum_div]
            exact div_le_div_of_nonneg_right (by exact_mod_cast confinedCount_le_sum_classes R X) hsc_pos.le
        _ = (sqfreeConfinedClassCount (0 : ZMod q) X R : ℝ) / sqfreeCount X +
            ∑ c ∈ nzc, (sqfreeConfinedClassCount c X R : ℝ) / sqfreeCount X := by
          rw [show (Finset.univ : Finset (ZMod q)) = {(0 : ZMod q)} ∪ nzc from by
              ext c; simp only [nzc, Finset.mem_union, Finset.mem_singleton, Finset.mem_univ,
                Finset.mem_filter, true_and, true_iff]; exact eq_or_ne c 0]
          rw [Finset.sum_union (by
            rw [Finset.disjoint_left]
            intro c hc hc'; exact (hnzc_ne c hc') (Finset.mem_singleton.mp hc))]
          simp only [Finset.sum_singleton]
        _ = ∑ c ∈ nzc, (sqfreeConfinedClassCount c X R : ℝ) / sqfreeCount X := by
            simp [hclass0 X]
        _ ≤ ∑ c ∈ nzc, (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X := by
            apply Finset.sum_le_sum; intro c hc
            apply div_le_div_of_nonneg_right _ hsc_pos.le
            exact_mod_cast le_trans (confinedClass_le_sievedClass c R Y X) (sievedClass_le_sieved c _ X)
    -- Each class density ≤ ε/q
    have hclass_bound : ∀ c ∈ nzc,
        (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X ≤ ε / ↑q := by
      intro c hc
      calc (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X
          ≤ (ε / ↑q * sqfreeCount X) / sqfreeCount X :=
            div_le_div_of_nonneg_right (hbound c hc) hsc_pos.le
        _ = ε / ↑q := by field_simp
    -- Sum over nzc: nzc has at most q-1 elements, and q ≥ 2
    have hnzc_card : nzc.card ≤ q - 1 := by
      have h1 : nzc.card < q := by
        calc nzc.card < (Finset.univ : Finset (ZMod q)).card :=
              Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨0, Finset.mem_univ _, by simp⟩)
          _ = q := ZMod.card q
      omega
    calc (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X
        ≤ ∑ c ∈ nzc, (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X :=
          hdensity_bound
      _ ≤ ∑ _ ∈ nzc, ε / ↑q := Finset.sum_le_sum hclass_bound
      _ = nzc.card • (ε / ↑q) := Finset.sum_const _
      _ ≤ (q - 1) • (ε / ↑q) := by
          apply smul_le_smul_of_nonneg_right hnzc_card
          exact div_nonneg hε.le (Nat.cast_nonneg _)
      _ < q • (ε / ↑q) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          have hεq_pos : (0 : ℝ) < ε / ↑q := div_pos hε hq_pos
          have hcast_lt : (↑(q - 1) : ℝ) < (↑q : ℝ) := by
            exact_mod_cast show q - 1 < q from Nat.sub_lt hq.pos Nat.one_pos
          nlinarith
      _ = ε := by rw [nsmul_eq_mul]; field_simp

end FMCD

/-! ## Part 16: FMCD Chain Composition -/

section FMCDChain

variable {q : ℕ}

/-- **FMCD chain**: PEAP + FMCD imply PSCD for all primes q.

    Composes peap_implies_fcd_proved with fmcd_fcd_implies_pscd.
    This replaces SieveUpperBound with FixedModulusCoprimeDensity
    as the sole open hypothesis (alongside PEAP = standard ANT). -/
theorem fmcd_chain_implies_pscd (hq : q.Prime)
    (hPEAP : IK.PrimesEquidistributedInAP)
    (hFMCD : FixedModulusCoprimeDensity) :
    PSCD q :=
  fmcd_fcd_implies_pscd hq hFMCD (peap_implies_fcd_proved hPEAP q hq.two_le)

/-- **FMCD chain implies almost all mixed hitting**: composition. -/
theorem fmcd_chain_implies_almost_all_mixed_hitting (hq : q.Prime)
    (hPEAP : IK.PrimesEquidistributedInAP)
    (hFMCD : FixedModulusCoprimeDensity) :
    Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact pscd_implies_trapped_density_zero q hq (fmcd_chain_implies_pscd hq hPEAP hFMCD)

end FMCDChain

/-! ## Part 17: FMCD Landscape -/

section FMCDLandscape

/-- **FMCD Landscape**: Summary of the FMCD-based reduction.

    The reduction chain:
    * IK.PrimesEquidistributedInAP (standard ANT = Wiener-Ikehara)
      + FixedModulusCoprimeDensity (elementary CRT, replaces SieveUpperBound)
      -> PSCD
      -> almost all mixed hitting (trapped density -> 0)

    FixedModulusCoprimeDensity is MUCH simpler than SieveUpperBound:
    - FMCD: for FIXED finite product of primes, density is prod(1-1/p) + eps
    - SUB: for GROWING sieve level, density bounded by C * prod(1-1/p)
    FMCD follows from CRT + inclusion-exclusion for a fixed modulus.
    SUB requires the fundamental lemma of sieve theory (Brun/Selberg). -/
theorem fmcd_landscape (q : ℕ) [NeZero q] (hq : q.Prime) :
    -- 1. FMCD + FCD -> PSCD
    (FixedModulusCoprimeDensity → ForbiddenClassDivergent q → PSCD q)
    ∧
    -- 2. PEAP + FMCD -> PSCD (via proved PEAP->FCD bridge)
    (IK.PrimesEquidistributedInAP → FixedModulusCoprimeDensity → PSCD q)
    ∧
    -- 3. PEAP + FMCD -> almost all mixed hitting
    (IK.PrimesEquidistributedInAP → FixedModulusCoprimeDensity →
      Filter.Tendsto
        (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
        Filter.atTop (nhds 0))
    ∧
    -- 4. sqfreeSievedCount <= sqfreeCount (trivial bound)
    (∀ S X, sqfreeSievedCount S X ≤ sqfreeCount X) :=
  ⟨fun hFMCD hFCD => fmcd_fcd_implies_pscd hq hFMCD hFCD,
   fun hPEAP hFMCD => fmcd_chain_implies_pscd hq hPEAP hFMCD,
   fun hPEAP hFMCD => fmcd_chain_implies_almost_all_mixed_hitting hq hPEAP hFMCD,
   fun S X => sqfreeSievedCount_le S X⟩

end FMCDLandscape

/-! ## Part 18: Weak FMCD (Unconditional) -/

section WeakFMCD

/-- Count of m in [1,X] with m+1 coprime to all primes in S.
    Drops the squarefree condition from sqfreeSievedCount. -/
def coprimeShiftCount (S : Finset ℕ) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => ∀ p ∈ S, ¬(p ∣ (m + 1)))).card

/-- Dropping Squarefree from sqfreeSievedCount gives upper bound by coprimeShiftCount. -/
theorem sqfreeSievedCount_le_coprimeShiftCount (S : Finset ℕ) (X : ℕ) :
    sqfreeSievedCount S X ≤ coprimeShiftCount S X := by
  apply Finset.card_le_card; intro m hm
  simp only [sqfreeSievedCount, coprimeShiftCount, Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.2⟩

/-- Coprimality to all primes in S implies coprimality to their product. -/
private theorem coprime_prod_of_not_dvd' {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {n : ℕ} (hn : ∀ p ∈ S, ¬(p ∣ n)) : Nat.Coprime n (∏ p ∈ S, p) := by
  rw [Nat.coprime_comm, Nat.coprime_prod_left_iff]
  intro p hp
  exact (hS p hp).coprime_iff_not_dvd.mpr (hn p hp)

/-- In [1,X], the count of m with (m+1) % N = r is at most X/N + 2. -/
private theorem residue_class_count_le' (N : ℕ) (hN : 0 < N) (r : ℕ) (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun m => (m + 1) % N = r)).card ≤ X / N + 2 := by
  set T := (Finset.Icc 1 X).filter (fun m => (m + 1) % N = r)
  set f := fun (m : ℕ) => (m + 1) / N
  have hinj : Set.InjOn f ↑T := by
    intro a ha b hb hab
    simp only [T, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_Icc] at ha hb
    simp only [f] at hab
    have ha_eq := Nat.div_add_mod (a + 1) N
    have hb_eq := Nat.div_add_mod (b + 1) N
    rw [ha.2] at ha_eq
    rw [hb.2, ← hab] at hb_eq
    omega
  have hmaps : Set.MapsTo f ↑T ↑(Finset.range (X / N + 2)) := by
    intro m hm
    simp only [T, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, f] at hm ⊢
    have hle : (m + 1) / N ≤ (X + 1) / N :=
      Nat.div_le_div_right (Nat.succ_le_succ hm.1.2)
    have hsucc_div : (X + 1) / N ≤ X / N + 1 := by
      apply Nat.div_le_of_le_mul
      nlinarith [Nat.div_add_mod X N, Nat.mod_lt X hN]
    linarith
  calc T.card ≤ (Finset.range (X / N + 2)).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = X / N + 2 := Finset.card_range _

/-- The coprime shift count is bounded by phi(N)*(X/N + 2) where N = prod S. -/
theorem coprimeShiftCount_le_totient_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (X : ℕ) :
    coprimeShiftCount S X ≤ Nat.totient (∏ p ∈ S, p) * (X / (∏ p ∈ S, p) + 2) := by
  set N := ∏ p ∈ S, p with hN_def
  have hN_pos : 0 < N := Finset.prod_pos (fun p hp => (hS p hp).pos)
  -- Each coprime m+1 falls in a coprime residue class mod N
  have hsub : (Finset.Icc 1 X).filter (fun m => ∀ p ∈ S, ¬(p ∣ (m + 1))) ⊆
      ((Finset.range N).filter (fun r => N.Coprime r)).biUnion
        (fun r => (Finset.Icc 1 X).filter (fun m => (m + 1) % N = r)) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_range] at hm ⊢
    refine ⟨(m + 1) % N, ⟨Nat.mod_lt _ hN_pos, ?_⟩, ⟨hm.1.1, hm.1.2⟩, rfl⟩
    have hcop := coprime_prod_of_not_dvd' hS hm.2
    rw [Nat.coprime_comm] at hcop
    -- hcop : Nat.Coprime N (m+1), i.e., gcd N (m+1) = 1
    -- goal : N.Coprime ((m+1) % N), i.e., gcd N ((m+1) % N) = 1
    rw [Nat.Coprime, Nat.gcd_comm,
      show Nat.gcd ((m + 1) % N) N = Nat.gcd N (m + 1) from by rw [Nat.gcd_rec N (m + 1)]]
    exact hcop
  calc coprimeShiftCount S X
      = ((Finset.Icc 1 X).filter (fun m => ∀ p ∈ S, ¬(p ∣ (m + 1)))).card := rfl
    _ ≤ (((Finset.range N).filter (fun r => N.Coprime r)).biUnion
          (fun r => (Finset.Icc 1 X).filter (fun m => (m + 1) % N = r))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ r ∈ (Finset.range N).filter (fun r => N.Coprime r),
          ((Finset.Icc 1 X).filter (fun m => (m + 1) % N = r)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ (Finset.range N).filter (fun r => N.Coprime r), (X / N + 2) := by
        apply Finset.sum_le_sum; intro r _
        exact residue_class_count_le' N hN_pos r X
    _ = ((Finset.range N).filter (fun r => N.Coprime r)).card * (X / N + 2) := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ = Nat.totient N * (X / N + 2) := by
        simp only [Nat.totient_eq_card_coprime]

/-- Euler product: phi(prod primes) = prod(p-1) for pairwise coprime primes. -/
private theorem totient_prod_primes' (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  induction S using Finset.cons_induction with
  | empty => simp [Nat.totient_one]
  | cons p S hp ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := by
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      have hp_prime := hS p (Finset.mem_cons.mpr (Or.inl rfl))
      have hq_prime := hS q (Finset.mem_cons.mpr (Or.inr hq))
      exact hp_prime.coprime_iff_not_dvd.mpr (fun hdvd => by
        have heq : p = q :=
          (hq_prime.eq_one_or_self_of_dvd p hdvd).resolve_left hp_prime.one_lt.ne'
        exact hp (heq ▸ hq))
    rw [Nat.totient_mul hcop, Nat.totient_prime
      (hS p (Finset.mem_cons.mpr (Or.inl rfl)))]
    congr 1
    exact ih (fun q hq => hS q (Finset.mem_cons.mpr (Or.inr hq)))

/-- Real-valued: (prod(p-1)) / (prod p) = prod(1-1/p) for primes. -/
private theorem prod_sub_one_div_eq' (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, ((p : ℝ) - 1)) / (∏ p ∈ S, (p : ℝ)) = ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
  field_simp

/-- **Weak FMCD (PROVED)**: For any fixed finite set of primes S,
    sqfreeSievedCount S X <= (4 * prod(1-1/p) + eps) * sqfreeCount X
    for X sufficiently large.

    The constant 4 comes from sqfreeCount X >= X/4.
    This is unconditionally provable and suffices for the PSCD chain
    since the sieve product prod(1-1/p) -> 0 absorbs the constant. -/
theorem weak_fmcd_proved (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (sqfreeSievedCount S X : ℝ) ≤
        (4 * ∏ p ∈ S, (1 - 1 / (p : ℝ)) + ε) * (sqfreeCount X : ℝ) := by
  set N := ∏ p ∈ S, p with hN_def
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast Finset.prod_pos (fun p hp => (hS p hp).pos)
  have htot_eq : Nat.totient N = ∏ p ∈ S, (p - 1) := totient_prod_primes' S hS
  have htot_le_N : Nat.totient N ≤ N := Nat.totient_le N
  have hprod_nonneg : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_nonneg; intro p hp
    exact one_sub_inv_nonneg_of_prime (hS p hp)
  -- Choose X₀ large enough that 2*N <= eps*X/4 and X >= 4
  set X₀ := max 4 (Nat.ceil (8 * ↑N / ε) + 1) with hX₀_def
  refine ⟨X₀, fun X hX => ?_⟩
  have hX4 : 4 ≤ X := le_trans (le_max_left _ _) hX
  have hsfc : (X : ℝ) / 4 ≤ (sqfreeCount X : ℝ) := sqfreeCount_ge_quarter_real X hX4
  -- 2*N <= eps*X/4 from X₀ choice
  have hXN : 2 * (N : ℝ) ≤ ε * X / 4 := by
    have hceil_le : Nat.ceil (8 * ↑N / ε) + 1 ≤ X₀ := le_max_right _ _
    have h1 : (8 * ↑N / ε : ℝ) ≤ Nat.ceil (8 * ↑N / ε) := Nat.le_ceil _
    have h2 : (↑(Nat.ceil (8 * ↑N / ε) + 1) : ℝ) ≤ X := by
      calc (↑(Nat.ceil (8 * ↑N / ε) + 1) : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hceil_le
        _ ≤ X := by exact_mod_cast hX
    have h3 : 8 * (N : ℝ) / ε ≤ X - 1 := by
      have : (↑(Nat.ceil (8 * ↑N / ε) + 1) : ℝ) = (↑(Nat.ceil (8 * ↑N / ε)) : ℝ) + 1 := by
        push_cast; ring
      linarith
    have h4 : 8 * (N : ℝ) ≤ (↑X - 1) * ε := by rwa [div_le_iff₀ hε] at h3
    linarith [mul_comm ε (↑X : ℝ)]
  -- Coprime count bounds
  have hle_coprime : sqfreeSievedCount S X ≤ coprimeShiftCount S X :=
    sqfreeSievedCount_le_coprimeShiftCount S X
  have htot_bound : (coprimeShiftCount S X : ℝ) ≤
      (Nat.totient N : ℝ) * ((X / N : ℕ) + 2 : ℝ) := by
    exact_mod_cast coprimeShiftCount_le_totient_bound S hS X
  have hdiv_le : ((X / N : ℕ) : ℝ) ≤ (X : ℝ) / N := Nat.cast_div_le
  -- Tight bound: coprimeShiftCount <= prod(1-1/p)*X + 2*N
  have hcop_tight : (coprimeShiftCount S X : ℝ) ≤
      (∏ p ∈ S, (1 - 1 / (p : ℝ))) * X + 2 * N := by
    calc (coprimeShiftCount S X : ℝ)
        ≤ (Nat.totient N : ℝ) * ((X / N : ℕ) + 2 : ℝ) := htot_bound
      _ ≤ (Nat.totient N : ℝ) * ((X : ℝ) / N + 2) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          linarith [hdiv_le]
      _ = (Nat.totient N : ℝ) / N * X + 2 * (Nat.totient N : ℝ) := by ring
      _ ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ))) * X + 2 * N := by
          have hcast_prod : (↑(∏ p ∈ S, (p - 1)) : ℝ) = ∏ p ∈ S, ((p : ℝ) - 1) := by
            rw [Finset.prod_natCast]
            apply Finset.prod_congr rfl
            intro p hp
            have h1le : 1 ≤ p := (hS p hp).one_lt.le
            rw [Nat.cast_sub h1le, Nat.cast_one]
          have htot_ratio : (Nat.totient N : ℝ) / N =
              (∏ p ∈ S, ((p : ℝ) - 1)) / (∏ p ∈ S, (p : ℝ)) := by
            congr 1
            · rw [htot_eq]; exact hcast_prod
            · exact Finset.prod_natCast S (fun p => p)
          rw [htot_ratio, prod_sub_one_div_eq' S hS]
          linarith [show (Nat.totient N : ℝ) ≤ N from by exact_mod_cast htot_le_N]
  -- Assembly: sqfreeSievedCount <= prod*X + 2*N <= (4*prod + eps)*sqfreeCount
  have hX4sf : (X : ℝ) ≤ 4 * sqfreeCount X := by linarith [hsfc]
  calc (sqfreeSievedCount S X : ℝ)
      ≤ (coprimeShiftCount S X : ℝ) := by exact_mod_cast hle_coprime
    _ ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ))) * X + 2 * N := hcop_tight
    _ ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ))) * X + ε * X / 4 := by linarith [hXN]
    _ ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ))) * (4 * sqfreeCount X) + ε * sqfreeCount X := by
        have h1 : (∏ p ∈ S, (1 - 1 / (p : ℝ))) * X ≤
            (∏ p ∈ S, (1 - 1 / (p : ℝ))) * (4 * sqfreeCount X) :=
          mul_le_mul_of_nonneg_left hX4sf hprod_nonneg
        have h2 : ε * X / 4 ≤ ε * sqfreeCount X := by nlinarith [hsfc]
        linarith
    _ = (4 * ∏ p ∈ S, (1 - 1 / (p : ℝ)) + ε) * sqfreeCount X := by ring

end WeakFMCD

/-! ## Part 19: Weak FMCD Chain (PROVED -- eliminates FixedModulusCoprimeDensity) -/

section WeakFMCDChain

/-- **Weak FMCD + FCD imply PSCD** (unconditional on FMCD).

    This mirrors fmcd_fcd_implies_pscd but uses weak_fmcd_proved
    instead of FixedModulusCoprimeDensity. The constant 4 from WeakFMCD
    is absorbed because the sieve product -> 0.

    Key constant adjustment: use eps/(8q) for sieve target and eps/(2q)
    for WeakFMCD tolerance. Then 4*(eps/(8q)) + eps/(2q) = eps/q. -/
theorem weak_fmcd_fcd_implies_pscd {q : ℕ} (hq : q.Prime)
    (hFCD : ForbiddenClassDivergent q) :
    PSCD q := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  intro R hR h0R
  obtain ⟨a, ha_ne, ha_notR⟩ := hR
  have hdensity_nonneg : ∀ X, 0 ≤ (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X :=
    fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  set nzc := (Finset.univ : Finset (ZMod q)).filter (· ≠ (0 : ZMod q))
  have hnzc_ne : ∀ c ∈ nzc, c ≠ (0 : ZMod q) := fun c hc => (Finset.mem_filter.mp hc).2
  -- Class 0: confined count is always 0
  have hclass0 : ∀ X, sqfreeConfinedClassCount (0 : ZMod q) X R = 0 := by
    intro X; apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro m hmIcc
    push_neg; intro hsf hm0 hconf
    have hempty : allowedFactors q (0 : ZMod q) (↑R : Set (ZMod q)) = ∅ := by
      ext b; simp only [allowedFactors, Set.mem_setOf_eq, zero_mul,
        Set.mem_empty_iff_false, iff_false]; exact h0R
    have hm_ge : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show (m + 1 : ℕ) ≠ 1 by omega)
    have hmem := hconf p hp (show p ∣ m.succ from hpdvd)
    simp [hempty] at hmem
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Use eps/(8q) for sieve target and eps/(2q) for FMCD tolerance
  have hε8q : (0 : ℝ) < ε / (8 * q) := div_pos hε (mul_pos (by norm_num : (0 : ℝ) < 8) hq_pos)
  have hε2q : (0 : ℝ) < ε / (2 * q) := div_pos hε (mul_pos two_pos hq_pos)
  -- Step 1: For each nonzero class c, sieve product < eps/(8q)
  have hvanish : ∀ c : ZMod q, c ≠ 0 → ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
      ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) < ε / (8 * q) := by
    intro c hc
    have htend := excluded_sieve_product_vanishes hq ha_ne ha_notR h0R hc hFCD
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨Y₀, hY₀⟩ := htend (ε / (8 * q)) hε8q
    refine ⟨Y₀, fun Y hY => ?_⟩
    have h := hY₀ Y hY
    rw [Real.dist_eq] at h
    have hnn : 0 ≤ ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) :=
      Finset.prod_nonneg fun p hp => one_sub_inv_nonneg_of_prime (excludedPrimesUpTo_prime c R Y p hp)
    rw [sub_zero] at h
    rwa [abs_of_nonneg hnn] at h
  -- Extract uniform Y
  have hchoice : ∀ c ∈ nzc, ∃ Y₀, ∀ Y ≥ Y₀,
      ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) < ε / (8 * q) :=
    fun c hc => hvanish c (hnzc_ne c hc)
  set Yfun : ZMod q → ℕ := fun c =>
    if hc : c ∈ nzc then (hchoice c hc).choose else 0
  set Y := nzc.sup Yfun ⊔ 0
  have hprod_small : ∀ c ∈ nzc,
      ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) < ε / (8 * q) := by
    intro c hc
    apply (hchoice c hc).choose_spec
    have hYfun : Yfun c = (hchoice c hc).choose := dif_pos hc
    calc (hchoice c hc).choose = Yfun c := hYfun.symm
      _ ≤ nzc.sup Yfun := Finset.le_sup hc
      _ ≤ Y := le_sup_left
  -- Step 2: Apply weak_fmcd_proved with tolerance eps/(2q)
  have hwfmcd_applied : ∀ c ∈ nzc, ∃ X₀, ∀ X ≥ X₀,
      (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) ≤
        (4 * ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) + ε / (2 * q)) *
          sqfreeCount X :=
    fun c hc => weak_fmcd_proved _ (excludedPrimesUpTo_prime c R Y) (ε / (2 * q)) hε2q
  set Xfun : ZMod q → ℕ := fun c =>
    if hc : c ∈ nzc then (hwfmcd_applied c hc).choose else 0
  set X₀ := nzc.sup Xfun ⊔ 1
  refine ⟨X₀, fun X hX => ?_⟩
  -- Each nonzero class: sievedCount <= eps/q * sqfreeCount
  have hbound : ∀ c ∈ nzc,
      (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) ≤ ε / ↑q * sqfreeCount X := by
    intro c hc
    have hXge : X ≥ (hwfmcd_applied c hc).choose := by
      have : Xfun c = (hwfmcd_applied c hc).choose := dif_pos hc
      calc (hwfmcd_applied c hc).choose = Xfun c := this.symm
        _ ≤ nzc.sup Xfun := Finset.le_sup hc
        _ ≤ X₀ := le_sup_left
        _ ≤ X := hX
    calc (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ)
        ≤ (4 * ∏ p ∈ excludedPrimesUpTo c R Y, (1 - 1 / (p : ℝ)) + ε / (2 * q)) * sqfreeCount X :=
          (hwfmcd_applied c hc).choose_spec X hXge
      _ ≤ (4 * (ε / (8 * q)) + ε / (2 * q)) * sqfreeCount X := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          linarith [hprod_small c hc]
      _ = ε / ↑q * sqfreeCount X := by ring
  -- Assembly: confined density < eps
  simp only [Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (hdensity_nonneg X)]
  by_cases hsc : sqfreeCount X = 0
  · have := sqfreeConfinedCount_le q X R
    have hconf0 : sqfreeConfinedCount q X R = 0 := by omega
    simp [hconf0, hε]
  · have hsc_pos : (0 : ℝ) < sqfreeCount X := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsc)
    have hdensity_bound : (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X ≤
        ∑ c ∈ nzc, (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X := by
      calc (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X
          ≤ ∑ c : ZMod q, (sqfreeConfinedClassCount c X R : ℝ) / sqfreeCount X := by
            rw [← Finset.sum_div]
            exact div_le_div_of_nonneg_right (by exact_mod_cast confinedCount_le_sum_classes R X) hsc_pos.le
        _ = (sqfreeConfinedClassCount (0 : ZMod q) X R : ℝ) / sqfreeCount X +
            ∑ c ∈ nzc, (sqfreeConfinedClassCount c X R : ℝ) / sqfreeCount X := by
          rw [show (Finset.univ : Finset (ZMod q)) = {(0 : ZMod q)} ∪ nzc from by
              ext c; simp only [nzc, Finset.mem_union, Finset.mem_singleton, Finset.mem_univ,
                Finset.mem_filter, true_and, true_iff]; exact eq_or_ne c 0]
          rw [Finset.sum_union (by
            rw [Finset.disjoint_left]
            intro c hc hc'; exact (hnzc_ne c hc') (Finset.mem_singleton.mp hc))]
          simp only [Finset.sum_singleton]
        _ = ∑ c ∈ nzc, (sqfreeConfinedClassCount c X R : ℝ) / sqfreeCount X := by
            simp [hclass0 X]
        _ ≤ ∑ c ∈ nzc, (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X := by
            apply Finset.sum_le_sum; intro c hc
            apply div_le_div_of_nonneg_right _ hsc_pos.le
            exact_mod_cast le_trans (confinedClass_le_sievedClass c R Y X) (sievedClass_le_sieved c _ X)
    have hclass_bound : ∀ c ∈ nzc,
        (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X ≤ ε / ↑q := by
      intro c hc
      calc (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X
          ≤ (ε / ↑q * sqfreeCount X) / sqfreeCount X :=
            div_le_div_of_nonneg_right (hbound c hc) hsc_pos.le
        _ = ε / ↑q := by field_simp
    have hnzc_card : nzc.card ≤ q - 1 := by
      have h1 : nzc.card < q := by
        calc nzc.card < (Finset.univ : Finset (ZMod q)).card :=
              Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨0, Finset.mem_univ _, by simp⟩)
          _ = q := ZMod.card q
      omega
    calc (sqfreeConfinedCount q X R : ℝ) / sqfreeCount X
        ≤ ∑ c ∈ nzc, (sqfreeSievedCount (excludedPrimesUpTo c R Y) X : ℝ) / sqfreeCount X :=
          hdensity_bound
      _ ≤ ∑ _ ∈ nzc, ε / ↑q := Finset.sum_le_sum hclass_bound
      _ = nzc.card • (ε / ↑q) := Finset.sum_const _
      _ ≤ (q - 1) • (ε / ↑q) := by
          apply smul_le_smul_of_nonneg_right hnzc_card
          exact div_nonneg hε.le (Nat.cast_nonneg _)
      _ < q • (ε / ↑q) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          have hεq_pos : (0 : ℝ) < ε / ↑q := div_pos hε hq_pos
          have hcast_lt : (↑(q - 1) : ℝ) < (↑q : ℝ) := by
            exact_mod_cast show q - 1 < q from Nat.sub_lt hq.pos Nat.one_pos
          nlinarith
      _ = ε := by rw [nsmul_eq_mul]; field_simp

/-- **Weak FMCD chain**: PEAP alone implies PSCD for all primes q.
    This is UNCONDITIONAL on FMCD (uses weak_fmcd_proved).
    Only remaining hypothesis: PrimesEquidistributedInAP (standard ANT). -/
theorem weak_fmcd_chain_implies_pscd {q : ℕ} (hq : q.Prime)
    (hPEAP : IK.PrimesEquidistributedInAP) :
    PSCD q :=
  weak_fmcd_fcd_implies_pscd hq (peap_implies_fcd_proved hPEAP q hq.two_le)

/-- **Weak FMCD chain implies almost all mixed hitting**: composition. -/
theorem weak_fmcd_chain_implies_almost_all (hq : q.Prime)
    (hPEAP : IK.PrimesEquidistributedInAP) :
    Filter.Tendsto
      (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
      Filter.atTop (nhds 0) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact pscd_implies_trapped_density_zero q hq (weak_fmcd_chain_implies_pscd hq hPEAP)

/-- **Weak FMCD Landscape**: Summary of the unconditional reduction.

    Eliminates FixedModulusCoprimeDensity entirely.
    The only remaining open hypothesis is PrimesEquidistributedInAP (= WPNT = standard ANT). -/
theorem weak_fmcd_landscape {q : ℕ} (hq : q.Prime) :
    -- 1. FCD alone -> PSCD (no FMCD needed)
    (ForbiddenClassDivergent q → PSCD q)
    ∧
    -- 2. PEAP alone -> PSCD
    (IK.PrimesEquidistributedInAP → PSCD q)
    ∧
    -- 3. PEAP alone -> almost all mixed hitting
    (IK.PrimesEquidistributedInAP →
      Filter.Tendsto
        (fun X => (sqfreeTrappedCount q X : ℝ) / sqfreeCount X)
        Filter.atTop (nhds 0))
    ∧
    -- 4. WeakFMCD is unconditional
    (∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ ε > 0, ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (sqfreeSievedCount S X : ℝ) ≤
        (4 * ∏ p ∈ S, (1 - 1 / (p : ℝ)) + ε) * (sqfreeCount X : ℝ)) :=
  ⟨fun hFCD => weak_fmcd_fcd_implies_pscd hq hFCD,
   fun hPEAP => weak_fmcd_chain_implies_pscd hq hPEAP,
   fun hPEAP => weak_fmcd_chain_implies_almost_all hq hPEAP,
   fun S hS ε hε => weak_fmcd_proved S hS ε hε⟩

end WeakFMCDChain
