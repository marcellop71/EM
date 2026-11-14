import EM.Stochastic.RandomTwoPointMC

/-!
# Random Two-Point MC: Fourier Counting

## Overview

This file contains Parts 7-9 of the Random Two-Point MC framework:
* Part 7: Fourier counting infrastructure for self-consistent paths
* Part 8: (archived) the `PathSurvival` hypothesis, refuted at `q = 3`
* Part 9: Fourier counting estimates for surviving paths

Split from `RandomTwoPointMC.lean` for compilation performance.

## Main Results

* `char_count_formula_units` -- Fourier counting formula for multisets over (ZMod q)ˣ
* `survival_plus_death` -- survivalCount + deathCount = 2^N

`PathSurvival` and `tca_path_survival_implies_random_mc_proved` were archived on 2026-11-11
(RED #22, `HypothesisAudit.not_pathSurvival_three`).
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 7: Fourier Counting for Self-Consistent Paths

We build the character orthogonality infrastructure for `(ZMod q)ˣ` and
use it to prove a Fourier counting formula for path endpoints. This reduces
`TreeContractionImpliesRandomMC` to a **survival hypothesis**: the survival
count grows faster than the nontrivial character error terms.

### Structure

1. Character orthogonality on `(ZMod q)ˣ` (locally reproved since VanishingNoise versions are private)
2. Death/survival counts and their partition property
3. Fourier counting formula: `(q-1) * pathCount(a) = ∑_χ conj(χ(a)) * U(χ, N)`
4. Uniform bound extraction for finitely many tendsto-zero sequences
5. Lower bound on `pathCount` in terms of `survivalCount` and `deathCount`

### Key insight

TreeContractionAtHalf gives vanishing `pathCharSum(χ, N)` for nontrivial χ.
By ChiAtMultiplicativity, for paths whose endpoint is a unit mod q,
the character product relates to χ(unit(endpoint)). For "death" paths
(q | endpoint), ChiAtMultiplicativity does not apply.

The Fourier argument shows: IF the survival count (unit endpoints) is positive,
the distribution over unit classes is approximately uniform for large N,
giving positive pathCount for each unit class.

What the argument needs is that `deathCount` be small against `survivalCount`.  The
hypothesis `PathSurvival` that used to supply this (ratio → ∞) can only hold when no path
ever dies; it was archived on 2026-11-11 (see Part 8). -/

section FourierCounting

variable {q : ℕ} [hq : Fact (Nat.Prime q)] [NeZero q]

/-! ### Character orthogonality for (ZMod q)ˣ -/

/-- Fintype instance for (ZMod q)ˣ →* ℂˣ, via the MulChar bridge. -/
noncomputable instance homFintype_inst : Fintype ((ZMod q)ˣ →* ℂˣ) :=
  Fintype.ofEquiv _ (mulCharHomEquiv (G := (ZMod q)ˣ))

/-- Fintype.card ((ZMod q)ˣ →* ℂˣ) = Fintype.card (ZMod q)ˣ. -/
theorem hom_card_eq_units :
    Fintype.card ((ZMod q)ˣ →* ℂˣ) = Fintype.card (ZMod q)ˣ := by
  have h1 : Fintype.card ((ZMod q)ˣ →* ℂˣ) = Fintype.card (MulChar (ZMod q)ˣ ℂ) :=
    Fintype.card_congr (mulCharHomEquiv (G := (ZMod q)ˣ)).symm
  have hexp_pos : 0 < Monoid.exponent ((ZMod q)ˣˣ) :=
    Monoid.exponent_pos_of_exists (Fintype.card ((ZMod q)ˣˣ)) Fintype.card_pos
      (fun g => pow_card_eq_one)
  have : NeZero (Monoid.exponent ((ZMod q)ˣˣ) : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have h2 : Fintype.card (MulChar (ZMod q)ˣ ℂ) = Fintype.card (ZMod q)ˣ := by
    rw [show Fintype.card (MulChar (ZMod q)ˣ ℂ) = Nat.card (MulChar (ZMod q)ˣ ℂ) from
      Nat.card_eq_fintype_card.symm]
    rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity (ZMod q)ˣ ℂ]
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_congr (toUnits (G := (ZMod q)ˣ)).toEquiv).symm
  omega

/-- Character orthogonality for MulChar on (ZMod q)ˣ: for a != 1, sum chi(a) = 0. -/
private theorem mulChar_sum_eq_zero_units {a : (ZMod q)ˣ} (ha : a ≠ 1) :
    ∑ chi : MulChar (ZMod q)ˣ ℂ, chi a = 0 := by
  have hexp_pos : 0 < Monoid.exponent ((ZMod q)ˣˣ) :=
    Monoid.exponent_pos_of_exists (Fintype.card ((ZMod q)ˣˣ)) Fintype.card_pos
      (fun g => pow_card_eq_one)
  have : NeZero (Monoid.exponent ((ZMod q)ˣˣ) : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  obtain ⟨chi, hchi⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod q)ˣ ℂ ha
  exact eq_zero_of_mul_eq_self_left hchi
    (by simp only [Finset.mul_sum, ← MulChar.mul_apply]
        exact Fintype.sum_bijective _ (Group.mulLeft_bijective chi) _ _ fun _ => rfl)

/-- Character orthogonality for hom: for a != 1, sum f(a) = 0. -/
private theorem hom_sum_eq_zero_units {a : (ZMod q)ˣ} (ha : a ≠ 1) :
    ∑ f : (ZMod q)ˣ →* ℂˣ, (f a : ℂ) = 0 := by
  rw [show ∑ f : (ZMod q)ˣ →* ℂˣ, (f a : ℂ) =
      ∑ chi : MulChar (ZMod q)ˣ ℂ, (mulCharToHom chi a : ℂ) from
    (Fintype.sum_equiv (mulCharHomEquiv (G := (ZMod q)ˣ)) _ _ (fun _ => rfl)).symm]
  simp_rw [mulCharToHom_apply]
  exact mulChar_sum_eq_zero_units ha

/-- Combined orthogonality: sum f(g) = |G| if g = 1, 0 otherwise. -/
private theorem hom_sum_units (g : (ZMod q)ˣ) :
    ∑ f : (ZMod q)ˣ →* ℂˣ, (f g : ℂ) =
    if g = 1 then ↑(Fintype.card (ZMod q)ˣ) else 0 := by
  split_ifs with h
  · subst h
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1; exact hom_card_eq_units
  · exact hom_sum_eq_zero_units h

/-- Fourier indicator: sum conj(f(a)) * f(g) = |G| if g = a, 0 otherwise. -/
theorem hom_indicator_units (a g : (ZMod q)ˣ) :
    ∑ f : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (f a : ℂ) * (f g : ℂ) =
    if g = a then ↑(Fintype.card (ZMod q)ˣ) else 0 := by
  have conj_eq : ∀ f : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (f a : ℂ) = (f a⁻¹ : ℂ) := by
    intro f
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact (Complex.inv_eq_conj (char_norm_one_of_hom f a)).symm
  simp_rw [conj_eq, ← Units.val_mul, ← map_mul,
    show a⁻¹ * g = g * a⁻¹ from mul_comm _ _]
  rw [hom_sum_units (g * a⁻¹)]
  simp only [mul_inv_eq_one]

/-- Fourier counting formula for multisets over (ZMod q)^*:
    |G| * count(a, M) = sum_f conj(f(a)) * sum_{g in M} f(g). -/
theorem char_count_formula_units (a : (ZMod q)ˣ) (M : Multiset (ZMod q)ˣ) :
    (↑(Fintype.card (ZMod q)ˣ) : ℂ) * ↑(Multiset.count a M) =
    ∑ f : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (f a : ℂ) *
      (M.map (fun g => (f g : ℂ))).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons x M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← ih]
    by_cases hax : a = x
    · subst hax; simp [hom_indicator_units]; ring
    · have hxa : ¬(x = a) := fun h => hax h.symm
      simp only [hom_indicator_units, if_neg hxa, if_neg hax]
      ring_nf

/-- Uniform bound extraction: for finitely many tendsto-zero sequences,
    find N_0 such that all are below epsilon for N >= N_0. -/
theorem uniform_bound_of_tendsto_local
    {ι : Type*} (T : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ T, Filter.Tendsto (f i) Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀, ∀ i ∈ T, ∀ N, N₀ ≤ N → f i N < ε := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | @insert a s hna ih_ind =>
    obtain ⟨N₁, hN₁⟩ := ih_ind (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ha_tends := hf a (Finset.mem_insert_self a s)
    rw [Metric.tendsto_atTop] at ha_tends
    obtain ⟨N₂, hN₂⟩ := ha_tends ε hε
    refine ⟨max N₁ N₂, fun i hi N hN => ?_⟩
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · have h := hN₂ N (le_of_max_le_right hN)
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact h.2
    · exact hN₁ i hi N (le_of_max_le_left hN)

/-! ### Death and survival counts -/

/-- The death count: number of paths where q divides the endpoint. -/
def deathCount (q : ℕ) [Fact (Nat.Prime q)] (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N → Bool)).filter
    (fun σ => ¬IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q))).card

/-- The survival count: number of paths with unit endpoints. -/
def survivalCount (q : ℕ) [Fact (Nat.Prime q)] (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N → Bool)).filter
    (fun σ => IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q))).card

omit [NeZero q] in
/-- Survival + death = 2^N (partition). -/
theorem survival_plus_death (N : ℕ) :
    survivalCount q N + deathCount q N = 2 ^ N := by
  rw [survivalCount, deathCount]
  rw [← Finset.card_union_of_disjoint]
  · rw [Finset.filter_union_filter_not_eq]
    simp [Fintype.card_fin, Fintype.card_bool]
  · exact Finset.disjoint_filter.mpr (fun σ _ h1 h2 => h2 h1)

end FourierCounting

/-! ## Part 8: PathSurvival (archived 2026-11-11)

`PathSurvival q` asked that the ratio `survivalCount / deathCount` grow without bound.  But a
path that has died stays dead (once `q` divides the accumulator it divides every later one),
and each dead path of length `N` has two dead extensions of length `N + 1`: the death count at
least doubles per level while the total is `2^N`.  So after the first death the ratio is bounded,
and `PathSurvival q` says exactly "no two-point path ever captures `q`" — the opposite of what
the two-point model is for.  At `q = 3` every path dies at step 1 (`2 + 1 = 3`), and
`HypothesisAudit.not_pathSurvival_three` refutes it (review
`docs/analysis/review_2026-11-10.md`, row H10; the general collapse to
`∀ N, deathCount q N = 0` is argued above but not machine-checked).

The definition now lives in `EM/Meta/HypothesisAudit.lean` next to that refutation.

-- TCAPathSurvivalImpliesRandomMC archived to EM/Archive/Stochastic/PathSurvivalArchive.lean (RED #22)
-- tca_path_survival_implies_random_mc_proved archived to EM/Archive/Stochastic/PathSurvivalArchive.lean (RED #22)
-/

/-! ## Part 9: Fourier counting estimates for surviving paths

The estimates below are unconditional and stay live.  They were assembled into
`tca_path_survival_implies_random_mc_proved` (TCA + PathSurvival ⇒ RandomTwoPointMC), which is
archived with `PathSurvival` (RED #22).

- `path_sum_decomp`: the unscaled path sum splits into surviving and death terms
- `death_error_norm_le`: the death term has norm at most `deathCount`
- `uecsi_norm_le`: `‖U(χ,N)‖ ≤ 2^N ‖pathCharSum‖ + deathCount`
- `fourier_counting_identity`: `(q-1)·pathCount(a) = ∑_χ conj(χ(a))·U(χ,N)`
- `fourier_lower_bound`: `(q-1)·pathCount(a) ≥ survivalCount − (q−2)·B` -/

section TCAPathSurvivalProof

variable {q : ℕ} [hq : Fact (Nat.Prime q)] [NeZero q]

/-- Character sum over surviving paths with unit-endpoint indicator.
    For surviving σ: contributes χ(unit(endpoint)).
    For death σ: contributes 0.
    Defined over ALL 2^N paths using `dite`. -/
noncomputable def unitEndpointCharSumInd
    (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) : ℂ :=
  ∑ σ : Fin N → Bool,
    if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
    then (chi h.unit : ℂ)
    else 0

omit [NeZero q] in
/-- IsUnit at ZMod q implies q does not divide the natural number. -/
private theorem survive_not_dvd {n : ℕ}
    (h : IsUnit (n : ZMod q)) : ¬(q ∣ n) := by
  intro hdvd
  have h0 : (n : ZMod q) = 0 := by
    rwa [ZMod.natCast_eq_zero_iff]
  exact not_isUnit_zero (h0 ▸ h)

/-- unitEndpointCharSumInd for the trivial character equals survivalCount. -/
private theorem uecsi_trivial (N : ℕ) :
    unitEndpointCharSumInd (1 : (ZMod q)ˣ →* ℂˣ) N = ↑(survivalCount q N) := by
  simp only [unitEndpointCharSumInd, survivalCount]
  -- Simplify: trivial character maps everything to 1
  have h1 : ∀ σ : Fin N → Bool,
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then ((1 : (ZMod q)ˣ →* ℂˣ) h.unit : ℂ) else 0) =
      if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
      then (1 : ℂ) else 0 := by
    intro σ; split_ifs with h <;> simp
  simp_rw [h1, Finset.sum_boole]
private theorem chiAt_mult_fin (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (σ : ℕ → Bool)
    (hndvd : ¬(q ∣ epsWalkProdFrom 2 σ N)) :
    chiAt q chi 2 * ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 σ k) =
    chiAt q chi (epsWalkProdFrom 2 σ N) := by
  have h := chiAt_multiplicativity_proved chi 2 le_rfl σ N hndvd
  rw [← Fin.prod_univ_eq_prod_range] at h
  exact h

/-- For a unit value, chiAt extracts the character value at that unit. -/
private theorem chiAt_of_unit' {n : ℕ} (chi : (ZMod q)ˣ →* ℂˣ)
    (h : IsUnit (n : ZMod q)) :
    chiAt q chi n = (chi h.unit : ℂ) := by
  unfold chiAt
  rw [dif_pos h]

/-- For q ≥ 3, chiAt(2) has norm 1. -/
private theorem chiAt_two_norm_one' (hq3 : 2 < q) (chi : (ZMod q)ˣ →* ℂˣ) :
    ‖chiAt q chi 2‖ = 1 := by
  have hu := two_isUnit_of_gt_two hq3
  rw [chiAt_of_unit' chi hu]
  exact char_norm_one_of_hom chi hu.unit

/-- For q ≥ 3, chiAt(2) ≠ 0. -/
private theorem chiAt_two_ne_zero' (hq3 : 2 < q) (chi : (ZMod q)ˣ →* ℂˣ) :
    chiAt q chi 2 ≠ 0 := by
  intro h0
  have h1 := chiAt_two_norm_one' hq3 chi
  have h2 : ‖chiAt q chi 2‖ = 0 := by rw [h0]; exact norm_zero
  linarith [h1, h2]

set_option maxHeartbeats 400000 in
/-- Key decomposition: the unscaled path sum splits into surviving and death terms.
    For surviving paths, we use ChiAtMultiplicativity to relate factor products to χ(endpoint).
    For death paths, the factor product has norm ≤ 1. -/
private theorem path_sum_decomp (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (hq3 : 2 < q) :
    (2 : ℂ) ^ N * pathCharSum q chi N 2 =
    (chiAt q chi 2)⁻¹ * unitEndpointCharSumInd chi N +
    ∑ σ : Fin N → Bool,
      if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
      then 0
      else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k) := by
  have hne := chiAt_two_ne_zero' hq3 chi
  -- Rewrite LHS using pathCharSum definition
  have hunscaled : (2 : ℂ) ^ N * pathCharSum q chi N 2 =
      ∑ σ : Fin N → Bool,
        ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k) := by
    simp only [pathCharSum]
    have h2N : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [hunscaled]
  -- Split each term based on surviving/death
  have hsplit_term : ∀ σ : Fin N → Bool,
      ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k) =
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ)
       else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)) := by
    intro σ; split_ifs with h
    · -- Surviving: use ChiAtMultiplicativity
      have hndvd := survive_not_dvd h
      have hmult := chiAt_mult_fin chi N (finDecisionExtend σ) hndvd
      -- hmult: chiAt(2) * ∏ chiAt(factor_k) = chiAt(endpoint)
      -- Factor product = chiAt(2)⁻¹ * chiAt(endpoint) = chiAt(2)⁻¹ * chi(unit)
      have : ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) ↑k) =
          (chiAt q chi 2)⁻¹ * chiAt q chi (epsWalkProdFrom 2 (finDecisionExtend σ) N) := by
        rw [inv_mul_eq_div, eq_comm, div_eq_iff hne]
        rw [mul_comm]; exact hmult.symm
      rw [this, chiAt_of_unit' chi h]
    · rfl
  have : ∀ σ ∈ Finset.univ, (∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k) : ℂ) =
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ)
       else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)) :=
    fun σ _ => hsplit_term σ
  rw [Finset.sum_congr rfl this]
  -- Split into surviving + death parts
  rw [show (∑ σ : Fin N → Bool,
        if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
        then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ)
        else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)) =
      (∑ σ : Fin N → Bool,
        if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
        then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ) else 0) +
      (∑ σ : Fin N → Bool,
        if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q) then 0
        else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k))
    from by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs with h
      · simp
      · simp]
  congr 1
  -- Surviving part: factor out chiAt(2)⁻¹
  have hfactor : ∀ σ ∈ (Finset.univ : Finset (Fin N → Bool)),
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (chiAt q chi 2)⁻¹ * (chi h.unit : ℂ) else 0) =
      (chiAt q chi 2)⁻¹ *
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (chi h.unit : ℂ) else 0) := by
    intro σ _; split_ifs <;> simp
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  rfl

/-- Norm bound on the death error term: |∑_{death} ∏ chiAt| ≤ deathCount. -/
private theorem death_error_norm_le (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    ‖∑ σ : Fin N → Bool,
      (if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (0 : ℂ)
       else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k))‖ ≤
    ↑(deathCount q N) := by
  calc ‖∑ σ : Fin N → Bool, _‖
      ≤ ∑ σ : Fin N → Bool, ‖(if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
          then (0 : ℂ)
          else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ σ : Fin N → Bool,
          (if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q) then 0 else 1 : ℝ) := by
        apply Finset.sum_le_sum; intro σ _
        split_ifs with h
        · simp
        · calc ‖∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)‖
              ≤ ∏ k : Fin N, ‖chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)‖ :=
                Finset.norm_prod_le _ _
            _ ≤ ∏ _k : Fin N, (1 : ℝ) := by
                apply Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)
                  (fun k _ => chiAt_norm_le_one q chi _)
            _ = 1 := by simp
    _ = ↑(deathCount q N) := by
        -- Convert indicator sum to card of filter
        have hconv : ∀ σ ∈ (Finset.univ : Finset (Fin N → Bool)),
            (if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
              then (0 : ℝ) else 1) =
            (if ¬IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
              then (1 : ℝ) else 0) := by
          intro σ _; split_ifs <;> simp_all
        rw [Finset.sum_congr rfl hconv, Finset.sum_boole]
        simp [deathCount]

/-- Norm bound on the unit endpoint character sum:
    |unitEndpointCharSumInd(χ, N)| ≤ 2^N * |pathCharSum| + deathCount. -/
private theorem uecsi_norm_le (chi : (ZMod q)ˣ →* ℂˣ) (N : ℕ) (hq3 : 2 < q) :
    ‖unitEndpointCharSumInd chi N‖ ≤
    (2 : ℝ) ^ N * ‖pathCharSum q chi N 2‖ + ↑(deathCount q N) := by
  have hdecomp := path_sum_decomp chi N hq3
  set E := ∑ σ : Fin N → Bool,
    if IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q) then (0 : ℂ)
    else ∏ k : Fin N, chiAt q chi (epsWalkFactorFrom 2 (finDecisionExtend σ) k)
  have hchiAt2_ne := chiAt_two_ne_zero' hq3 chi
  have hchiAt2_norm := chiAt_two_norm_one' hq3 chi
  -- From decomp: chiAt(2)⁻¹ * uecsi + E = 2^N * pathCharSum
  -- So uecsi = chiAt(2) * (2^N * pathCharSum - E)
  have huecsi_eq : unitEndpointCharSumInd chi N =
      chiAt q chi 2 * ((2 : ℂ) ^ N * pathCharSum q chi N 2 - E) := by
    have h1 : (chiAt q chi 2)⁻¹ * unitEndpointCharSumInd chi N + E =
        (2 : ℂ) ^ N * pathCharSum q chi N 2 := hdecomp.symm
    have h2 : (chiAt q chi 2)⁻¹ * unitEndpointCharSumInd chi N =
        (2 : ℂ) ^ N * pathCharSum q chi N 2 - E := by
      linear_combination h1
    rw [← h2, ← mul_assoc, mul_inv_cancel₀ hchiAt2_ne, one_mul]
  rw [huecsi_eq]
  calc ‖chiAt q chi 2 * ((2 : ℂ) ^ N * pathCharSum q chi N 2 - E)‖
      = ‖chiAt q chi 2‖ * ‖(2 : ℂ) ^ N * pathCharSum q chi N 2 - E‖ := norm_mul _ _
    _ = 1 * ‖(2 : ℂ) ^ N * pathCharSum q chi N 2 - E‖ := by rw [hchiAt2_norm]
    _ = ‖(2 : ℂ) ^ N * pathCharSum q chi N 2 - E‖ := one_mul _
    _ ≤ ‖(2 : ℂ) ^ N * pathCharSum q chi N 2‖ + ‖E‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ N * ‖pathCharSum q chi N 2‖ + ↑(deathCount q N) := by
        gcongr
        · rw [norm_mul, Complex.norm_pow, Complex.norm_ofNat]
        · exact death_error_norm_le chi N

set_option maxHeartbeats 400000 in
/-- Fourier counting identity for unitEndpointCharSumInd:
    ∑_χ conj(χ(a)) * unitEndpointCharSumInd(χ, N) = (q-1) * pathCount(a, N). -/
private theorem fourier_counting_identity (N : ℕ) (a : (ZMod q)ˣ) :
    ∑ chi : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (chi a : ℂ) *
      unitEndpointCharSumInd chi N =
    ↑(Fintype.card (ZMod q)ˣ) * ↑(pathCount q N a) := by
  simp only [unitEndpointCharSumInd]
  -- Swap sum order
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Now for each σ, compute ∑_χ conj(χ(a)) * (dite)
  have hper_sigma : ∀ σ : Fin N → Bool,
      ∑ chi : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (chi a : ℂ) *
        (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
         then (chi h.unit : ℂ) else 0) =
      if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
      then (if h.unit = a then ↑(Fintype.card (ZMod q)ˣ) else 0)
      else 0 := by
    intro σ
    by_cases h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
    · -- Surviving
      simp_rw [dif_pos h]
      exact hom_indicator_units a h.unit
    · -- Death: sum of conj(chi(a)) * 0 = 0
      simp_rw [dif_neg h, mul_zero, Finset.sum_const_zero]
  simp_rw [hper_sigma]
  -- Collapse to pathCount
  -- Need to show: ∑_σ [dite IsUnit (if unit=a then |G| else 0) 0] = |G| * pathCount
  -- pathCount uses epsWalkProd, not epsWalkProdFrom 2
  -- Bridge: epsWalkProdFrom_two_eq
  have hcollapse : ∀ σ : Fin N → Bool,
      (if h : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
       then (if h.unit = a then (↑(Fintype.card (ZMod q)ˣ) : ℂ) else 0)
       else 0) =
      if (epsWalkProd (finDecisionExtend σ) N : ZMod q) = ↑a
      then (↑(Fintype.card (ZMod q)ˣ) : ℂ)
      else 0 := by
    intro σ
    by_cases hu : IsUnit (epsWalkProdFrom 2 (finDecisionExtend σ) N : ZMod q)
    · rw [dif_pos hu]
      by_cases heq : hu.unit = a
      · rw [if_pos heq, if_pos]
        rw [← heq, IsUnit.unit_spec, epsWalkProdFrom_two_eq]
      · rw [if_neg heq, if_neg]
        intro heq'
        apply heq
        rw [← epsWalkProdFrom_two_eq] at heq'
        exact Units.ext (by rw [IsUnit.unit_spec]; exact heq')
    · rw [dif_neg hu, if_neg]
      intro heq
      apply hu
      rw [← epsWalkProdFrom_two_eq] at heq
      rw [heq]; exact Units.isUnit a
  simp_rw [hcollapse]
  -- Now it's ∑_σ (if endpoint = a then card else 0) = card * pathCount
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- card of filter = pathCount
  rw [mul_comm]; simp [pathCount]

/-- Fourier lower bound on pathCount:
    (q-1) * pathCount(a) ≥ survivalCount - (q-2) * B
    when |unitEndpointCharSumInd(χ)| ≤ B for all nontrivial χ. -/
private theorem fourier_lower_bound (N : ℕ) (a : (ZMod q)ˣ) (B : ℝ) (_hB : 0 ≤ B)
    (hbound : ∀ chi : (ZMod q)ˣ →* ℂˣ, chi ≠ 1 →
      ‖unitEndpointCharSumInd chi N‖ ≤ B) :
    (↑(Fintype.card (ZMod q)ˣ) : ℝ) * ↑(pathCount q N a) ≥
    ↑(survivalCount q N) - (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
  have hfci := fourier_counting_identity N a
  -- Extract the real part
  have hreal : (↑(Fintype.card (ZMod q)ˣ) : ℝ) * ↑(pathCount q N a) =
    (∑ chi : (ZMod q)ˣ →* ℂˣ, starRingEnd ℂ (chi a : ℂ) *
      unitEndpointCharSumInd chi N).re := by
    rw [hfci]; simp
  rw [hreal]
  -- Split sum into trivial + nontrivial
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : (ZMod q)ˣ →* ℂˣ))]
  -- Evaluate trivial term
  have htrivial_term :
    starRingEnd ℂ ((1 : (ZMod q)ˣ →* ℂˣ) a : ℂ) *
      unitEndpointCharSumInd (1 : (ZMod q)ˣ →* ℂˣ) N =
    ↑(survivalCount q N : ℕ) := by
    rw [uecsi_trivial]; simp [Units.val_one]
  rw [htrivial_term]
  -- Bound the nontrivial sum
  set S := ∑ chi ∈ (Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1,
    starRingEnd ℂ (chi a : ℂ) * unitEndpointCharSumInd chi N
  have hnt_bound : ‖S‖ ≤ (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
    calc ‖S‖
        ≤ ∑ chi ∈ (Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1,
          ‖starRingEnd ℂ (chi a : ℂ) * unitEndpointCharSumInd chi N‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _chi ∈ (Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1, B := by
          apply Finset.sum_le_sum; intro chi hmem
          calc ‖starRingEnd ℂ (chi a : ℂ) * unitEndpointCharSumInd chi N‖
              = ‖starRingEnd ℂ (chi a : ℂ)‖ * ‖unitEndpointCharSumInd chi N‖ :=
                norm_mul _ _
            _ ≤ 1 * B := by
                gcongr
                · rw [RCLike.norm_conj]; exact (char_norm_one_of_hom chi a).le
                · exact hbound chi (Finset.ne_of_mem_erase hmem)
            _ = B := one_mul _
      _ = ↑((Finset.univ : Finset ((ZMod q)ˣ →* ℂˣ)).erase 1).card * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
          have hcard_pos : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hom_card_eq_units,
            Nat.cast_sub (by omega : 1 ≤ Fintype.card (ZMod q)ˣ)]
          simp
  -- Combine: re(survivalCount + S) ≥ survivalCount - ‖S‖
  have hre_ge : (↑↑(survivalCount q N) + S).re ≥
      ↑(survivalCount q N : ℕ) - (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
    calc (↑↑(survivalCount q N) + S).re
        = (↑↑(survivalCount q N) : ℂ).re + S.re := Complex.add_re _ _
      _ ≥ ↑(survivalCount q N : ℕ) - ‖S‖ := by
          simp only [Complex.natCast_re]
          have hre_lb : -‖S‖ ≤ S.re := by
            calc -‖S‖ ≤ -|S.re| := by linarith [Complex.abs_re_le_norm S]
              _ ≤ S.re := neg_abs_le S.re
          linarith
      _ ≥ ↑(survivalCount q N : ℕ) - (↑(Fintype.card (ZMod q)ˣ) - 1) * B := by
          linarith [hnt_bound]
  exact hre_ge

end TCAPathSurvivalProof
