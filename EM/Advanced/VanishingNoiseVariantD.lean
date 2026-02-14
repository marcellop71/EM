import EM.Advanced.VanishingNoiseVariantC

/-!
# Vanishing Noise Variant Part D: Non-Faithful Character Escape Infrastructure

## Overview

This file contains Parts 25-27 of the vanishing noise framework, split from
`VanishingNoiseVariant.lean` for modularity.

**Part 25**: Non-Faithful Character Escape Infrastructure. Develops kernel
characterizations, factor ratio definition, and gap-kernel equivalence.

**Part 26**: NFCE for q=5 and small primes.

**Part 27**: Intersection Kernel Dichotomy. Coprime order zpowers have trivial
intersection; total NFCE failure implies confinement.
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter

/-! ## Part 25: Non-Faithful Character Escape Infrastructure

Infrastructure and reductions for `NonFaithfulCharacterEscape(q)` -- the sole
remaining open hypothesis for `UFDStrong(q)` at primes q >= 5.

Part 24 proved: for faithful (injective) characters, spectral gaps are
non-summable unconditionally. This closes UFDStrong(3) since every nontrivial
character of a prime-order group is faithful. For q >= 5, the unit group
(ZMod q)^x has composite order q-1, so non-faithful nontrivial characters exist.

This part develops:
1. Kernel characterizations for non-faithful nontrivial characters
2. Factor ratio definition and gap-kernel equivalence
3. NFCE <-> ratio kernel escape reduction
4. Kernel index bound
5. Connection to existing UFDStrong routes (MinFacRatioEscapeQual -> NFCE)
6. Landscape theorem summarizing Part 25
-/

section NonFaithfulCharacterEscapeInfra

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Task 1: Kernel characterizations -/

/-- A non-faithful nontrivial character has a nontrivial proper kernel:
    ker(chi) != bot (not injective) AND ker(chi) != top (nontrivial). -/
theorem nonfaithful_nontrivial_ker_proper (chi : (ZMod q)ˣ →* ℂˣ)
    (hchi : chi ≠ 1) (hnf : ¬IsFaithfulChar q chi) :
    chi.ker ≠ ⊥ ∧ chi.ker ≠ ⊤ := by
  constructor
  · rwa [Ne, MonoidHom.ker_eq_bot_iff]
  · rwa [Ne, MonoidHom.ker_eq_top_iff]

/-- ker(chi) != bot iff there exists a nontrivial kernel element. -/
theorem ker_ne_bot_iff_exists_nontrivial (chi : (ZMod q)ˣ →* ℂˣ) :
    chi.ker ≠ ⊥ ↔ ∃ u : (ZMod q)ˣ, u ≠ 1 ∧ chi u = 1 := by
  rw [Ne, Subgroup.eq_bot_iff_forall]
  push Not
  constructor
  · intro ⟨u, hu_mem, hu_ne⟩
    exact ⟨u, hu_ne, by rwa [MonoidHom.mem_ker] at hu_mem⟩
  · intro ⟨u, hu_ne, hu_ker⟩
    exact ⟨u, by rwa [MonoidHom.mem_ker], hu_ne⟩

/-! ### Task 2: Factor ratio and gap-kernel equivalence -/

/-- The ratio of the two lifted units (minFac and secondMinFac) at step n.
    When both are genuine units, this captures whether their chi-values coincide:
    chi(a) = chi(b) iff a * b^{-1} is in ker(chi). -/
noncomputable def factorRatio (n : ℕ) : (ZMod q)ˣ :=
  liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) *
  (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q))⁻¹

/-- chi(a) = chi(b) (as units) iff a * b^{-1} in ker(chi), for any CommGroup hom. -/
theorem chi_eq_iff_ratio_in_ker {G : Type*} [CommGroup G]
    (chi : G →* ℂˣ) (a b : G) :
    chi a = chi b ↔ a * b⁻¹ ∈ chi.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

/-- chi(a) = chi(b) as complex numbers iff a * b^{-1} in ker(chi). -/
theorem chi_coe_eq_iff_ratio_in_ker {G : Type*} [CommGroup G]
    (chi : G →* ℂˣ) (a b : G) :
    (chi a : ℂ) = (chi b : ℂ) ↔ a * b⁻¹ ∈ chi.ker := by
  rw [← chi_eq_iff_ratio_in_ker]
  exact Units.val_injective.eq_iff

/-- At a non-fallback step (raw card >= 2), the spectral gap is zero iff
    the character values at the two lifted units coincide (as complex numbers). -/
theorem gap_zero_iff_chi_eq (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 0 ↔
    (chi (liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)) : ℂ) =
    (chi (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)) : ℂ) := by
  set a := liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)
  set b := liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)
  have hne : a ≠ b := raw_card_two_implies_ne n hcard
  constructor
  · -- gap = 0 means norm = 1; contrapositive of meanCharValue_norm_lt_one_of_distinct
    intro hgap
    have hnorm : ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 1 := by linarith
    by_contra hdiff
    rw [paddedUnitSet_eq_raw_of_card n hcard] at hnorm
    have hlt := meanCharValue_norm_lt_one_of_distinct chi (rawTwoPointUnitSet (q := q) n) hcard
      ⟨a, liftToUnit_minFac_mem_raw n, b, liftToUnit_secondMinFac_mem_raw n, hdiff⟩
    linarith
  · -- chi(a) = chi(b) means mean = (chi(a) + chi(b))/2 = chi(a), which has norm 1
    intro heq
    rw [paddedUnitSet_eq_raw_of_card n hcard]
    simp only [meanCharValue, rawTwoPointUnitSet]
    rw [Finset.sum_pair hne, Finset.card_pair hne]
    rw [heq]
    have h1 : ‖((chi b : ℂ) + (chi b : ℂ)) / (2 : ℂ)‖ = 1 := by
      rw [show (chi b : ℂ) + (chi b : ℂ) = 2 * (chi b : ℂ) from by ring]
      rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
      exact char_norm_one_of_hom chi b
    linarith

/-- Gap = 0 iff the factor ratio lies in the kernel of chi (at non-fallback steps). -/
theorem gap_zero_iff_ratio_in_ker (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 0 ↔
    factorRatio (q := q) n ∈ chi.ker := by
  rw [gap_zero_iff_chi_eq n chi hcard]
  rw [show factorRatio (q := q) n =
    liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) *
    (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q))⁻¹ from rfl]
  exact chi_coe_eq_iff_ratio_in_ker chi _ _

/-! ### Task 3: Kernel confinement and ratio escape -/

/-- The factor ratio is eventually always in ker(chi). -/
def KernelConfinement (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  ∃ N₀, ∀ n, N₀ ≤ n → factorRatio (q := q) n ∈ chi.ker

/-- The factor ratio escapes ker(chi) infinitely often. -/
def RatioKernelEscape (q : ℕ) [Fact (Nat.Prime q)]
    (chi : (ZMod q)ˣ →* ℂˣ) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ factorRatio (q := q) n ∉ chi.ker

/-- Ratio escape is the negation of kernel confinement. -/
theorem kernel_escape_iff_not_confinement (chi : (ZMod q)ˣ →* ℂˣ) :
    RatioKernelEscape q chi ↔ ¬KernelConfinement q chi := by
  simp only [RatioKernelEscape, KernelConfinement]
  push Not
  rfl

/-- If the factor ratio escapes ker(chi) infinitely often AND cofinitely many steps
    are non-fallback, then spectral gaps are non-summable.
    Proof: ratio not in ker -> gap != 0 -> gap > 0 (nonneg). Infinitely many positive
    gaps from a function with finite range gives non-summability. -/
theorem ratio_escape_implies_gap_nonsummable (_hq3 : 2 < q)
    (chi : (ZMod q)ˣ →* ℂˣ) (_hchi : chi ≠ 1)
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card)
    (hescape : RatioKernelEscape q chi) :
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) := by
  obtain ⟨N₀, hN₀⟩ := hcofinite
  apply not_summable_of_frequently_pos_finite_range
  · exact fun n => paddedUnitSet_gap_nonneg chi n
  · exact gap_function_finite_range chi
  · intro N
    obtain ⟨n, hn, hratio⟩ := hescape (max N N₀)
    have hn_N : N ≤ n := le_of_max_le_left hn
    have hn_N₀ : N₀ ≤ n := le_of_max_le_right hn
    have hcard := hN₀ n hn_N₀
    have hgap_ne : 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ ≠ 0 := by
      intro heq
      exact hratio ((gap_zero_iff_ratio_in_ker n chi hcard).mp heq)
    exact ⟨n, hn_N, lt_of_le_of_ne (paddedUnitSet_gap_nonneg chi n) (Ne.symm hgap_ne)⟩

/-- RatioKernelEscape for all non-faithful nontrivial chi (+ cofinitely many non-fallback)
    implies NonFaithfulCharacterEscape.
    Proof: case split on infinitely many fallback vs cofinitely many non-fallback. -/
theorem nfce_of_ratio_escape_cofinite (hq3 : 2 < q)
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card)
    (h : ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar q chi →
      RatioKernelEscape q chi) :
    NonFaithfulCharacterEscape q := by
  intro chi hchi hnfaith
  exact ratio_escape_implies_gap_nonsummable hq3 chi hchi hcofinite (h chi hchi hnfaith)

/-- Summable gap + cofinitely many non-fallback steps implies kernel confinement.
    Proof: summable -> tendsto 0 -> eventually < min positive value of finite range
    -> eventually gap = 0 -> eventually ratio in ker. -/
theorem summable_implies_ratio_confined (chi : (ZMod q)ˣ →* ℂˣ)
    (hsum : Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖))
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    KernelConfinement q chi := by
  obtain ⟨N₀, hN₀⟩ := hcofinite
  -- summable nonneg => tendsto 0
  have htends := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htends
  -- The gap function has finite range
  have hfin := gap_function_finite_range (q := q) chi
  -- Extract positive values in the range
  set gapFn := fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖
  -- Case: are there any positive gap values at non-fallback steps beyond N₀?
  by_cases hexists_pos : ∃ n, N₀ ≤ n ∧ 0 < gapFn n
  · -- There exist positive values; use finite range to get a uniform positive lower bound
    set posRange := {x ∈ hfin.toFinset | (0 : ℝ) < x}
    have hne : posRange.Nonempty := by
      obtain ⟨n, _, hfn⟩ := hexists_pos
      exact ⟨gapFn n, by rw [Finset.mem_filter]; exact
        ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩⟩
    set δ := posRange.min' hne
    have hδ_pos : 0 < δ := by
      have hmem := Finset.min'_mem posRange hne
      exact (Finset.mem_filter.mp hmem).2
    -- Eventually gap < δ
    obtain ⟨N₁, hN₁⟩ := htends δ hδ_pos
    -- Beyond max(N₀, N₁), gaps must be 0 (can't be positive and < δ at same time)
    refine ⟨max N₀ N₁, fun n hn => ?_⟩
    have hn_N₀ := le_of_max_le_left hn
    have hn_N₁ := le_of_max_le_right hn
    have hcard := hN₀ n hn_N₀
    rw [← gap_zero_iff_ratio_in_ker n chi hcard]
    -- Show gap = 0 by contradiction: if > 0, it's >= δ but also < δ
    by_contra hne_zero
    have hpos : 0 < gapFn n := lt_of_le_of_ne (paddedUnitSet_gap_nonneg chi n) (Ne.symm hne_zero)
    have hge_delta : δ ≤ gapFn n := by
      apply Finset.min'_le
      rw [Finset.mem_filter]
      exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hpos⟩
    have hlt_delta : gapFn n < δ := by
      have h := hN₁ n hn_N₁
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (paddedUnitSet_gap_nonneg chi n)] at h
      exact h
    linarith
  · -- No positive gap values beyond N₀: all gaps are 0
    push Not at hexists_pos
    refine ⟨N₀, fun n hn => ?_⟩
    have hcard := hN₀ n hn
    rw [← gap_zero_iff_ratio_in_ker n chi hcard]
    exact le_antisymm (hexists_pos n hn) (paddedUnitSet_gap_nonneg chi n)

/-- NFCE failure implies some non-faithful nontrivial chi has summable gaps. -/
theorem nfce_failure_implies_summable (hfail : ¬NonFaithfulCharacterEscape q) :
    ∃ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 ∧ ¬IsFaithfulChar q chi ∧
      Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) := by
  simp only [NonFaithfulCharacterEscape, not_forall, Classical.not_not] at hfail
  obtain ⟨chi, hchi, hnf, hsum⟩ := hfail
  exact ⟨chi, hchi, hnf, hsum⟩

/-! ### Task 4: Kernel index bound -/

/-- For a nontrivial character, the kernel has index >= 2 in the unit group.
    Proof: chi != 1 means ker != top, and for finite groups index 1 <-> subgroup = top. -/
theorem ker_index_ge_two (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1) :
    2 ≤ chi.ker.index := by
  have h_ne_top : chi.ker ≠ ⊤ := by rwa [Ne, MonoidHom.ker_eq_top_iff]
  exact chi.ker.one_lt_index_of_ne_top h_ne_top

/-! ### Task 5: Connections to existing routes -/

/-- MinFacRatioEscapeQual implies NonFaithfulCharacterEscape.
    Proof: MinFacRatioEscapeQual gives non-summability for ALL nontrivial chi
    (including non-faithful ones), by composing through UFDStrong. -/
theorem qual_escape_implies_nfce (_hq3 : 2 < q)
    (hq : MinFacRatioEscapeQual q) :
    NonFaithfulCharacterEscape q := by
  intro chi hchi _hnfaith
  exact ratio_escape_implies_ufdStrong (qual_implies_quant hq) chi hchi

/-- The full chain: NFCE -> UFDStrong -> StochasticTwoPointMC. -/
theorem nfce_implies_variant_mc (hq3 : 2 < q)
    (hnfce : NonFaithfulCharacterEscape q) (a : (ZMod q)ˣ) :
    ∃ N, 0 < Multiset.count a (productMultiset (paddedUnitSet (q := q)) N) :=
  stochastic_two_point_mc_proved hq3 (nfce_implies_ufdStrong hq3 hnfce) a

/-! ### Task 6: Structural consequence: non-fallback gap = 0 iff ratio in ker -/

/-- At non-fallback steps, the gap is positive iff the ratio is NOT in ker(chi). -/
theorem gap_pos_iff_ratio_not_in_ker (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ ↔
    factorRatio (q := q) n ∉ chi.ker := by
  constructor
  · intro hpos hmem
    have heq := (gap_zero_iff_ratio_in_ker n chi hcard).mpr hmem
    linarith
  · intro hnotin
    have hne : 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ ≠ 0 := by
      intro heq
      exact hnotin ((gap_zero_iff_ratio_in_ker n chi hcard).mp heq)
    exact lt_of_le_of_ne (paddedUnitSet_gap_nonneg chi n) (Ne.symm hne)

/-! ### Task 7: Landscape theorem -/

/-- **Non-Faithful Character Escape Infrastructure Landscape**: summary of Part 25.

    PROVED:
    1. Kernel characterization: non-faithful nontrivial -> ker proper nontrivial
    2. Gap = 0 <-> factor ratio in kernel (at non-fallback steps)
    3. Kernel index >= 2 for nontrivial characters
    4. MinFacRatioEscapeQual -> NFCE
    5. NFCE -> UFDStrong -> StochasticTwoPointMC (full chain)
    6. Ratio escape + cofinitely non-fallback -> NFCE
    7. Summable gaps + cofinitely non-fallback -> kernel confinement -/
theorem nfce_infrastructure_landscape :
    -- 1. Non-faithful nontrivial => proper nontrivial kernel
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ),
      chi ≠ 1 → ¬IsFaithfulChar q' chi → chi.ker ≠ ⊥ ∧ chi.ker ≠ ⊤)
    ∧
    -- 2. Gap = 0 <-> ratio in kernel (at non-fallback steps)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ) (n : ℕ),
      2 ≤ (rawTwoPointUnitSet (q := q') n).card →
      (1 - ‖meanCharValue chi (paddedUnitSet (q := q') n)‖ = 0 ↔
       factorRatio (q := q') n ∈ chi.ker))
    ∧
    -- 3. Kernel index >= 2 for nontrivial characters
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ),
      chi ≠ 1 → 2 ≤ chi.ker.index)
    ∧
    -- 4. MinFacRatioEscapeQual -> NFCE
    (∀ (q' : ℕ) [Fact (Nat.Prime q')], 2 < q' →
      MinFacRatioEscapeQual q' → NonFaithfulCharacterEscape q')
    ∧
    -- 5. NFCE -> UFDStrong -> StochasticTwoPointMC (full chain)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')], 2 < q' →
      NonFaithfulCharacterEscape q' →
      ∀ (a : (ZMod q')ˣ), ∃ N,
        0 < Multiset.count a (productMultiset (paddedUnitSet (q := q')) N)) :=
  ⟨fun _ _ => nonfaithful_nontrivial_ker_proper,
   fun _ _ chi n hcard => gap_zero_iff_ratio_in_ker n chi hcard,
   fun _ _ => ker_index_ge_two,
   fun _ _ => qual_escape_implies_nfce,
   fun _ _ => nfce_implies_variant_mc⟩

end NonFaithfulCharacterEscapeInfra

/-! ## Part 26: NFCE(5) Infrastructure — Unconditional Variant MC for q = 5

For q = 5, the unit group (ZMod 5)ˣ has order 4 (cyclic, ≅ Z/4Z).
Characters partition as:
  - trivial (1 character)
  - faithful (injective, order 4): handled unconditionally by Part 24
  - non-faithful nontrivial (order 2, the quadratic character): exactly 1

The sole remaining open hypothesis for UFDStrong(5) is NonFaithfulCharacterEscape(5),
which reduces to: the factorRatio escapes the unique index-2 subgroup of (ZMod 5)ˣ
infinitely often.

### Main results
* `units_zmod_five_card` — Fintype.card (ZMod 5)ˣ = 4
* `natCard_units_zmod_five` — Nat.card (ZMod 5)ˣ = 4
* `nonfaithful_ker_card_eq_two_of_order_four` — non-faithful nontrivial chi in group of order 4 has |ker| = 2
* `nonfaithful_ker_index_eq_two_of_order_four` — same chi has ker.index = 2
* `ratio_escape_implies_nfce_five` — RatioKernelEscape for all non-faithful chi → NFCE(5)
* `ufdStrong_five_of_ratio_escape` — RatioKernelEscape for all non-faithful → UFDStrong(5)
* `variant_mc_five_of_ratio_escape` — same → StochasticTwoPointMC(5)
* `nfce_five_landscape` — 4-clause summary
-/

section NFCEFive

/-! ### Card computations for (ZMod 5)ˣ -/

/-- Fintype.card (ZMod 5)ˣ = 4, since φ(5) = 4 for prime 5. -/
theorem units_zmod_five_card :
    letI := Fact.mk (by decide : Nat.Prime 5)
    Fintype.card (ZMod 5)ˣ = 4 := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  rw [ZMod.card_units_eq_totient, Nat.totient_prime (by decide : Nat.Prime 5)]

/-- Nat.card (ZMod 5)ˣ = 4, since φ(5) = 4 for prime 5. -/
theorem natCard_units_zmod_five :
    letI := Fact.mk (by decide : Nat.Prime 5)
    Nat.card (ZMod 5)ˣ = 4 := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  rw [Nat.card_eq_fintype_card, units_zmod_five_card]

/-! ### Non-faithful characters in groups of order 4 -/

/-- In a finite commutative group of order 4, a non-faithful nontrivial character has
    kernel of cardinality 2. Proof: ker is proper nontrivial, so 1 < |ker| and
    ker.index ≥ 2. By Lagrange, |ker| · index = 4. Since both ≥ 2, both = 2. -/
theorem nonfaithful_ker_card_eq_two_of_order_four
    {G : Type*} [CommGroup G] [Fintype G]
    (hcard : Nat.card G = 4)
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) (hnf : ¬Function.Injective chi) :
    Nat.card chi.ker = 2 := by
  have hker_ne_bot : chi.ker ≠ ⊥ := by rwa [Ne, MonoidHom.ker_eq_bot_iff]
  have hker_ne_top : chi.ker ≠ ⊤ := by rwa [Ne, MonoidHom.ker_eq_top_iff]
  have hlag := chi.ker.card_mul_index; rw [hcard] at hlag
  have hidx_ge : 2 ≤ chi.ker.index := chi.ker.one_lt_index_of_ne_top hker_ne_top
  have hker_ge : 2 ≤ Nat.card chi.ker := by
    exact Nat.succ_le_of_lt (chi.ker.one_lt_card_iff_ne_bot.mpr hker_ne_bot)
  -- From |ker| * index = 4 with both >= 2, both must be 2
  have : Nat.card chi.ker ≤ 2 := by nlinarith
  omega

/-- In a finite commutative group of order 4, a non-faithful nontrivial character has
    kernel of index 2. Proof: dual of the cardinality result above. -/
theorem nonfaithful_ker_index_eq_two_of_order_four
    {G : Type*} [CommGroup G] [Fintype G]
    (hcard : Nat.card G = 4)
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) (hnf : ¬Function.Injective chi) :
    chi.ker.index = 2 := by
  have hlag := chi.ker.card_mul_index
  rw [hcard, nonfaithful_ker_card_eq_two_of_order_four hcard chi hchi hnf] at hlag
  omega

/-! ### NFCE(5) from ratio escape -/

/-- RatioKernelEscape for all non-faithful nontrivial characters implies NFCE(5),
    provided cofinitely many steps are non-fallback (raw card >= 2).

    This uses `ratio_escape_implies_gap_nonsummable` from Part 25 for the non-fallback
    case and `ufd_fallback_not_summable` for the fallback case. -/
theorem ratio_escape_implies_nfce_five
    (h : letI := Fact.mk (by decide : Nat.Prime 5)
         ∀ (chi : (ZMod 5)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar 5 chi →
           RatioKernelEscape 5 chi) :
    letI := Fact.mk (by decide : Nat.Prime 5)
    NonFaithfulCharacterEscape 5 := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  intro chi hchi hnf
  by_cases hfallback : ∀ N, ∃ n, N ≤ n ∧ ¬(2 ≤ (rawTwoPointUnitSet (q := 5) n).card)
  · exact ufd_fallback_not_summable (by norm_num : (2 : ℕ) < 5) chi hchi hfallback
  · push Not at hfallback
    obtain ⟨N₀, hN₀⟩ := hfallback
    exact ratio_escape_implies_gap_nonsummable (by norm_num : (2 : ℕ) < 5) chi hchi
      ⟨N₀, hN₀⟩ (h chi hchi hnf)

/-! ### UFDStrong(5) and StochasticTwoPointMC(5) from ratio escape -/

/-- If every non-faithful nontrivial character has its kernel escaped by the factor ratio
    infinitely often, then UFDStrong(5) holds.
    Proof: NFCE(5) follows from ratio escape (by the iff above), then
    NFCE(5) + unconditional faithful escape gives UFDStrong(5). -/
theorem ufdStrong_five_of_ratio_escape
    (h : letI := Fact.mk (by decide : Nat.Prime 5)
         ∀ (chi : (ZMod 5)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar 5 chi →
           RatioKernelEscape 5 chi) :
    letI := Fact.mk (by decide : Nat.Prime 5)
    UFDStrong 5 := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  exact nfce_implies_ufdStrong (by norm_num : (2 : ℕ) < 5) (ratio_escape_implies_nfce_five h)

/-- If every non-faithful nontrivial character has its kernel escaped by the factor ratio
    infinitely often, then StochasticTwoPointMC(5) holds: every element of (ZMod 5)ˣ
    is reachable by some selection path. -/
theorem variant_mc_five_of_ratio_escape
    (h : letI := Fact.mk (by decide : Nat.Prime 5)
         ∀ (chi : (ZMod 5)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar 5 chi →
           RatioKernelEscape 5 chi) :
    letI := Fact.mk (by decide : Nat.Prime 5)
    ∀ (a : (ZMod 5)ˣ), ∃ N,
      0 < Multiset.count a (productMultiset (paddedUnitSet (q := 5)) N) := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  exact stochastic_two_point_mc_proved (by norm_num : (2 : ℕ) < 5) (ufdStrong_five_of_ratio_escape h)

/-! ### Structural properties of (ZMod 5)ˣ for non-faithful characters -/

/-- For q = 5, any non-faithful nontrivial character has kernel of cardinality exactly 2.
    This follows from the general result for groups of order 4. -/
theorem nonfaithful_ker_card_two_at_five
    (chi : letI := Fact.mk (by decide : Nat.Prime 5); (ZMod 5)ˣ →* ℂˣ)
    (hchi : chi ≠ 1)
    (hnf : letI := Fact.mk (by decide : Nat.Prime 5); ¬IsFaithfulChar 5 chi) :
    letI := Fact.mk (by decide : Nat.Prime 5)
    Nat.card chi.ker = 2 := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  exact nonfaithful_ker_card_eq_two_of_order_four natCard_units_zmod_five chi hchi hnf

/-- For q = 5, any non-faithful nontrivial character has kernel of index exactly 2.
    The coset structure of the kernel partitions (ZMod 5)ˣ into exactly 2 classes:
    the kernel elements (quadratic residues) and their complement (non-residues). -/
theorem nonfaithful_ker_index_two_at_five
    (chi : letI := Fact.mk (by decide : Nat.Prime 5); (ZMod 5)ˣ →* ℂˣ)
    (hchi : chi ≠ 1)
    (hnf : letI := Fact.mk (by decide : Nat.Prime 5); ¬IsFaithfulChar 5 chi) :
    letI := Fact.mk (by decide : Nat.Prime 5)
    chi.ker.index = 2 := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  exact nonfaithful_ker_index_eq_two_of_order_four natCard_units_zmod_five chi hchi hnf

/-- At a non-fallback step, factor ratio NOT in ker(chi) means the ratio is in the
    non-identity coset of ker(chi). For q = 5 with non-faithful chi, this means the
    ratio is a quadratic non-residue mod 5 (relative to the character's kernel). -/
theorem ratio_escape_iff_gap_pos_five (n : ℕ)
    (chi : letI := Fact.mk (by decide : Nat.Prime 5); (ZMod 5)ˣ →* ℂˣ)
    (hcard : letI := Fact.mk (by decide : Nat.Prime 5);
      2 ≤ (rawTwoPointUnitSet (q := 5) n).card) :
    letI := Fact.mk (by decide : Nat.Prime 5)
    (factorRatio (q := 5) n ∉ chi.ker ↔
     0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := 5) n)‖) := by
  letI : Fact (Nat.Prime 5) := Fact.mk (by decide)
  exact (gap_pos_iff_ratio_not_in_ker n chi hcard).symm

/-! ### Landscape theorem -/

/-- **NFCE(5) Infrastructure Landscape**: summary of Part 26.

    PROVED:
    1. units_zmod_five_card: |(ZMod 5)ˣ| = 4
    2. nonfaithful_ker_card_two_at_five: non-faithful nontrivial chi has |ker| = 2
    3. ratio_escape_implies_nfce_five: ratio escape for all non-faithful chi → NFCE(5)
    4. variant_mc_five_of_ratio_escape: ratio escape → StochasticTwoPointMC(5)

    The sole remaining hypothesis for variant MC(5) is:
    every non-faithful nontrivial character of (ZMod 5)ˣ has its kernel
    escaped by the factor ratio infinitely often. Since |(ZMod 5)ˣ| = 4 and
    non-faithful nontrivial characters have ker.index = 2, this means:
    the factor ratio is a quadratic non-residue mod 5 (relative to the unique
    index-2 subgroup) at infinitely many steps. -/
theorem nfce_five_landscape :
    -- 1. |(ZMod 5)ˣ| = 4
    (letI := Fact.mk (by decide : Nat.Prime 5); Fintype.card (ZMod 5)ˣ = 4)
    ∧
    -- 2. Non-faithful nontrivial chi of (ZMod 5)ˣ has ker of cardinality 2
    (letI := Fact.mk (by decide : Nat.Prime 5);
     ∀ (chi : (ZMod 5)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar 5 chi →
       Nat.card chi.ker = 2)
    ∧
    -- 3. Ratio escape for all non-faithful → NFCE(5)
    (letI := Fact.mk (by decide : Nat.Prime 5);
     (∀ (chi : (ZMod 5)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar 5 chi →
       RatioKernelEscape 5 chi) →
     NonFaithfulCharacterEscape 5)
    ∧
    -- 4. Ratio escape → UFDStrong(5) → StochasticTwoPointMC(5)
    (letI := Fact.mk (by decide : Nat.Prime 5);
     (∀ (chi : (ZMod 5)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar 5 chi →
       RatioKernelEscape 5 chi) →
     ∀ (a : (ZMod 5)ˣ), ∃ N,
       0 < Multiset.count a (productMultiset (paddedUnitSet (q := 5)) N)) :=
  ⟨units_zmod_five_card,
   nonfaithful_ker_card_two_at_five,
   ratio_escape_implies_nfce_five,
   variant_mc_five_of_ratio_escape⟩

end NFCEFive

/-! ## Part 27: Intersection Kernel Dichotomy

### Mathematical content

If NonFaithfulCharacterEscape fails for ALL non-faithful nontrivial characters
simultaneously, then KernelConfinement holds for all of them (from Part 25).
The factor ratio is then eventually in the intersection of all such kernels.

The key GROUP-THEORETIC FACT: In a finite group, if two subgroups have coprime
orders, their intersection is trivial (Mathlib: `Subgroup.inf_eq_bot_of_coprime`).
Combined with Cauchy's theorem, when |G| has >= 2 distinct prime factors, there
exist subgroups of distinct prime orders p_1, p_2 with trivial intersection.

For CYCLIC groups, every subgroup is a kernel of some character. This gives:
if the factor ratio is in the kernel of every non-faithful nontrivial character,
and |G| has >= 2 distinct prime factors, then the factor ratio = 1.

This yields a DICHOTOMY: Either NFCE(q) holds, or the factor ratio is
eventually the identity element. The dichotomy is conditional on
`NonFaithfulCharSeparation` (non-faithful characters separate points in
cyclic groups with composite order).

### Main results

* `coprime_order_zpowers_inf_bot` -- zpowers with coprime orders intersect trivially
* `mem_both_zpowers_coprime_eq_one` -- element in both coprime-order zpowers is 1
* `NonFaithfulCharSeparation` -- open Prop (character separation by non-faithful chars)
* `total_confinement_implies_ratio_one` -- all confined + separation -> ratio = 1
* `nfce_or_ratio_eventually_one` -- the main dichotomy
* `intersection_kernel_landscape` -- summary theorem
-/

section IntersectionKernelDichotomy

/-! ### Group-theoretic infrastructure -/

/-- In a finite group, zpowers of elements with coprime orders have trivial intersection.
    This is a direct application of `Subgroup.inf_eq_bot_of_coprime`. -/
theorem coprime_order_zpowers_inf_bot
    {G : Type*} [Group G] [Fintype G]
    {x₁ x₂ : G} (hcop : Nat.Coprime (orderOf x₁) (orderOf x₂)) :
    Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
  apply Subgroup.inf_eq_bot_of_coprime
  rwa [Nat.card_zpowers, Nat.card_zpowers]

/-- If g belongs to both zpowers(x₁) and zpowers(x₂) where x₁ and x₂ have
    coprime orders, then g = 1. -/
theorem mem_both_zpowers_coprime_eq_one
    {G : Type*} [Group G] [Fintype G]
    {x₁ x₂ g : G}
    (hcop : Nat.Coprime (orderOf x₁) (orderOf x₂))
    (h₁ : g ∈ Subgroup.zpowers x₁)
    (h₂ : g ∈ Subgroup.zpowers x₂) :
    g = 1 := by
  have hmem : g ∈ Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ :=
    Subgroup.mem_inf.mpr ⟨h₁, h₂⟩
  rw [coprime_order_zpowers_inf_bot hcop] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- By Cauchy's theorem, for each prime p dividing |G|, there exists an element
    of order exactly p. The subgroup zpowers of this element has order p. -/
theorem exists_zpowers_of_prime_order
    {G : Type*} [Group G] [Fintype G]
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Fintype.card G) :
    ∃ x : G, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card p hdvd

/-- If |G| has two distinct prime factors p₁, p₂, then there exist elements g₁, g₂
    with coprime orders p₁, p₂. Hence zpowers(g₁) ⊓ zpowers(g₂) = ⊥,
    and any element in both subgroups is 1. -/
theorem exists_coprime_order_pair
    {G : Type*} [Group G] [Fintype G]
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂)
    (hd₁ : p₁ ∣ Fintype.card G) (hd₂ : p₂ ∣ Fintype.card G) :
    ∃ g₁ g₂ : G, orderOf g₁ = p₁ ∧ orderOf g₂ = p₂ ∧
      Subgroup.zpowers g₁ ⊓ Subgroup.zpowers g₂ = ⊥ := by
  obtain ⟨g₁, hg₁⟩ := exists_zpowers_of_prime_order hp₁ hd₁
  obtain ⟨g₂, hg₂⟩ := exists_zpowers_of_prime_order hp₂ hd₂
  exact ⟨g₁, g₂, hg₁, hg₂, coprime_order_zpowers_inf_bot (by rwa [hg₁, hg₂, Nat.coprime_primes hp₁ hp₂])⟩

/-- If g is in a subgroup of prime order p, then orderOf(g) divides p,
    so orderOf(g) = 1 or orderOf(g) = p. -/
theorem orderOf_mem_zpowers_prime
    {G : Type*} [Group G] [Fintype G]
    {x g : G} (hp : (orderOf x).Prime) (hg : g ∈ Subgroup.zpowers x) :
    orderOf g = 1 ∨ orderOf g = orderOf x := by
  have hdvd := orderOf_dvd_of_mem_zpowers hg
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · left; exact h
  · right; exact h

/-! ### Non-faithful character separation (PROVED)

In a finite commutative group G with |G| having >= 2 distinct prime factors, for
any g != 1, there exists a non-faithful nontrivial character chi with chi(g) != 1.

**Proof**: By Cauchy's theorem, there exist subgroups H1, H2 of coprime prime
orders p1, p2. Their intersection is trivial (coprime orders). For g != 1,
g lies outside at least one Hi. Taking the quotient G/Hi, the image of g is
nontrivial, so character duality (`MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`)
gives a character of G/Hi separating the image from 1. Composing with the quotient
map gives a character of G whose kernel contains Hi (hence non-faithful) and
separates g from 1. -/

/-- **NonFaithfulCharSeparation**: In a finite commutative group G with |G| having
    >= 2 distinct prime factors, for any g != 1, there exists a non-faithful
    nontrivial character chi : G ->* C^x with chi(g) != 1.

    PROVED for groups with 2 distinct prime factors dividing |G|.
    See `nonFaithfulCharSeparation_of_two_prime_factors`.
    Specialized to (ZMod q)^x via `nonFaithfulCharSeparation_units_zmod`
    when q-1 has an odd prime factor (all primes except 2, 3, 5, Fermat primes).

    NOTE: This is FALSE for groups whose order is a prime power (e.g. Z/4Z),
    since the unique non-faithful nontrivial character maps the order-p^(k-1)
    element to 1. -/
def NonFaithfulCharSeparation (G : Type*) [CommGroup G] [Fintype G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ chi : G →* ℂˣ, chi ≠ 1 ∧ ¬Function.Injective chi ∧ chi g ≠ 1

/-! ### Proof of NonFaithfulCharSeparation

For a finite commutative group G whose order has >= 2 distinct prime factors,
NonFaithfulCharSeparation holds. The proof constructs a non-faithful separating
character via quotients:

1. By Cauchy's theorem, |G| having 2 distinct prime factors p1, p2 gives
   subgroups H1, H2 of orders p1, p2 respectively.
2. Since H1 cap H2 = {1} (coprime orders), any g != 1 lies outside at least one Hi.
3. For g not in Hi, the image of g in G/Hi is nontrivial.
4. Character duality (exists_apply_ne_one_of_hasEnoughRootsOfUnity) gives a
   character chi_q of G/Hi separating the image of g from 1.
5. Composing chi_q with the quotient map gives a character of G whose kernel
   contains Hi (hence non-faithful, since |Hi| >= 2) and separates g from 1. -/

/-- A non-faithful character separating g from 1 exists whenever g lies outside
    a nontrivial normal subgroup H. The character factors through G/H. -/
private theorem exists_nonfaithful_separating_char
    {G : Type*} [CommGroup G] [Fintype G]
    {H : Subgroup G} {g : G}
    (_hg_ne : g ≠ 1) (hg_notin : g ∉ H) (hH_card : 1 < Fintype.card H) :
    ∃ chi : G →* ℂˣ, chi ≠ 1 ∧ ¬Function.Injective chi ∧ chi g ≠ 1 := by
  -- The image of g in G/H is nontrivial since g not in H
  have himg_ne : (QuotientGroup.mk' H g : G ⧸ H) ≠ 1 :=
    mt (by simp [QuotientGroup.eq_one_iff]) hg_notin
  -- G/H is a finite commutative group with enough roots of unity in C
  haveI : Fintype (G ⧸ H) := Quotient.fintype _
  haveI : DecidableEq (G ⧸ H) := Classical.decEq _
  -- exponent of (G/H)^x divides |G/H| which is finite
  haveI : NeZero (Monoid.exponent (G ⧸ H)ˣ : ℂ) := by
    constructor
    have hexp_pos : 0 < Monoid.exponent (G ⧸ H)ˣ :=
      Monoid.exponent_pos_of_exists (Fintype.card (G ⧸ H)ˣ) Fintype.card_pos
        (fun g => pow_card_eq_one)
    exact Nat.cast_ne_zero.mpr (by omega)
  -- Get a MulChar on G/H separating the image of g from 1
  obtain ⟨chi_q, hchi_q⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ H) ℂ himg_ne
  -- Convert to G ->* C* via composition with the quotient map
  let psi : (G ⧸ H) →* ℂˣ := mulCharToHom chi_q
  let phi : G →* ℂˣ := psi.comp (QuotientGroup.mk' H)
  refine ⟨phi, ?_, ?_, ?_⟩
  · -- phi is nontrivial (since phi g != 1, proved below)
    intro heq
    apply hchi_q
    have : phi g = 1 := by rw [heq]; simp [MonoidHom.one_apply]
    show chi_q (QuotientGroup.mk' H g) = 1
    have hval : (psi (QuotientGroup.mk' H g) : ℂ) = chi_q (QuotientGroup.mk' H g) :=
      mulCharToHom_apply chi_q (QuotientGroup.mk' H g)
    have hval2 : (phi g : ℂ) = (psi (QuotientGroup.mk' H g) : ℂ) := rfl
    rw [← hval]
    rw [← hval2, this]
    simp [Units.val_one]
  · -- phi is not injective: H is in the kernel and has > 1 elements
    intro hinj
    -- Pick a nontrivial element h of H
    haveI : Nontrivial H := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      exact hH_card
    obtain ⟨⟨h, hh_mem⟩, hh_ne⟩ := exists_ne (1 : H)
    -- h is in the kernel of phi, since mk' H h = 1
    have hmk : (QuotientGroup.mk' H h : G ⧸ H) = 1 := by
      simp [QuotientGroup.eq_one_iff, hh_mem]
    have hker : phi h = 1 := by
      show psi (QuotientGroup.mk' H h) = 1
      rw [hmk, map_one]
    -- But phi is injective and phi 1 = 1, so h = 1
    have h_eq_one : h = 1 := hinj (hker.trans (map_one phi).symm)
    -- Contradiction: ⟨h, hh_mem⟩ ≠ 1 but h = 1
    exact hh_ne (Subtype.ext h_eq_one)
  · -- phi g != 1: follows from chi_q separating the image of g
    intro heq
    apply hchi_q
    have hval : (psi (QuotientGroup.mk' H g) : ℂ) = chi_q (QuotientGroup.mk' H g) :=
      mulCharToHom_apply chi_q (QuotientGroup.mk' H g)
    have hval2 : (phi g : ℂ) = (psi (QuotientGroup.mk' H g) : ℂ) := rfl
    rw [← hval, ← hval2]
    rw [show (phi g : ℂ) = ((1 : ℂˣ) : ℂ) from by rw [heq]]
    simp [Units.val_one]

/-- **NonFaithfulCharSeparation** holds for any finite commutative group whose
    order has at least 2 distinct prime factors. -/
theorem nonFaithfulCharSeparation_of_two_prime_factors
    {G : Type*} [CommGroup G] [Fintype G]
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂)
    (hd₁ : p₁ ∣ Fintype.card G) (hd₂ : p₂ ∣ Fintype.card G) :
    NonFaithfulCharSeparation G := by
  intro g hg
  -- Get elements of order p₁ and p₂
  obtain ⟨x₁, hx₁⟩ := exists_zpowers_of_prime_order hp₁ hd₁
  obtain ⟨x₂, hx₂⟩ := exists_zpowers_of_prime_order hp₂ hd₂
  -- Their zpowers have coprime orders and trivial intersection
  have hcop : Nat.Coprime (orderOf x₁) (orderOf x₂) := by
    rwa [hx₁, hx₂, Nat.coprime_primes hp₁ hp₂]
  -- g is not in both subgroups (since their intersection is trivial)
  have hbot := coprime_order_zpowers_inf_bot hcop
  have : g ∉ Subgroup.zpowers x₁ ∨ g ∉ Subgroup.zpowers x₂ := by
    by_contra h
    push Not at h
    have hmem : g ∈ Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ :=
      Subgroup.mem_inf.mpr ⟨h.1, h.2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hg hmem
  -- Use the subgroup that g lies outside of
  rcases this with hnotin | hnotin
  · have : 1 < Fintype.card (Subgroup.zpowers x₁) := by
      rw [show Fintype.card (Subgroup.zpowers x₁) = orderOf x₁ from Fintype.card_zpowers, hx₁]
      exact hp₁.one_lt
    exact exists_nonfaithful_separating_char hg hnotin this
  · have : 1 < Fintype.card (Subgroup.zpowers x₂) := by
      rw [show Fintype.card (Subgroup.zpowers x₂) = orderOf x₂ from Fintype.card_zpowers, hx₂]
      exact hp₂.one_lt
    exact exists_nonfaithful_separating_char hg hnotin this

/-- For prime q where q-1 has an odd prime factor (equivalently, q-1 is NOT a
    power of 2), NonFaithfulCharSeparation holds for (ZMod q)^x.
    This covers all primes except q = 2, 3, 5, and Fermat primes (q = 2^k + 1).
    For Fermat primes, |(ZMod q)^x| = 2^k has only one prime factor, and
    NonFaithfulCharSeparation is FALSE (same issue as q = 5). -/
theorem nonFaithfulCharSeparation_units_zmod
    {q : ℕ} [hqp : Fact (Nat.Prime q)]
    {p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2) (hp_dvd : p ∣ q - 1) :
    NonFaithfulCharSeparation (ZMod q)ˣ := by
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hqp.out]
  have h2dvd : 2 ∣ Fintype.card (ZMod q)ˣ := by
    rw [hcard]
    have hq2 : q ≠ 2 := by
      intro heq; subst heq
      have h1 : p ∣ 1 := hp_dvd
      have h2 := Nat.le_of_dvd Nat.one_pos h1
      have h3 := hp.one_lt
      omega
    obtain ⟨k, hk⟩ := hqp.out.odd_of_ne_two hq2
    omega
  have hp_dvd_card : p ∣ Fintype.card (ZMod q)ˣ := hcard ▸ hp_dvd
  exact nonFaithfulCharSeparation_of_two_prime_factors
    Nat.prime_two hp (Ne.symm hp_odd) h2dvd hp_dvd_card

/-! ### Connection to kernel confinement -/

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-- `TotalKernelConfinement q` means that for every non-faithful nontrivial character,
    the factor ratio is eventually in the kernel. This is STRICTLY STRONGER than
    the negation of NFCE (which only guarantees existence of one such character).
    TotalKernelConfinement is the condition under which the intersection argument
    gives factorRatio = 1. -/
def TotalKernelConfinement (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar q chi →
    KernelConfinement q chi

/-- `TotalNFCEFailure q` means that EVERY non-faithful nontrivial character has
    summable spectral gaps. This is strictly stronger than `¬NFCE(q)`.
    Combined with cofinitely many non-fallback steps, it implies
    TotalKernelConfinement. -/
def TotalNFCEFailure (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 → ¬IsFaithfulChar q chi →
    Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)

/-- Total NFCE failure + cofinitely many non-fallback steps implies
    total kernel confinement. Each character's summable gaps give
    kernel confinement via `summable_implies_ratio_confined`. -/
theorem total_nfce_failure_implies_confinement
    (hfail : TotalNFCEFailure q)
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    TotalKernelConfinement q := by
  intro chi hchi hnfaith
  exact summable_implies_ratio_confined chi (hfail chi hchi hnfaith) hcofinite

/-- Under total kernel confinement, factorRatio is eventually in the kernel
    of every non-faithful nontrivial character simultaneously.
    Proof: take the max threshold over all (finitely many) characters. -/
theorem total_confinement_eventually_in_all_kernels
    (htotal : TotalKernelConfinement q) :
    ∃ N₀, ∀ n, N₀ ≤ n → ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
      ¬IsFaithfulChar q chi → factorRatio (q := q) n ∈ chi.ker := by
  -- The set of characters is finite
  haveI : Fintype ((ZMod q)ˣ →* ℂˣ) := Fintype.ofFinite _
  -- For each non-faithful nontrivial chi, extract its threshold
  -- Use Finset.sup over all characters to get a uniform threshold
  let thresholds : ((ZMod q)ˣ →* ℂˣ) → ℕ := fun chi =>
    if h : chi ≠ 1 ∧ ¬IsFaithfulChar q chi then
      (htotal chi h.1 h.2).choose
    else 0
  use Finset.sup Finset.univ thresholds
  intro n hn chi hchi hnfaith
  -- thresholds chi = (htotal chi hchi hnfaith).choose, by dif_pos
  have hle : thresholds chi ≤ Finset.sup Finset.univ thresholds :=
    Finset.le_sup (Finset.mem_univ chi)
  -- The threshold for chi is specifically the choose of the confinement proof
  have hN_spec := (htotal chi hchi hnfaith).choose_spec
  have hthresh_eq : thresholds chi = (htotal chi hchi hnfaith).choose := by
    show (if h : chi ≠ 1 ∧ ¬IsFaithfulChar q chi then
      (htotal chi h.1 h.2).choose else 0) = _
    rw [dif_pos (And.intro hchi hnfaith)]
  rw [hthresh_eq] at hle
  exact hN_spec n (le_trans hle hn)

/-- Under NonFaithfulCharSeparation and TotalKernelConfinement, the factor ratio
    is eventually 1 (the identity in (ZMod q)ˣ).

    Proof: By `total_confinement_eventually_in_all_kernels`, beyond some N₀,
    factorRatio ∈ ker(chi) for all non-faithful nontrivial chi.
    If factorRatio ≠ 1, NonFaithfulCharSeparation gives a non-faithful nontrivial
    chi with chi(factorRatio) ≠ 1, contradicting membership in ker(chi). -/
theorem total_confinement_implies_ratio_one
    (hsep : NonFaithfulCharSeparation (ZMod q)ˣ)
    (htotal : TotalKernelConfinement q) :
    ∃ N₀, ∀ n, N₀ ≤ n → factorRatio (q := q) n = 1 := by
  obtain ⟨N₀, hN₀⟩ := total_confinement_eventually_in_all_kernels htotal
  exact ⟨N₀, fun n hn => by
    by_contra hratio_ne
    obtain ⟨chi, hchi, hnfaith, hsep_val⟩ := hsep _ hratio_ne
    have hmem := hN₀ n hn chi hchi (by rwa [IsFaithfulChar])
    rw [MonoidHom.mem_ker] at hmem
    exact hsep_val hmem⟩

/-! ### Per-character dichotomy -/

/-- Per-character dichotomy: for each non-faithful nontrivial character,
    either its gaps are non-summable OR the factor ratio is eventually
    confined to its kernel. This uses `summable_implies_ratio_confined`
    from Part 25. -/
theorem per_char_nonsummable_or_confined
    (chi : (ZMod q)ˣ →* ℂˣ)
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    (¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)) ∨
    KernelConfinement q chi := by
  by_cases hsum : Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)
  · right; exact summable_implies_ratio_confined chi hsum hcofinite
  · left; exact hsum

/-! ### Fallback dichotomy -/

/-- If there are infinitely many fallback steps, NFCE holds (and hence UFDStrong).
    This is the easy case where ufd_fallback_not_summable gives non-summability for
    every nontrivial character. -/
theorem nfce_of_infinite_fallback (hq3 : 2 < q)
    (hfallback : ∀ N, ∃ n, N ≤ n ∧ ¬(2 ≤ (rawTwoPointUnitSet (q := q) n).card)) :
    NonFaithfulCharacterEscape q := by
  intro chi hchi _hnfaith
  exact ufd_fallback_not_summable hq3 chi hchi hfallback

/-- **The full dichotomy**: For prime q >= 3 with NonFaithfulCharSeparation,
    either:
    (A) NonFaithfulCharacterEscape(q) holds (and hence UFDStrong(q)), or
    (B) TotalKernelConfinement(q) holds and factorRatio is eventually 1.

    When there are infinitely many fallback steps, case (A) holds
    unconditionally. When cofinitely many steps are non-fallback,
    the per-character dichotomy gives: for each chi, either non-summable
    or confined. Whether ALL are non-summable (NFCE) or ALL are confined (TKC)
    depends on the specific dynamics. Under TotalNFCEFailure (all summable),
    we get TKC and ratio -> 1.

    This theorem shows: TotalNFCEFailure + cofinite + separation -> ratio = 1. -/
theorem total_nfce_failure_implies_ratio_one
    (hsep : NonFaithfulCharSeparation (ZMod q)ˣ)
    (hfail : TotalNFCEFailure q)
    (hcofinite : ∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    ∃ N₀, ∀ n, N₀ ≤ n → factorRatio (q := q) n = 1 :=
  total_confinement_implies_ratio_one hsep
    (total_nfce_failure_implies_confinement hfail hcofinite)

/-! ### Landscape theorem -/

set_option linter.unusedVariables false in
/-- **Intersection Kernel Dichotomy Landscape**: summary of Part 27.

    ALL PROVED:
    1. coprime_order_zpowers_inf_bot: coprime-order subgroups have trivial intersection
    2. exists_coprime_order_pair: groups with 2+ prime factors have coprime-order subgroups
    3. total_nfce_failure_implies_confinement: TotalNFCEFailure + cofinite -> TKC
    4. total_confinement_implies_ratio_one: TKC + separation -> ratio = 1
    5. per_char_nonsummable_or_confined: per-character dichotomy
    6. nonFaithfulCharSeparation_of_two_prime_factors: NFCS for groups with 2+ prime factors
    7. nonFaithfulCharSeparation_units_zmod: NFCS for (ZMod q)^x when q-1 has odd prime factor

    NonFaithfulCharSeparation is NOW PROVED for groups with >= 2 distinct prime
    factors dividing |G|. For (ZMod q)^x, this requires q-1 to have an odd prime
    factor, which excludes Fermat primes. For Fermat primes, the intersection
    dichotomy does not apply (NFCS is false for prime-power-order groups). -/
theorem intersection_kernel_landscape :
    -- 1. Coprime-order zpowers intersect trivially
    (∀ (G : Type*) [inst1 : Group G] [inst2 : Fintype G] (x₁ x₂ : G),
      Nat.Coprime (orderOf x₁) (orderOf x₂) →
      @Subgroup.zpowers G inst1 x₁ ⊓ @Subgroup.zpowers G inst1 x₂ = ⊥)
    ∧
    -- 2. Total NFCE failure + cofinite non-fallback -> TKC
    (∀ (q' : ℕ) [Fact (Nat.Prime q')],
      TotalNFCEFailure q' →
      (∃ N₀, ∀ n, N₀ ≤ n → 2 ≤ (rawTwoPointUnitSet (q := q') n).card) →
      TotalKernelConfinement q')
    ∧
    -- 3. TKC + separation -> ratio = 1
    (∀ (q' : ℕ) [Fact (Nat.Prime q')],
      NonFaithfulCharSeparation (ZMod q')ˣ →
      TotalKernelConfinement q' →
      ∃ N₀, ∀ n, N₀ ≤ n → factorRatio (q := q') n = 1) :=
  ⟨fun _ _ _ _ _ => coprime_order_zpowers_inf_bot,
   fun _ _ => total_nfce_failure_implies_confinement,
   fun _ _ => total_confinement_implies_ratio_one⟩

end IntersectionKernelDichotomy

/-! ## Part 28: Quotient Character Lift and NFCE Reduction

### Mathematical content

For a non-faithful nontrivial character χ : (ZMod q)ˣ →* ℂˣ, the kernel ker(χ) is
a proper nontrivial normal subgroup. The character factors through the quotient:
χ = χ̄ ∘ π where π : G → G/ker(χ) is the quotient map and χ̄ is the induced
character on the quotient group.

The key fact: χ̄ is FAITHFUL (injective) on G/ker(χ). This follows from
`QuotientGroup.ker_lift` + `QuotientGroup.map_mk'_self` which shows the
kernel of the lifted map is trivial.

This reduces NonFaithfulCharacterEscape to: for each non-faithful nontrivial χ,
the IMAGE of factorRatio in G/ker(χ) escapes {1} infinitely often. Since χ̄ is
faithful on the (smaller) quotient group, the faithful escape result from Part 24
applies to the quotient.

### Main results

* `quotientChar` — induced character on G/ker(χ), well-defined by universal property
* `quotientChar_faithful` — quotient character is injective
* `quotientChar_apply` — χ(g) = quotientChar(π(g))
* `quotient_factorRatio_eq_one_iff` — π(factorRatio) = 1 ↔ factorRatio ∈ ker(χ)
* `quotient_card_ge_two` — |G/ker(χ)| ≥ 2 for nontrivial χ
* `quotient_escape_landscape` — summary theorem
-/

section QuotientCharacterLift

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Task 1: Quotient character definition -/

/-- A character χ : G →* ℂˣ factors through the quotient G/ker(χ).
    The induced character χ̄ on the quotient is defined by
    χ̄(g · ker(χ)) = χ(g), which is well-defined since ker(χ) ≤ ker(χ). -/
noncomputable def quotientChar (chi : (ZMod q)ˣ →* ℂˣ) :
    (ZMod q)ˣ ⧸ chi.ker →* ℂˣ :=
  QuotientGroup.lift chi.ker chi le_rfl

/-! ### Task 2: Quotient character is faithful -/

/-- The quotient character is faithful (injective): ker(χ̄) = ⊥ in G/ker(χ).
    Proof: by `ker_lift`, ker(χ̄) = π(ker(χ)) where π is the quotient map.
    By `map_mk'_self`, π(ker(χ)) = ⊥. -/
theorem quotientChar_faithful (chi : (ZMod q)ˣ →* ℂˣ) :
    Function.Injective (quotientChar chi) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  show (QuotientGroup.lift chi.ker chi le_rfl).ker = ⊥
  rw [QuotientGroup.ker_lift]
  exact QuotientGroup.map_mk'_self chi.ker

/-! ### Task 3: Quotient character recovers original character -/

/-- χ(g) = quotientChar(π(g)) where π is the quotient map. -/
theorem quotientChar_apply (chi : (ZMod q)ˣ →* ℂˣ) (g : (ZMod q)ˣ) :
    quotientChar chi (QuotientGroup.mk' chi.ker g) = chi g :=
  rfl

/-- χ = quotientChar ∘ π as functions. -/
theorem quotientChar_comp_mk (chi : (ZMod q)ˣ →* ℂˣ) :
    (quotientChar chi).comp (QuotientGroup.mk' chi.ker) = chi := by
  show (QuotientGroup.lift chi.ker chi le_rfl).comp (QuotientGroup.mk' chi.ker) = chi
  exact QuotientGroup.lift_comp_mk' chi.ker chi le_rfl

/-! ### Task 4: Quotient projection and kernel membership -/

/-- The quotient projection of factorRatio is trivial iff factorRatio ∈ ker(χ). -/
theorem quotient_factorRatio_eq_one_iff (chi : (ZMod q)ˣ →* ℂˣ) (n : ℕ) :
    QuotientGroup.mk' chi.ker (factorRatio (q := q) n) = 1 ↔
    factorRatio (q := q) n ∈ chi.ker :=
  QuotientGroup.eq_one_iff _

/-- The quotient projection of factorRatio is nontrivial iff factorRatio ∉ ker(χ). -/
theorem quotient_factorRatio_ne_one_iff (chi : (ZMod q)ˣ →* ℂˣ) (n : ℕ) :
    QuotientGroup.mk' chi.ker (factorRatio (q := q) n) ≠ 1 ↔
    factorRatio (q := q) n ∉ chi.ker := by
  rw [ne_eq, quotient_factorRatio_eq_one_iff]

/-! ### Task 5: Quotient group cardinality bound -/

/-- The quotient group (ZMod q)ˣ / ker(χ) has cardinality at least 2 for nontrivial χ.
    Proof: χ ≠ 1 implies ker(χ) ≠ ⊤, so ker(χ).index ≥ 2, and
    |G/ker(χ)| = ker(χ).index. -/
theorem quotient_card_ge_two (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1) :
    2 ≤ Nat.card ((ZMod q)ˣ ⧸ chi.ker) := by
  have h_ne_top : chi.ker ≠ ⊤ := by rwa [Ne, MonoidHom.ker_eq_top_iff]
  have h_index := chi.ker.one_lt_index_of_ne_top h_ne_top
  rwa [Subgroup.index_eq_card] at h_index

/-- The quotient group cardinality divides the unit group cardinality. -/
theorem quotient_card_dvd (chi : (ZMod q)ˣ →* ℂˣ) :
    Nat.card ((ZMod q)ˣ ⧸ chi.ker) ∣ Nat.card (ZMod q)ˣ := by
  rw [← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_card chi.ker

/-! ### Task 6: Spectral gap via quotient character -/

/-- The character sum of χ over a finset S equals the character sum of the
    quotient character over the same set via the quotient map.
    Since χ(s) = χ̄(π(s)) for all s, the sums are literally equal. -/
theorem chi_sum_eq_quotientChar_sum (chi : (ZMod q)ˣ →* ℂˣ)
    (S : Finset (ZMod q)ˣ) :
    (∑ s ∈ S, (chi s : ℂ)) =
    (∑ s ∈ S, (quotientChar chi (QuotientGroup.mk' chi.ker s) : ℂ)) :=
  rfl

/-- The mean character value of χ over S equals the mean character value computed
    via the quotient character (summing over original elements, not image). -/
theorem meanCharValue_via_quotient (chi : (ZMod q)ˣ →* ℂˣ)
    (S : Finset (ZMod q)ˣ) :
    meanCharValue chi S =
    (∑ s ∈ S, (quotientChar chi (QuotientGroup.mk' chi.ker s) : ℂ)) / S.card :=
  rfl

/-! ### Task 7: KernelConfinement via quotient -/

/-- KernelConfinement is equivalent to the quotient projection of factorRatio
    being eventually trivial. -/
theorem kernelConfinement_iff_quotient_eventually_one (chi : (ZMod q)ˣ →* ℂˣ) :
    KernelConfinement q chi ↔
    ∃ N₀, ∀ n, N₀ ≤ n → QuotientGroup.mk' chi.ker (factorRatio (q := q) n) = 1 := by
  simp only [KernelConfinement, quotient_factorRatio_eq_one_iff]

/-- RatioKernelEscape is equivalent to the quotient projection of factorRatio
    being nontrivial infinitely often. -/
theorem ratioKernelEscape_iff_quotient_io_ne_one (chi : (ZMod q)ˣ →* ℂˣ) :
    RatioKernelEscape q chi ↔
    ∀ N, ∃ n, N ≤ n ∧ QuotientGroup.mk' chi.ker (factorRatio (q := q) n) ≠ 1 := by
  simp only [RatioKernelEscape, quotient_factorRatio_ne_one_iff]

/-! ### Task 8: Landscape theorem -/

/-- **Quotient Character Lift Landscape**: summary of Part 28.

    ALL PROVED:
    1. quotientChar is well-defined (χ factors through G/ker(χ))
    2. quotientChar is faithful (injective)
    3. χ(g) = quotientChar(π(g)) (recovery)
    4. π(factorRatio) = 1 ↔ factorRatio ∈ ker(χ)
    5. |G/ker(χ)| ≥ 2 for nontrivial χ
    6. KernelConfinement ↔ quotient projection eventually 1
    7. RatioKernelEscape ↔ quotient projection i.o. nontrivial

    This reduces NFCE to: the quotient image of factorRatio escapes {1}
    infinitely often in each quotient group G/ker(χ). Since the quotient
    character is FAITHFUL on each such quotient, this connects the
    non-faithful case to the faithful escape framework (Part 24). -/
theorem quotient_escape_landscape :
    -- 1. quotientChar is faithful
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ),
      Function.Injective (quotientChar chi))
    ∧
    -- 2. χ(g) = quotientChar(π(g))
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ) (g : (ZMod q')ˣ),
      quotientChar chi (QuotientGroup.mk' chi.ker g) = chi g)
    ∧
    -- 3. π(factorRatio) = 1 ↔ factorRatio ∈ ker(χ)
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ) (n : ℕ),
      QuotientGroup.mk' chi.ker (factorRatio (q := q') n) = 1 ↔
      factorRatio (q := q') n ∈ chi.ker)
    ∧
    -- 4. |G/ker(χ)| ≥ 2 for nontrivial χ
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (chi : (ZMod q')ˣ →* ℂˣ),
      chi ≠ 1 → 2 ≤ Nat.card ((ZMod q')ˣ ⧸ chi.ker)) :=
  ⟨fun _ _ => quotientChar_faithful,
   fun _ _ => quotientChar_apply,
   fun _ _ => quotient_factorRatio_eq_one_iff,
   fun _ _ => quotient_card_ge_two⟩

end QuotientCharacterLift
