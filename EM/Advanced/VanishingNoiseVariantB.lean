import EM.Advanced.VanishingNoiseVariant

/-!
# Vanishing Noise Variant Part B: Non-Self-Consistent Variant MC and Routes to UFDStrong

## Overview

This file contains Parts 21-22 of the vanishing noise framework, split from
`VanishingNoiseVariant.lean` for modularity.

**Part 21**: Non-self-consistent variant MC under `UFDStrong`. Shows that if spectral gaps
at padded factor sets are non-summable, then every element of `(ZMod q)^*` is reachable
by some selection path.

**Part 22**: Routes to UFDStrong. Characterizes UFDStrong qualitatively and provides
multiple routes to establishing the hypothesis.
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter



/-! ## Part 21: Non-Self-Consistent Variant MC

Under suitable factor diversity hypotheses, the EM walk's Euclid numbers provide
enough spectral diversity that flexible two-point selection covers all residue
classes. This establishes **variant MC**: for each prime q, some selection from
{minFac, secondMinFac} of Euclid numbers hits -1 mod q, though the selection
may differ per prime.

The core chain:
1. Both minFac and secondMinFac of prod(n)+1 are prime
2. A prime p different from q gives a unit in (ZMod q)
3. Under `UFDStrong`, for each nontrivial chi, the spectral gaps at the
   two-element unit set are non-summable
4. `sparse_avgCharProduct_tendsto_zero` gives vanishing products
5. `pathExistenceFromVanishing_proved` gives path existence in (ZMod q)ˣ

Key point: this does NOT prove standard MC. The selection sigma may differ
per prime q. The gap between variant MC and actual MC is the selection
bias problem (Dead End #130).

### UFD vs UFDStrong gap

`UniformFactorDiversity(q)` guarantees: at infinitely many steps, minFac and
secondMinFac have DISTINCT RESIDUES mod q. This gives distinct ELEMENTS in
(ZMod q)ˣ, but NOT necessarily distinct CHARACTER VALUES for every nontrivial
chi. A nontrivial chi can map distinct elements to the same value if their
ratio lies in ker(chi).

`UFDStrong(q)` directly asserts non-summability of spectral gaps, which suffices
for the chain. The implication UFD => UFDStrong would require showing that the
ratio minFac/secondMinFac does not persistently lie in ker(chi) for any fixed
nontrivial chi -- a genuine number-theoretic question about the distribution of
Euclid number factorizations. -/

section NonSelfConsistentVariant

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Unit lifting for primes in ZMod q -/

/-- A prime p with p different from q is a unit in ZMod q. This follows from the
    fact that distinct primes are coprime. -/
theorem prime_ne_isUnit_zmod {p : ℕ} (hp : Nat.Prime p) (hpq : p ≠ q) :
    IsUnit ((p : ℕ) : ZMod q) := by
  rw [ZMod.isUnit_prime_iff_not_dvd hp]
  intro hdvd
  exact hpq ((Fact.out : Nat.Prime q).eq_one_or_self_of_dvd p hdvd |>.resolve_left
    (by have := hp.two_le; omega))

/-- If p is a prime and p differs from q, we can lift (p : ZMod q) to a unit. -/
noncomputable def primeToUnit {p : ℕ} (hp : Nat.Prime p) (hpq : p ≠ q) : (ZMod q)ˣ :=
  (prime_ne_isUnit_zmod hp hpq).unit

/-- The coercion of primeToUnit back to ZMod q equals the natural cast. -/
theorem primeToUnit_coe {p : ℕ} (hp : Nat.Prime p) (hpq : p ≠ q) :
    (primeToUnit hp hpq : ZMod q) = (p : ZMod q) :=
  IsUnit.unit_spec (prime_ne_isUnit_zmod hp hpq)

/-! ### The padded unit set: always has card at least 2

For each step n, we form a Finset (ZMod q)ˣ containing (at least) the units
corresponding to the prime factors of prod(n)+1. When the natural construction
has card < 2 (e.g., when one factor equals q), we pad with the full group
Finset.univ, which has card q-1 for q prime and q-1 >= 2 for q >= 3.
The meanCharValue over Finset.univ is 0 for nontrivial characters (by
orthogonality), giving PERFECT contraction at padded steps. -/

/-- Helper: lift a ZMod q element to a unit, defaulting to 1 if not a unit. -/
noncomputable def liftToUnit (x : ZMod q) : (ZMod q)ˣ :=
  if h : IsUnit x then h.unit else 1

/-- The raw two-element unit set: image of {minFac, secondMinFac} under unit lifting.
    May have card 1 or 2 depending on whether factors collapse mod q. -/
noncomputable def rawTwoPointUnitSet (n : ℕ) : Finset (ZMod q)ˣ :=
  {liftToUnit (Nat.minFac (prod n + 1) : ZMod q),
   liftToUnit (secondMinFac (prod n + 1) : ZMod q)}

/-- The padded unit set: uses raw set when card >= 2, otherwise falls back to
    Finset.univ (the full group). For q >= 3, Finset.univ always has card >= 2. -/
noncomputable def paddedUnitSet (n : ℕ) : Finset (ZMod q)ˣ :=
  let raw := rawTwoPointUnitSet (q := q) n
  if 2 ≤ raw.card then raw else Finset.univ

/-- The padded unit set is always nonempty. -/
theorem paddedUnitSet_nonempty (n : ℕ) :
    (paddedUnitSet (q := q) n).Nonempty := by
  simp only [paddedUnitSet]
  split
  · exact Finset.card_pos.mp (by omega)
  · exact Finset.univ_nonempty

/-- For q >= 3, the unit group (ZMod q)ˣ has card >= 2. -/
theorem card_units_zmod_ge_two (hq3 : 2 < q) : 2 ≤ Fintype.card (ZMod q)ˣ := by
  rw [ZMod.card_units_eq_totient]
  have hq_prime := (Fact.out : Nat.Prime q)
  rw [Nat.totient_prime hq_prime]
  omega

/-- For q >= 3, the padded unit set always has card >= 2. -/
theorem paddedUnitSet_card_ge_two (hq3 : 2 < q) (n : ℕ) :
    2 ≤ (paddedUnitSet (q := q) n).card := by
  simp only [paddedUnitSet]
  split
  · assumption
  · rw [Finset.card_univ]
    exact card_units_zmod_ge_two hq3

/-! ### Orthogonality: meanCharValue over full group is 0 for nontrivial chi -/

/-- For a nontrivial group homomorphism chi : G ->* Cˣ, the sum of chi over all
    elements of G is 0. This is character orthogonality (first kind). -/
private theorem hom_sum_eq_zero' {G : Type*} [CommGroup G] [Fintype G]
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    ∑ g : G, (chi g : ℂ) = 0 := by
  have hmc := @homToMulChar_ne_one G _ _ _ chi hchi
  have := MulChar.sum_eq_zero_of_ne_one (R' := ℂ) hmc
  have heq : ∀ g : G, (homToMulChar chi : MulChar G ℂ) g = (chi g : ℂ) := by
    intro g
    have h := mulCharToHom_apply (homToMulChar chi) g
    rw [mulCharToHom_homToMulChar] at h
    exact h.symm
  simp_rw [heq] at this
  exact this

/-- The meanCharValue over Finset.univ is 0 for nontrivial chi. -/
theorem meanCharValue_univ_eq_zero {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    meanCharValue chi Finset.univ = 0 := by
  simp only [meanCharValue]
  rw [show ∑ s ∈ Finset.univ, (chi s : ℂ) = ∑ g : G, (chi g : ℂ) from
    Finset.sum_congr rfl (fun _ _ => rfl)]
  rw [hom_sum_eq_zero' chi hchi]
  simp

/-- The norm of meanCharValue over the full group is 0 for nontrivial chi. -/
theorem meanCharValue_univ_norm_eq_zero {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (hchi : chi ≠ 1) :
    ‖meanCharValue chi Finset.univ‖ = 0 := by
  simp [meanCharValue_univ_eq_zero chi hchi]

/-! ### Spectral gap at padded steps -/

/-- The spectral gap of the padded unit set is always nonneg. -/
theorem paddedUnitSet_gap_nonneg (chi : (ZMod q)ˣ →* ℂˣ) (n : ℕ) :
    0 ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  have h := meanCharValue_norm_le_one chi (paddedUnitSet (q := q) n)
    (paddedUnitSet_nonempty n)
  linarith

/-- At padded fallback steps, the spectral gap is exactly 1 (perfect contraction). -/
theorem paddedUnitSet_gap_at_fallback (_hq3 : 2 < q) (n : ℕ)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1)
    (hsmall : ¬(2 ≤ (rawTwoPointUnitSet (q := q) n).card)) :
    1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ = 1 := by
  simp only [paddedUnitSet, if_neg hsmall]
  rw [meanCharValue_univ_norm_eq_zero chi hchi]
  ring

/-! ### UFDStrong: Per-chi spectral gap non-summability -/

/-- **UFDStrong**: For each nontrivial character on (ZMod q)ˣ, the spectral gaps
    of the padded unit set sequence are non-summable. This directly feeds into
    `sparse_avgCharProduct_tendsto_zero` for vanishing averaged products. -/
def UFDStrong (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)

/-! ### Main chain: UFDStrong => vanishing => path existence => VariantHitting -/

/-- **UFDStrong implies vanishing**: Under UFDStrong, for every nontrivial chi,
    the averaged character product over the padded unit sets tends to 0. -/
theorem ufdStrong_implies_vanishing (hufd : UFDStrong q)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1) :
    Filter.Tendsto (fun N => ‖avgCharProduct chi (paddedUnitSet (q := q)) N‖)
      Filter.atTop (nhds 0) :=
  sparse_avgCharProduct_tendsto_zero chi _ (fun k => paddedUnitSet_nonempty k)
    (hufd chi hchi)

/-- **UFDStrong implies path existence**: Under UFDStrong with q >= 3, every element
    of (ZMod q)ˣ appears in the product multiset of padded unit sets. -/
theorem ufdStrong_implies_path_existence (hq3 : 2 < q) (hufd : UFDStrong q)
    (a : (ZMod q)ˣ) :
    ∃ N, a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  pathExistenceFromVanishing_proved
    (paddedUnitSet (q := q))
    (fun k => paddedUnitSet_nonempty k)
    (fun k => paddedUnitSet_card_ge_two hq3 k)
    (fun chi hchi => ufdStrong_implies_vanishing hufd chi hchi)
    a

/-- **VariantHitting**: For each prime q >= 3, under UFDStrong, every element of
    (ZMod q)ˣ is reachable by some selection from the padded factor sets. -/
def VariantHitting (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → UFDStrong q →
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset

/-- **VariantHitting PROVED**: fully proved from the chain
    UFDStrong => sparse contraction => vanishing products => path existence. -/
theorem variant_hitting_proved : VariantHitting q :=
  fun hq3 hufd a => ufdStrong_implies_path_existence hq3 hufd a

/-! ### UFD structural lemmas (unconditional) -/

/-- If infinitely many terms of a nonneg sequence are >= 1, the sequence is
    not summable. -/
private theorem not_summable_of_infinitely_many_ge_one
    (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    (hinf : ∀ N, ∃ n, N ≤ n ∧ 1 ≤ f n) :
    ¬Summable f := by
  intro hsum
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hsum.tendsto_atTop_zero) (1/2) (by positivity)
  obtain ⟨n, hn, hfn⟩ := hinf N₀
  have h := hN₀ n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf_nonneg n)] at h
  linarith

/-- Under UFD, if infinitely many steps have raw card < 2 (fallback steps),
    the spectral gaps include infinitely many 1's, making the sum non-summable. -/
theorem ufd_fallback_not_summable (hq3 : 2 < q)
    (chi : (ZMod q)ˣ →* ℂˣ) (hchi : chi ≠ 1)
    (hfallback : ∀ N, ∃ n, N ≤ n ∧ ¬(2 ≤ (rawTwoPointUnitSet (q := q) n).card)) :
    ¬Summable (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖) :=
  not_summable_of_infinitely_many_ge_one _
    (fun n => paddedUnitSet_gap_nonneg chi n)
    (fun N => by
      obtain ⟨n, hn, hsmall⟩ := hfallback N
      exact ⟨n, hn, by rw [paddedUnitSet_gap_at_fallback hq3 n chi hchi hsmall]⟩)

/-! ### Bridge from UFD to UFDStrong: the open gap

The implication `UniformFactorDiversity => UFDStrong` splits into two cases:
1. If infinitely many steps have raw card < 2: UFDStrong follows from
   `ufd_fallback_not_summable` (PROVED above).
2. If cofinitely many steps have raw card >= 2: we need that for each nontrivial
   chi, the chi-values at the two factor residues are infinitely often distinct.
   This requires showing minFac/secondMinFac mod q does not persistently lie in
   ker(chi) for any fixed nontrivial chi.

Case 2 is a genuine number-theoretic question. -/

/-- **UFDImpliesUFDStrong**: the bridge from element-level to character-level
    diversity. Open Prop. -/
def UFDImpliesUFDStrong (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → UniformFactorDiversity q → UFDStrong q

/-! ### Capture bridge: direct hitting when q is a factor -/

/-- Both minFac and secondMinFac of prod(n)+1 are prime. -/
theorem both_factors_prime (n : ℕ) :
    (Nat.minFac (prod n + 1)).Prime ∧ (secondMinFac (prod n + 1)).Prime :=
  ⟨Nat.minFac_prime (by have := prod_ge_two n; omega),
   secondMinFac_prime (by have := prod_ge_two n; omega)⟩

/-- minFac of prod(n)+1 always divides prod(n)+1. -/
theorem minFac_always_divides_euclid (n : ℕ) :
    Nat.minFac (prod n + 1) ∣ prod n + 1 :=
  Nat.minFac_dvd (prod n + 1)

/-- secondMinFac of prod(n)+1 always divides prod(n)+1. -/
theorem secondMinFac_always_divides_euclid (n : ℕ) :
    secondMinFac (prod n + 1) ∣ prod n + 1 :=
  secondMinFac_dvd (by have := prod_ge_two n; omega)

/-- If a prime p divides prod(n)+1, then the walk hits -1 at step n in ZMod p.
    This means p is "captured" at step n. -/
theorem factor_captures_prime (n : ℕ) {p : ℕ} (_hp : Nat.Prime p)
    (hdvd : p ∣ prod n + 1) :
    walkZ p n = -1 := by
  rw [walkZ_eq_neg_one_iff]
  exact hdvd

/-- minFac of prod(n)+1 is captured at step n by the standard EM walk. -/
theorem minFac_captured (n : ℕ) :
    walkZ (Nat.minFac (prod n + 1)) n = -1 :=
  factor_captures_prime n (both_factors_prime n).1 (minFac_always_divides_euclid n)

/-- secondMinFac of prod(n)+1 is captured at step n by the alternative selection. -/
theorem secondMinFac_captured (n : ℕ) :
    walkZ (secondMinFac (prod n + 1)) n = -1 :=
  factor_captures_prime n (both_factors_prime n).2 (secondMinFac_always_divides_euclid n)

/-! ### VariantMC from UFDStrong -/

/-- **VariantMCFromUFDStrong**: UFDStrong at every prime q >= 3 implies that
    for every prime q >= 3 and every target a in (ZMod q)ˣ, some selection
    path through the padded unit sets reaches a. -/
def VariantMCFromUFDStrong : Prop :=
  ∀ (q : ℕ) (hqp' : Fact (Nat.Prime q)), 2 < q → @UFDStrong q hqp' →
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (G := (ZMod q)ˣ) (@paddedUnitSet q hqp') N).toFinset

/-- VariantMCFromUFDStrong is PROVED. -/
theorem variant_mc_from_ufd_strong_proved : VariantMCFromUFDStrong :=
  fun q hqp' hq3 hufd a => @ufdStrong_implies_path_existence q hqp' hq3 hufd a

/-! ### Landscape theorem -/

/-- **Non-Self-Consistent Variant MC Landscape**: summary of Part 21.

    ALL PROVED (no open hypotheses used):
    1. prime_ne_isUnit_zmod: p prime, q prime, p != q => (p : ZMod q) is a unit
    2. paddedUnitSet_nonempty: padded unit set is always nonempty
    3. paddedUnitSet_card_ge_two: for q >= 3, padded set has card >= 2
    4. meanCharValue_univ_eq_zero: orthogonality for nontrivial characters
    5. ufdStrong_implies_vanishing: UFDStrong => avgCharProduct -> 0
    6. ufdStrong_implies_path_existence: UFDStrong => path existence in (ZMod q)ˣ
    7. variant_hitting_proved: VariantHitting PROVED
    8. variant_mc_from_ufd_strong_proved: VariantMCFromUFDStrong PROVED
    9. ufd_fallback_not_summable: fallback case of UFD => UFDStrong (PROVED)
    10. Factor capture: minFac and secondMinFac always divide prod(n)+1

    OPEN hypotheses documented:
    A. UFDImpliesUFDStrong: gap between element-level and character-level diversity
    B. UniformFactorDiversity: minFac != secondMinFac mod q infinitely often -/
theorem variant_mc_landscape :
    -- 1. Unit lifting for distinct primes
    (∀ (q' : ℕ) [Fact (Nat.Prime q')],
      ∀ {p : ℕ}, Nat.Prime p → p ≠ q' → IsUnit ((p : ℕ) : ZMod q'))
    ∧
    -- 2. Padded unit set always nonempty
    (∀ (q' : ℕ) [Fact (Nat.Prime q')] (n : ℕ),
      (@paddedUnitSet q' _ n).Nonempty)
    ∧
    -- 3. For q >= 3, padded set has card >= 2
    (∀ (q' : ℕ) [Fact (Nat.Prime q')], 2 < q' →
      ∀ n, 2 ≤ (@paddedUnitSet q' _ n).card)
    ∧
    -- 4. Character orthogonality over full group
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ), chi ≠ 1 →
       meanCharValue chi Finset.univ = 0)
    ∧
    -- 5. VariantMCFromUFDStrong
    VariantMCFromUFDStrong
    ∧
    -- 6. Both factors of Euclid numbers are prime
    (∀ n, (Nat.minFac (prod n + 1)).Prime ∧ (secondMinFac (prod n + 1)).Prime)
    ∧
    -- 7. Both factors divide the Euclid number
    (∀ n, Nat.minFac (prod n + 1) ∣ prod n + 1 ∧
           secondMinFac (prod n + 1) ∣ prod n + 1) :=
  ⟨fun _q' _ => @prime_ne_isUnit_zmod _q' _,
   fun _q' _ => @paddedUnitSet_nonempty _q' _,
   fun _q' _ hq3 => @paddedUnitSet_card_ge_two _q' _ hq3,
   fun _ _ _ _ chi hchi => meanCharValue_univ_eq_zero chi hchi,
   variant_mc_from_ufd_strong_proved,
   both_factors_prime,
   fun n => ⟨minFac_always_divides_euclid n, secondMinFac_always_divides_euclid n⟩⟩

end NonSelfConsistentVariant

/-! ## Part 22: Routes to UFDStrong

Three independent routes reducing `UFDStrong` to progressively weaker hypotheses,
plus assembly theorems and a landscape theorem.

* Route 1: `MinFacRatioEscape` (quantitative: per-chi, infinitely many steps with
  gap bounded below by a fixed positive constant) implies `UFDStrong` directly.
* Route 2: `MinFacRatioEscapeQual` (qualitative: per-chi, infinitely many steps
  with card >= 2 and distinct chi-values) implies `MinFacRatioEscape` via finite
  group pigeonhole: the gap function has finite range, so positive gaps are
  bounded away from 0.
* Route 3: `OrbitMFRE` (orbit-level minFac residue equidistribution) implies
  `MinFacRatioEscapeQual` because equidistribution prevents character values from
  being confined to a proper coset.

All three compose with the proved chain `UFDStrong => VariantMC`.
-/

section RoutesToUFDStrong

variable {q : ℕ} [hqp : Fact (Nat.Prime q)]

/-! ### Utility: Non-summability from frequently exceeding a fixed threshold -/

/-- If a nonneg sequence has infinitely many terms above a fixed positive threshold,
    the sequence is not summable. Proof: summable implies convergence to 0,
    contradicting the infinitely-many-large-terms condition. -/
theorem not_summable_of_frequently_ge (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    {δ : ℝ} (hδ : 0 < δ) (hinf : ∀ N, ∃ n, N ≤ n ∧ δ ≤ f n) :
    ¬Summable f := by
  intro hsum
  have htends := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htends
  obtain ⟨N₀, hN₀⟩ := htends δ hδ
  obtain ⟨n, hn, hfn⟩ := hinf N₀
  have h := hN₀ n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf_nonneg n)] at h
  linarith

/-- Non-summability when a nonneg function with finite range has infinitely many
    positive values. The key insight: a finite set of positive reals has a positive
    minimum, providing the uniform lower bound needed for non-summability. -/
theorem not_summable_of_frequently_pos_finite_range (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n)
    (hfinite : Set.Finite (Set.range f))
    (hinf : ∀ N, ∃ n, N ≤ n ∧ 0 < f n) :
    ¬Summable f := by
  -- The positive values in the range form a finite nonempty set
  set posRange := {x ∈ hfinite.toFinset | (0 : ℝ) < x} with hposRange_def
  have hne : posRange.Nonempty := by
    obtain ⟨n, -, hfn⟩ := hinf 0
    exact ⟨f n, by rw [hposRange_def, Finset.mem_filter]; exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩⟩
  -- The minimum of posRange is positive
  set δ := posRange.min' hne
  have hδ_pos : 0 < δ := by
    have hmem := Finset.min'_mem posRange hne
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  -- Every positive value of f is >= δ
  have hδ_le : ∀ n, 0 < f n → δ ≤ f n := by
    intro n hfn
    apply Finset.min'_le
    rw [Finset.mem_filter]
    exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩
  -- Apply the quantitative non-summability lemma
  exact not_summable_of_frequently_ge f hf_nonneg hδ_pos
    (fun N => by obtain ⟨n, hn, hfn⟩ := hinf N; exact ⟨n, hn, hδ_le n hfn⟩)

/-! ### Route 1: MinFacRatioEscape (quantitative) => UFDStrong -/

/-- **MinFacRatioEscape** (quantitative): For each nontrivial character chi on
    (ZMod q)ˣ, there exists a fixed positive spectral gap threshold delta such that
    infinitely many steps n have gap >= delta at the padded unit set.

    This is the quantitative version that directly feeds into non-summability.
    The qualitative version `MinFacRatioEscapeQual` (card >= 2 + distinct chi-values)
    implies this via the finite-group argument. -/
def MinFacRatioEscape (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ N, ∃ n, N ≤ n ∧ δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖

/-- MinFacRatioEscape directly implies UFDStrong: the quantitative gap bound
    feeds into non-summability via `not_summable_of_frequently_ge`. -/
theorem ratio_escape_implies_ufdStrong (hre : MinFacRatioEscape q) :
    UFDStrong q := by
  intro chi hchi
  obtain ⟨δ, hδ_pos, hinf⟩ := hre chi hchi
  exact not_summable_of_frequently_ge _ (fun n => paddedUnitSet_gap_nonneg chi n) hδ_pos hinf

/-! ### Route 2: Qualitative MinFacRatioEscape => Quantitative (finite group argument) -/

/-- **MinFacRatioEscapeQual** (qualitative): For each nontrivial character chi,
    infinitely many steps n have (a) rawTwoPointUnitSet with card >= 2, and
    (b) the chi-values at the two lifted primes are distinct.

    This is the more natural number-theoretic condition. -/
def MinFacRatioEscapeQual (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (chi : (ZMod q)ˣ →* ℂˣ), chi ≠ 1 →
    ∀ N, ∃ n, N ≤ n ∧
      2 ≤ (rawTwoPointUnitSet (q := q) n).card ∧
      (chi (liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)) : ℂ) ≠
      (chi (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)) : ℂ)

/-- When rawTwoPointUnitSet has card >= 2, paddedUnitSet equals rawTwoPointUnitSet. -/
theorem paddedUnitSet_eq_raw_of_card (n : ℕ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card) :
    paddedUnitSet (q := q) n = rawTwoPointUnitSet (q := q) n := by
  simp only [paddedUnitSet, if_pos hcard]

/-- The rawTwoPointUnitSet contains liftToUnit of minFac. -/
theorem liftToUnit_minFac_mem_raw (n : ℕ) :
    liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)
      ∈ rawTwoPointUnitSet (q := q) n := by
  simp [rawTwoPointUnitSet, Finset.mem_insert, Finset.mem_singleton]

/-- The rawTwoPointUnitSet contains liftToUnit of secondMinFac. -/
theorem liftToUnit_secondMinFac_mem_raw (n : ℕ) :
    liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)
      ∈ rawTwoPointUnitSet (q := q) n := by
  simp [rawTwoPointUnitSet, Finset.mem_insert, Finset.mem_singleton]

/-- At a qualitative escape step, the gap at paddedUnitSet is strictly positive.
    Key: rawTwoPointUnitSet has card >= 2, so paddedUnitSet = rawTwoPointUnitSet,
    and distinct chi-values give strict contraction via `meanCharValue_norm_lt_one_of_distinct`. -/
theorem gap_pos_at_escape (n : ℕ) (chi : (ZMod q)ˣ →* ℂˣ)
    (hcard : 2 ≤ (rawTwoPointUnitSet (q := q) n).card)
    (hdiff : (chi (liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q)) : ℂ) ≠
             (chi (liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q)) : ℂ)) :
    0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
  rw [paddedUnitSet_eq_raw_of_card n hcard]
  have hlt := meanCharValue_norm_lt_one_of_distinct chi (rawTwoPointUnitSet (q := q) n) hcard
    ⟨liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q),
     liftToUnit_minFac_mem_raw n,
     liftToUnit (q := q) (secondMinFac (prod n + 1) : ZMod q),
     liftToUnit_secondMinFac_mem_raw n,
     hdiff⟩
  linarith

/-- The gap function n -> 1 - ||meanCharValue chi (paddedUnitSet n)|| has finite range.
    This follows from the fact that paddedUnitSet maps N to Finset (ZMod q)^x, which is
    a Fintype (power set of a finite type). So the composition through meanCharValue
    and norm produces only finitely many distinct values. -/
theorem gap_function_finite_range (chi : (ZMod q)ˣ →* ℂˣ) :
    Set.Finite (Set.range (fun n => 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖)) := by
  -- paddedUnitSet maps to Finset (ZMod q)ˣ, which is a Fintype
  -- The composition gap ∘ paddedUnitSet factors through this Fintype
  apply Set.Finite.subset
    (Set.Finite.image (fun S => 1 - ‖meanCharValue chi S‖)
      (Set.toFinite (Set.univ : Set (Finset (ZMod q)ˣ))))
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact ⟨paddedUnitSet (q := q) n, Set.mem_univ _, rfl⟩

/-- The qualitative MinFacRatioEscape implies the quantitative version.
    Proof: the gap function has finite range (by `gap_function_finite_range`),
    escape steps give positive gaps (by `gap_pos_at_escape`), and a finite set
    of positive reals has a positive minimum. -/
theorem qual_implies_quant (hq : MinFacRatioEscapeQual q) : MinFacRatioEscape q := by
  intro chi hchi
  -- The gap function has finite range
  have hfin := gap_function_finite_range (q := q) chi
  -- Escape steps give positive gaps
  have hpos : ∀ N, ∃ n, N ≤ n ∧
      0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
    intro N
    obtain ⟨n, hn, hcard, hdiff⟩ := hq chi hchi N
    exact ⟨n, hn, gap_pos_at_escape n chi hcard hdiff⟩
  -- Extract the positive values in the range
  set posRange := {x ∈ hfin.toFinset | (0 : ℝ) < x}
  have hne : posRange.Nonempty := by
    obtain ⟨n, -, hfn⟩ := hpos 0
    exact ⟨_, by rw [Finset.mem_filter]; exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩⟩
  set δ := posRange.min' hne
  have hδ_pos : 0 < δ := by
    have hmem := Finset.min'_mem posRange hne
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  have hδ_le : ∀ n, 0 < 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ →
      δ ≤ 1 - ‖meanCharValue chi (paddedUnitSet (q := q) n)‖ := by
    intro n hfn
    apply Finset.min'_le
    rw [Finset.mem_filter]
    exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨n, rfl⟩, hfn⟩
  exact ⟨δ, hδ_pos, fun N => by
    obtain ⟨n, hn, hfn⟩ := hpos N
    exact ⟨n, hn, hδ_le n hfn⟩⟩

/-- The qualitative MinFacRatioEscape implies UFDStrong. Composition of
    `qual_implies_quant` and `ratio_escape_implies_ufdStrong`. -/
theorem qual_escape_implies_ufdStrong (hq : MinFacRatioEscapeQual q) :
    UFDStrong q :=
  ratio_escape_implies_ufdStrong (qual_implies_quant hq)

/-! ### Route 3: OrbitMFRE => MinFacRatioEscapeQual

OrbitMFRE says that for each unit a in (ZMod q)ˣ, the density of steps n where
liftToUnit(minFac(prod(n)+1)) = a tends to 1/(q-1). Under this, for any nontrivial
character chi, the density of steps where chi(minFac-unit) takes any particular value
is at most |ker(chi)|/(q-1) < 1, so infinitely many steps have a non-default chi-value.

Combined with the fact that secondMinFac also divides prod(n)+1 and gives a unit in
(ZMod q)ˣ, we get infinitely many steps where chi-values at minFac and secondMinFac
can differ.

The formal proof requires density-based arguments (eventually, density of steps with
chi(minFac) = chi(secondMinFac) is bounded away from 1). This involves quantitative
Fourier analysis on the finite group, which we state as an open Prop and document
the proof strategy. -/

/-- **OrbitMFRE**: Orbit-level minFac residue equidistribution. For each unit a in
    (ZMod q)ˣ, the density of steps n where liftToUnit(minFac(prod(n)+1)) = a
    converges to 1/(q-1). -/
def OrbitMFRE (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ (a : (ZMod q)ˣ), ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
    |((Finset.range N).filter (fun n =>
        liftToUnit (q := q) (Nat.minFac (prod n + 1) : ZMod q) = a)).card / (N : ℝ) -
     1 / (Fintype.card (ZMod q)ˣ : ℝ)| < ε

/-- **OrbitMFREImpliesEscapeQual**: OrbitMFRE implies qualitative MinFacRatioEscape.

    Proof sketch: Under OrbitMFRE, for any nontrivial chi, the density of steps where
    chi(minFac-unit) = 1 is at most |ker(chi)|/(q-1) < 1 (since chi is nontrivial,
    ker(chi) is a proper subgroup). So at positive density, chi(minFac-unit) != 1.
    At these steps, either (a) rawTwoPointUnitSet has card < 2 (covered by fallback),
    or (b) card >= 2 and chi(minFac-unit) != chi(secondMinFac-unit) = 1 does not
    hold trivially -- we need chi(minFac) != chi(secondMinFac) specifically.

    The gap between "chi(minFac) takes non-identity value" and "chi(minFac) != chi(secondMinFac)"
    requires additional analysis of secondMinFac distribution. This is a genuine gap
    when secondMinFac = minFac mod q at those steps. We formalize this as an open Prop
    documenting the proof strategy. -/
def OrbitMFREImpliesEscapeQual (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  2 < q → OrbitMFRE q → MinFacRatioEscapeQual q

/-! ### Assembly chains: composing routes to VariantMC -/

/-- **Route 1 assembly**: Quantitative MinFacRatioEscape => UFDStrong => VariantMC. -/
theorem route1_mfre_to_variant_mc (hq3 : 2 < q) (hre : MinFacRatioEscape q) :
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  ufdStrong_implies_path_existence hq3 (ratio_escape_implies_ufdStrong hre)

/-- **Route 2 assembly**: Qualitative MinFacRatioEscapeQual => UFDStrong => VariantMC. -/
theorem route2_qual_to_variant_mc (hq3 : 2 < q) (hq : MinFacRatioEscapeQual q) :
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  ufdStrong_implies_path_existence hq3 (qual_escape_implies_ufdStrong hq)

/-- **Route 3 assembly**: OrbitMFRE + bridge => UFDStrong => VariantMC. -/
theorem route3_orbit_to_variant_mc (hq3 : 2 < q)
    (hbridge : OrbitMFREImpliesEscapeQual q) (hmfre : OrbitMFRE q) :
    ∀ (a : (ZMod q)ˣ), ∃ N,
      a ∈ (productMultiset (paddedUnitSet (q := q)) N).toFinset :=
  route2_qual_to_variant_mc hq3 (hbridge hq3 hmfre)

/-- **Route 1 to UFDStrong assembly**: quantitative escape directly gives UFDStrong. -/
theorem route1_to_ufdStrong (hre : MinFacRatioEscape q) : UFDStrong q :=
  ratio_escape_implies_ufdStrong hre

/-- **Route 2 to UFDStrong assembly**: qualitative escape gives UFDStrong via
    the finite-range argument. -/
theorem route2_to_ufdStrong (hq : MinFacRatioEscapeQual q) : UFDStrong q :=
  qual_escape_implies_ufdStrong hq

/-- **Route 3 to UFDStrong assembly**: OrbitMFRE + bridge gives UFDStrong. -/
theorem route3_to_ufdStrong
    (hq3 : 2 < q) (hbridge : OrbitMFREImpliesEscapeQual q) (hmfre : OrbitMFRE q) :
    UFDStrong q :=
  qual_escape_implies_ufdStrong (hbridge hq3 hmfre)

/-! ### Landscape theorem -/

/-- **Routes to UFDStrong Landscape**: summary of Part 22.

    ALL internal reductions PROVED (no sorry). Open hypotheses:
    A. MinFacRatioEscape (quantitative spectral gap at infinitely many steps)
    B. MinFacRatioEscapeQual (qualitative: card >= 2 + distinct chi-values i.o.)
    C. OrbitMFRE (orbit-level minFac equidistribution)
    D. OrbitMFREImpliesEscapeQual (density argument bridge)

    PROVED reductions:
    1. not_summable_of_frequently_ge (utility)
    2. not_summable_of_frequently_pos_finite_range (finite range + i.o. positive => not summable)
    3. ratio_escape_implies_ufdStrong (Route 1: quantitative => UFDStrong)
    4. qual_implies_quant (Route 2: qualitative => quantitative via finite group)
    5. qual_escape_implies_ufdStrong (Route 2 composed)
    6. gap_function_finite_range (paddedUnitSet finite range)
    7. gap_pos_at_escape (positive gap at escape steps)
    8. route1/2/3_to_variant_mc (assembly chains to VariantMC) -/
theorem routes_to_ufdStrong_landscape :
    -- 1. Quantitative MinFacRatioEscape => UFDStrong
    (MinFacRatioEscape q → UFDStrong q)
    ∧
    -- 2. Qualitative MinFacRatioEscapeQual => quantitative MinFacRatioEscape
    (MinFacRatioEscapeQual q → MinFacRatioEscape q)
    ∧
    -- 3. Qualitative => UFDStrong (composed)
    (MinFacRatioEscapeQual q → UFDStrong q)
    ∧
    -- 4. Gap function has finite range (structural fact)
    Set.Finite (Set.range (fun n => 1 - ‖meanCharValue (1 : (ZMod q)ˣ →* ℂˣ) (paddedUnitSet (q := q) n)‖))
    ∧
    -- 5. Not summable from frequently positive + finite range (utility)
    (∀ (f : ℕ → ℝ), (∀ n, 0 ≤ f n) → Set.Finite (Set.range f) →
      (∀ N, ∃ n, N ≤ n ∧ 0 < f n) → ¬Summable f)
    ∧
    -- 6. Route 3 with bridge: OrbitMFRE + bridge => UFDStrong
    (2 < q → OrbitMFREImpliesEscapeQual q → OrbitMFRE q → UFDStrong q) :=
  ⟨ratio_escape_implies_ufdStrong,
   qual_implies_quant,
   qual_escape_implies_ufdStrong,
   gap_function_finite_range 1,
   not_summable_of_frequently_pos_finite_range,
   route3_to_ufdStrong⟩

end RoutesToUFDStrong
