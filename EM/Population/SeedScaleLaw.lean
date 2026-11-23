import EM.Population.SelectionLaw
import EM.Population.ScaleLaw

/-!
# The scale law for seeds: above the running maximum the history drops out

2026-11-23.

`ScaleLaw.lean` gives the law of the size of `minFac` on the integers. This file carries it to
seed populations, through the selection law (`SelectionLaw.selection_law`): inside a type
cell — the seeds sharing the first `k` multipliers of a reference seed `m` and its
divisibility by small primes — the proportion of seeds whose next Euclid number has no prime
factor `≤ y` is exactly `survival q m y k = ∏_{r ≤ y} (1 − ρ_r)`, where `ρ_r` is read off the
box of `r` (`LargeStepRoughness`).

The box of a prime `r` only records the steps at which `r` was *exposed*, i.e. the steps whose
multiplier is larger than `r`. So if `M` is at least the running maximum of the first `k`
multipliers, every prime `r > M` has a full box, and `ρ_r = 1/(r − 1)` for `r ∤ m`
(`rho_above`). Consequently:

* `survival_tail` — **the history drops out above the running maximum.**
  `survival q m y k = survival q m M k · ∏ (1 − 1/(r − 1))`, the product over the primes
  `M < r ≤ y` other than `q` that do not divide `m`.
* `survival_tail_ge` — in general `survival q m y k ≥ survival q m M k · gap M y`, where
  `gap M y = ∏_{M < r ≤ y} (1 − 1/(r − 1))` over all primes; equality if no prime of `(M, y]`
  is `q` or divides `m` (`survival_tail_eq_gap`). Seed divisors and the avoided prime can only
  make the next multiplier larger.
* `cell_tail_count` — the counting form: inside the cell, the number of seeds surviving up to
  `y` is the number surviving up to `M` times the tail product.
* `gap_scale_law` — under Mertens' third theorem (quoted from Tau Ceti as
  `ScaleLaw.MertensThird`): `|gap M y − log M / log y| ≤ C / log M` for `y₀ ≤ M ≤ y`.

## Reading

Conditionally on its first `k` multipliers, the next multiplier of a seed splits into two
regimes. Below the running maximum `M` it is governed by the boxes, that is by the whole
history. Above `M` it is governed by nothing: given that it exceeds `M`, the quantity
`log M / log (next multiplier)` is uniform on `(0, 1)` up to `O(1 / log M)`, for every cell.
A new record of the multipliers is drawn from the same scale-invariant law as the least prime
factor of a random `M`-rough integer.

These are statements about seed populations in the `q`-free dynamics of the seed-average
programme. Nothing here concerns an individual orbit.
-/

noncomputable section
open Classical Finset

namespace SeedScaleLaw

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw HeadDomination ScaleLaw

variable {q m k M y : ℕ}

/-! ## 1. Above the running maximum the box is full -/

/-- No step is `r`-exposed when `r` exceeds all the multipliers so far. -/
theorem visitedAt_eq_empty (hM : ∀ j < k, genSeqAvoid q m j ≤ M) {r : ℕ} (hr : M < r) :
    visitedAt q m r k = ∅ := by
  unfold visitedAt
  rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro j hj hlt
  have := hM j (Finset.mem_range.mp hj)
  omega

/-- **The local density above the running maximum.** For a prime `r` larger than all the
multipliers so far and not dividing the seed, `ρ_r = 1/(r − 1)`. -/
theorem rho_above (hM : ∀ j < k, genSeqAvoid q m j ≤ M) {r : ℕ} (hr : r.Prime) (hMr : M < r)
    (hrm : ¬ r ∣ m) : rho q m r k = 1 / ((r : ℝ) - 1) := by
  have hv := visitedAt_eq_empty hM hMr
  have hbag : ¬ inBag q m r k := by
    rintro (h | ⟨j, hj, hjr⟩)
    · exact hrm h
    · have := hM j hj
      omega
  have hnew : isNew q m r k := by
    unfold isNew
    rw [hv]
    exact Finset.notMem_empty _
  rw [rho_of_active ⟨hbag, hnew⟩]
  have hcard : boxCard q m r k = r - 1 := by
    unfold boxCard box
    rw [hv, Finset.image_empty, Finset.sdiff_empty, unitFinset_card hr]
  rw [hcard, Nat.cast_sub hr.one_le, Nat.cast_one]

/-! ## 2. The tail of the survival product -/

/-- The primes of `(M, y]` other than `q` that do not divide the seed. -/
def tailBand (q m M y : ℕ) : Finset ℕ :=
  (Finset.Ioc M y).filter (fun r => r.Prime ∧ r ≠ q ∧ ¬ r ∣ m)

/-- **The history drops out above the running maximum.** If `M` bounds the first `k`
multipliers and `M ≤ y`, the survival product up to `y` is the survival product up to `M`
times `∏ (1 − 1/(r − 1))` over the primes `M < r ≤ y`, `r ≠ q`, `r ∤ m`. -/
theorem survival_tail (hM : ∀ j < k, genSeqAvoid q m j ≤ M) (hMy : M ≤ y) :
    survival q m y k
      = survival q m M k * ∏ r ∈ tailBand q m M y, (1 - 1 / ((r : ℝ) - 1)) := by
  unfold survival
  rw [← Finset.prod_filter_mul_prod_filter_not (bandUpTo q y) (fun r => r ≤ M),
    bandUpTo_filter hMy]
  congr 1
  have hsub : tailBand q m M y ⊆ (bandUpTo q y).filter (fun r => ¬ r ≤ M) := by
    intro r hr
    obtain ⟨hI, hp, hrq, -⟩ := Finset.mem_filter.mp hr
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hI
    exact Finset.mem_filter.mpr ⟨mem_bandUpTo.mpr ⟨h2, hp, hrq⟩, by omega⟩
  rw [← Finset.prod_subset hsub]
  · refine Finset.prod_congr rfl fun r hr => ?_
    obtain ⟨hI, hp, -, hrm⟩ := Finset.mem_filter.mp hr
    rw [rho_above hM hp (Finset.mem_Ioc.mp hI).1 hrm]
  · intro r hr hnot
    obtain ⟨hband, hrM⟩ := Finset.mem_filter.mp hr
    obtain ⟨hry, hp, hrq⟩ := mem_bandUpTo.mp hband
    have hdvd : r ∣ m := by
      by_contra hrm
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hry⟩, hp, hrq, hrm⟩)
    rw [rho_eq_zero_of_inBag (Or.inl hdvd), sub_zero]

/-- The tail product over all the primes of `(M, y]`. -/
def gap (M y : ℕ) : ℝ := ∏ r ∈ (Finset.Ioc M y).filter Nat.Prime, (1 - 1 / ((r : ℝ) - 1))

theorem gap_factor_nonneg {r : ℕ} (hr : r.Prime) : 0 ≤ 1 - 1 / ((r : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  have h1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  rw [sub_nonneg, div_le_one h1]
  linarith

theorem gap_factor_le_one {r : ℕ} (hr : r.Prime) : 1 - 1 / ((r : ℝ) - 1) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  have h1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have : 0 ≤ 1 / ((r : ℝ) - 1) := by positivity
  linarith

theorem prod_mem_unit {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : 0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ 1 :=
  Finset.prod_induction f (fun x => 0 ≤ x ∧ x ≤ 1)
    (fun _ _ ha hb => ⟨mul_nonneg ha.1 hb.1, by nlinarith [ha.1, ha.2, hb.1, hb.2]⟩)
    ⟨zero_le_one, le_rfl⟩ (fun i hi => ⟨h0 i hi, h1 i hi⟩)

/-- If no prime of `(M, y]` is `q` or divides the seed, the tail is `gap M y`. -/
theorem survival_tail_eq_gap (hM : ∀ j < k, genSeqAvoid q m j ≤ M) (hMy : M ≤ y)
    (hfree : ∀ r : ℕ, r.Prime → M < r → r ≤ y → r ≠ q ∧ ¬ r ∣ m) :
    survival q m y k = survival q m M k * gap M y := by
  rw [survival_tail hM hMy]
  congr 1
  unfold gap tailBand
  refine Finset.prod_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun r hr => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hr
  exact ⟨fun h => h.1, fun h => ⟨h, hfree r h h1 h2⟩⟩

/-- In general the tail is at least `gap M y`: seed divisors and the avoided prime remove
factors `≤ 1`. -/
theorem survival_tail_ge (hq : q.Prime) (hm : 1 ≤ m) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j)
    (hM : ∀ j < k, genSeqAvoid q m j ≤ M) (hMy : M ≤ y) :
    survival q m M k * gap M y ≤ survival q m y k := by
  rw [survival_tail hM hMy]
  refine mul_le_mul_of_nonneg_left ?_ (survival_nonneg hq hm hnd M)
  unfold gap
  have hsub : tailBand q m M y ⊆ (Finset.Ioc M y).filter Nat.Prime := by
    intro r hr
    obtain ⟨hI, hp, -, -⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hI, hp⟩
  rw [← Finset.prod_sdiff hsub]
  have h1 := prod_mem_unit ((Finset.Ioc M y).filter Nat.Prime \ tailBand q m M y)
    (fun r : ℕ => 1 - 1 / ((r : ℝ) - 1))
    (fun r hr => gap_factor_nonneg (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).2)
    (fun r hr => gap_factor_le_one (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).2)
  have h2 := prod_mem_unit (tailBand q m M y) (fun r : ℕ => 1 - 1 / ((r : ℝ) - 1))
    (fun r hr => gap_factor_nonneg (Finset.mem_filter.mp hr).2.1)
    (fun r hr => gap_factor_le_one (Finset.mem_filter.mp hr).2.1)
  exact mul_le_of_le_one_left h2.1 h1.2

/-- **The counting form.** Inside a type cell whose first `k` multipliers are at most `M`,
the number of seeds whose next Euclid number has no prime factor `≤ y` (other than `q`) is
the number of those with no prime factor `≤ M`, times the tail product. -/
theorem cell_tail_count {Y m₀ : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hM : ∀ j < k, genSeqAvoid q m₀ j ≤ M) (hMy : M ≤ y) (hyY : y ≤ Y) :
    (((stepCell q Y k m₀).filter (fun s => SurvivesUpTo q y k s)).card : ℝ)
      = (∏ r ∈ tailBand q m₀ M y, (1 - 1 / ((r : ℝ) - 1)))
        * (((stepCell q Y k m₀).filter (fun s => SurvivesUpTo q M k s)).card : ℝ) := by
  rw [selection_law hq hm₀ hnd hyY, selection_law hq hm₀ hnd (hMy.trans hyY),
    survival_tail hM hMy]
  ring

/-! ## 3. The gap against the Euler product -/

theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have ha0 := h0 i (Finset.mem_insert_self i s)
    have ha1 := h1 i (Finset.mem_insert_self i s)
    have ih' := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    have hS : 0 ≤ ∑ j ∈ s, a j :=
      Finset.sum_nonneg fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr ha1), mul_nonneg ha0 hS]

theorem sum_inv_sq_le (hM : 2 ≤ M) (y : ℕ) (hMy : M ≤ y) :
    ∑ r ∈ Finset.Ioc M y, 1 / ((r : ℝ) - 1) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / ((y : ℝ) - 1) := by
  induction y, hMy using Nat.le_induction with
  | base => simp
  | succ y hy ih =>
    rw [Finset.sum_Ioc_succ_top hy]
    push_cast
    have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hM.trans hy
    have h1 : (0 : ℝ) < (y : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < (y : ℝ) := by linarith
    have hstep : 1 / ((y : ℝ) + 1 - 1) ^ 2 ≤ 1 / ((y : ℝ) - 1) - 1 / ((y : ℝ) + 1 - 1) := by
      rw [add_sub_cancel_right, div_sub_div _ _ h1.ne' h2.ne',
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem cfun_split (hMy : M ≤ y) :
    cfun (y + 1) = cfun (M + 1) * ∏ r ∈ (Finset.Ioc M y).filter Nat.Prime, (1 - (r : ℝ)⁻¹) := by
  rw [cfun_eq_prod, cfun_eq_prod,
    ← Finset.prod_filter_mul_prod_filter_not ((range (y + 1)).filter Nat.Prime) (fun r => r ≤ M)]
  congr 1
  · refine Finset.prod_congr ?_ fun _ _ => rfl
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨-, hp⟩, hr⟩; exact ⟨by omega, hp⟩
    · rintro ⟨hr, hp⟩; exact ⟨⟨by omega, hp⟩, by omega⟩
  · refine Finset.prod_congr ?_ fun _ _ => rfl
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hr, hp⟩, hrM⟩; exact ⟨⟨by omega, by omega⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨by omega, hp⟩, by omega⟩

/-- `gap M y` is the Euler-product ratio times a factor in `[1 − 1/(M − 1), 1]`. -/
theorem gap_bounds (hM : 2 ≤ M) (hMy : M ≤ y) :
    (cfun (y + 1) / cfun (M + 1)) * (1 - 1 / ((M : ℝ) - 1)) ≤ gap M y ∧
      gap M y ≤ cfun (y + 1) / cfun (M + 1) := by
  set P := (Finset.Ioc M y).filter Nat.Prime with hP
  set R : ℝ := ∏ r ∈ P, (1 - (r : ℝ)⁻¹) with hR
  set T : ℝ := ∏ r ∈ P, (1 - 1 / ((r : ℝ) - 1) ^ 2) with hT
  have hmem : ∀ r ∈ P, r.Prime ∧ (3 : ℝ) ≤ r := by
    intro r hr
    obtain ⟨hI, hp⟩ := Finset.mem_filter.mp hr
    have : M < r := (Finset.mem_Ioc.mp hI).1
    exact ⟨hp, by exact_mod_cast (by omega : 3 ≤ r)⟩
  have hRq : cfun (y + 1) / cfun (M + 1) = R := by
    rw [cfun_split hMy, mul_div_assoc, mul_comm, div_mul_cancel₀ _ (cfun_pos (M + 1)).ne']
  have hgap : gap M y = R * T := by
    rw [hR, hT, ← Finset.prod_mul_distrib]
    unfold gap
    refine Finset.prod_congr rfl fun r hr => ?_
    have h3 := (hmem r hr).2
    have hr0 : (r : ℝ) ≠ 0 := by linarith
    have hr1 : (r : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hR0 : 0 ≤ R := by
    rw [← hRq]
    exact div_nonneg (cfun_nonneg _) (cfun_nonneg _)
  have hfac : ∀ r ∈ P, 0 ≤ 1 / ((r : ℝ) - 1) ^ 2 ∧ 1 / ((r : ℝ) - 1) ^ 2 ≤ 1 := by
    intro r hr
    have h3 := (hmem r hr).2
    have h1 : (1 : ℝ) ≤ ((r : ℝ) - 1) ^ 2 := by nlinarith
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact h1⟩
  have hT1 : T ≤ 1 :=
    (prod_mem_unit P (fun r : ℕ => 1 - 1 / ((r : ℝ) - 1) ^ 2)
      (fun r hr => sub_nonneg.mpr (hfac r hr).2)
      (fun r hr => by linarith [(hfac r hr).1])).2
  have hTlow : 1 - 1 / ((M : ℝ) - 1) ≤ T := by
    have h1 := one_sub_sum_le_prod P (fun r : ℕ => 1 / ((r : ℝ) - 1) ^ 2)
      (fun r hr => (hfac r hr).1) (fun r hr => (hfac r hr).2)
    have h2 : ∑ r ∈ P, 1 / ((r : ℝ) - 1) ^ 2 ≤ ∑ r ∈ Finset.Ioc M y, 1 / ((r : ℝ) - 1) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun r _ _ => by positivity)
    have h3 := sum_inv_sq_le hM y hMy
    have h4 : (0 : ℝ) ≤ 1 / ((y : ℝ) - 1) := by
      have : (2 : ℝ) ≤ y := by exact_mod_cast hM.trans hMy
      have : (0 : ℝ) < (y : ℝ) - 1 := by linarith
      positivity
    linarith
  rw [hRq, hgap]
  exact ⟨mul_le_mul_of_nonneg_left hTlow hR0, by nlinarith⟩

/-! ## 4. The scale law above the running maximum -/

/-- **The scale law for the gap.** Under Mertens' third theorem there are `C, y₀` with

  `|gap M y − log M / log y| ≤ C / log M`  for all integers `y₀ ≤ M ≤ y`.

With `survival_tail_eq_gap` and `cell_tail_count`: inside any type cell, given that the next
multiplier exceeds the running maximum `M`, the proportion of seeds for which it exceeds `y`
is `log M / log y` up to `O(1 / log M)`. -/
theorem gap_scale_law (h : MertensThird) :
    ∃ C y₀ : ℝ, ∀ M y : ℕ, y₀ ≤ (M : ℝ) → M ≤ y →
      |gap M y - Real.log M / Real.log y| ≤ C / Real.log M := by
  obtain ⟨C, y₀, hC⟩ := scale_law h
  refine ⟨C + 1, max y₀ 2, fun M y hM hMy => ?_⟩
  have hM2r : (2 : ℝ) ≤ M := (le_max_right _ _).trans hM
  have hM2 : 2 ≤ M := by exact_mod_cast hM2r
  have hsc := hC M y ((le_max_left _ _).trans hM) hMy
  obtain ⟨hlow, hup⟩ := gap_bounds hM2 hMy
  set R : ℝ := cfun (y + 1) / cfun (M + 1) with hR
  have hR0 : 0 ≤ R := div_nonneg (cfun_nonneg _) (cfun_nonneg _)
  have hR1 : R ≤ 1 :=
    div_le_one_of_le₀ (cfun_antitone (by omega)) (cfun_nonneg _)
  have hlog : 0 < Real.log M := Real.log_pos (by linarith)
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hinv : 1 / ((M : ℝ) - 1) ≤ 1 / Real.log M :=
    one_div_le_one_div_of_le hlog (Real.log_le_sub_one_of_pos (by linarith))
  have hinv0 : 0 ≤ 1 / ((M : ℝ) - 1) := by positivity
  have hdiff : R - 1 / Real.log M ≤ gap M y := by
    have : R * (1 / ((M : ℝ) - 1)) ≤ 1 / Real.log M :=
      (mul_le_of_le_one_left hinv0 hR1).trans hinv
    nlinarith
  obtain ⟨h1, h2⟩ := abs_le.mp hsc
  have hsplit : (C + 1) / Real.log M = C / Real.log M + 1 / Real.log M := by ring
  rw [abs_le, hsplit]
  have hpos : 0 ≤ 1 / Real.log M := by positivity
  constructor <;> linarith

end SeedScaleLaw
