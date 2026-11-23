import EM.Population.SeedScaleLaw

/-!
# The probability of a new record

2026-11-23.

`SeedScaleLaw.lean` shows that, inside a type cell, the law of the next multiplier above the
running maximum `M` of the multipliers is free of the history. The remaining quantity is the
weight of that regime: the proportion of seeds of the cell whose next Euclid number has no
prime factor `≤ M`. By the selection law this is `survival q m M k`, and it does depend on the
history. This file bounds it from above.

A prime `r ≤ M`, `r ≠ q`, contributes a factor `1 − ρ_r` to the survival product, and the
factor is `1` in exactly two cases: `r` is in the bag (it divides the seed or is one of the
multipliers), or the current cofactor residue has already been visited at an exposed step. In
the second case `r` divides one of the numbers `p̃_j p̃_{j+1} ⋯ p̃_{k−1} − 1`, `j < k`
(`dvd_returnNumber_of_old`). So all the primes with a trivial factor divide the explicit
integer

  `D = m · c_k · W_k`,   `W_k = ∏_{j<k} (p̃_j ⋯ p̃_{k−1} − 1)`,

and every other prime has `ρ_r ≥ 1/(r − 1)`, since a box is never larger than the unit group
(`rho_ge`). Hence:

* `survival_le` — `survival q m M k ≤ ∏ (1 − 1/r)` over the primes `r ≤ M`, `r ≠ q`,
  `r ∤ D`.
* `record_le_cfun` — `survival q m M k · ∏_{r ≤ M, r = q or r ∣ D} (1 − 1/r) ≤ cfun (M+1)`,
  the Euler product over all primes `≤ M`.
* `record_le_log` — under the two-sided Mertens product bounds quoted from Tau Ceti
  (`ScaleLaw.MertensProductBounds`), the right side is at most `c / log M`.

## Reading

In every cell, the proportion of seeds whose next multiplier is a new record is at most
`(D'/φ(D')) · c / log M`, where `D'` is the part of `q · D` supported on primes `≤ M`. Up to
the arithmetic factor `D'/φ(D')`, which is `1` on average over integers and grows at most like
`log log D'`, a new record has the probability `1 / log M` that an integer has of being
`M`-rough. Together with `SeedScaleLaw.gap_scale_law`, the one-step growth law of a seed
population reads: with probability about `1/log M` the next multiplier is a record, and then
`log M / log (multiplier)` is uniform on `(0, 1)`; otherwise the step collects a prime below
the running maximum.

Population statements in the `q`-free dynamics. Nothing here concerns an individual orbit.
-/

noncomputable section
open Classical Finset

namespace RecordProbability

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw HeadDomination ScaleLaw SeedScaleLaw

variable {q m k M r : ℕ}

/-! ## 1. Primes with a trivial factor divide an explicit integer -/

/-- The return number: `∏_{j<k} (p̃_j p̃_{j+1} ⋯ p̃_{k−1} − 1)`. -/
def returnNumber (q m k : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k, (∏ i ∈ Finset.Ico j k, genSeqAvoid q m i - 1)

/-- The integer carrying all the primes whose survival factor is trivial. -/
def support (q m k : ℕ) : ℕ := m * seedCofactorAvoid q m k * returnNumber q m k

theorem cofactor_split {j : ℕ} (hjk : j ≤ k) :
    seedCofactorAvoid q m k
      = seedCofactorAvoid q m j * ∏ i ∈ Finset.Ico j k, genSeqAvoid q m i := by
  unfold seedCofactorAvoid
  exact (Finset.prod_range_mul_prod_Ico _ hjk).symm

/-- A prime in the bag divides `m · c_k`. -/
theorem dvd_of_inBag (h : inBag q m r k) : r ∣ m * seedCofactorAvoid q m k := by
  rcases h with h | ⟨j, hj, rfl⟩
  · exact Dvd.dvd.mul_right h _
  · exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)) _

/-- **Old positions are returns.** If `r` is out of the bag and the current cofactor residue
has been visited, then `r` divides `p̃_j ⋯ p̃_{k−1} − 1` for some `j < k`, hence the return
number. -/
theorem dvd_returnNumber_of_old (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hold : ¬ isNew q m r k) :
    r ∣ returnNumber q m k := by
  have : Fact r.Prime := ⟨hr⟩
  unfold isNew at hold
  rw [not_not] at hold
  obtain ⟨j, hj, -, hveq⟩ := mem_visitedAt hold
  have hcj : ((seedCofactorAvoid q m j : ℕ) : ZMod r) ≠ 0 :=
    cofactor_ne_zero_of_not_inBag hr hbag hnd hj.le
  set T := ∏ i ∈ Finset.Ico j k, genSeqAvoid q m i with hT
  have hT1 : 1 ≤ T :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i hi => by
      have := hnd i (Finset.mem_Ico.mp hi).2
      omega)
  have hsplit := cofactor_split (q := q) (m := m) hj.le
  have hcast : ((seedCofactorAvoid q m j : ℕ) : ZMod r) * ((T : ℕ) : ZMod r)
      = ((seedCofactorAvoid q m j : ℕ) : ZMod r) := by
    rw [← Nat.cast_mul, ← hsplit]
    exact hveq.symm
  have hone : ((T : ℕ) : ZMod r) = 1 := by
    have h : ((seedCofactorAvoid q m j : ℕ) : ZMod r) * (((T : ℕ) : ZMod r) - 1) = 0 := by
      rw [mul_sub, hcast, mul_one, sub_self]
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hcj
    · exact sub_eq_zero.mp h
  have hdvd : r ∣ T - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hT1, hone, Nat.cast_one, sub_self]
  exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj))

/-- A prime not dividing `support` is active at a new position. -/
theorem active_of_not_dvd (hr : r.Prime) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j)
    (hD : ¬ r ∣ support q m k) : ¬ inBag q m r k ∧ isNew q m r k := by
  have hbag : ¬ inBag q m r k := fun h => hD (Dvd.dvd.mul_right (dvd_of_inBag h) _)
  refine ⟨hbag, ?_⟩
  by_contra hold
  exact hD (Dvd.dvd.mul_left (dvd_returnNumber_of_old hr hbag hnd hold) _)

/-! ## 2. The local density is at least `1/(r − 1)` -/

/-- At an active new position the local density is at least `1/(r − 1)`: the box is nonempty
and no larger than the unit group. -/
theorem rho_ge (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime) (hrq : r ≠ q)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (h : ¬ inBag q m r k ∧ isNew q m r k) :
    1 / ((r : ℝ) - 1) ≤ rho q m r k := by
  rw [rho_of_active h]
  have hrm : ¬ r ∣ m := fun hd => h.1 (Or.inl hd)
  have hpos : 0 < boxCard q m r k := boxCard_pos hq hm hr hrq hrm h.1 hnd
  have hle : boxCard q m r k ≤ r - 1 := boxCard_le hr
  have hpos' : (0 : ℝ) < (boxCard q m r k : ℝ) := by exact_mod_cast hpos
  have hle' : (boxCard q m r k : ℝ) ≤ (r : ℝ) - 1 := by
    have : ((boxCard q m r k : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast hle
    rwa [Nat.cast_sub hr.one_le, Nat.cast_one] at this
  exact one_div_le_one_div_of_le hpos' hle'

theorem one_sub_rho_le (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime) (hrq : r ≠ q)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hD : ¬ r ∣ support q m k) :
    1 - rho q m r k ≤ 1 - (r : ℝ)⁻¹ := by
  have h1 := rho_ge hq hm hr hrq hnd (active_of_not_dvd hr hnd hD)
  have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  have h3 : (r : ℝ)⁻¹ ≤ 1 / ((r : ℝ) - 1) := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith

/-! ## 3. The upper bound for the survival product -/

/-- **The record probability, upper bound.** The survival product up to `M` is at most the
Euler product over the primes `r ≤ M`, `r ≠ q`, not dividing `support q m k`. -/
theorem survival_le (hq : q.Prime) (hm : 1 ≤ m) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j)
    (M : ℕ) :
    survival q m M k
      ≤ ∏ r ∈ (bandUpTo q M).filter (fun r => ¬ r ∣ support q m k), (1 - (r : ℝ)⁻¹) := by
  unfold survival
  rw [← Finset.prod_filter_mul_prod_filter_not (bandUpTo q M) (fun r => ¬ r ∣ support q m k)]
  have hfac : ∀ r ∈ bandUpTo q M, 0 ≤ 1 - rho q m r k ∧ 1 - rho q m r k ≤ 1 := by
    intro r hr
    obtain ⟨-, hp, hrq⟩ := mem_bandUpTo.mp hr
    exact ⟨sub_nonneg.mpr (rho_le_one hq hm hp hrq hnd), by
      have := rho_nonneg (q := q) (m := m) (r := r) (k := k)
      linarith⟩
  have h1 : ∏ r ∈ (bandUpTo q M).filter (fun r => ¬ r ∣ support q m k), (1 - rho q m r k)
      ≤ ∏ r ∈ (bandUpTo q M).filter (fun r => ¬ r ∣ support q m k), (1 - (r : ℝ)⁻¹) := by
    refine Finset.prod_le_prod₀ (fun r hr => (hfac r (Finset.mem_filter.mp hr).1).1) ?_
    intro r hr
    obtain ⟨hband, hD⟩ := Finset.mem_filter.mp hr
    obtain ⟨-, hp, hrq⟩ := mem_bandUpTo.mp hband
    exact one_sub_rho_le hq hm hp hrq hnd hD
  have h2 := prod_mem_unit ((bandUpTo q M).filter (fun r => ¬ ¬ r ∣ support q m k))
    (fun r : ℕ => 1 - rho q m r k) (fun r hr => (hfac r (Finset.mem_filter.mp hr).1).1)
    (fun r hr => (hfac r (Finset.mem_filter.mp hr).1).2)
  have h0 := prod_mem_unit ((bandUpTo q M).filter (fun r => ¬ r ∣ support q m k))
    (fun r : ℕ => 1 - rho q m r k) (fun r hr => (hfac r (Finset.mem_filter.mp hr).1).1)
    (fun r hr => (hfac r (Finset.mem_filter.mp hr).1).2)
  exact (mul_le_of_le_one_right h0.1 h2.2).trans h1

/-- The primes `≤ M` that are `q` or divide `support q m k`. -/
def excluded (q m k M : ℕ) : Finset ℕ :=
  ((Finset.range (M + 1)).filter Nat.Prime).filter (fun r => ¬ (r ≠ q ∧ ¬ r ∣ support q m k))

theorem euler_factor_mem {r : ℕ} (hr : r.Prime) :
    0 ≤ 1 - (r : ℝ)⁻¹ ∧ 1 - (r : ℝ)⁻¹ ≤ 1 := by
  have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.two_le
  have h0 : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  have h1 : (r : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- **The record probability against the full Euler product.**
`survival q m M k · ∏_{r ∈ excluded} (1 − 1/r) ≤ cfun (M + 1) = ∏_{r ≤ M} (1 − 1/r)`. -/
theorem record_le_cfun (hq : q.Prime) (hm : 1 ≤ m) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j)
    (M : ℕ) :
    survival q m M k * ∏ r ∈ excluded q m k M, (1 - (r : ℝ)⁻¹) ≤ cfun (M + 1) := by
  rw [cfun_eq_prod, ← Finset.prod_filter_mul_prod_filter_not
    ((range (M + 1)).filter Nat.Prime) (fun r => r ≠ q ∧ ¬ r ∣ support q m k)]
  have hset : ((range (M + 1)).filter Nat.Prime).filter
      (fun r => r ≠ q ∧ ¬ r ∣ support q m k)
      = (bandUpTo q M).filter (fun r => ¬ r ∣ support q m k) := by
    ext r
    simp only [Finset.mem_filter, bandUpTo]
    tauto
  rw [hset]
  refine mul_le_mul_of_nonneg_right (survival_le hq hm hnd M) ?_
  exact (prod_mem_unit _ (fun r : ℕ => 1 - (r : ℝ)⁻¹)
    (fun r hr => (euler_factor_mem (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2).1)
    (fun r hr => (euler_factor_mem (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2).2)).1

/-- **A new record has probability `O(1 / log M)`, up to the excluded primes.** Under the
two-sided Mertens product bounds there is `c` such that for every cell and every `M ≥ 2`,

  `survival q m M k · ∏_{r ∈ excluded} (1 − 1/r) ≤ c / log M`. -/
theorem record_le_log (h : MertensProductBounds) :
    ∃ c : ℝ, 0 < c ∧ ∀ q m k M : ℕ, q.Prime → 1 ≤ m → (∀ j < k, 2 ≤ genSeqAvoid q m j) →
      2 ≤ M →
      survival q m M k * ∏ r ∈ excluded q m k M, (1 - (r : ℝ)⁻¹) ≤ c / Real.log M := by
  obtain ⟨c₁, c₂, -, hc₂, hb⟩ := h
  refine ⟨c₂, hc₂, fun q m k M hq hm hnd hM => ?_⟩
  have h2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hup := (hb M h2).2
  rw [Nat.floor_natCast, ← cfun_succ_eq_prod_primesLE] at hup
  exact (record_le_cfun hq hm hnd M).trans hup

end RecordProbability
