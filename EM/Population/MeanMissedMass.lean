import EM.Population.AlmostAllDensity
import Mathlib.Analysis.PSeries

/-!
# The mean missed mass of a seed tends to zero, for every summable weight

2026-11-22.  A weak analytic form of the conjecture, for the seed ensemble.

For a seed `m` let `missed m` be the set of primes `q ∤ m` that the greedy rule from `m`
never selects.  For a nonnegative weight `w` on the primes put

  `mass w m = ∑_{q ∈ missed m} w q`.

`GenMullinConjecture m` says `missed m = ∅`, i.e. `mass w m = 0` for every `w`.

## Results

* `mean_missed_mass` — for every summable `w ≥ 0` and `ε > 0`, eventually
  `∑_{m ≤ X} mass w m ≤ ε · X`: the mean missed mass over seeds tends to `0`.
* `markov_missed_mass` — the seeds with `mass w m > δ` have natural density `0`.
* `mean_missed_primeZeta` — the case `w q = q^{-s}`, `s > 1`: the mean over seeds of the
  prime zeta function of the missed set, `∑_{q ∈ missed m} q^{-s}`, tends to `0`.
* `relMass_le_one`, `mean_relMass_diagonal` — the relative analytic mass
  `(∑_{q ∈ missed m} q^{-s}) / (∑_{q prime} q^{-s}) ∈ [0, 1]`, and an `s(X) ↓ 1` along which
  its mean over the seeds `m ≤ X` tends to `0` (diagonal, no rate).

## Scope — what this is not

The weight is summable.  The proof is: a finite set of primes carries all but `ε/2` of the
weight, and for each of those primes almost all seeds capture it
(`AlmostAllDensity.almost_all_genmc_density`).  It is a first-moment form of the per-prime
almost-all theorem, not more.

"The missed set of almost every seed has density zero" is a statement with a non-summable
weight: natural density weighs the primes `≤ Q` equally with `Q → ∞`, analytic density is the
limit `s → 1` of `∑_{missed} q^{-s} / ∑_{all} q^{-s}`, and the denominator diverges.  Here `s`
is fixed before `X → ∞`.  Exchanging the two limits needs control of the primes that are
large compared with the seed, where the seed carries no randomness; that is the open
simultaneous-in-`q` form (see the module docstring of `AlmostAllDensity.lean`).

Nothing is asserted about any individual seed, in particular nothing about the seed `2`.
-/

noncomputable section
open Classical

namespace MeanMissedMass

open Mullin

/-- `q` is a prime not dividing `m` that the greedy rule from `m` never selects. -/
def Missed (m q : ℕ) : Prop := q.Prime ∧ ¬ q ∣ m ∧ ¬ ∃ j, genSeq m j = q

/-- The missed mass of the seed `m` for the weight `w`. -/
def mass (w : ℕ → ℝ) (m : ℕ) : ℝ := ∑' q, if Missed m q then w q else 0

theorem summable_missed {w : ℕ → ℝ} (hw0 : ∀ q, 0 ≤ w q) (hws : Summable w) (m : ℕ) :
    Summable fun q => if Missed m q then w q else 0 :=
  Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hw0 q])
    (fun q => by split_ifs <;> simp [hw0 q]) hws

theorem mass_nonneg {w : ℕ → ℝ} (hw0 : ∀ q, 0 ≤ w q) (m : ℕ) : 0 ≤ mass w m :=
  tsum_nonneg fun q => by split_ifs <;> simp [hw0 q]

/-- Splitting the mass at a finite set `S` of primes: the part on `S` plus the tail of `w`. -/
theorem mass_le {w : ℕ → ℝ} (hw0 : ∀ q, 0 ≤ w q) (hws : Summable w) (S : Finset ℕ) (m : ℕ) :
    mass w m ≤ (∑ q ∈ S, if Missed m q then w q else 0) + ∑' q : {q // q ∉ S}, w q := by
  have hs := summable_missed hw0 hws m
  rw [mass, ← hs.sum_add_tsum_compl (s := S)]
  have htail : (∑' q : ↥((S : Set ℕ)ᶜ), if Missed m q then w q else 0) ≤
      ∑' q : {q // q ∉ S}, w q :=
    Summable.tsum_le_tsum (fun q => by split_ifs <;> simp [hw0 q.1])
      (hs.subtype _) (hws.subtype _)
  linarith

/-- **The mean missed mass tends to zero.**  For every summable nonnegative weight `w` on
the primes and every `ε > 0`, for all large `X`

  `∑_{1 ≤ m ≤ X} ∑_{q ∤ m prime, never selected from m} w q  ≤  ε · X`. -/
theorem mean_missed_mass {w : ℕ → ℝ} (hw0 : ∀ q, 0 ≤ w q) (hws : Summable w) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∑ m ∈ Finset.Icc 1 X, mass w m ≤ ε * (X : ℝ) := by
  -- a finite set carrying all but `ε/2` of the weight
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∑' q : {q // q ∉ S}, w q < ε / 2 := by
    have h := tendsto_tsum_compl_atTop_zero w
    have := (h.eventually (gt_mem_nhds (half_pos hε))).exists
    obtain ⟨S, hS⟩ := this
    exact ⟨S, hS⟩
  -- per prime of `S`: a horizon and a threshold
  set c : ℝ := 2 * ((S.card : ℝ) + 1) with hc
  have hcpos : 0 < c := by positivity
  have hper : ∀ q : ℕ, ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (∑ m ∈ Finset.Icc 1 X, if Missed m q then w q else 0) ≤ ε / c * (X : ℝ) := by
    intro q
    by_cases hq : q.Prime
    · have hδ : 0 < ε / (c * (w q + 1)) := div_pos hε (mul_pos hcpos (by linarith [hw0 q]))
      obtain ⟨n, X₀, h⟩ := AlmostAllDensity.almost_all_genmc_density q hq hδ
      refine ⟨X₀, fun X hX => ?_⟩
      have hsub : (Finset.Icc 1 X).filter (fun m => Missed m q) ⊆
          (Finset.Icc 1 X).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q) := by
        intro m hm
        rw [Finset.mem_filter] at hm ⊢
        exact ⟨hm.1, hm.2.2.1, fun ⟨j, _, hj⟩ => hm.2.2.2 ⟨j, hj⟩⟩
      have hcard : (((Finset.Icc 1 X).filter (fun m => Missed m q)).card : ℝ) ≤
          ε / (c * (w q + 1)) * (X : ℝ) :=
        le_trans (by exact_mod_cast Finset.card_le_card hsub) (h X hX)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      calc (((Finset.Icc 1 X).filter (fun m => Missed m q)).card : ℝ) * w q
          ≤ ε / (c * (w q + 1)) * (X : ℝ) * w q :=
            mul_le_mul_of_nonneg_right hcard (hw0 q)
        _ = ε / c * (X : ℝ) * (w q / (w q + 1)) := by
            have : w q + 1 ≠ 0 := by linarith [hw0 q]
            field_simp
        _ ≤ ε / c * (X : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_one (by linarith [hw0 q])]
            linarith
        _ = ε / c * (X : ℝ) := mul_one _
    · refine ⟨0, fun X _ => ?_⟩
      have : ∀ m, ¬ Missed m q := fun m h => hq h.1
      simp only [this, ite_false, Finset.sum_const_zero]
      positivity
  choose T hT using hper
  refine ⟨S.sup T, fun X hX => ?_⟩
  have hXT : ∀ q ∈ S, T q ≤ X := fun q hq => le_trans (Finset.le_sup hq) hX
  calc ∑ m ∈ Finset.Icc 1 X, mass w m
      ≤ ∑ m ∈ Finset.Icc 1 X,
          ((∑ q ∈ S, if Missed m q then w q else 0) + ∑' q : {q // q ∉ S}, w q) :=
        Finset.sum_le_sum fun m _ => mass_le hw0 hws S m
    _ = (∑ q ∈ S, ∑ m ∈ Finset.Icc 1 X, if Missed m q then w q else 0) +
          (X : ℝ) * ∑' q : {q // q ∉ S}, w q := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_const, Nat.card_Icc,
          nsmul_eq_mul]
        simp
    _ ≤ (∑ _q ∈ S, ε / c * (X : ℝ)) + (X : ℝ) * (ε / 2) := by
        gcongr with q hq
        exact hT q X (hXT q hq)
    _ = ε * (X : ℝ) * ((S.card : ℝ) / c + 1 / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ε * (X : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (S.card : ℝ) / c ≤ 1 / 2 := by
          rw [hc, div_le_iff₀ (by positivity)]
          linarith
        linarith
    _ = ε * (X : ℝ) := mul_one _

/-- **Markov.**  For every summable nonnegative weight and every `δ > 0`, the seeds whose
missed mass exceeds `δ` have natural density `0`. -/
theorem markov_missed_mass {w : ℕ → ℝ} (hw0 : ∀ q, 0 ≤ w q) (hws : Summable w) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter (fun m => δ < mass w m)).card : ℝ) ≤ ε * (X : ℝ) := by
  obtain ⟨X₀, h⟩ := mean_missed_mass hw0 hws (mul_pos hδ hε)
  refine ⟨X₀, fun X hX => ?_⟩
  have h1 : (((Finset.Icc 1 X).filter (fun m => δ < mass w m)).card : ℝ) * δ ≤
      ∑ m ∈ Finset.Icc 1 X, mass w m := by
    calc (((Finset.Icc 1 X).filter (fun m => δ < mass w m)).card : ℝ) * δ
        = ∑ _m ∈ (Finset.Icc 1 X).filter (fun m => δ < mass w m), δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ (Finset.Icc 1 X).filter (fun m => δ < mass w m), mass w m :=
          Finset.sum_le_sum fun m hm => (Finset.mem_filter.mp hm).2.le
      _ ≤ ∑ m ∈ Finset.Icc 1 X, mass w m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => mass_nonneg hw0 m
  have h2 := h X hX
  have h3 : (((Finset.Icc 1 X).filter (fun m => δ < mass w m)).card : ℝ) * δ ≤
      ε * (X : ℝ) * δ := by linarith
  exact le_of_mul_le_mul_right h3 hδ

/-- **The prime zeta function of the missed set.**  For every real `s > 1`, the mean over
seeds `m ≤ X` of `∑_{q missed by m} q^{-s}` tends to `0` as `X → ∞`. -/
theorem mean_missed_primeZeta {s : ℝ} (hs : 1 < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      ∑ m ∈ Finset.Icc 1 X, mass (fun q => ((q : ℝ) ^ s)⁻¹) m ≤ ε * (X : ℝ) :=
  mean_missed_mass (fun q => by positivity) (Real.summable_nat_rpow_inv.mpr hs) hε

/-! ## The limit `s → 1` along the seeds: relative analytic mass

The relative mass `relMass s m = (∑_{q missed by m} q^{-s}) / (∑_{q prime} q^{-s})` lies in
`[0, 1]`, and its limit as `s → 1⁺`, when it exists, is the analytic density of the missed set
of `m`.  Below, `s` tends to `1` *along* `X`: there is `s(X) ↓ 1` such that the mean of
`relMass (s X)` over the seeds `m ≤ X` tends to `0`.

This is a diagonal consequence of `mean_missed_primeZeta` and carries no rate.  The weight
`q^{-s}` lives, up to a bounded factor, on the primes `q ≤ exp(1/(s-1))`, so the statement
has the strength of the growing-range theorem (`GrowingRange.growing_range_density`): control
of the primes up to an ineffective `R(X) → ∞`.  It is not the statement that the missed set of
almost every seed has analytic density zero; that needs `s → 1` at fixed seed. -/

/-- A diagonal: if `f k X → 0` as `X → ∞` for every `k`, some `κ X → ∞` has
`f (κ X) X → 0`. -/
theorem exists_diagonal (f : ℕ → ℕ → ℝ)
    (hf : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → f k X ≤ ε) :
    ∃ κ : ℕ → ℕ, Filter.Tendsto κ Filter.atTop Filter.atTop ∧
      ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → f (κ X) X ≤ ε := by
  have hk : ∀ k : ℕ, ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → f k X ≤ 1 / ((k : ℝ) + 1) :=
    fun k => hf k _ (by positivity)
  choose T hT using hk
  let T' : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup T ⊔ k
  have hT'mono : Monotone T' := fun a b h =>
    sup_le_sup (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ h))) h
  have hTT' : ∀ k, T k ≤ T' k := fun k =>
    le_trans (Finset.le_sup (f := T) (Finset.mem_range.mpr (Nat.lt_succ_self k))) le_sup_left
  have hkT' : ∀ k, k ≤ T' k := fun k => le_sup_right
  let κ : ℕ → ℕ := fun X => Nat.findGreatest (fun k => T' k ≤ X) X
  have hκge : ∀ K X, T' K ≤ X → K ≤ κ X := fun K X h =>
    Nat.le_findGreatest (le_trans (hkT' K) h) h
  have hκspec : ∀ X, T' 0 ≤ X → T' (κ X) ≤ X := fun X h =>
    Nat.findGreatest_spec (P := fun k => T' k ≤ X) (Nat.zero_le X) h
  refine ⟨κ, Filter.tendsto_atTop_atTop.mpr fun K => ⟨T' K, fun X hX => hκge K X hX⟩, ?_⟩
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  refine ⟨T' K, fun X hX => ?_⟩
  have h0 : T' 0 ≤ X := le_trans (hT'mono (Nat.zero_le K)) hX
  have h1 := hT (κ X) X (le_trans (hTT' _) (hκspec X h0))
  have h2 : (K : ℝ) ≤ (κ X : ℝ) := by exact_mod_cast hκge K X hX
  calc f (κ X) X ≤ 1 / ((κ X : ℝ) + 1) := h1
    _ ≤ 1 / ((K : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
    _ ≤ ε := hK.le

/-- The prime zeta function at real `s`. -/
def primeZeta (s : ℝ) : ℝ := ∑' q : ℕ, if q.Prime then ((q : ℝ) ^ s)⁻¹ else 0

/-- The relative analytic mass of the missed set of `m` at `s`. -/
def relMass (s : ℝ) (m : ℕ) : ℝ := mass (fun q => ((q : ℝ) ^ s)⁻¹) m / primeZeta s

theorem summable_primeZeta {s : ℝ} (hs : 1 < s) :
    Summable fun q : ℕ => if q.Prime then ((q : ℝ) ^ s)⁻¹ else 0 :=
  Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity)
    (fun q => by split_ifs <;> first | exact le_rfl | positivity)
    (Real.summable_nat_rpow_inv.mpr hs)

theorem primeZeta_ge {s : ℝ} (hs : 1 < s) : ((2 : ℝ) ^ s)⁻¹ ≤ primeZeta s := by
  have h := (summable_primeZeta hs).le_tsum 2 (fun q _ => by split_ifs <;> positivity)
  simpa [primeZeta, Nat.prime_two] using h

theorem primeZeta_pos {s : ℝ} (hs : 1 < s) : 0 < primeZeta s :=
  lt_of_lt_of_le (by positivity) (primeZeta_ge hs)

theorem relMass_nonneg {s : ℝ} (hs : 1 < s) (m : ℕ) : 0 ≤ relMass s m :=
  div_nonneg (mass_nonneg (fun q => by positivity) m) (primeZeta_pos hs).le

/-- The relative mass is at most `1`. -/
theorem relMass_le_one {s : ℝ} (hs : 1 < s) (m : ℕ) : relMass s m ≤ 1 := by
  rw [relMass, div_le_one (primeZeta_pos hs), mass, primeZeta]
  exact Summable.tsum_le_tsum
    (fun q => by
      by_cases h : Missed m q
      · simp [h, h.1]
      · simp only [h, ite_false]; split_ifs <;> positivity)
    (summable_missed (fun q => by positivity) (Real.summable_nat_rpow_inv.mpr hs) m)
    (summable_primeZeta hs)

/-- For `1 < s ≤ 2` the relative mass is at most four times the mass. -/
theorem relMass_le {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) (m : ℕ) :
    relMass s m ≤ 4 * mass (fun q => ((q : ℝ) ^ s)⁻¹) m := by
  have hm := mass_nonneg (w := fun q : ℕ => ((q : ℝ) ^ s)⁻¹) (fun q => by positivity) m
  have h4 : (1 : ℝ) / 4 ≤ primeZeta s := by
    refine le_trans ?_ (primeZeta_ge hs)
    have : (2 : ℝ) ^ s ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs2
    have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    rw [h22] at this
    rw [one_div]
    exact inv_anti₀ (by positivity) this
  rw [relMass, div_le_iff₀ (primeZeta_pos hs)]
  nlinarith

/-- **The relative analytic mass along `s(X) → 1`.**  There is `s : ℕ → ℝ` with `s X > 1`
and `s X → 1` such that the mean over the seeds `m ≤ X` of the relative analytic mass of the
missed set at `s X` tends to `0`. -/
theorem mean_relMass_diagonal : ∃ s : ℕ → ℝ, (∀ X, 1 < s X) ∧
    Filter.Tendsto s Filter.atTop (nhds 1) ∧
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      ∑ m ∈ Finset.Icc 1 X, relMass (s X) m ≤ ε * (X : ℝ) := by
  let σ : ℕ → ℝ := fun k => 1 + 1 / ((k : ℝ) + 1)
  have hσ1 : ∀ k, 1 < σ k := fun k => by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    show 1 < 1 + 1 / ((k : ℝ) + 1)
    linarith
  have hσ2 : ∀ k, σ k ≤ 2 := fun k => by
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    show 1 + 1 / ((k : ℝ) + 1) ≤ 2
    linarith
  have hf : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (∑ m ∈ Finset.Icc 1 X, relMass (σ k) m) / (X : ℝ) ≤ ε := by
    intro k ε hε
    obtain ⟨X₀, h⟩ := mean_missed_primeZeta (hσ1 k) (show (0 : ℝ) < ε / 4 by positivity)
    refine ⟨X₀, fun X hX => ?_⟩
    rcases Nat.eq_zero_or_pos X with rfl | hXpos
    · simp [hε.le]
    · have hXr : (0 : ℝ) < X := by exact_mod_cast hXpos
      rw [div_le_iff₀ hXr]
      calc ∑ m ∈ Finset.Icc 1 X, relMass (σ k) m
          ≤ ∑ m ∈ Finset.Icc 1 X, 4 * mass (fun q => ((q : ℝ) ^ σ k)⁻¹) m :=
            Finset.sum_le_sum fun m _ => relMass_le (hσ1 k) (hσ2 k) m
        _ = 4 * ∑ m ∈ Finset.Icc 1 X, mass (fun q => ((q : ℝ) ^ σ k)⁻¹) m := by
            rw [Finset.mul_sum]
        _ ≤ 4 * (ε / 4 * (X : ℝ)) := by gcongr; exact h X hX
        _ = ε * (X : ℝ) := by ring
  obtain ⟨κ, hκ, hdiag⟩ := exists_diagonal _ hf
  refine ⟨fun X => σ (κ X), fun X => hσ1 _, ?_, ?_⟩
  · have h0 : Filter.Tendsto σ Filter.atTop (nhds 1) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
      simpa [σ] using this
    exact h0.comp hκ
  · intro ε hε
    obtain ⟨X₀, h⟩ := hdiag ε hε
    refine ⟨X₀, fun X hX => ?_⟩
    rcases Nat.eq_zero_or_pos X with rfl | hXpos
    · simp
    · have hXr : (0 : ℝ) < X := by exact_mod_cast hXpos
      exact (div_le_iff₀ hXr).mp (h X hX)

end MeanMissedMass

end
