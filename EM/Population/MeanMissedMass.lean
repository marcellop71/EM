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

end MeanMissedMass

end
